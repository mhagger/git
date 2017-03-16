#include "../cache.h"
#include "../refs.h"
#include "refs-internal.h"
#include "ref-cache.h"
#include "packed-backend.h"
#include "../iterator.h"
#include "../dir-iterator.h"
#include "../tempfile.h"
#include "../lockfile.h"
#include "../object.h"
#include "../dir.h"

/*
 * Return true if refname, which has the specified oid and flags, can
 * be resolved to an object in the database. If the referred-to object
 * does not exist, emit a warning and return false.
 *
 * FIXME: there are currently two copies of this function.
 */
static int ref_resolves_to_object(const char *refname,
				  const struct object_id *oid,
				  unsigned int flags)
{
	if (flags & REF_ISBROKEN)
		return 0;
	if (!has_sha1_file(oid->hash)) {
		error("%s does not point to a valid object!", refname);
		return 0;
	}
	return 1;
}

/*
 * This basically represents one "snapshot" of the packed-refs file.
 * Its validity can be checked via its `validity` member, and it can
 * be replaced in `packed_ref_store` by a newer snapshot.
 *
 * The packed-refs file can be locked using `packed_refs_lock()`,
 * which creates a `packed-refs.lock` file and points the current
 * `packed_ref_cache`'s `lock` member at the resulting `lock_file`
 * instance. In that case the snapshot *cannot* spontaneously become
 * stale (assuming that everybody touching the Git repository is
 * adhering to the usual lock protocol). The lock is relinquished by
 * calling `packed_refs_unlock()`.
 *
 * These instances are reference-counted because they mustn't
 * disappear while somebody is using (e.g., iterating over) them. So
 * before using one, call `acquire_packed_ref_cache()`, which
 * increments the `referrers` count. When you are done with it, call
 * `release_packed_ref_cache()`, which decrements the reference count
 * and possibly frees the memory associated with the instance.
 * (Locking/unlocking the `packed-refs` file as described in the
 * previous paragraph also increments/decrements the reference count.)
 */
struct packed_ref_cache {
	struct ref_cache *cache;

	/*
	 * What is the peeled state of this cache? (This is usually
	 * determined from the header of the "packed-refs" file.)
	 */
	enum { PEELED_NONE, PEELED_TAGS, PEELED_FULLY } peeled;

	/*
	 * Count of references to the data structure in this instance,
	 * including the pointer from packed_ref_store::cache if any.
	 * The data will not be freed until the reference count
	 * reaches zero.
	 */
	unsigned int referrers;

	/*
	 * The `packed-refs` file metadata from when this packed-refs
	 * cache was read. It is used to determine when the file has
	 * changed out from under us.
	 */
	struct stat_validity validity;
};

/*
 * Increment the reference count of *packed_refs.
 */
static void acquire_packed_ref_cache(struct packed_ref_cache *packed_refs)
{
	packed_refs->referrers++;
}

/*
 * Decrease the reference count of *packed_refs. If it goes to zero,
 * free *packed_refs and return true; otherwise return false.
 */
static int release_packed_ref_cache(struct packed_ref_cache *packed_refs)
{
	if (!--packed_refs->referrers) {
		free_ref_cache(packed_refs->cache);
		stat_validity_clear(&packed_refs->validity);
		free(packed_refs);
		return 1;
	} else {
		return 0;
	}
}

struct packed_ref_store {
	struct ref_store base;
	unsigned int store_flags;

	char *packed_refs_path;

	/*
	 * A cache of the values read from the `packed-refs` file, if
	 * it might still be current; otherwise, NULL.
	 */
	struct packed_ref_cache *cache;

	/*
	 * Lock used for the "packed-refs" file. Note that this (and
	 * thus the enclosing packed_ref_store) must not be freed.
	 */
	struct lock_file lock;

	/*
	 * Temporary file used when rewriting new contents to the
	 * "packed-refs" file. Note that this (and thus the enclosing
	 * `packed_ref_store`) must not be freed.
	 */
	struct tempfile packtemp;
};

/*
 * Any cached values are thought/known to be stale. Clear them (though
 * the data might still be retained for a while if somebody is
 * currently iterating through them).
 *
 * Normally it is an error to call this function while the
 * `packed-refs` file is locked, because it normally shouldn't be
 * necessary, and we don't want some random caller of
 * `get_packed_ref_cache()` to trigger a cache refresh in this
 * situation. But if `allow_locked` is set, that restriction is
 * removed. A caller might use that option if the caller itself just
 * rewrote the `packed-refs` file while retaining the lock.
 */
static void clear_packed_ref_cache(struct packed_ref_store *refs,
				   int allow_locked)
{
	if (refs->cache) {
		struct packed_ref_cache *packed_refs = refs->cache;

		if (!allow_locked && is_lock_file_locked(&refs->lock))
			die("internal error: packed-ref cache cleared while locked");
		refs->cache = NULL;
		release_packed_ref_cache(packed_refs);
	}
}

/*
 * Create a new packed_ref_store for the specified directory.
 */
struct ref_store *packed_ref_store_create(const char *gitdir,
					  unsigned int flags)
{
	struct packed_ref_store *refs = xcalloc(1, sizeof(*refs));
	struct ref_store *ref_store = (struct ref_store *)refs;
	struct strbuf sb = STRBUF_INIT;

	base_ref_store_init(ref_store, &refs_be_packed);
	refs->store_flags = flags;

	get_common_dir_noenv(&sb, gitdir);
	strbuf_addstr(&sb, "/packed-refs");
	refs->packed_refs_path = strbuf_detach(&sb, NULL);

	return ref_store;
}

/*
 * Die if refs is not the main ref store. caller is used in any
 * necessary error messages.
 */
static void packed_assert_main_repository(struct packed_ref_store *refs,
					 const char *caller)
{
	if (refs->store_flags & REF_STORE_MAIN)
		return;

	die("BUG: unallowed operation (%s), only works "
	    "on main ref store\n", caller);
}

/*
 * Downcast ref_store to packed_ref_store. Die if ref_store is not a
 * packed_ref_store. Also die if `packed_ref_store` doesn't support at
 * least the flags specified in `required_flags`. caller is used in
 * any necessary error messages.
 */
static struct packed_ref_store *packed_downcast(struct ref_store *ref_store,
						unsigned int required_flags,
						const char *caller)
{
	struct packed_ref_store *refs;

	if (ref_store->be != &refs_be_packed)
		die("BUG: ref_store is type \"%s\" not \"packed\" in %s",
		    ref_store->be->name, caller);

	refs = (struct packed_ref_store *)ref_store;

	if ((refs->store_flags & required_flags) != required_flags)
		die("BUG: unallowed operation (%s), requires %x, has %x\n",
		    caller, required_flags, refs->store_flags);

	return refs;
}

/* The length of a peeled reference line in packed-refs, including EOL: */
#define PEELED_LINE_LENGTH 42

/*
 * The packed-refs header line that we write out.  Perhaps other
 * traits will be added later.  The trailing space is required.
 */
static const char PACKED_REFS_HEADER[] =
	"# pack-refs with: peeled fully-peeled \n";

/*
 * Parse one line from a packed-refs file.  Write the SHA1 to sha1.
 * Return a pointer to the refname within the line (null-terminated),
 * or NULL if there was a problem.
 */
static const char *parse_ref_line(struct strbuf *line, unsigned char *sha1)
{
	const char *ref;

	/*
	 * 42: the answer to everything.
	 *
	 * In this case, it happens to be the answer to
	 *  40 (length of sha1 hex representation)
	 *  +1 (space in between hex and name)
	 *  +1 (newline at the end of the line)
	 */
	if (line->len <= 42)
		return NULL;

	if (get_sha1_hex(line->buf, sha1) < 0)
		return NULL;
	if (!isspace(line->buf[40]))
		return NULL;

	ref = line->buf + 41;
	if (isspace(*ref))
		return NULL;

	if (line->buf[line->len - 1] != '\n')
		return NULL;
	line->buf[--line->len] = 0;

	return ref;
}

static const char *packed_packed_refs_path(struct packed_ref_store *refs)
{
	return refs->packed_refs_path;
}

/*
 * Create and return a `packed_ref_cache` object representing the
 * current contents of the `packed-refs` file for the specified
 * `packed_ref_store`.
 *
 * A comment line of the form "# pack-refs with: " may contain zero or
 * more traits. We interpret the traits as follows:
 *
 *   No traits:
 *
 *      Probably no references are peeled. But if the file contains a
 *      peeled value for a reference, we will use it.
 *
 *   peeled:
 *
 *      References under "refs/tags/", if they *can* be peeled, *are*
 *      peeled in this file. References outside of "refs/tags/" are
 *      probably not peeled even if they could have been, but if we find
 *      a peeled value for such a reference we will use it.
 *
 *   fully-peeled:
 *
 *      All references in the file that can be peeled are peeled.
 *      Inversely (and this is more important), any references in the
 *      file for which no peeled value is recorded is not peelable. This
 *      trait should typically be written alongside "peeled" for
 *      compatibility with older clients, but we do not require it
 *      (i.e., "peeled" is a no-op if "fully-peeled" is set).
 */
static struct packed_ref_cache *read_packed_refs(struct packed_ref_store *refs)
{
	struct packed_ref_cache *cache;
	struct ref_dir *dir;
	struct ref_entry *last = NULL;
	struct strbuf line = STRBUF_INIT;
	const char *packed_refs_file = packed_packed_refs_path(refs);
	int fd;
	struct stat st;
	char *buf;
	const char *p, *end;
	size_t size, len;

	cache = xcalloc(1, sizeof(*cache));
	cache->cache = create_ref_cache(&refs->base, NULL);
	cache->cache->root->flag &= ~REF_INCOMPLETE;
	fd = open(packed_refs_file, O_RDONLY);
	if (fd < 0) {
		if (errno == ENOENT) {
			/*
			 * This is OK; it just means that no
			 * "packed-refs" file has been written yet,
			 * which is equivalent to it being empty.
			 */
			return cache;
		} else {
			die("couldn't read %s: %s",
			    packed_refs_file, strerror(errno));
		}
	}

	stat_validity_update(&cache->validity, fd);

	if (fstat(fd, &st) < 0)
		die("couldn't stat %s: %s", packed_refs_file, strerror(errno));
	size = xsize_t(st.st_size);
	buf = xmmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);

	cache->peeled = PEELED_NONE;

	dir = get_ref_dir(cache->cache->root);

	p = buf;
	len = size;
	while (len) {
		unsigned char sha1[20];
		const char *refname;
		const char *traits;

		end = memchr(p, '\n', len);
		if (!end)
			die("packed-refs contents are truncated");

		end++; /* Include the LF */
		strbuf_add(&line, p, end - p);

		if (skip_prefix(line.buf, "# pack-refs with:", &traits)) {
			if (strstr(traits, " fully-peeled "))
				cache->peeled = PEELED_FULLY;
			else if (strstr(traits, " peeled "))
				cache->peeled = PEELED_TAGS;
			/* perhaps other traits later as well */
			goto next_line;
		}

		refname = parse_ref_line(&line, sha1);
		if (refname) {
			int flag = REF_ISPACKED;

			if (check_refname_format(refname, REFNAME_ALLOW_ONELEVEL)) {
				if (!refname_is_safe(refname))
					die("packed refname is dangerous: %s", refname);
				hashclr(sha1);
				flag |= REF_BAD_NAME | REF_ISBROKEN;
			}
			last = create_ref_entry(refname, sha1, flag, 0);
			if (cache->peeled == PEELED_FULLY ||
			    (cache->peeled == PEELED_TAGS && starts_with(refname, "refs/tags/")))
				last->flag |= REF_KNOWS_PEELED;
			add_ref_entry(dir, last);
			goto next_line;
		}
		if (last &&
		    line.buf[0] == '^' &&
		    line.len == PEELED_LINE_LENGTH &&
		    line.buf[PEELED_LINE_LENGTH - 1] == '\n' &&
		    !get_sha1_hex(line.buf + 1, sha1)) {
			hashcpy(last->u.value.peeled.hash, sha1);
			/*
			 * Regardless of what the file header said,
			 * we definitely know the value of *this*
			 * reference:
			 */
			last->flag |= REF_KNOWS_PEELED;
		}

	next_line:
		len -= end - p;
		p = end;
		strbuf_reset(&line);
	}

	if (munmap(buf, size))
		die("error ummapping packed-refs file: %s", strerror(errno));
	close(fd);

	strbuf_release(&line);
	return cache;
}

/*
 * Get the packed_ref_cache for the specified packed_ref_store,
 * creating and populating it if it hasn't been read before or if the
 * file has been changed (according to its `validity` field) since it
 * was last read. On the other hand, if we hold the lock, then assume
 * that the file hasn't been changed out from under us, so skip the
 * extra `stat()` call in `stat_validity_check()`.
 */
static struct packed_ref_cache *get_packed_ref_cache(struct packed_ref_store *refs)
{
	const char *packed_refs_file = packed_packed_refs_path(refs);

	if (refs->cache &&
	    //FIXME: Is this still legit?:
	    //!is_lock_file_locked(&refs->lock) &&
	    !stat_validity_check(&refs->cache->validity, packed_refs_file))
		clear_packed_ref_cache(refs, 0);

	if (!refs->cache) {
		refs->cache = read_packed_refs(refs);
		acquire_packed_ref_cache(refs->cache);
	}


	return refs->cache;
}

/*
 * Return the `ref_dir` for the specified `packed_ref_cache` (which
 * might not be the current one).
 */
static struct ref_dir *get_packed_ref_dir(struct packed_ref_cache *packed_ref_cache)
{
	return get_ref_dir(packed_ref_cache->cache->root);
}

/*
 * Return the `ref_dir` for the current `packed_ref_cache` for the
 * specified `packed_ref_store` (freshening it if needed).
 */
static struct ref_dir *get_packed_refs(struct packed_ref_store *refs)
{
	return get_packed_ref_dir(get_packed_ref_cache(refs));
}

/*
 * Return the ref_entry for the given refname from the packed
 * references.  If it does not exist, return NULL.
 */
static struct ref_entry *get_packed_ref(struct packed_ref_store *refs,
					const char *refname)
{
	return find_ref_entry(get_packed_refs(refs), refname);
}

static int packed_read_raw_ref(struct ref_store *ref_store,
			      const char *refname, unsigned char *sha1,
			      struct strbuf *referent, unsigned int *type)
{
	struct packed_ref_store *refs =
		packed_downcast(ref_store, REF_STORE_READ, "read_raw_ref");
	struct ref_entry *entry;

	*type = 0;

	entry = get_packed_ref(refs, refname);
	if (!entry) {
		/* refname is not a packed reference. */
		errno = ENOENT;
		return -1;
	}

	hashcpy(sha1, entry->u.value.oid.hash);
	*type = REF_ISPACKED;
	return 0;
}

static int packed_peel_ref(struct ref_store *ref_store,
			   const char *refname, unsigned char *sha1)
{
	struct packed_ref_store *refs =
		packed_downcast(ref_store, REF_STORE_READ | REF_STORE_ODB,
				"peel_ref");
	int flag;
	unsigned char base[20];

	(void)refs; /* FIXME: we need the check, but not the value */

	if (current_ref_iter && current_ref_iter->refname == refname) {
		struct object_id peeled;

		if (ref_iterator_peel(current_ref_iter, &peeled))
			return -1;
		hashcpy(sha1, peeled.hash);
		return 0;
	}

	if (refs_read_ref_full(ref_store, refname,
			       RESOLVE_REF_READING, base, &flag))
		return -1;

	return peel_object(base, sha1);
}

struct packed_ref_iterator {
	struct ref_iterator base;

	struct packed_ref_cache *packed_ref_cache;
	struct ref_iterator *iter0;
	unsigned int flags;
};

static int packed_ref_iterator_advance(struct ref_iterator *ref_iterator)
{
	struct packed_ref_iterator *iter =
		(struct packed_ref_iterator *)ref_iterator;
	int ok;

	while ((ok = ref_iterator_advance(iter->iter0)) == ITER_OK) {
		if (iter->flags & DO_FOR_EACH_PER_WORKTREE_ONLY &&
		    ref_type(iter->iter0->refname) != REF_TYPE_PER_WORKTREE)
			continue;

		if (!(iter->flags & DO_FOR_EACH_INCLUDE_BROKEN) &&
		    !ref_resolves_to_object(iter->iter0->refname,
					    iter->iter0->oid,
					    iter->iter0->flags))
			continue;

		iter->base.refname = iter->iter0->refname;
		iter->base.oid = iter->iter0->oid;
		iter->base.flags = iter->iter0->flags;
		return ITER_OK;
	}

	iter->iter0 = NULL;
	if (ref_iterator_abort(ref_iterator) != ITER_DONE)
		ok = ITER_ERROR;

	return ok;
}

static int packed_ref_iterator_peel(struct ref_iterator *ref_iterator,
				   struct object_id *peeled)
{
	struct packed_ref_iterator *iter =
		(struct packed_ref_iterator *)ref_iterator;

	return ref_iterator_peel(iter->iter0, peeled);
}

static int packed_ref_iterator_abort(struct ref_iterator *ref_iterator)
{
	struct packed_ref_iterator *iter =
		(struct packed_ref_iterator *)ref_iterator;
	int ok = ITER_DONE;

	if (iter->iter0)
		ok = ref_iterator_abort(iter->iter0);

	release_packed_ref_cache(iter->packed_ref_cache);
	base_ref_iterator_free(ref_iterator);
	return ok;
}

static struct ref_iterator_vtable packed_ref_iterator_vtable = {
	packed_ref_iterator_advance,
	packed_ref_iterator_peel,
	packed_ref_iterator_abort
};

/*
 * Note that the packed-refs that the iterator sees are a snapshot of
 * those that are in the `packed-refs` file when this function is
 * called. (This is important for guaranteeing the right order of
 * packed/loose reference reads.)
 */
static struct ref_iterator *packed_ref_iterator_begin(
		struct ref_store *ref_store,
		const char *prefix, unsigned int flags)
{
	struct packed_ref_store *refs;
	struct ref_iterator *packed_iter;
	struct packed_ref_iterator *iter;
	struct ref_iterator *ref_iterator;

	// FIXME: are we handling GIT_REF_PARANOIA correctly?

	if (ref_paranoia < 0)
		ref_paranoia = git_env_bool("GIT_REF_PARANOIA", 0);
	if (ref_paranoia)
		flags |= DO_FOR_EACH_INCLUDE_BROKEN;

	refs = packed_downcast(ref_store,
			       REF_STORE_READ | (ref_paranoia ? 0 : REF_STORE_ODB),
			       "ref_iterator_begin");

	iter = xcalloc(1, sizeof(*iter));
	ref_iterator = &iter->base;
	base_ref_iterator_init(ref_iterator, &packed_ref_iterator_vtable);

	iter->packed_ref_cache = get_packed_ref_cache(refs);
	acquire_packed_ref_cache(iter->packed_ref_cache);
	packed_iter = cache_ref_iterator_begin(iter->packed_ref_cache->cache,
					       prefix, 0);
	iter->iter0 = packed_iter;
	iter->flags = flags;

	return ref_iterator;
}

int packed_refs_lock(struct ref_store *ref_store, int flags)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE,
			"packed_refs_lock");
	static int timeout_configured = 0;
	static int timeout_value = 1000;
	struct packed_ref_cache *packed_ref_cache;

	packed_assert_main_repository(refs, "packed_refs_lock");

	if (!timeout_configured) {
		git_config_get_int("core.packedrefstimeout", &timeout_value);
		timeout_configured = 1;
	}

	/*
	 * Note that we close the lockfile immediately because we
	 * don't write new content to it, but rather to a separate
	 * tempfile.
	 */
	if (hold_lock_file_for_update_timeout(
			    &refs->lock, packed_packed_refs_path(refs),
			    flags, timeout_value) < 0 ||
	    close_lock_file(&refs->lock))
		return -1;
	/*
	 * Get the current packed-refs while holding the lock. It is
	 * important that we call `get_packed_ref_cache()` before
	 * setting `packed_ref_cache->lock`, because otherwise the
	 * former will see that the file is locked and assume that the
	 * cache can't be stale.
	 */
	// FIXME: The above important thing isn't the case anymore.
	packed_ref_cache = get_packed_ref_cache(refs);
	/* Increment the reference count to prevent it from being freed: */
	acquire_packed_ref_cache(packed_ref_cache);
	return 0;
}

void packed_refs_unlock(struct ref_store *ref_store)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE,
			"packed_refs_lock");

	if (!is_lock_file_locked(&refs->lock))
		die("BUG: packed_refs_unlock() called when not locked");
	rollback_lock_file(&refs->lock);
}

int packed_refs_is_locked(struct ref_store *ref_store)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE,
			"packed_refs_is_locked");

	return is_lock_file_locked(&refs->lock);
}

/*
 * Rollback the tempfile, if active, for the packed-refs file. This
 * must only be called while the lock is held.
 */
static void rollback_packed_refs(struct packed_ref_store *refs)
{
	struct packed_ref_cache *packed_ref_cache =
		get_packed_ref_cache(refs);

	packed_assert_main_repository(refs, "rollback_packed_refs");

	if (!packed_ref_cache || !is_lock_file_locked(&refs->lock))
		die("BUG: rollback_packed_refs() called when not locked");
	if (is_tempfile_active(&refs->packtemp))
		delete_tempfile(&refs->packtemp);
}

/*
 * Commit the packed-refs changes that have been written to
 * "packed-refs.new" by renaming them on top of "packed-refs". This
 * must only be called when the file is locked. It does not release
 * the lock.
 */
static int commit_packed_refs(struct packed_ref_store *refs)
{
	int ret = 0;
	int save_errno = 0;

	packed_assert_main_repository(refs, "rollback_packed_refs");

	if (!is_lock_file_locked(&refs->lock))
		die("BUG: commit_packed_refs() called when not locked");
	if (!is_tempfile_active(&refs->packtemp))
		die("BUG: commit_packed_refs() called when no content written");

	// FIXME: add a sanity check that the cache is still fresh.

	if (rename_tempfile(&refs->packtemp, packed_packed_refs_path(refs))) {
		save_errno = errno;
		ret = -1;
	}

	clear_packed_ref_cache(refs, 1);

	errno = save_errno;
	return ret;
}

static int packed_pack_refs(struct ref_store *ref_store, unsigned int flags)
{
	/*
	 * Packed refs are already packed. It might be that loose refs
	 * are packed *into* a packed refs store, but that is done by
	 * updating the packed references via a transaction.
	 */
	return 0;
}

/*
 * Write an entry to the packed-refs file for the specified refname.
 * If peeled is non-NULL, write it as the entry's peeled value.
 */
static void write_packed_entry(FILE *fh, const char *refname,
			       const unsigned char *sha1,
			       const unsigned char *peeled)
{
	fprintf_or_die(fh, "%s %s\n", sha1_to_hex(sha1), refname);
	if (peeled)
		fprintf_or_die(fh, "^%s\n", sha1_to_hex(peeled));
}

/*
 * Write the packed-refs from the cache to the packed-refs tempfile,
 * incorporating any changes from `updates`. `updates` must be a
 * sorted string list whose keys are the refnames and whose util
 * values are `struct ref_update *`. On error, rollback the tempfile,
 * write an error message to `err`, and return a nonzero value.
 *
 * The packfile must be locked before calling this function.
 *
 * `err` must not be NULL.
 */
static int write_with_updates(struct packed_ref_store *refs,
			       struct string_list *updates,
			       struct strbuf *err)
{
	struct ref_iterator *iter;
	size_t i;
	int ok;
	FILE *fh;
	struct strbuf sb = STRBUF_INIT;

	if (!is_lock_file_locked(&refs->lock))
		die("BUG: write_with_updates() called while unlocked");

	strbuf_addf(&sb, "%s.new", packed_packed_refs_path(refs));
	if (create_tempfile(&refs->packtemp, sb.buf) < 0) {
		strbuf_addf(err, "unable to create file %s: %s",
			    sb.buf, strerror(errno));
		strbuf_release(&sb);
		return -1;
	}
	strbuf_release(&sb);

	fh = fdopen_tempfile(&refs->packtemp, "w");

	fprintf_or_die(fh, "%s", PACKED_REFS_HEADER);

	/*
	 * We iterate in parallel through the current list of refs and
	 * the list of updates, processing an entry from at least one
	 * of the lists each time through the loop. When the current
	 * list of refs is exhausted, set iter to NULL. When the list
	 * of updates is exhausted, leave i set to updates->nr.
	 */
	// FIXME: do we handle broken references correctly here? It's
	// OK for packed references to point at missing objects, in
	// which case either the old values should be carried along
	// without objections, or they should be elided from the new
	// file entirely.
	iter = packed_ref_iterator_begin(&refs->base, "",
					 DO_FOR_EACH_INCLUDE_BROKEN);
	if ((ok = ref_iterator_advance(iter)) != ITER_OK)
		iter = NULL;

	i = 0;

	while (iter || i < updates->nr) {
		struct ref_update *update;
		int cmp;

		if (i >= updates->nr) {
			cmp = -1;
		} else {
			update = updates->items[i].util;

			if (!iter)
				cmp = +1;
			else
				cmp = strcmp(iter->refname, update->refname);
		}

		if (!cmp) {
			/*
			 * There are an existing reference and an
			 * update with the same refname. Figure out
			 * what to do.
			 */
			if ((update->flags & REF_HAVE_NEW)) {
				/*
				 * The update takes precedence. Skip
				 * the iterator over the unneeded
				 * value.
				 */
				if ((ok = ref_iterator_advance(iter)) != ITER_OK)
					iter = NULL;
				cmp = +1;
			} else {
				/*
				 * The update doesn't actually want to
				 * change anything. Ignore it.
				 */
				i++;
				cmp = -1;
			}
		}

		if (cmp < 0) {
			struct object_id peeled;
			int peel_error;

			/* Pass the old reference through. */
			peel_error = ref_iterator_peel(iter, &peeled);

			write_packed_entry(fh, iter->refname, iter->oid->hash,
					   peel_error ? NULL : peeled.hash);
			if ((ok = ref_iterator_advance(iter)) != ITER_OK)
				iter = NULL;
		} else if (is_null_sha1(update->new_sha1)) {
			/*
			 * The update wants to delete the reference,
			 * and the reference either didn't exist or we
			 * have already skipped it. So we're done with
			 * the update (and don't have to write
			 * anything).
			 */
			i++;
		} else {
			struct object_id peeled;
			int peel_error;

			peel_error = peel_object(update->new_sha1, peeled.hash);

			write_packed_entry(fh, update->refname, update->new_sha1,
					   peel_error ? NULL : peeled.hash);
			i++;
		}
	}

	if (ok != ITER_DONE) {
		strbuf_addf(err, "unable to write packed-refs file: "
			    "error iterating over old contents");
		delete_tempfile(&refs->packtemp);
		return -1;
	}

	if (close_tempfile(&refs->packtemp)) {
		strbuf_addf(err, "error closing file %s: %s",
			    get_tempfile_path(&refs->packtemp),
			    strerror(errno));
		strbuf_release(&sb);
		return -1;
	}

	return 0;
}

static int packed_delete_refs(struct ref_store *ref_store,
			     struct string_list *refnames, unsigned int flags)
{
	struct packed_ref_store *refs =
		packed_downcast(ref_store, REF_STORE_WRITE, "delete_refs");
	struct strbuf err = STRBUF_INIT;
	struct ref_transaction *transaction;
	struct string_list_item *item;
	int result = 0;

	(void) refs; /* FIXME: we need the check above, but don't use the variable */

	if (!refnames->nr)
		return 0;

	transaction = ref_store_transaction_begin(ref_store, &err);
	if (!transaction)
		return -1;

	for_each_string_list_item(item, refnames) {
		if (ref_transaction_delete(transaction, item->string, NULL,
					   flags, NULL, &err)) {
			result = -1;
			break;
		}
	}

	if (!result)
		result = ref_transaction_commit(transaction, &err);

	if (result) {
		if (refnames->nr == 1)
			error(_("could not delete reference %s: %s"),
			      refnames->items[0].string, err.buf);
		else
			error(_("could not delete references: %s"), err.buf);
	}

	strbuf_release(&err);
	return result;
}

static int packed_rename_ref(struct ref_store *ref_store,
			    const char *oldrefname, const char *newrefname,
			    const char *logmsg)
{
	die("BUG: packed reference store does not support renaming references");
}

static int packed_create_reflog(struct ref_store *ref_store,
			       const char *refname, int force_create,
			       struct strbuf *err)
{
	die("BUG: packed reference store does not support reflogs");
}

static int packed_create_symref(struct ref_store *ref_store,
			       const char *refname, const char *target,
			       const char *logmsg)
{
	die("BUG: packed reference store does not support symrefs");
}

static int packed_reflog_exists(struct ref_store *ref_store,
			       const char *refname)
{
	die("BUG: packed reference store does not support reflogs");
}

static int packed_delete_reflog(struct ref_store *ref_store,
			       const char *refname)
{
	die("BUG: packed reference store does not support reflogs");
}

static int packed_for_each_reflog_ent_reverse(struct ref_store *ref_store,
					      const char *refname,
					      each_reflog_ent_fn fn,
					      void *cb_data)
{
	die("BUG: packed reference store does not support reflogs");
}

static int packed_for_each_reflog_ent(struct ref_store *ref_store,
				      const char *refname,
				      each_reflog_ent_fn fn, void *cb_data)
{
	die("BUG: packed reference store does not support reflogs");
}

static struct ref_iterator *packed_reflog_iterator_begin(struct ref_store *ref_store)
{
	die("BUG: packed reference store does not support reflogs");
}

struct packed_transaction_backend_data {
	/* True iff the transaction owns the packed-refs lock. */
	int own_lock;

	struct string_list updates;
};

static void packed_transaction_cleanup(struct packed_ref_store *refs,
				       struct ref_transaction *transaction)
{
	struct packed_transaction_backend_data *data = transaction->backend_data;

	if (data) {
		string_list_clear(&data->updates, 0);

		if (is_tempfile_active(&refs->packtemp))
			rollback_packed_refs(refs);

		if (data->own_lock && is_lock_file_locked(&refs->lock)) {
			packed_refs_unlock(&refs->base);
			data->own_lock = 0;
		}

		free(data);
		transaction->backend_data = NULL;
	}

	transaction->state = REF_TRANSACTION_CLOSED;
}

static int packed_transaction_prepare(struct ref_store *ref_store,
				      struct ref_transaction *transaction,
				      struct strbuf *err)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE | REF_STORE_ODB,
			"ref_transaction_commit");
	struct packed_transaction_backend_data *data;
	size_t i;
	int ret = TRANSACTION_GENERIC_ERROR;

	assert(err);

	if (transaction->state != REF_TRANSACTION_OPEN)
		die("BUG: commit called for transaction that is not open");

	/*
	 * Note that we *don't* skip transactions with zero updates,
	 * because such a transaction might be executed for the side
	 * effect of ensuring that all of the references are peeled.
	 * If the caller wants to optimize away empty transactions, it
	 * should do so itself.
	 */

	data = xcalloc(1, sizeof(*data));
	string_list_init(&data->updates, 0);

	transaction->backend_data = data;

	/*
	 * Stick the updates in a string list by refname so that we
	 * can sort them:
	 */
	for (i = 0; i < transaction->nr; i++) {
		struct ref_update *update = transaction->updates[i];
		struct string_list_item *item =
			string_list_append(&data->updates, update->refname);

		/* Store a pointer to update in item->util: */
		item->util = update;
	}
	string_list_sort(&data->updates);

	/* Fail if a refname appears more than once in the transaction: */
	if (ref_update_reject_duplicates(&data->updates, err))
		goto failure;

	if (!is_lock_file_locked(&refs->lock)) {
		if (packed_refs_lock(ref_store, 0)) {
			strbuf_addf(err, "unable to lock packed-refs file: %s",
				    strerror(errno));
			goto failure;
		}
		data->own_lock = 1;
	}

	// FIXME: check for D/F conflicts

	// FIXME: check pre-values of updates where they are supplied (or forbid pre-values)

	// FIXME: check for NOOP (?)

	if (write_with_updates(refs, &data->updates, err))
		goto failure;

	transaction->state = REF_TRANSACTION_PREPARED;
	return 0;

failure:
	packed_transaction_cleanup(refs, transaction);
	return ret;
}

static void packed_transaction_abort(struct ref_store *ref_store,
				     struct ref_transaction *transaction)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE | REF_STORE_ODB,
			"ref_transaction_abort");

	packed_transaction_cleanup(refs, transaction);
}

static int packed_transaction_finish(struct ref_store *ref_store,
				     struct ref_transaction *transaction,
				     struct strbuf *err)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE | REF_STORE_ODB,
			"ref_transaction_finish");
	struct packed_transaction_backend_data *data;
	int ret = 0;

	if (transaction->state != REF_TRANSACTION_PREPARED)
		die("BUG: finish called for transaction that is not prepared");

	data = transaction->backend_data;
	if (!data) {
		transaction->state = REF_TRANSACTION_CLOSED;
		return 0;
	}

	if (commit_packed_refs(refs)) {
		strbuf_addf(err, "couldn't commit packed-refs file: %s",
			    strerror(errno));
		ret = -1;
		goto cleanup;
	}

cleanup:
	packed_transaction_cleanup(refs, transaction);
	transaction->state = REF_TRANSACTION_CLOSED;
	return ret;
}

static int packed_initial_transaction_commit(struct ref_store *ref_store,
					    struct ref_transaction *transaction,
					    struct strbuf *err)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE | REF_STORE_ODB,
			"initial_ref_transaction_commit");

	packed_assert_main_repository(refs, "initial_ref_transaction_commit");

	return ref_transaction_commit(transaction, err);
}

static int packed_reflog_expire(struct ref_store *ref_store,
				const char *refname, const unsigned char *sha1,
				unsigned int flags,
				reflog_expiry_prepare_fn prepare_fn,
				reflog_expiry_should_prune_fn should_prune_fn,
				reflog_expiry_cleanup_fn cleanup_fn,
				void *policy_cb_data)
{
	die("BUG: packed reference store does not support reflogs");
}

static int packed_init_db(struct ref_store *ref_store, struct strbuf *err)
{
	/* Nothing to do. */
	return 0;
}

struct ref_storage_be refs_be_packed = {
	NULL,
	"files",
	packed_ref_store_create,
	packed_init_db,
	packed_transaction_prepare,
	packed_transaction_finish,
	packed_transaction_abort,
	packed_initial_transaction_commit,

	packed_pack_refs,
	packed_peel_ref,
	packed_create_symref,
	packed_delete_refs,
	packed_rename_ref,

	packed_ref_iterator_begin,
	packed_read_raw_ref,

	packed_reflog_iterator_begin,
	packed_for_each_reflog_ent,
	packed_for_each_reflog_ent_reverse,
	packed_reflog_exists,
	packed_create_reflog,
	packed_delete_reflog,
	packed_reflog_expire
};
