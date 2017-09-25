#include "../cache.h"
#include "../config.h"
#include "../refs.h"
#include "refs-internal.h"
#include "ref-cache.h"
#include "packed-backend.h"
#include "../iterator.h"
#include "../lockfile.h"

enum mmap_strategy {
	/*
	 * Don't use mmap() at all for reading `packed-refs`.
	 */
	MMAP_NONE,

	/*
	 * Can use mmap() for reading `packed-refs`, but the file must
	 * not remain mmapped. This is the usual option on Windows,
	 * where you cannot rename a new version of a file onto a file
	 * that is currently mmapped.
	 */
	MMAP_TEMPORARY,

	/*
	 * It is OK to leave the `packed-refs` file mmapped while
	 * arbitrary other code is running.
	 */
	MMAP_OK
};

#if defined(NO_MMAP)
static enum mmap_strategy mmap_strategy = MMAP_NONE;
#elif defined(MMAP_PREVENTS_DELETE)
static enum mmap_strategy mmap_strategy = MMAP_TEMPORARY;
#else
static enum mmap_strategy mmap_strategy = MMAP_OK;
#endif

struct packed_ref_store;

struct packed_ref_cache {
	/*
	 * A back-pointer to the packed_ref_store with which this
	 * cache is associated:
	 */
	struct packed_ref_store *refs;

	struct ref_cache *cache;

	/* Is the `packed-refs` file currently mmapped? */
	int mmapped;

	/*
	 * The contents of the `packed-refs` file. If the file was
	 * already sorted, this points at the mmapped contents of the
	 * file. If not, this points at heap-allocated memory
	 * containing the contents, sorted. If there were no contents
	 * (e.g., because the file didn't exist), `buf` and `eof` are
	 * both NULL.
	 */
	char *buf, *eof;

	/* The size of the header line, if any; otherwise, 0: */
	size_t header_len;

	/*
	 * What is the peeled state of this cache? (This is usually
	 * determined from the header of the "packed-refs" file.)
	 */
	enum { PEELED_NONE, PEELED_TAGS, PEELED_FULLY } peeled;

	/*
	 * Count of references to the data structure in this instance,
	 * including the pointer from files_ref_store::packed if any.
	 * The data will not be freed as long as the reference count
	 * is nonzero.
	 */
	unsigned int referrers;

	/* The metadata from when this packed-refs cache was read */
	struct stat_validity validity;
};

/*
 * A container for `packed-refs`-related data. It is not (yet) a
 * `ref_store`.
 */
struct packed_ref_store {
	struct ref_store base;

	unsigned int store_flags;

	/* The path of the "packed-refs" file: */
	char *path;

	/*
	 * A cache of the values read from the `packed-refs` file, if
	 * it might still be current; otherwise, NULL.
	 */
	struct packed_ref_cache *cache;

	/*
	 * Lock used for the "packed-refs" file. Note that this (and
	 * thus the enclosing `packed_ref_store`) must not be freed.
	 */
	struct lock_file lock;

	/*
	 * Temporary file used when rewriting new contents to the
	 * "packed-refs" file. Note that this (and thus the enclosing
	 * `packed_ref_store`) must not be freed.
	 */
	struct tempfile tempfile;
};

/*
 * Increment the reference count of *packed_refs.
 */
static void acquire_packed_ref_cache(struct packed_ref_cache *packed_refs)
{
	packed_refs->referrers++;
}

/*
 * If the buffer in `packed_refs` is active, then either munmap the
 * memory and close the file, or free the memory. Then set the buffer
 * pointers to NULL.
 */
static void release_packed_ref_buffer(struct packed_ref_cache *packed_refs)
{
	if (packed_refs->mmapped) {
		if (munmap(packed_refs->buf,
			   packed_refs->eof - packed_refs->buf))
			die_errno("error ummapping packed-refs file %s",
				  packed_refs->refs->path);
		packed_refs->mmapped = 0;
	} else {
		free(packed_refs->buf);
	}
	packed_refs->buf = packed_refs->eof = NULL;
	packed_refs->header_len = 0;
}

/*
 * Decrease the reference count of *packed_refs.  If it goes to zero,
 * free *packed_refs and return true; otherwise return false.
 */
static int release_packed_ref_cache(struct packed_ref_cache *packed_refs)
{
	if (!--packed_refs->referrers) {
		free_ref_cache(packed_refs->cache);
		stat_validity_clear(&packed_refs->validity);
		release_packed_ref_buffer(packed_refs);
		free(packed_refs);
		return 1;
	} else {
		return 0;
	}
}

struct ref_store *packed_ref_store_create(const char *path,
					  unsigned int store_flags)
{
	struct packed_ref_store *refs = xcalloc(1, sizeof(*refs));
	struct ref_store *ref_store = (struct ref_store *)refs;

	base_ref_store_init(ref_store, &refs_be_packed);
	refs->store_flags = store_flags;

	refs->path = xstrdup(path);
	return ref_store;
}

/*
 * Downcast `ref_store` to `packed_ref_store`. Die if `ref_store` is
 * not a `packed_ref_store`. Also die if `packed_ref_store` doesn't
 * support at least the flags specified in `required_flags`. `caller`
 * is used in any necessary error messages.
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

static void clear_packed_ref_cache(struct packed_ref_store *refs)
{
	if (refs->cache) {
		struct packed_ref_cache *cache = refs->cache;

		refs->cache = NULL;
		release_packed_ref_cache(cache);
	}
}

static NORETURN void die_unterminated_line(const char *path,
					   const char *p, size_t len)
{
	if (len < 80)
		die("unterminated line in %s: %.*s", path, (int)len, p);
	else
		die("unterminated line in %s: %.75s...", path, p);
}

static NORETURN void die_invalid_line(const char *path,
				      const char *p, size_t len)
{
	const char *eol = memchr(p, '\n', len);

	if (!eol)
		die_unterminated_line(path, p, len);
	else if (eol - p < 80)
		die("unexpected line in %s: %.*s", path, (int)(eol - p), p);
	else
		die("unexpected line in %s: %.75s...", path, p);

}

/*
 * An iterator over a packed-refs file that is currently mmapped.
 */
struct mmapped_ref_iterator {
	struct ref_iterator base;

	struct packed_ref_cache *packed_refs;

	/* The current position in the mmapped file: */
	const char *pos;

	/* The end of the mmapped file: */
	const char *eof;

	struct object_id oid, peeled;

	struct strbuf refname_buf;
};

static int mmapped_ref_iterator_advance(struct ref_iterator *ref_iterator)
{
	struct mmapped_ref_iterator *iter =
		(struct mmapped_ref_iterator *)ref_iterator;
	const char *p = iter->pos, *eol;

	strbuf_reset(&iter->refname_buf);

	if (iter->pos == iter->eof)
		return ref_iterator_abort(ref_iterator);

	iter->base.flags = REF_ISPACKED;

	if (iter->eof - p < GIT_SHA1_HEXSZ + 2 ||
	    parse_oid_hex(p, &iter->oid, &p) ||
	    !isspace(*p++))
		die_invalid_line(iter->packed_refs->refs->path,
				 iter->pos, iter->eof - iter->pos);

	eol = memchr(p, '\n', iter->eof - p);
	if (!eol)
		die_unterminated_line(iter->packed_refs->refs->path,
				      iter->pos, iter->eof - iter->pos);

	strbuf_add(&iter->refname_buf, p, eol - p);
	iter->base.refname = iter->refname_buf.buf;

	if (check_refname_format(iter->base.refname, REFNAME_ALLOW_ONELEVEL)) {
		if (!refname_is_safe(iter->base.refname))
			die("packed refname is dangerous: %s",
			    iter->base.refname);
		oidclr(&iter->oid);
		iter->base.flags |= REF_BAD_NAME | REF_ISBROKEN;
	}
	if (iter->packed_refs->peeled == PEELED_FULLY ||
	    (iter->packed_refs->peeled == PEELED_TAGS &&
	     starts_with(iter->base.refname, "refs/tags/")))
		iter->base.flags |= REF_KNOWS_PEELED;

	iter->pos = eol + 1;

	if (iter->pos < iter->eof && *iter->pos == '^') {
		p = iter->pos + 1;
		if (iter->eof - p < GIT_SHA1_HEXSZ + 1 ||
		    parse_oid_hex(p, &iter->peeled, &p) ||
		    *p++ != '\n')
			die_invalid_line(iter->packed_refs->refs->path,
					 iter->pos, iter->eof - iter->pos);
		iter->pos = p;

		/*
		 * Regardless of what the file header said, we
		 * definitely know the value of *this* reference. But
		 * we suppress it if the reference is broken:
		 */
		if ((iter->base.flags & REF_ISBROKEN)) {
			oidclr(&iter->peeled);
			iter->base.flags &= ~REF_KNOWS_PEELED;
		} else {
			iter->base.flags |= REF_KNOWS_PEELED;
		}
	} else {
		oidclr(&iter->peeled);
	}

	return ITER_OK;
}

static int mmapped_ref_iterator_peel(struct ref_iterator *ref_iterator,
				    struct object_id *peeled)
{
	struct mmapped_ref_iterator *iter =
		(struct mmapped_ref_iterator *)ref_iterator;

	if ((iter->base.flags & REF_KNOWS_PEELED)) {
		oidcpy(peeled, &iter->peeled);
		return is_null_oid(&iter->peeled) ? -1 : 0;
	} else if ((iter->base.flags & (REF_ISBROKEN | REF_ISSYMREF))) {
		return -1;
	} else {
		return !!peel_object(iter->oid.hash, peeled->hash);
	}
}

static int mmapped_ref_iterator_abort(struct ref_iterator *ref_iterator)
{
	struct mmapped_ref_iterator *iter =
		(struct mmapped_ref_iterator *)ref_iterator;

	release_packed_ref_cache(iter->packed_refs);
	strbuf_release(&iter->refname_buf);
	base_ref_iterator_free(ref_iterator);
	return ITER_DONE;
}

static struct ref_iterator_vtable mmapped_ref_iterator_vtable = {
	mmapped_ref_iterator_advance,
	mmapped_ref_iterator_peel,
	mmapped_ref_iterator_abort
};

struct ref_iterator *mmapped_ref_iterator_begin(
		struct packed_ref_cache *packed_refs,
		const char *pos, const char *eof)
{
	struct mmapped_ref_iterator *iter = xcalloc(1, sizeof(*iter));
	struct ref_iterator *ref_iterator = &iter->base;

	if (!packed_refs->buf)
		return empty_ref_iterator_begin();

	base_ref_iterator_init(ref_iterator, &mmapped_ref_iterator_vtable, 1);

	iter->packed_refs = packed_refs;
	acquire_packed_ref_cache(iter->packed_refs);
	iter->pos = pos;
	iter->eof = eof;
	strbuf_init(&iter->refname_buf, 0);

	iter->base.oid = &iter->oid;

	return ref_iterator;
}

struct packed_ref_entry {
	const char *start;
	size_t len;
};

static int cmp_packed_ref_entries(const void *v1, const void *v2)
{
	const struct packed_ref_entry *e1 = v1, *e2 = v2;
	const char *r1 = e1->start + GIT_SHA1_HEXSZ + 1;
	const char *r2 = e2->start + GIT_SHA1_HEXSZ + 1;

	while (1) {
		if (*r1 == '\n')
			return *r2 == '\n' ? 0 : -1;
		if (*r1 != *r2) {
			if (*r2 == '\n')
				return 1;
			else
				return (unsigned char)*r1 < (unsigned char)*r2 ? -1 : +1;
		}
		r1++;
		r2++;
	}
}

/*
 * `packed_refs->buf` is not known to be sorted. Check whether it is,
 * and if not, sort it into new memory and munmap/free the old
 * storage.
 */
static void sort_packed_refs(struct packed_ref_cache *packed_refs)
{
	struct packed_ref_entry *entries = NULL;
	size_t alloc = 0, nr = 0;
	int sorted = 1;
	const char *pos, *eof, *eol;
	size_t len, i;
	char *new_buffer, *dst;

	pos = packed_refs->buf + packed_refs->header_len;
	eof = packed_refs->eof;
	len = eof - pos;

	if (!len)
		return;

	/*
	 * Initialize entries based on a crude estimate of the number
	 * of references in the file (we'll grow it below if needed):
	 */
	ALLOC_GROW(entries, len / 80 + 20, alloc);

	while (pos < eof) {
		eol = memchr(pos, '\n', eof - pos);
		if (!eol)
			/* The safety check should prevent this. */
			BUG("unterminated line found in packed-refs");
		if (eol - pos < GIT_SHA1_HEXSZ + 2)
			die_invalid_line(packed_refs->refs->path,
					 pos, eof - pos);
		eol++;
		if (eol < eof && *eol == '^') {
			/*
			 * Keep any peeled line together with its
			 * reference:
			 */
			const char *peeled_start = eol;

			eol = memchr(peeled_start, '\n', eof - peeled_start);
			if (!eol)
				/* The safety check should prevent this. */
				BUG("unterminated peeled line found in packed-refs");
			eol++;
		}

		ALLOC_GROW(entries, nr + 1, alloc);
		entries[nr].start = pos;
		entries[nr].len = eol - pos;
		nr++;

		if (sorted &&
		    nr > 1 &&
		    cmp_packed_ref_entries(&entries[nr - 2],
					   &entries[nr - 1]) >= 0)
			sorted = 0;

		pos = eol;
	}

	if (sorted)
		goto cleanup;

	/* We need to sort the memory. First we sort the entries array: */
	QSORT(entries, nr, cmp_packed_ref_entries);

	/*
	 * Allocate a new chunk of memory, and copy the old memory to
	 * the new in the order indicated by `entries` (not bothering
	 * with the header line):
	 */
	new_buffer = xmalloc(len);
	for (dst = new_buffer, i = 0; i < nr; i++) {
		memcpy(dst, entries[i].start, entries[i].len);
		dst += entries[i].len;
	}

	/*
	 * Now munmap the old buffer and use the sorted buffer in its
	 * place:
	 */
	release_packed_ref_buffer(packed_refs);
	packed_refs->buf = new_buffer;
	packed_refs->eof = new_buffer + len;
	packed_refs->header_len = 0;

cleanup:
	free(entries);
}

/*
 * Return a pointer to the start of the record that contains the
 * character `*p` (which must be within the buffer). If no other
 * record start is found, return `buf`.
 */
static const char *find_start_of_record(const char *buf, const char *p)
{
	while (p > buf && (p[-1] != '\n' || p[0] == '^'))
		p--;
	return p;
}

/*
 * We want to be able to compare mmapped reference records quickly,
 * without totally parsing them. We can do so because the records are
 * LF-terminated, and the refname should start exactly (GIT_SHA1_HEXSZ
 * + 1) bytes past the beginning of the record.
 *
 * But what if the `packed-refs` file contains garbage? We're willing
 * to tolerate not detecting the problem, as long as we don't produce
 * totally garbled output (we can't afford to check the integrity of
 * the whole file during every Git invocation). But we do want to be
 * sure that we never read past the end of the buffer in memory and
 * perform an illegal memory access.
 *
 * Guarantee that minimum level of safety by verifying that the last
 * record in the file is LF-terminated, and that it has at least
 * (GIT_SHA1_HEXSZ + 1) characters before the LF. Die if either of
 * these checks fails.
 */
static void verify_buffer_safe(struct packed_ref_cache *packed_refs)
{
	const char *buf = packed_refs->buf + packed_refs->header_len;
	const char *eof = packed_refs->eof;
	const char *last_line;

	if (buf == eof)
		return;

	last_line = find_start_of_record(buf, eof - 1);
	if (*(eof - 1) != '\n' || eof - last_line < GIT_SHA1_HEXSZ + 2)
		die_invalid_line(packed_refs->refs->path,
				 last_line, eof - last_line);
}

/*
 * Depending on `mmap_strategy`, either mmap or read the contents of
 * the `packed-refs` file into the `packed_refs` instance. Return 1 if
 * the file existed and was read, or 0 if the file was absent. Die on
 * errors.
 */
static int load_contents(struct packed_ref_cache *packed_refs)
{
	int fd;
	struct stat st;
	size_t size;
	ssize_t bytes_read;

	fd = open(packed_refs->refs->path, O_RDONLY);
	if (fd < 0) {
		if (errno == ENOENT) {
			/*
			 * This is OK; it just means that no
			 * "packed-refs" file has been written yet,
			 * which is equivalent to it being empty,
			 * which is its state when initialized with
			 * zeros.
			 */
			return 0;
		} else {
			die_errno("couldn't read %s", packed_refs->refs->path);
		}
	}

	stat_validity_update(&packed_refs->validity, fd);

	if (fstat(fd, &st) < 0)
		die_errno("couldn't stat %s", packed_refs->refs->path);
	size = xsize_t(st.st_size);

	switch (mmap_strategy) {
	case MMAP_NONE:
		packed_refs->buf = xmalloc(size);
		bytes_read = read_in_full(fd, packed_refs->buf, size);
		if (bytes_read < 0 || bytes_read != size)
			die_errno("couldn't read %s", packed_refs->refs->path);
		packed_refs->eof = packed_refs->buf + size;
		packed_refs->mmapped = 0;
		break;
	case MMAP_TEMPORARY:
	case MMAP_OK:
		packed_refs->buf = xmmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
		packed_refs->eof = packed_refs->buf + size;
		packed_refs->mmapped = 1;
		break;
	}
	close(fd);

	return 1;
}

/*
 * Read from the `packed-refs` file into a newly-allocated
 * `packed_ref_cache` and return it. The return value will already
 * have its reference count incremented.
 *
 * A comment line of the form "# pack-refs with: " may contain zero or
 * more traits. We interpret the traits as follows:
 *
 *   Neither `peeled` nor `fully-peeled`:
 *
 *      Probably no references are peeled. But if the file contains a
 *      peeled value for a reference, we will use it.
 *
 *   `peeled`:
 *
 *      References under "refs/tags/", if they *can* be peeled, *are*
 *      peeled in this file. References outside of "refs/tags/" are
 *      probably not peeled even if they could have been, but if we find
 *      a peeled value for such a reference we will use it.
 *
 *   `fully-peeled`:
 *
 *      All references in the file that can be peeled are peeled.
 *      Inversely (and this is more important), any references in the
 *      file for which no peeled value is recorded is not peelable. This
 *      trait should typically be written alongside "peeled" for
 *      compatibility with older clients, but we do not require it
 *      (i.e., "peeled" is a no-op if "fully-peeled" is set).
 *
 *   `sorted`:
 *
 *      The references in this file are known to be sorted by refname.
 */
static struct packed_ref_cache *read_packed_refs(struct packed_ref_store *refs)
{
	struct packed_ref_cache *packed_refs = xcalloc(1, sizeof(*packed_refs));
	struct ref_dir *dir;
	struct ref_iterator *iter;
	int sorted = 0;
	int ok;

	packed_refs->refs = refs;
	acquire_packed_ref_cache(packed_refs);
	packed_refs->cache = create_ref_cache(NULL, NULL);
	packed_refs->cache->root->flag &= ~REF_INCOMPLETE;
	packed_refs->peeled = PEELED_NONE;

	if (!load_contents(packed_refs))
		return packed_refs;

	/* If the file has a header line, process it: */
	if (packed_refs->buf < packed_refs->eof && *packed_refs->buf == '#') {
		struct strbuf tmp = STRBUF_INIT;
		char *p;
		const char *eol;
		struct string_list traits = STRING_LIST_INIT_NODUP;

		eol = memchr(packed_refs->buf, '\n',
			     packed_refs->eof - packed_refs->buf);
		if (!eol)
			die_unterminated_line(refs->path,
					      packed_refs->buf,
					      packed_refs->eof - packed_refs->buf);

		strbuf_add(&tmp, packed_refs->buf, eol - packed_refs->buf);

		if (!skip_prefix(tmp.buf, "# pack-refs with:", (const char **)&p))
			die_invalid_line(refs->path,
					 packed_refs->buf,
					 packed_refs->eof - packed_refs->buf);

		string_list_split_in_place(&traits, p, ' ', -1);

		if (unsorted_string_list_has_string(&traits, "fully-peeled"))
			packed_refs->peeled = PEELED_FULLY;
		else if (unsorted_string_list_has_string(&traits, "peeled"))
			packed_refs->peeled = PEELED_TAGS;

		sorted = unsorted_string_list_has_string(&traits, "sorted");

		/* perhaps other traits later as well */

		/* The "+ 1" is for the LF character. */
		packed_refs->header_len = eol + 1 - packed_refs->buf;

		string_list_clear(&traits, 0);
		strbuf_release(&tmp);
	}

	verify_buffer_safe(packed_refs);

	if (!sorted) {
		sort_packed_refs(packed_refs);

		/*
		 * Reordering the records might have moved a short one
		 * to the end of the buffer, so verify the buffer's
		 * safety again:
		 */
		verify_buffer_safe(packed_refs);
	}

	if (mmap_strategy != MMAP_OK && packed_refs->mmapped) {
		/*
		 * We don't want to leave the file mmapped, so we are
		 * forced to make a copy now:
		 */
		size_t size = packed_refs->eof -
			(packed_refs->buf + packed_refs->header_len);
		char *buf_copy = xmalloc(size);

		memcpy(buf_copy, packed_refs->buf + packed_refs->header_len, size);
		release_packed_ref_buffer(packed_refs);
		packed_refs->buf = buf_copy;
		packed_refs->eof = buf_copy + size;
	}

	dir = get_ref_dir(packed_refs->cache->root);
	iter = mmapped_ref_iterator_begin(
			packed_refs,
			packed_refs->buf + packed_refs->header_len,
			packed_refs->eof);
	while ((ok = ref_iterator_advance(iter)) == ITER_OK) {
		struct ref_entry *entry =
			create_ref_entry(iter->refname, iter->oid, iter->flags);

		if ((iter->flags & REF_KNOWS_PEELED))
			ref_iterator_peel(iter, &entry->u.value.peeled);
		add_ref_entry(dir, entry);
	}

	if (ok != ITER_DONE)
		die("error reading packed-refs file %s", refs->path);

	return packed_refs;
}

/*
 * Check that the packed refs cache (if any) still reflects the
 * contents of the file. If not, clear the cache.
 */
static void validate_packed_ref_cache(struct packed_ref_store *refs)
{
	if (refs->cache &&
	    !stat_validity_check(&refs->cache->validity, refs->path))
		clear_packed_ref_cache(refs);
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
	if (!is_lock_file_locked(&refs->lock))
		validate_packed_ref_cache(refs);

	if (!refs->cache)
		refs->cache = read_packed_refs(refs);

	return refs->cache;
}

static struct ref_dir *get_packed_ref_dir(struct packed_ref_cache *packed_ref_cache)
{
	return get_ref_dir(packed_ref_cache->cache->root);
}

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
	struct ref_entry *r = get_packed_ref(refs, refname);

	if (!r || peel_entry(r, 0))
		return -1;

	hashcpy(sha1, r->u.value.peeled.hash);
	return 0;
}

struct packed_ref_iterator {
	struct ref_iterator base;

	struct packed_ref_cache *cache;
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

	release_packed_ref_cache(iter->cache);
	base_ref_iterator_free(ref_iterator);
	return ok;
}

static struct ref_iterator_vtable packed_ref_iterator_vtable = {
	packed_ref_iterator_advance,
	packed_ref_iterator_peel,
	packed_ref_iterator_abort
};

static struct ref_iterator *packed_ref_iterator_begin(
		struct ref_store *ref_store,
		const char *prefix, unsigned int flags)
{
	struct packed_ref_store *refs;
	struct packed_ref_iterator *iter;
	struct ref_iterator *ref_iterator;
	unsigned int required_flags = REF_STORE_READ;

	if (!(flags & DO_FOR_EACH_INCLUDE_BROKEN))
		required_flags |= REF_STORE_ODB;
	refs = packed_downcast(ref_store, required_flags, "ref_iterator_begin");

	iter = xcalloc(1, sizeof(*iter));
	ref_iterator = &iter->base;
	base_ref_iterator_init(ref_iterator, &packed_ref_iterator_vtable, 1);

	/*
	 * Note that get_packed_ref_cache() internally checks whether
	 * the packed-ref cache is up to date with what is on disk,
	 * and re-reads it if not.
	 */

	iter->cache = get_packed_ref_cache(refs);
	acquire_packed_ref_cache(iter->cache);
	iter->iter0 = cache_ref_iterator_begin(iter->cache->cache, prefix, 0);

	iter->flags = flags;

	return ref_iterator;
}

/*
 * Write an entry to the packed-refs file for the specified refname.
 * If peeled is non-NULL, write it as the entry's peeled value. On
 * error, return a nonzero value and leave errno set at the value left
 * by the failing call to `fprintf()`.
 */
static int write_packed_entry(FILE *fh, const char *refname,
			      const unsigned char *sha1,
			      const unsigned char *peeled)
{
	if (fprintf(fh, "%s %s\n", sha1_to_hex(sha1), refname) < 0 ||
	    (peeled && fprintf(fh, "^%s\n", sha1_to_hex(peeled)) < 0))
		return -1;

	return 0;
}

int packed_refs_lock(struct ref_store *ref_store, int flags, struct strbuf *err)
{
	struct packed_ref_store *refs =
		packed_downcast(ref_store, REF_STORE_WRITE | REF_STORE_MAIN,
				"packed_refs_lock");
	static int timeout_configured = 0;
	static int timeout_value = 1000;

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
			    &refs->lock,
			    refs->path,
			    flags, timeout_value) < 0) {
		unable_to_lock_message(refs->path, errno, err);
		return -1;
	}

	if (close_lock_file(&refs->lock)) {
		strbuf_addf(err, "unable to close %s: %s", refs->path, strerror(errno));
		return -1;
	}

	/*
	 * Now that we hold the `packed-refs` lock, make sure that our
	 * cache matches the current version of the file. Normally
	 * `get_packed_ref_cache()` does that for us, but that
	 * function assumes that when the file is locked, any existing
	 * cache is still valid. We've just locked the file, but it
	 * might have changed the moment *before* we locked it.
	 */
	validate_packed_ref_cache(refs);

	/*
	 * Now make sure that the packed-refs file as it exists in the
	 * locked state is loaded into the cache:
	 */
	get_packed_ref_cache(refs);
	return 0;
}

void packed_refs_unlock(struct ref_store *ref_store)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE,
			"packed_refs_unlock");

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
 * The packed-refs header line that we write out.  Perhaps other
 * traits will be added later.
 *
 * Note that earlier versions of Git used to parse these traits by
 * looking for " trait " in the line. For this reason, the space after
 * the colon and the trailing space are required.
 */
static const char PACKED_REFS_HEADER[] =
	"# pack-refs with: peeled fully-peeled sorted \n";

static int packed_init_db(struct ref_store *ref_store, struct strbuf *err)
{
	/* Nothing to do. */
	return 0;
}

/*
 * Write the packed-refs from the cache to the packed-refs tempfile,
 * incorporating any changes from `updates`. `updates` must be a
 * sorted string list whose keys are the refnames and whose util
 * values are `struct ref_update *`. On error, rollback the tempfile,
 * write an error message to `err`, and return a nonzero value.
 *
 * The packfile must be locked before calling this function and will
 * remain locked when it is done.
 */
static int write_with_updates(struct packed_ref_store *refs,
			      struct string_list *updates,
			      struct strbuf *err)
{
	struct ref_iterator *iter = NULL;
	size_t i;
	int ok;
	FILE *out;
	struct strbuf sb = STRBUF_INIT;
	char *packed_refs_path;

	if (!is_lock_file_locked(&refs->lock))
		die("BUG: write_with_updates() called while unlocked");

	/*
	 * If packed-refs is a symlink, we want to overwrite the
	 * symlinked-to file, not the symlink itself. Also, put the
	 * staging file next to it:
	 */
	packed_refs_path = get_locked_file_path(&refs->lock);
	strbuf_addf(&sb, "%s.new", packed_refs_path);
	free(packed_refs_path);
	if (create_tempfile(&refs->tempfile, sb.buf) < 0) {
		strbuf_addf(err, "unable to create file %s: %s",
			    sb.buf, strerror(errno));
		strbuf_release(&sb);
		return -1;
	}
	strbuf_release(&sb);

	out = fdopen_tempfile(&refs->tempfile, "w");
	if (!out) {
		strbuf_addf(err, "unable to fdopen packed-refs tempfile: %s",
			    strerror(errno));
		goto error;
	}

	if (fprintf(out, "%s", PACKED_REFS_HEADER) < 0)
		goto write_error;

	/*
	 * We iterate in parallel through the current list of refs and
	 * the list of updates, processing an entry from at least one
	 * of the lists each time through the loop. When the current
	 * list of refs is exhausted, set iter to NULL. When the list
	 * of updates is exhausted, leave i set to updates->nr.
	 */
	iter = packed_ref_iterator_begin(&refs->base, "",
					 DO_FOR_EACH_INCLUDE_BROKEN);
	if ((ok = ref_iterator_advance(iter)) != ITER_OK)
		iter = NULL;

	i = 0;

	while (iter || i < updates->nr) {
		struct ref_update *update = NULL;
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
			 * There is both an old value and an update
			 * for this reference. Check the old value if
			 * necessary:
			 */
			if ((update->flags & REF_HAVE_OLD)) {
				if (is_null_oid(&update->old_oid)) {
					strbuf_addf(err, "cannot update ref '%s': "
						    "reference already exists",
						    update->refname);
					goto error;
				} else if (oidcmp(&update->old_oid, iter->oid)) {
					strbuf_addf(err, "cannot update ref '%s': "
						    "is at %s but expected %s",
						    update->refname,
						    oid_to_hex(iter->oid),
						    oid_to_hex(&update->old_oid));
					goto error;
				}
			}

			/* Now figure out what to use for the new value: */
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
				 * change anything. We're done with it.
				 */
				i++;
				cmp = -1;
			}
		} else if (cmp > 0) {
			/*
			 * There is no old value but there is an
			 * update for this reference. Make sure that
			 * the update didn't expect an existing value:
			 */
			if ((update->flags & REF_HAVE_OLD) &&
			    !is_null_oid(&update->old_oid)) {
				strbuf_addf(err, "cannot update ref '%s': "
					    "reference is missing but expected %s",
					    update->refname,
					    oid_to_hex(&update->old_oid));
				goto error;
			}
		}

		if (cmp < 0) {
			/* Pass the old reference through. */

			struct object_id peeled;
			int peel_error = ref_iterator_peel(iter, &peeled);

			if (write_packed_entry(out, iter->refname,
					       iter->oid->hash,
					       peel_error ? NULL : peeled.hash))
				goto write_error;

			if ((ok = ref_iterator_advance(iter)) != ITER_OK)
				iter = NULL;
		} else if (is_null_oid(&update->new_oid)) {
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
			int peel_error = peel_object(update->new_oid.hash,
						     peeled.hash);

			if (write_packed_entry(out, update->refname,
					       update->new_oid.hash,
					       peel_error ? NULL : peeled.hash))
				goto write_error;

			i++;
		}
	}

	if (ok != ITER_DONE) {
		strbuf_addf(err, "unable to write packed-refs file: "
			    "error iterating over old contents");
		goto error;
	}

	if (close_tempfile(&refs->tempfile)) {
		strbuf_addf(err, "error closing file %s: %s",
			    get_tempfile_path(&refs->tempfile),
			    strerror(errno));
		strbuf_release(&sb);
		return -1;
	}

	return 0;

write_error:
	strbuf_addf(err, "error writing to %s: %s",
		    get_tempfile_path(&refs->tempfile), strerror(errno));

error:
	if (iter)
		ref_iterator_abort(iter);

	delete_tempfile(&refs->tempfile);
	return -1;
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

		if (is_tempfile_active(&refs->tempfile))
			delete_tempfile(&refs->tempfile);

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
			"ref_transaction_prepare");
	struct packed_transaction_backend_data *data;
	size_t i;
	int ret = TRANSACTION_GENERIC_ERROR;

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

	if (ref_update_reject_duplicates(&data->updates, err))
		goto failure;

	if (!is_lock_file_locked(&refs->lock)) {
		if (packed_refs_lock(ref_store, 0, err))
			goto failure;
		data->own_lock = 1;
	}

	if (write_with_updates(refs, &data->updates, err))
		goto failure;

	transaction->state = REF_TRANSACTION_PREPARED;
	return 0;

failure:
	packed_transaction_cleanup(refs, transaction);
	return ret;
}

static int packed_transaction_abort(struct ref_store *ref_store,
				    struct ref_transaction *transaction,
				    struct strbuf *err)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE | REF_STORE_ODB,
			"ref_transaction_abort");

	packed_transaction_cleanup(refs, transaction);
	return 0;
}

static int packed_transaction_finish(struct ref_store *ref_store,
				     struct ref_transaction *transaction,
				     struct strbuf *err)
{
	struct packed_ref_store *refs = packed_downcast(
			ref_store,
			REF_STORE_READ | REF_STORE_WRITE | REF_STORE_ODB,
			"ref_transaction_finish");
	int ret = TRANSACTION_GENERIC_ERROR;
	char *packed_refs_path;

	clear_packed_ref_cache(refs);

	packed_refs_path = get_locked_file_path(&refs->lock);
	if (rename_tempfile(&refs->tempfile, packed_refs_path)) {
		strbuf_addf(err, "error replacing %s: %s",
			    refs->path, strerror(errno));
		goto cleanup;
	}

	ret = 0;

cleanup:
	free(packed_refs_path);
	packed_transaction_cleanup(refs, transaction);
	return ret;
}

static int packed_initial_transaction_commit(struct ref_store *ref_store,
					    struct ref_transaction *transaction,
					    struct strbuf *err)
{
	return ref_transaction_commit(transaction, err);
}

static int packed_delete_refs(struct ref_store *ref_store, const char *msg,
			     struct string_list *refnames, unsigned int flags)
{
	struct packed_ref_store *refs =
		packed_downcast(ref_store, REF_STORE_WRITE, "delete_refs");
	struct strbuf err = STRBUF_INIT;
	struct ref_transaction *transaction;
	struct string_list_item *item;
	int ret;

	(void)refs; /* We need the check above, but don't use the variable */

	if (!refnames->nr)
		return 0;

	/*
	 * Since we don't check the references' old_oids, the
	 * individual updates can't fail, so we can pack all of the
	 * updates into a single transaction.
	 */

	transaction = ref_store_transaction_begin(ref_store, &err);
	if (!transaction)
		return -1;

	for_each_string_list_item(item, refnames) {
		if (ref_transaction_delete(transaction, item->string, NULL,
					   flags, msg, &err)) {
			warning(_("could not delete reference %s: %s"),
				item->string, err.buf);
			strbuf_reset(&err);
		}
	}

	ret = ref_transaction_commit(transaction, &err);

	if (ret) {
		if (refnames->nr == 1)
			error(_("could not delete reference %s: %s"),
			      refnames->items[0].string, err.buf);
		else
			error(_("could not delete references: %s"), err.buf);
	}

	ref_transaction_free(transaction);
	strbuf_release(&err);
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

static int packed_create_symref(struct ref_store *ref_store,
			       const char *refname, const char *target,
			       const char *logmsg)
{
	die("BUG: packed reference store does not support symrefs");
}

static int packed_rename_ref(struct ref_store *ref_store,
			    const char *oldrefname, const char *newrefname,
			    const char *logmsg)
{
	die("BUG: packed reference store does not support renaming references");
}

static struct ref_iterator *packed_reflog_iterator_begin(struct ref_store *ref_store)
{
	return empty_ref_iterator_begin();
}

static int packed_for_each_reflog_ent(struct ref_store *ref_store,
				      const char *refname,
				      each_reflog_ent_fn fn, void *cb_data)
{
	return 0;
}

static int packed_for_each_reflog_ent_reverse(struct ref_store *ref_store,
					      const char *refname,
					      each_reflog_ent_fn fn,
					      void *cb_data)
{
	return 0;
}

static int packed_reflog_exists(struct ref_store *ref_store,
			       const char *refname)
{
	return 0;
}

static int packed_create_reflog(struct ref_store *ref_store,
			       const char *refname, int force_create,
			       struct strbuf *err)
{
	die("BUG: packed reference store does not support reflogs");
}

static int packed_delete_reflog(struct ref_store *ref_store,
			       const char *refname)
{
	return 0;
}

static int packed_reflog_expire(struct ref_store *ref_store,
				const char *refname, const unsigned char *sha1,
				unsigned int flags,
				reflog_expiry_prepare_fn prepare_fn,
				reflog_expiry_should_prune_fn should_prune_fn,
				reflog_expiry_cleanup_fn cleanup_fn,
				void *policy_cb_data)
{
	return 0;
}

struct ref_storage_be refs_be_packed = {
	NULL,
	"packed",
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
