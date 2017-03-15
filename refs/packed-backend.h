/*
 * Module for dealing with references stored in a "packed-refs" file.
 * Note that `packed_refs_store` has several limitations compared to a files_ref_store:
 *
 * - It cannot represent symbolic refs
 *
 * - It cannot store reflogs
 *
 * - It does not support renaming refs (though this could be added if
 *   needed).
 *
 * - It locks the "packed-refs" file before writes, but it cannot lock
 *   individual references, as is needed to implement Git's locking
 *   protocol. It depends on the caller locking the references
 *   involved in a reference updates to the extent that the
 *   externally-visible values of the references might change.
 *   Conversely, it doesn't check that individual reference locks are
 *   held before overwriting the "packed-refs" file; that is also the
 *   responsibility of the caller.
 *
 * Therefore, `packed_ref_store` doesn't implement all of the methods
 * of the `ref_store` interface.
 *
 * Note also that a reference in a `packed_ref_store` might be hidden
 * "behind" a loose reference with the same name. In this case, the
 * reference might point at an object that doesn't even exist anymore.
 *
 * However, `packed_ref_store` has one skill that a generic
 * `ref_store` doesn't have: the whole packed-refs file can be locked,
 * blocking changes by other processes, even independent of a
 * transaction. Moreover, if it is locked when
 * ref_transaction_commit() is called, then the lock is retained even
 * after the new content has been written and activated. (The lock is
 * held via lock file "packed-refs.lock", while new content is written
 * via temporary file "packed-refs.new".) This lock is
 * acquired/released via functions `packed_refs_lock()` and
 * `packed_refs_unlock()`.
 *
 * `packed_ref_store` tries to give an up-to-date view of the
 * "packed-refs" file contents. Whenever a reference is looked up, the
 * validity of the cache is checked by verifying that either the
 * "packed-refs" file has already been locked, or that its metadata
 * hasn't changed since the last time it was read into the cache. When
 * a `packed_ref_store` is iterated over, the cache is checked for
 * currency at the start of the iteration, and is retained until the
 * iteration is done. This means that the references included in the
 * iteration represent a snapshot of the contents of the "packed-refs"
 * file at the start of the iteration, even if the file is changed by
 * another process during the iteration (which can happen unless it is
 * locked).
 */

#ifndef REFS_PACKED_BACKEND_H
#define REFS_PACKED_BACKEND_H

/*
 * Acquire the "packed-refs" lock. The argument must be an instance of
 * packed_ref_store. `flags` is passed to
 * `hold_lock_file_for_update()`. Return 0 on success. On failure, set
 * errno appropriately and return a nonzero value.
 */
int packed_refs_lock(struct ref_store *ref_store, int flags);

/*
 * Release the "packed-refs" lock. The argument must be an instance of
 * packed_ref_store.
 */
void packed_refs_unlock(struct ref_store *ref_store);

/*
 * Return true if `ref_store` is currently locked. The argument must
 * be an instance of packed_ref_store.
 */
int packed_refs_is_locked(struct ref_store *ref_store);

#endif /* REFS_PACKED_BACKEND_H */
