#ifndef TEMPFILE_H
#define TEMPFILE_H

/*
 * Handle temporary files.
 *
 * The tempfile API allows temporary files to be created, deleted, and
 * atomically renamed. Temporary files that are still active when the
 * program ends are cleaned up automatically. Lockfiles (see
 * "lockfile.h") are built on top of this API.
 *
 *
 * Calling sequence
 * ----------------
 *
 * The caller:
 *
 * * Allocates a `struct tempfile` either as a static variable or on
 *   the heap, initialized to zeros. Once you use the structure to
 *   call `create_tempfile()`, it belongs to the tempfile subsystem
 *   and its storage must remain valid throughout the life of the
 *   program (i.e. you cannot use an on-stack variable to hold this
 *   structure).
 *
 * * Attempts to create a temporary file by calling
 *   `create_tempfile()`.
 *
 * * Writes new content to the file by either:
 *
 *   * writing to the file descriptor returned by `create_tempfile()`
 *     (also available via `tempfile->fd`).
 *
 *   * calling `fdopen_tempfile()` to get a `FILE` pointer for the
 *     open file and writing to the file using stdio.
 *
 * When finished writing, the caller can:
 *
 * * Close the file descriptor and remove the temporary file by
 *   calling `delete_tempfile()`.
 *
 * * Close the temporary file and rename it atomically to a specified
 *   filename by calling `rename_tempfile()`. This relinquishes
 *   control of the file.
 *
 * * Close the file descriptor without removing or renaming the
 *   temporary file by calling `close_tempfile()`, and later call
 *   `delete_tempfile()` or `rename_tempfile()`.
 *
 * Even after the temporary file is renamed or deleted, the `tempfile`
 * object must not be freed or altered by the caller. However, it may
 * be reused; just pass it to another call of `create_tempfile()`.
 *
 * If the program exits before `rename_tempfile()` or
 * `delete_tempfile()` is called, an `atexit(3)` handler will close
 * and remove the temporary file.
 *
 * If you need to close the file descriptor yourself, do so by calling
 * `close_tempfile()`. You should never call `close(2)` or `fclose(3)`
 * yourself, otherwise the `struct tempfile` structure would still
 * think that the file descriptor needs to be closed, and a later
 * cleanup would result in duplicate calls to `close(2)`. Worse yet,
 * if you close and then later open another file descriptor for a
 * completely different purpose, then the unrelated file descriptor
 * might get closed.
 *
 *
 * State diagram and cleanup
 * -------------------------
 *
 * If the program exits while a temporary file is active, we want to
 * make sure that we remove it. This is done by remembering the active
 * temporary files in a linked list, `tempfile_list`. An `atexit(3)`
 * handler and a signal handler are registered, to clean up any active
 * temporary files.
 *
 * Because the signal handler can run at any time, `tempfile_list` and
 * the `tempfile` objects that comprise it must be kept in
 * self-consistent states at all times.
 *
 * The possible states of a `tempfile` object are as follows:
 *
 * - Uninitialized. In this state the object's `on_list` field must be
 *   zero but the rest of its contents need not be initialized. As
 *   soon as the object is used in any way, it is irrevocably
 *   registered in `tempfile_list`, and `on_list` is set.
 *
 * - Active, file open (after `create_tempfile()` or
 *   `reopen_tempfile()`). In this state:
 *
 *   - the temporary file exists
 *   - `active` is set
 *   - `filename` holds the filename of the temporary file
 *   - `fd` holds a file descriptor open for writing to it
 *   - `fp` holds a pointer to an open `FILE` object if and only if
 *     `fdopen_tempfile()` has been called on the object
 *   - `owner` holds the PID of the process that created the file
 *
 * - Active, file closed (after successful `close_tempfile()`). Same
 *   as the previous state, except that the temporary file is closed,
 *   `fd` is -1, and `fp` is `NULL`.
 *
 * - Inactive (after `delete_tempfile()`, `rename_tempfile()`, a
 *   failed attempt to create a temporary file, or a failed
 *   `close_tempfile()`). In this state:
 *
 *   - `active` is unset
 *   - `filename` is empty (usually, though there are transitory
 *     states in which this condition doesn't hold). Client code should
 *     *not* rely on the filename being empty in this state.
 *   - `fd` is -1 and `fp` is `NULL`
 *   - the object is left registered in the `tempfile_list`, and
 *     `on_list` is set.
 *
 * A temporary file is owned by the process that created it. The
 * `tempfile` has an `owner` field that records the owner's PID. This
 * field is used to prevent a forked process from deleting a temporary
 * file created by its parent.
 *
 *
 * Error handling
 * --------------
 *
 * `create_tempfile()` returns a file descriptor on success or -1 on
 * failure. On errors, `errno` describes the reason for failure.
 *
 * `delete_tempfile()`, `rename_tempfile()`, and `close_tempfile()`
 * return 0 on success. On failure they set `errno` appropriately, do
 * their best to delete the temporary file, and return -1.
 */

struct tempfile {
	struct tempfile *volatile next;
	volatile sig_atomic_t active;
	volatile int fd;
	FILE *volatile fp;
	volatile pid_t owner;
	char on_list;
	struct strbuf filename;
};

/*
 * Attempt to create a temporary file at the specified `path`. Return
 * a file descriptor for writing to it, or -1 on error. It is an error
 * if a file already exists at that path.
 */
extern int create_tempfile(struct tempfile *tempfile, const char *path);

extern int mks_tempfile(struct tempfile *tempfile, const char *template);
extern int xmks_tempfile(struct tempfile *tempfile, const char *template);

/*
 * Associate a stdio stream with the temporary file (which must still
 * be open). Return `NULL` (*without* deleting the file) on error. The
 * stream is closed automatically when `close_tempfile()` is called or
 * when the file is deleted or renamed.
 */
extern FILE *fdopen_tempfile(struct tempfile *tempfile, const char *mode);

/*
 * If the temporary file is still open, close it (and the file pointer
 * too, if it has been opened using `fdopen_tempfile()`) without
 * deleting the file. Return 0 upon success. On failure to `close(2)`,
 * return a negative value and delete the file. Usually
 * `delete_tempfile()` or `rename_tempfile()` should eventually be
 * called if `close_tempfile()` succeeds.
 */
extern int close_tempfile(struct tempfile *tempfile);

/*
 * Re-open a temporary file that has been closed using
 * `close_tempfile()` but not yet deleted or renamed. This can be used
 * to implement a sequence of operations like the following:
 *
 * * Create temporary file.
 *
 * * Write new contents to file, then `close_tempfile()` to cause the
 *   contents to be written to disk.
 *
 * * Pass the name of the temporary file to another program to allow
 *   it (and nobody else) to inspect or even modify the file's
 *   contents.
 *
 * * `reopen_tempfile()` to reopen the temporary file. Make further
 *   updates to the contents.
 *
 * * `rename_tempfile()` to move the file to its permanent location.
 */
extern int reopen_tempfile(struct tempfile *tempfile);

/*
 * Close the file descriptor and/or file pointer and remove the
 * temporary file associated with `tempfile`. It is a NOOP to call
 * `delete_tempfile()` for a `tempfile` object that has already been
 * deleted or renamed.
 */
extern void delete_tempfile(struct tempfile *tempfile);

/*
 * Close the file descriptor and/or file pointer if they are still
 * open, and atomically rename the temporary file to `path`. `path`
 * must be on the same filesystem as the lock file. Return 0 on
 * success. On failure, delete the temporary file and return -1, with
 * `errno` set to the value from the failing call to `close(2)` or
 * `rename(2)`. It is a bug to call `rename_tempfile()` for a
 * `tempfile` object that is not currently active.
 */
extern int rename_tempfile(struct tempfile *tempfile, const char *path);

#endif /* TEMPFILE_H */
