//! The filesystem port — the seam every transaction lands through.
//!
//! This crate is generic over *where* files live. Rather than depend on any one
//! concrete backend — `std::fs`, `tokio::fs`, or a browser filesystem like
//! OPFS/IndexedDB — it asks only for a small async trait that mirrors the slice
//! of [`std::fs`] a transaction needs. Integrators implement it over whatever
//! backend they have; [`ChangeSet`](crate::ChangeSet) never learns which one.
//!
//! This is the classic *ports and adapters* seam. The traits use native
//! `async fn` (no boxed futures), so callers keep the backend's real future
//! types and their `Send`-ness: a backend whose futures are `Send` composes into
//! multithreaded runtimes unchanged, and one whose futures are not — a
//! browser backend on a single-threaded executor — is not forced to pretend
//! otherwise. The method set mirrors [`std::fs`] names exactly, so an adapter is
//! mechanical to write.
//!
//! ## The read/write split
//!
//! [`ReadStorage`] is everything that cannot change a byte; [`Storage`] adds the
//! writes, the mutations, and the durability vocabulary. The split is not
//! decoration — a consumer generic over `ReadStorage` is a *provably* read-only
//! consumer, checked by the compiler rather than by review. Only [`Storage`]
//! can drive a transaction.
//!
//! ## Durability is declared, not assumed
//!
//! Backends keep very different crash promises: `std::fs` has atomic rename and
//! `fsync` on every major OS, OPFS has a flush primitive but a weak rename,
//! IndexedDB has its own multi-object transactions. Rather than assume the
//! strongest and silently lie on the weakest, a backend *declares* what it can
//! keep through [`Capabilities`], and the crash-safety machinery adapts. Every
//! durability member defaults to the pessimistic answer, so an adapter that
//! forgets to override one degrades to the most defensive path rather than to a
//! false promise.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::SystemTime;

pub mod memory;

pub use memory::InMemoryFs;

/// The read half of an async filesystem backend: everything the traversal core
/// needs, and nothing that can change a byte on disk.
///
/// The split from [`Storage`] is not decoration — it is what lets a tree be
/// depended on by a consumer that must not, and cannot, write: a language
/// server, a renderer, a browser viewer. A backend that implements only this
/// is a *provably* read-only view, checked by the compiler rather than by
/// review.
///
/// Each method mirrors the [`std::fs`] function of the same name.
/// [`try_exists`] has a default in terms of [`metadata`].
///
/// [`try_exists`]: ReadStorage::try_exists
/// [`metadata`]: ReadStorage::metadata
pub trait ReadStorage {
    /// Read the entire contents of a file as bytes. Mirrors [`std::fs::read`].
    fn read(&self, path: &Path) -> impl Future<Output = io::Result<Vec<u8>>>;

    /// Read the entire contents of a file as a string. Mirrors
    /// [`std::fs::read_to_string`].
    fn read_to_string(&self, path: &Path) -> impl Future<Output = io::Result<String>>;

    /// Return the entries in a directory (non-recursive). Mirrors
    /// [`std::fs::read_dir`], but yields a `Vec` since async iterators are not
    /// yet stable.
    fn read_dir(&self, path: &Path) -> impl Future<Output = io::Result<Vec<DirEntry>>>;

    /// Return metadata about the entry at `path`. Mirrors
    /// [`std::fs::metadata`]; follows symlinks.
    fn metadata(&self, path: &Path) -> impl Future<Output = io::Result<Metadata>>;

    /// Returns `Ok(true)` if the path exists, `Ok(false)` if it does not, and
    /// `Err(_)` if the check itself failed. Mirrors `std::fs::try_exists`.
    fn try_exists(&self, path: &Path) -> impl Future<Output = io::Result<bool>> {
        async move {
            match self.metadata(path).await {
                Ok(_) => Ok(true),
                Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(false),
                Err(e) => Err(e),
            }
        }
    }

    /// Whether the file at `path` can be run — or `None` where that is not a
    /// thing this backend has.
    ///
    /// `None` is the load-bearing answer, and it is *declined*, never guessed:
    /// a backend that cannot observe the bit — Windows, [`InMemoryFs`], a
    /// document provider handing over opaque blobs — must not answer `false`,
    /// because "not executable" and "I do not model this" are different facts,
    /// and a consumer restoring modes across two machines must be able to tell
    /// them apart rather than take turns flipping a bit neither can see. The
    /// default is the decline, so a backend with no opinion is already correct.
    ///
    /// Follows symlinks, like [`metadata`](ReadStorage::metadata).
    fn executable(&self, path: &Path) -> impl Future<Output = io::Result<Option<bool>>> {
        async move {
            let _ = path;
            Ok(None)
        }
    }

    /// What the symbolic link at `path` points at, **read rather than
    /// followed** — or `None` where this backend models no links at all.
    /// Mirrors [`std::fs::read_link`], with the decline folded in.
    ///
    /// `Ok(None)` is reserved for the decline, exactly as
    /// [`executable`](ReadStorage::executable)'s is: it means *there is no such
    /// thing here*, it is the default's answer, and an implementation that does
    /// model links must never give it. Such an implementation answers with the
    /// target, or with an error where the path holds no link — which is what
    /// `readlink` already does, and what lets one call settle whether links
    /// exist at all. Reading the link is what makes recording one safe;
    /// following it would make the thing at the other end look like a file of
    /// this tree.
    fn read_link(&self, path: &Path) -> impl Future<Output = io::Result<Option<PathBuf>>> {
        async move {
            let _ = path;
            Ok(None)
        }
    }
}

/// A borrowed [`ReadStorage`] is itself a [`ReadStorage`] — so an owned backend
/// can be lent to something generic over `S: ReadStorage` without moving it or
/// wrapping it in an `Arc` the caller doesn't otherwise need.
///
/// Every member is forwarded explicitly. The matching [`Storage`] forwarding
/// below does the same for the durability members, where leaving any to
/// inherit the trait's defaults would silently downgrade a real backend's
/// guarantees the moment it was borrowed.
impl<S: ReadStorage + ?Sized> ReadStorage for &S {
    async fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        (**self).read(path).await
    }

    async fn read_to_string(&self, path: &Path) -> io::Result<String> {
        (**self).read_to_string(path).await
    }

    async fn read_dir(&self, path: &Path) -> io::Result<Vec<DirEntry>> {
        (**self).read_dir(path).await
    }

    async fn metadata(&self, path: &Path) -> io::Result<Metadata> {
        (**self).metadata(path).await
    }

    async fn try_exists(&self, path: &Path) -> io::Result<bool> {
        (**self).try_exists(path).await
    }

    async fn executable(&self, path: &Path) -> io::Result<Option<bool>> {
        (**self).executable(path).await
    }

    async fn read_link(&self, path: &Path) -> io::Result<Option<PathBuf>> {
        (**self).read_link(path).await
    }
}

/// An `Arc<S>` is itself a [`ReadStorage`] on the same terms as `&S` above — so
/// a backend shared across several owners (several open handles, a
/// multi-tab web client) still carries its real capabilities through the
/// `Arc`, rather than an adapter that forgot to unwrap it silently degrading
/// to the pessimistic defaults.
///
/// `Arc<S>` derefs to `S` exactly like `&S` does, so the same explicit,
/// every-member forwarding applies for the same reason: the trait's defaults
/// must never be reached by accident.
impl<S: ReadStorage + ?Sized> ReadStorage for Arc<S> {
    async fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        (**self).read(path).await
    }

    async fn read_to_string(&self, path: &Path) -> io::Result<String> {
        (**self).read_to_string(path).await
    }

    async fn read_dir(&self, path: &Path) -> io::Result<Vec<DirEntry>> {
        (**self).read_dir(path).await
    }

    async fn metadata(&self, path: &Path) -> io::Result<Metadata> {
        (**self).metadata(path).await
    }

    async fn try_exists(&self, path: &Path) -> io::Result<bool> {
        (**self).try_exists(path).await
    }

    async fn executable(&self, path: &Path) -> io::Result<Option<bool>> {
        (**self).executable(path).await
    }

    async fn read_link(&self, path: &Path) -> io::Result<Option<PathBuf>> {
        (**self).read_link(path).await
    }
}

/// One entry returned by [`ReadStorage::read_dir`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirEntry {
    path: PathBuf,
    file_type: FileType,
}

impl DirEntry {
    /// Construct an entry from its path and type.
    pub fn new(path: impl Into<PathBuf>, file_type: FileType) -> Self {
        Self {
            path: path.into(),
            file_type,
        }
    }

    /// The full path to the entry.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The final component of the entry's path.
    pub fn file_name(&self) -> Option<&std::ffi::OsStr> {
        self.path.file_name()
    }

    /// The entry's type.
    pub fn file_type(&self) -> FileType {
        self.file_type
    }
}

/// Metadata about a filesystem entry — the subset a transaction needs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Metadata {
    file_type: FileType,
    len: u64,
    modified: Option<SystemTime>,
}

impl Metadata {
    /// Construct metadata from its parts.
    pub fn new(file_type: FileType, len: u64, modified: Option<SystemTime>) -> Self {
        Self {
            file_type,
            len,
            modified,
        }
    }

    /// The entry's type.
    pub fn file_type(&self) -> FileType {
        self.file_type
    }

    /// Whether the entry is a regular file.
    pub fn is_file(&self) -> bool {
        self.file_type.is_file()
    }

    /// Whether the entry is a directory.
    pub fn is_dir(&self) -> bool {
        self.file_type.is_dir()
    }

    /// Size in bytes.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Whether the entry is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Last-modified time, if the backend reports one. Mirrors
    /// [`std::fs::Metadata::modified`], returning [`io::ErrorKind::Unsupported`]
    /// when unavailable.
    pub fn modified(&self) -> io::Result<SystemTime> {
        self.modified
            .ok_or_else(|| io::Error::new(io::ErrorKind::Unsupported, "modified time unavailable"))
    }
}

/// [`ReadStorage`] over the process filesystem (`std::fs`).
///
/// The reference adapter, and the one [`ChangeSet`](crate::ChangeSet) is
/// tuned for: it implements [`Storage`] too, and reports
/// [`Capabilities::LOCAL_FS`].
///
/// The traits are async so that genuinely async backends (network, OPFS) fit;
/// this adapter's futures are immediately ready, so any executor — including
/// the dependency-free [`crate::exec::block_on`] — drives them to completion
/// in a single poll.
#[derive(Debug, Clone, Copy, Default)]
pub struct StdFs;

impl ReadStorage for StdFs {
    async fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        std::fs::read(path)
    }

    async fn read_to_string(&self, path: &Path) -> io::Result<String> {
        std::fs::read_to_string(path)
    }

    async fn read_dir(&self, path: &Path) -> io::Result<Vec<DirEntry>> {
        std::fs::read_dir(path)?
            .map(|entry| {
                let entry = entry?;
                Ok(DirEntry::new(
                    entry.path(),
                    convert_file_type(entry.file_type()?),
                ))
            })
            .collect()
    }

    async fn metadata(&self, path: &Path) -> io::Result<Metadata> {
        let md = std::fs::metadata(path)?;
        Ok(Metadata::new(
            convert_file_type(md.file_type()),
            md.len(),
            md.modified().ok(),
        ))
    }

    #[cfg(unix)]
    async fn executable(&self, path: &Path) -> io::Result<Option<bool>> {
        use std::os::unix::fs::PermissionsExt as _;

        // Any execute bit counts: the question is "can this be run", not
        // "by whom" — the same one-bit grain `set_executable` writes.
        let md = std::fs::metadata(path)?;
        Ok(Some(md.permissions().mode() & 0o111 != 0))
    }

    // On a platform with no execute bit the trait's default — the decline —
    // is already the honest answer, so only unix overrides it.

    async fn read_link(&self, path: &Path) -> io::Result<Option<PathBuf>> {
        // `read_link` reads the link and does not follow it; it errors where
        // the path holds no link, which is what keeps `Ok(None)` meaning
        // "this backend has no such thing" — an answer `StdFs` never gives,
        // on Windows included, where links exist and can be read even though
        // creating one takes a privilege `set_link` may not have.
        std::fs::read_link(path).map(Some)
    }
}

fn convert_file_type(ft: std::fs::FileType) -> FileType {
    if ft.is_dir() {
        FileType::DIR
    } else if ft.is_file() {
        FileType::FILE
    } else {
        FileType::SYMLINK
    }
}

/// The type of a filesystem entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileType {
    is_dir: bool,
    is_file: bool,
    is_symlink: bool,
}

impl FileType {
    /// A regular file.
    pub const FILE: FileType = FileType {
        is_dir: false,
        is_file: true,
        is_symlink: false,
    };

    /// A directory.
    pub const DIR: FileType = FileType {
        is_dir: true,
        is_file: false,
        is_symlink: false,
    };

    /// A symbolic link.
    pub const SYMLINK: FileType = FileType {
        is_dir: false,
        is_file: false,
        is_symlink: true,
    };

    /// Whether this is a regular file.
    pub fn is_file(&self) -> bool {
        self.is_file
    }

    /// Whether this is a directory.
    pub fn is_dir(&self) -> bool {
        self.is_dir
    }

    /// Whether this is a symbolic link.
    pub fn is_symlink(&self) -> bool {
        self.is_symlink
    }
}

/// An async filesystem backend a transaction can drive — [`ReadStorage`] plus everything
/// that changes bytes on disk.
///
/// Each method mirrors the [`std::fs`] function of the same name. Backends
/// implement the write/mutate/durability surface here and the read surface on
/// [`ReadStorage`].
pub trait Storage: ReadStorage {
    // ---- write ----

    /// Write a file, replacing it if it already exists. Mirrors
    /// [`std::fs::write`].
    fn write(&self, path: &Path, contents: &[u8]) -> impl Future<Output = io::Result<()>>;

    /// Create a file that must not already exist, and write `contents` to it.
    /// Mirrors [`std::fs::File::create_new`] followed by a full write.
    ///
    /// The create and the test-for-existence are **one operation**, and that
    /// indivisibility is the entire point: of two writers racing to the same
    /// name, exactly one succeeds and the other is told
    /// [`AlreadyExists`](io::ErrorKind::AlreadyExists) — with no window between
    /// a check and a create for either to slip a half-written file through.
    /// `AlreadyExists` is therefore a *load-bearing answer*, not a failure to
    /// smooth over: a write-once consumer branches on it (typically by reading
    /// back what is there and confirming it is what it meant to write), so an
    /// implementation must report that kind and no other for an occupied path.
    ///
    /// Two things this deliberately does not do, both the caller's to ask for:
    /// parents are not created ([`create_dir_all`](Storage::create_dir_all)
    /// first, as [`std::fs::File::create_new`] would demand), and nothing is
    /// flushed — a caller that needs the new file to survive a crash pairs
    /// this with [`sync`](Storage::sync), which is what lets it choose the
    /// *weakest* durability that is correct where a built-in flush would
    /// impose the strongest everywhere.
    ///
    /// The default refuses with [`Unsupported`](io::ErrorKind::Unsupported),
    /// and [`Capabilities::exclusive_create`] defaults to `false` to match: a
    /// backend that can keep the exclusivity promise declares it and overrides
    /// this, and one that cannot must not paper over the difference with a
    /// check-then-write — the window in that emulation is exactly what a
    /// caller reaching for this method cannot tolerate.
    fn create_new(&self, path: &Path, contents: &[u8]) -> impl Future<Output = io::Result<()>> {
        async move {
            let _ = (path, contents);
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "this backend does not support exclusive create",
            ))
        }
    }

    /// Create a directory and all missing parents. Mirrors
    /// [`std::fs::create_dir_all`].
    fn create_dir_all(&self, path: &Path) -> impl Future<Output = io::Result<()>>;

    // ---- mutate ----

    /// Remove a regular file. Mirrors [`std::fs::remove_file`].
    fn remove_file(&self, path: &Path) -> impl Future<Output = io::Result<()>>;

    /// Recursively remove a directory and its contents. Mirrors
    /// [`std::fs::remove_dir_all`].
    fn remove_dir_all(&self, path: &Path) -> impl Future<Output = io::Result<()>>;

    /// Rename or move a file or directory. Mirrors [`std::fs::rename`] — and
    /// the load-bearing half of the mirror is that an occupied destination
    /// *file* is replaced, as `std::fs::rename` replaces one on every platform
    /// this crate targets. The default [`write_atomic`](Storage::write_atomic)
    /// publishes by renaming a staged sibling over the target, so a backend
    /// whose rename refuses an occupied file cannot take that default and must
    /// override `write_atomic` with its own atomic replacement. A *directory*
    /// destination is another matter — `std::fs::rename` itself is
    /// platform-divergent there — and nothing in this crate renames onto one.
    fn rename(&self, from: &Path, to: &Path) -> impl Future<Output = io::Result<()>>;

    /// Give `to` the same access permissions `from` has. A `from` that does not
    /// exist is not an error — there is no prior state to carry over, so the
    /// call has nothing to do.
    ///
    /// This exists for [`write_atomic`](Storage::write_atomic), which publishes
    /// its bytes by renaming a freshly-created sibling over the target. A new
    /// file is born with the backend's default permissions, and a rename carries
    /// those onto the name it replaces — so without this step, replacing a
    /// document the user had deliberately restricted (`chmod 600` on a private
    /// journal entry) silently widens it to whatever the umask allows. A
    /// content replacement must not be a permission change.
    ///
    /// What this does *not* close is the window before it: the sibling holds the
    /// new contents under default permissions from the moment it is written
    /// until this call narrows it. Shutting that window means creating the file
    /// with the final mode already on it, which is not something
    /// [`write`](Storage::write) — a `std::fs::write` mirror — can express. The
    /// sibling lives in the target's own directory throughout, so whatever gates
    /// access to the document gates access to it too.
    ///
    /// The default is a no-op, which is the *correct* behavior for a backend
    /// with no permission model at all — [`InMemoryFs`], OPFS, IndexedDB. There
    /// is nothing there to preserve, and nothing is lost by not preserving it.
    fn copy_permissions(&self, from: &Path, to: &Path) -> impl Future<Output = io::Result<()>> {
        async move {
            let _ = (from, to);
            Ok(())
        }
    }

    /// Make the file at `path` runnable, or not. One bit, not a mode: nothing
    /// else about the file changes.
    ///
    /// The write half of [`executable`](ReadStorage::executable), and the
    /// default follows from its decline: a backend whose `executable` answers
    /// `None` has nothing to set, so doing nothing *is* the honest
    /// implementation — the same reasoning as
    /// [`copy_permissions`](Storage::copy_permissions), where a backend with no
    /// permission model loses nothing by not preserving one. A backend that
    /// does model the bit overrides both members together; answering one
    /// without the other would let a change set read a bit it cannot restore,
    /// or restore one it cannot read.
    fn set_executable(
        &self,
        path: &Path,
        executable: bool,
    ) -> impl Future<Output = io::Result<()>> {
        async move {
            let _ = (path, executable);
            Ok(())
        }
    }

    /// Place a symbolic link at `path` pointing at `target`, replacing whatever
    /// is there.
    ///
    /// The write half of [`read_link`](ReadStorage::read_link). Nothing here
    /// opens or resolves `target`: a link may point outside the tree, at
    /// nothing, or at itself, and the only consequence is an honest symlink
    /// pointing where symlinks are allowed to point. The replacement addresses
    /// the entry itself, never the entry's referent — a link at `path` is
    /// removed and remade rather than written through, or a plain file there
    /// gives way to the link.
    ///
    /// The default *refuses* with [`Unsupported`](io::ErrorKind::Unsupported),
    /// where [`set_executable`](Storage::set_executable)'s default no-ops —
    /// the asymmetry is deliberate. An execute bit not modeled costs nothing to
    /// leave unset; a link not modeled has no honest substitute, because a
    /// plain file holding the target's text would invent content nothing asked
    /// to write. A backend with no links must say so, and the caller decides
    /// what its absence means.
    fn set_link(&self, path: &Path, target: &Path) -> impl Future<Output = io::Result<()>> {
        async move {
            let _ = (path, target);
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "this backend does not model symbolic links",
            ))
        }
    }

    // ---- durability ----
    //
    // This crate spans backends with very different crash guarantees — `std::fs`
    // (atomic rename and fsync on every major OS), OPFS (a flush primitive but a
    // weak rename), IndexedDB (its own multi-object transactions). Rather than
    // assume the strongest of these and silently lie on the weakest, the crash-
    // safety machinery *asks* what a backend can promise and adapts. These three
    // members are defaulted to the pessimistic answer, so a backend gains a
    // guarantee only by explicitly claiming it.

    /// What durability guarantees this backend can make. Defaults to
    /// [`Capabilities::NONE`] — a backend promises a guarantee only by saying so,
    /// so an adapter that forgets to override this degrades to the most defensive
    /// path rather than to a false promise.
    fn capabilities(&self) -> Capabilities {
        Capabilities::NONE
    }

    /// Flush `path` — and nothing else — to the strength `need` asks for.
    ///
    /// `path` names *one* object, and only that object is flushed. To make a
    /// directory entry durable (the naming half of a create or a rename), sync
    /// the directory itself: on a POSIX filesystem a directory is a thing that
    /// can be opened and fsynced, and this crate's own
    /// [`write_atomic`](Storage::write_atomic) does exactly that after its
    /// rename. Folding the parent into every call instead would flush twice as
    /// much as any single step needs, and would leave the caller unable to say
    /// which of the two it actually meant.
    ///
    /// `need` is the *weakest* guarantee that is still correct at the call site,
    /// not a wish. [`Durability::Ordered`] asks only that everything written to
    /// `path` before this call land before anything written after it — enough to
    /// stop a rename overtaking the bytes it publishes, and on some platforms far
    /// cheaper than the real thing. [`Durability::Durable`] asks that the bytes
    /// survive power loss. A backend may always answer with something stronger
    /// than it was asked for; it may never answer with something weaker.
    ///
    /// The default is a no-op, which is the *correct* behavior for any backend
    /// whose [`capabilities`](Storage::capabilities) report
    /// [`SyncGuarantee::None`]: it cannot make the promise, so it must not
    /// pretend to. A backend that can flush must both override this and report
    /// the strongest request it genuinely honors — the two always travel
    /// together, and [`SyncGuarantee::satisfies`] is how a caller asks.
    fn sync(&self, path: &Path, need: Durability) -> impl Future<Output = io::Result<()>> {
        async move {
            let _ = (path, need);
            Ok(())
        }
    }

    /// Replace `path`'s contents with `contents` atomically and durably: no
    /// observer — concurrent reader or post-crash survivor — ever sees a splice
    /// of old and new bytes, and once this returns the new contents outlive a
    /// power loss.
    ///
    /// The default composes the primitives into the standard protocol, whenever
    /// [`capabilities`](Storage::capabilities) report `atomic_replace`:
    ///
    /// 1. write the bytes to a temporary sibling;
    /// 2. [`sync`](Storage::sync) that sibling [`Ordered`](Durability::Ordered),
    ///    so the rename cannot be reordered ahead of the bytes it publishes;
    /// 3. [`copy_permissions`](Storage::copy_permissions) from the target onto
    ///    that sibling, so the replacement carries the target's access
    ///    permissions rather than a fresh file's defaults;
    /// 4. [`rename`](Storage::rename) it over the target — *this* is the atomic
    ///    instant;
    /// 5. `sync` the target's **parent directory** [`Durable`](Durability::Durable),
    ///    which is what carries the rename itself through a power cut.
    ///
    /// Steps 2 and 3 are in that order because a backend may implement `sync` by
    /// opening the path, and a mode faithfully copied from the target can be one
    /// that forbids opening it to read — `0o200` is replaceable but not readable.
    /// The cost is that the mode change lands after the flush and so is not
    /// itself durable: a crash in that window can leave the new contents under
    /// the *default* permissions. That is precisely the outcome every write had
    /// before step 3 existed, so the window is a smaller bad case, never a new
    /// one.
    ///
    /// Two flushes, and each one is load-bearing. Neither of the two this
    /// protocol conspicuously does *not* do would buy anything. The bytes are
    /// never flushed under their final name, because a rename does not move an
    /// inode: the file the target now names is the very one step 2 flushed, and
    /// nothing has been written to it since. The sibling's own directory entry is
    /// never flushed either, because nobody is owed a temporary that survives a
    /// crash — only the directory state *after* the rename is worth a barrier.
    ///
    /// A backend that cannot rename atomically falls back to a plain durable
    /// write, which is *not* crash-atomic; a caller that needs the guarantee
    /// consults `capabilities` and leans on the journal instead of pretending
    /// this call gave it. A backend with a better native path — a transactional
    /// store — overrides this method wholesale.
    ///
    /// The temporary is removed on any failure, so a torn attempt leaves the
    /// target exactly as it was and no litter behind. It is a dotted sibling in
    /// the target's own directory, so the follow-up rename stays within one
    /// filesystem (a cross-device rename is neither atomic nor, often, even
    /// permitted).
    fn write_atomic(&self, path: &Path, contents: &[u8]) -> impl Future<Output = io::Result<()>> {
        async move {
            if !self.capabilities().atomic_replace {
                // No atomic rename to lean on: the honest best effort is a plain
                // durable write. Not crash-atomic — and the caller was told so by
                // `capabilities`, so this is a documented degrade, not a lie.
                // Both the bytes and, if this call created the file, the entry
                // naming them have to be flushed; there is no rename here to fold
                // the second into.
                self.write(path, contents).await?;
                self.sync(path, Durability::Durable).await?;
                return match parent_dir(path) {
                    Some(dir) => self.sync(dir, Durability::Durable).await,
                    None => Ok(()),
                };
            }
            let tmp = temp_sibling(path);
            // Any failure past this point must not leave the staging file behind,
            // and must never have touched the target — hence the whole dance
            // happens on `tmp` and only the rename names `path`.
            let staged = async {
                self.write(&tmp, contents).await?;
                self.sync(&tmp, Durability::Ordered).await?;
                // The sibling was just created, so it carries default
                // permissions rather than the target's. Carry the target's over
                // before the rename publishes them — a replacement changes
                // contents, never who may read them. A target that does not
                // exist yet has nothing to carry, and this is a no-op.
                //
                // After the flush, not before: a backend may well implement
                // `sync` by opening the path (`StdFs` does), and a target whose
                // mode this faithfully copies can be one that forbids exactly
                // that — a write-only `0o200` document is replaceable but not
                // openable for reading. Narrowing the sibling first would make
                // its own flush fail.
                self.copy_permissions(path, &tmp).await?;
                self.rename(&tmp, path).await
            }
            .await;
            match staged {
                // The bytes are already flushed and the rename has happened, so
                // the directory entry is the last thing standing between this
                // write and a power cut.
                Ok(()) => match parent_dir(path) {
                    Some(dir) => self.sync(dir, Durability::Durable).await,
                    // A bare relative filename, whose directory is the process's
                    // current one — not a path this crate holds, nor one it owns.
                    None => Ok(()),
                },
                Err(e) => {
                    // Best-effort cleanup: if even this fails the target is still
                    // untouched, so the atomicity promise holds regardless — the
                    // worst case is one stray dotfile, not a torn document.
                    let _ = self.remove_file(&tmp).await;
                    Err(e)
                }
            }
        }
    }
}

impl<S: Storage + ?Sized> Storage for &S {
    async fn write(&self, path: &Path, contents: &[u8]) -> io::Result<()> {
        (**self).write(path, contents).await
    }

    async fn create_new(&self, path: &Path, contents: &[u8]) -> io::Result<()> {
        (**self).create_new(path, contents).await
    }

    async fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        (**self).create_dir_all(path).await
    }

    async fn remove_file(&self, path: &Path) -> io::Result<()> {
        (**self).remove_file(path).await
    }

    async fn remove_dir_all(&self, path: &Path) -> io::Result<()> {
        (**self).remove_dir_all(path).await
    }

    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        (**self).rename(from, to).await
    }

    async fn copy_permissions(&self, from: &Path, to: &Path) -> io::Result<()> {
        (**self).copy_permissions(from, to).await
    }

    async fn set_executable(&self, path: &Path, executable: bool) -> io::Result<()> {
        (**self).set_executable(path, executable).await
    }

    async fn set_link(&self, path: &Path, target: &Path) -> io::Result<()> {
        (**self).set_link(path, target).await
    }

    fn capabilities(&self) -> Capabilities {
        (**self).capabilities()
    }

    async fn sync(&self, path: &Path, need: Durability) -> io::Result<()> {
        (**self).sync(path, need).await
    }

    async fn write_atomic(&self, path: &Path, contents: &[u8]) -> io::Result<()> {
        (**self).write_atomic(path, contents).await
    }
}

impl<S: Storage + ?Sized> Storage for Arc<S> {
    async fn write(&self, path: &Path, contents: &[u8]) -> io::Result<()> {
        (**self).write(path, contents).await
    }

    async fn create_new(&self, path: &Path, contents: &[u8]) -> io::Result<()> {
        (**self).create_new(path, contents).await
    }

    async fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        (**self).create_dir_all(path).await
    }

    async fn remove_file(&self, path: &Path) -> io::Result<()> {
        (**self).remove_file(path).await
    }

    async fn remove_dir_all(&self, path: &Path) -> io::Result<()> {
        (**self).remove_dir_all(path).await
    }

    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        (**self).rename(from, to).await
    }

    async fn copy_permissions(&self, from: &Path, to: &Path) -> io::Result<()> {
        (**self).copy_permissions(from, to).await
    }

    async fn set_executable(&self, path: &Path, executable: bool) -> io::Result<()> {
        (**self).set_executable(path, executable).await
    }

    async fn set_link(&self, path: &Path, target: &Path) -> io::Result<()> {
        (**self).set_link(path, target).await
    }

    fn capabilities(&self) -> Capabilities {
        (**self).capabilities()
    }

    async fn sync(&self, path: &Path, need: Durability) -> io::Result<()> {
        (**self).sync(path, need).await
    }

    async fn write_atomic(&self, path: &Path, contents: &[u8]) -> io::Result<()> {
        (**self).write_atomic(path, contents).await
    }
}

/// The durability guarantees a [`Storage`] backend can make — declared by the
/// backend through [`Storage::capabilities`], honored by the crash-safety
/// machinery in [`ChangeSet`](crate::ChangeSet).
///
/// The point of naming these explicitly is that a transaction must run correctly
/// over backends that keep very different promises. Rather than assume a
/// guarantee and corrupt data on the backend that cannot keep it, the apply path
/// reads the capabilities and picks the strongest *protocol the backend actually
/// supports*:
/// a filesystem gets atomic-rename writes and a journal; a transactional store is
/// handed the whole change set to commit itself; a backend that can promise
/// neither still works, it simply cannot claim a write survives a crash.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Capabilities {
    /// The backend can replace an existing file's contents in one indivisible
    /// step, so no crash exposes a half-written file — an observer sees the whole
    /// old contents or the whole new. On a filesystem this is realized by
    /// [`Storage::write_atomic`]'s write-temp-then-`rename`; a backend may
    /// instead be atomic by nature.
    pub atomic_replace: bool,

    /// The backend can create a file *only if nothing is at its path yet*, as
    /// one operation — [`Storage::create_new`]. The create and the
    /// test-for-existence cannot be split: two writers racing to the same name
    /// see exactly one succeed and the other told
    /// [`AlreadyExists`](io::ErrorKind::AlreadyExists), with no window between
    /// the test and the create for a half-written file to slip through. This is
    /// the primitive an append-only, write-once consumer builds its whole
    /// concurrency story on, which is why it is declared rather than emulated:
    /// a check-then-write emulation has the window in it, and a backend that
    /// cannot close the window must say so instead of pretending.
    pub exclusive_create: bool,

    /// How strong the backend's [`Storage::sync`] is: whether it can flush at
    /// all, and if so whether a flush merely orders writes or carries them
    /// through a power cut. `fsync` on `std::fs`, `FileSystemSyncAccessHandle
    /// .flush()` on OPFS, the implicit durability of a committed IndexedDB
    /// transaction.
    pub sync_guarantee: SyncGuarantee,

    /// The backend commits changes to *many* objects as one indivisible unit, so
    /// this crate's write-ahead journal would be redundant and a caller should
    /// defer to the backend instead. True for IndexedDB; false for a plain
    /// filesystem, where multi-file atomicity is the journal's job to provide.
    pub native_transactions: bool,
}

impl Capabilities {
    /// Promises nothing — the safe assumption for an unknown backend, and the
    /// [`Storage::capabilities`] default. Every field is the pessimistic value,
    /// so code that checks a capability before relying on it takes the most
    /// defensive branch unless a backend has explicitly earned a lighter one.
    pub const NONE: Self = Self {
        atomic_replace: false,
        exclusive_create: false,
        sync_guarantee: SyncGuarantee::None,
        native_transactions: false,
    };

    /// A conventional local filesystem: atomic replacement by rename, exclusive
    /// create (`O_CREAT|O_EXCL`, honored by every OS this crate targets), and
    /// durable fsync — but no native multi-object transaction (that is the
    /// journal's job). What [`StdFs`] reports on every platform this crate
    /// targets.
    pub const LOCAL_FS: Self = Self {
        atomic_replace: true,
        exclusive_create: true,
        sync_guarantee: SyncGuarantee::Durable,
        native_transactions: false,
    };

    /// An in-process, memory-only store ([`InMemoryFs`]): every mutation takes
    /// the backend's single lock for its whole duration, so one write already
    /// swaps old bytes for new as one indivisible step — no separate
    /// temp-then-rename dance is needed for `atomic_replace` to be true. But
    /// nothing here is backed by anything other than process memory, so its
    /// `sync_guarantee` is [`SyncGuarantee::None`]: there is nothing to flush,
    /// and the entire store evaporates the instant the process exits — it cannot
    /// even promise ordering against a crash it will not survive.
    /// `native_transactions`
    /// is false too — the lock makes each *single* call atomic, not a batch of
    /// several calls committed together, so a multi-file change set still
    /// needs the write-ahead journal over this backend exactly as it would over
    /// a real filesystem. `exclusive_create` is true on the same grounds as
    /// `atomic_replace`: one locked call checks and inserts without anything
    /// interleaving.
    pub const IN_MEMORY: Self = Self {
        atomic_replace: true,
        exclusive_create: true,
        sync_guarantee: SyncGuarantee::None,
        native_transactions: false,
    };
}

/// What a caller needs from one [`Storage::sync`] call — the *weakest* guarantee
/// that is still correct at that point, so that a backend able to serve it
/// cheaply is free to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Durability {
    /// A barrier: everything this backend was asked to write before this call —
    /// to the named path *or to any other* — must land before anything written
    /// after it. It says nothing about *when*: a crash may still lose the lot,
    /// only never a suffix without its prefix.
    ///
    /// The barrier is backend-wide on purpose, not scoped to the one path
    /// named. [`Storage::write_atomic`] only needs the narrow reading — the
    /// rename must not be seen before the bytes it publishes — but
    /// [`crate::ordered`] builds on the wide one: a batch whose second tier
    /// must never be seen without its first is ordering writes to *different*
    /// files against each other, and a "barrier" that only ordered a file
    /// against itself could not say that. Both `fsync` (which completes the
    /// named writes outright) and Apple's `F_BARRIERFSYNC` (a queue barrier
    /// the whole device honors) keep the wide promise; a primitive that
    /// orders only one file's own writes — `sync_file_range` and its kin —
    /// does not, and a backend with nothing stronger must declare
    /// [`SyncGuarantee::None`] rather than a barrier it cannot keep. On Apple
    /// platforms the distinction from [`Durable`](Durability::Durable) is the
    /// difference between a barrier and draining the drive's write cache.
    ///
    /// The wide promise has a corollary both protocols lean on: once any
    /// *later* write is durably on disk, everything ordered before it is too —
    /// a barrier followed by one durable flush makes the whole prefix durable,
    /// without flushing it piece by piece.
    Ordered,
    /// Once the call returns, the bytes survive power loss.
    Durable,
}

/// How strong a backend's [`Storage::sync`] actually is — the standing answer to
/// a [`Durability`] request, declared once in [`Capabilities`] rather than
/// discovered per call.
///
/// Deliberately three-valued rather than the "can this backend flush?" boolean
/// it replaces, because that question has a common and useful middle answer it
/// could not express: a backend that orders writes against each other without
/// paying for a device-wide cache drain. Offered only `true` and `false`, such a
/// backend has to either overstate — claiming a durability it does not deliver —
/// or understate, claiming it cannot flush at all when ordering is precisely
/// what [`Storage::write_atomic`] asks it for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SyncGuarantee {
    /// `sync` does nothing: an in-memory store, or a port with no flush
    /// primitive under it to call.
    None,
    /// `sync` orders writes against each other, but does not promise any of them
    /// outlives a power cut.
    Ordered,
    /// `sync` flushes through to durable storage.
    Durable,
}

impl SyncGuarantee {
    /// Whether a backend making this guarantee can honor `need`.
    pub const fn satisfies(self, need: Durability) -> bool {
        match need {
            Durability::Ordered => !matches!(self, SyncGuarantee::None),
            Durability::Durable => matches!(self, SyncGuarantee::Durable),
        }
    }
}

/// Create `dir` and every missing parent, returning the directories whose
/// entry set the creation changed: each directory made, plus the deepest
/// pre-existing ancestor, which received the topmost new name. Empty when
/// `dir` already existed.
///
/// The return value is the flush list a caller owes. A directory entry is its
/// own write, persisting separately from anything under it — so a
/// `create_dir_all` nobody flushes is a chain of names a power cut can take
/// back, leaving a durably-flushed file inside a directory that no longer
/// exists. [`crate::ordered`] flushes the list with each tier and the journal
/// flushes it before committing intent into a fresh
/// [home](crate::Journal::kept_in); the walk costs one existence probe per
/// ancestor, and nothing at all past the first one that already exists.
pub(crate) async fn create_dir_all_traced<FS: Storage>(
    fs: &FS,
    dir: &Path,
) -> io::Result<Vec<PathBuf>> {
    let mut changed = Vec::new();
    let mut cur = Some(dir);
    while let Some(d) = cur {
        if fs.try_exists(d).await? {
            // The deepest ancestor that already exists gains the topmost new
            // entry — but only if anything is being created at all.
            if !changed.is_empty() {
                changed.push(d.to_path_buf());
            }
            break;
        }
        changed.push(d.to_path_buf());
        cur = parent_dir(d);
    }
    if changed.is_empty() {
        return Ok(changed);
    }
    fs.create_dir_all(dir).await?;
    Ok(changed)
}

/// The directory holding `path`, when there is one to name. `Path::parent`
/// answers `Some("")` for a bare relative filename like `index.md` — the
/// process's current directory, which this crate neither holds a path to nor owns —
/// and that empty path is not something a backend can open, so it is folded in
/// with "no parent" here rather than at each call site.
pub(crate) fn parent_dir(path: &Path) -> Option<&Path> {
    path.parent().filter(|p| !p.as_os_str().is_empty())
}

/// The temporary sibling [`Storage::write_atomic`]'s default protocol stages a
/// write through before renaming it into place. A dotted, suffixed name in the
/// target's own directory: dotted and suffixed so it will not collide with a
/// real file, and a *sibling* so the rename that follows never crosses a
/// filesystem boundary.
pub(crate) fn temp_sibling(path: &Path) -> PathBuf {
    let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("file");
    path.with_file_name(format!(".{name}.fstx-tmp"))
}

impl Storage for StdFs {
    async fn write(&self, path: &Path, contents: &[u8]) -> io::Result<()> {
        std::fs::write(path, contents)
    }

    async fn create_new(&self, path: &Path, contents: &[u8]) -> io::Result<()> {
        use std::io::Write as _;

        // `O_CREAT|O_EXCL` (`CREATE_NEW` on Windows) — the one place the OS
        // itself promises the create and the existence test are indivisible.
        let mut file = std::fs::File::create_new(path)?;
        file.write_all(contents)
    }

    async fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        std::fs::create_dir_all(path)
    }

    async fn remove_file(&self, path: &Path) -> io::Result<()> {
        std::fs::remove_file(path)
    }

    async fn remove_dir_all(&self, path: &Path) -> io::Result<()> {
        std::fs::remove_dir_all(path)
    }

    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        std::fs::rename(from, to)
    }

    #[cfg(unix)]
    async fn set_executable(&self, path: &Path, executable: bool) -> io::Result<()> {
        use std::os::unix::fs::PermissionsExt as _;

        let mut permissions = std::fs::metadata(path)?.permissions();
        let held = permissions.mode();
        // Every bit the owner's own umask chose stays theirs. This carries one
        // bit, so it sets one bit: the execute bits follow the read bits, so a
        // file readable by its group becomes runnable by its group and a
        // private file stays private.
        let mode = if executable {
            held | ((held & 0o444) >> 2)
        } else {
            held & !0o111
        };
        if mode == held {
            return Ok(());
        }
        permissions.set_mode(mode);
        std::fs::set_permissions(path, permissions)
    }

    // On a platform with no execute bit, `set_executable`'s default — doing
    // nothing — is already correct, so only unix overrides it. `set_link` is
    // the other way round: Windows has symbolic links and does not hand them
    // out (creating one wants a privilege an ordinary account lacks), so the
    // default's refusal is the honest answer there and only unix overrides.

    #[cfg(unix)]
    async fn set_link(&self, path: &Path, target: &Path) -> io::Result<()> {
        // Made at a temporary sibling and renamed over the target, the same
        // shape as `write_atomic` and for the same reason: remove-then-symlink
        // has a window in which `path` names nothing, and a crash in it loses
        // the file that was there without leaving the link that was promised.
        // The rename is the atomic instant; a failure before it leaves the
        // target exactly as it was, plus at worst one stray dotfile.
        let tmp = temp_sibling(path);
        let _ = std::fs::remove_file(&tmp);
        std::os::unix::fs::symlink(target, &tmp)?;
        match std::fs::rename(&tmp, path) {
            Ok(()) => Ok(()),
            Err(e) => {
                let _ = std::fs::remove_file(&tmp);
                Err(e)
            }
        }
    }

    async fn copy_permissions(&self, from: &Path, to: &Path) -> io::Result<()> {
        let perms = match std::fs::metadata(from) {
            Ok(meta) => meta.permissions(),
            // Nothing to carry over: `write_atomic` is creating `from` rather
            // than replacing it, so the new file's default permissions are the
            // right ones and there is no prior state to lose.
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
            Err(e) => return Err(e),
        };
        // Deliberately best-effort. On a filesystem with no permission model —
        // exFAT or FAT32 on a USB stick, some FUSE mounts — `chmod` refuses
        // outright, but every file there already reports the same mount-wide
        // mode, so there was never a permission to preserve and failing the
        // whole document write over it would be absurd. Where modes *are* real,
        // this is a chmod on a file this process created moments ago and owns,
        // which does not fail for any reason a caller could act on.
        let _ = std::fs::set_permissions(to, perms);
        Ok(())
    }

    fn capabilities(&self) -> Capabilities {
        // Every OS this crate targets gives an atomic same-filesystem rename and an
        // fsync. `std::fs::rename` replaces the destination on all of them —
        // POSIX by definition, Windows via `MoveFileEx(MOVEFILE_REPLACE_EXISTING)`
        // — so the write-temp-then-rename protocol in the default `write_atomic`
        // is genuinely atomic here.
        Capabilities::LOCAL_FS
    }

    async fn sync(&self, path: &Path, need: Durability) -> io::Result<()> {
        // `sync_all` is the only flush in the standard library, and it is the
        // strong one — on Apple platforms it is `F_FULLFSYNC`, a drain of the
        // drive's whole write cache. By default both requests are answered
        // with it: stronger than `Ordered` asked for, which a backend is
        // always allowed to be. The `barrier-fsync` feature is the cheaper
        // answer where one exists — `F_BARRIERFSYNC` on Apple, a queue
        // barrier the device honors — and `sync_file` below is where the
        // request-by-request choice lives.
        sync_path(path, need)
    }
}

/// Flush exactly `path` — file or directory — to the strength `need` asks for.
/// The one place a real OS difference lives, quarantined behind the port here
/// rather than leaking up into the engine.
fn sync_path(path: &Path, need: Durability) -> io::Result<()> {
    // A fresh read handle is enough: fsync acts on the inode, not the descriptor,
    // so it flushes writes made through any handle. A path that does not exist (a
    // fallback write that failed before creating it) has nothing to flush and is
    // not an error.
    //
    // Opening a *directory* for reading and fsyncing it — how
    // [`Storage::write_atomic`] makes its rename durable — is a POSIX facility.
    // Windows has no equivalent (`MoveFileEx`'s durability is a separate story),
    // and rejects the open outright, so there the directory step is skipped
    // rather than faked.
    #[cfg(not(unix))]
    if path.is_dir() {
        return Ok(());
    }
    match std::fs::File::open(path) {
        Ok(file) => sync_file(&file, need)?,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    Ok(())
}

/// Flush one open handle to the strength `need` asks for — with the
/// `barrier-fsync` feature on an Apple platform, the one place `Ordered` is
/// answered more cheaply than `Durable`.
#[cfg(all(feature = "barrier-fsync", target_vendor = "apple"))]
fn sync_file(file: &std::fs::File, need: Durability) -> io::Result<()> {
    use std::os::fd::AsRawFd as _;

    match need {
        // A queue barrier: everything issued before it reaches the device
        // before anything issued after, without waiting for the drive to
        // drain its cache — which is the entire request `Ordered` makes, and
        // on these platforms often the difference between microseconds and
        // milliseconds. Works on files and directories alike.
        Durability::Ordered => {
            // SAFETY: `fcntl` with `F_BARRIERFSYNC` takes no argument beyond
            // the descriptor, and `file` holds that descriptor open for the
            // whole call.
            if unsafe { libc::fcntl(file.as_raw_fd(), libc::F_BARRIERFSYNC) } != -1 {
                return Ok(());
            }
            // A filesystem with no barrier support — a network mount, an
            // exotic FUSE — refuses the fcntl. Plain `fsync` still keeps the
            // ordering promise (the named writes reach the device before the
            // call returns, so nothing later can precede them); it is
            // `sync_all`'s `F_FULLFSYNC` that would overshoot here.
            //
            // SAFETY: as above — a plain fsync of a descriptor `file` keeps
            // open.
            if unsafe { libc::fsync(file.as_raw_fd()) } != -1 {
                return Ok(());
            }
            Err(io::Error::last_os_error())
        }
        Durability::Durable => file.sync_all(),
    }
}

/// Without the feature (or off Apple), both strengths are answered with
/// `sync_all` — stronger than `Ordered` asked for, which a backend may always
/// be, never weaker.
#[cfg(not(all(feature = "barrier-fsync", target_vendor = "apple")))]
fn sync_file(file: &std::fs::File, need: Durability) -> io::Result<()> {
    let _ = need;
    file.sync_all()
}

#[cfg(test)]
mod tests {
    use crate::exec::block_on;

    use super::*;

    fn tmp(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("fstx-fs-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    // ---- capability declaration ----

    #[test]
    fn stdfs_declares_the_local_filesystem_guarantees() {
        // The native adapter promises atomic replacement, exclusive create, and
        // durable fsync, but not native transactions — the journal's job, not
        // the filesystem's.
        assert_eq!(StdFs.capabilities(), Capabilities::LOCAL_FS);
        assert!(StdFs.capabilities().atomic_replace);
        assert!(StdFs.capabilities().exclusive_create);
        assert_eq!(StdFs.capabilities().sync_guarantee, SyncGuarantee::Durable);
        assert!(!StdFs.capabilities().native_transactions);
    }

    #[test]
    fn a_guarantee_answers_only_the_requests_it_can_keep() {
        // The whole point of the three-valued guarantee: the middle one can serve
        // `write_atomic`'s staging flush without being able to serve its final
        // one, which a boolean had no way to say.
        assert!(!SyncGuarantee::None.satisfies(Durability::Ordered));
        assert!(!SyncGuarantee::None.satisfies(Durability::Durable));
        assert!(SyncGuarantee::Ordered.satisfies(Durability::Ordered));
        assert!(!SyncGuarantee::Ordered.satisfies(Durability::Durable));
        assert!(SyncGuarantee::Durable.satisfies(Durability::Ordered));
        assert!(SyncGuarantee::Durable.satisfies(Durability::Durable));
    }

    // ---- the atomic-write protocol ----

    // ---- exclusive create ----

    #[test]
    fn create_new_writes_a_fresh_file() {
        let root = tmp("create-new");
        let path = root.join("once.md");
        block_on(StdFs.create_new(&path, b"first")).unwrap();
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "first");
    }

    #[test]
    fn create_new_refuses_an_occupied_path_with_already_exists() {
        // `AlreadyExists` is the load-bearing half of the contract: a
        // write-once caller branches on exactly this kind, so it must not
        // arrive as anything vaguer.
        let root = tmp("create-new-taken");
        let path = root.join("once.md");
        block_on(StdFs.create_new(&path, b"first")).unwrap();
        let err = block_on(StdFs.create_new(&path, b"second")).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::AlreadyExists);
        // The loser changed nothing: the winner's bytes are still what's there.
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "first");
    }

    #[test]
    fn the_default_create_new_declines_rather_than_emulating() {
        // A backend that overrides neither `create_new` nor `capabilities`
        // must refuse, not check-then-write: the emulation's window is what a
        // caller reaching for this method cannot tolerate.
        struct Bare;
        impl ReadStorage for Bare {
            async fn read(&self, _: &Path) -> io::Result<Vec<u8>> {
                unreachable!()
            }
            async fn read_to_string(&self, _: &Path) -> io::Result<String> {
                unreachable!()
            }
            async fn read_dir(&self, _: &Path) -> io::Result<Vec<DirEntry>> {
                unreachable!()
            }
            async fn metadata(&self, _: &Path) -> io::Result<Metadata> {
                unreachable!()
            }
        }
        impl Storage for Bare {
            async fn write(&self, _: &Path, _: &[u8]) -> io::Result<()> {
                unreachable!()
            }
            async fn create_dir_all(&self, _: &Path) -> io::Result<()> {
                unreachable!()
            }
            async fn remove_file(&self, _: &Path) -> io::Result<()> {
                unreachable!()
            }
            async fn remove_dir_all(&self, _: &Path) -> io::Result<()> {
                unreachable!()
            }
            async fn rename(&self, _: &Path, _: &Path) -> io::Result<()> {
                unreachable!()
            }
        }
        assert!(!Bare.capabilities().exclusive_create);
        let err = block_on(Bare.create_new(Path::new("x"), b"")).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::Unsupported);
    }

    // ---- sync ----

    #[test]
    fn sync_of_a_missing_path_is_not_an_error() {
        // A fallback write that failed before creating the file leaves nothing to
        // flush; asking to sync it is a no-op, not a failure.
        let root = tmp("sync-missing");
        block_on(StdFs.sync(&root.join("never-created.md"), Durability::Durable)).unwrap();
    }

    #[test]
    fn sync_flushes_a_directory_as_readily_as_a_file() {
        // `write_atomic` makes its rename durable by syncing the directory, so a
        // directory has to be something `sync` accepts rather than something it
        // reaches only via a file's parent.
        let root = tmp("sync-dir");
        block_on(StdFs.sync(&root, Durability::Durable)).unwrap();
    }

    #[test]
    fn sync_answers_both_strengths_on_files_and_directories() {
        // With `barrier-fsync` on an Apple platform this exercises the
        // F_BARRIERFSYNC path for `Ordered`; everywhere else it is `sync_all`
        // twice. Either way both strengths must simply work, on both kinds of
        // object, because both protocols ask for both.
        let root = tmp("sync-strengths");
        let file = root.join("doc.md");
        std::fs::write(&file, "bytes").unwrap();
        for need in [Durability::Ordered, Durability::Durable] {
            block_on(StdFs.sync(&file, need)).unwrap();
            block_on(StdFs.sync(&root, need)).unwrap();
        }
    }
}
