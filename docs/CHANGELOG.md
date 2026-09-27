# Changelog

What has changed in fs-transaction, release by release, for someone deciding
whether to move to a newer one.

The bulleted groups below — **Breaking**, **Added**, **Fixed**, **Changed**,
and a **Behavioural changes** section under them — are **generated** from the
commit log by `dx changelog --write`, which reads the org's shared
`cliff.toml`. Anything inside a `git-cliff:begin` / `git-cliff:end` pair is
rewritten on every run, so an edit made there is an edit thrown away.
Everything else is handwritten and stays: this prose, and any intro a release
needs under its own heading, below the end marker where regeneration cannot
reach it.

**Behavioural changes** are collected from `Behavioural-change:` trailers on the
commits themselves: one trailer per difference a caller who upgrades without
editing their own code would observe.

## Unreleased

<!-- git-cliff:begin — generated; edits here are overwritten -->

_No commits since the last tag._

<!-- git-cliff:end -->

## v0.4.0 — 2026-09-27

### Breaking

- **change** — refuse sets replay cannot recover, and roll back by moving aside ([`7f553a5`](https://github.com/diaryx-org/fs-transaction/commit/7f553a5dc6720dd12589f051f360cd1e756de816))
- **replayable** — refuse a set that writes a path and later renames it ([`8f8e1bf`](https://github.com/diaryx-org/fs-transaction/commit/8f8e1bffb5dc70ed0e02a1a73313a8ce4edc026d))

### Changed

- **replayable** — take path keys as slices ([`9cba584`](https://github.com/diaryx-org/fs-transaction/commit/9cba5841419f7658fba228d6dfa8d6c6adcb0760))
- **change** — route the executor through the port ([`1c5f9e9`](https://github.com/diaryx-org/fs-transaction/commit/1c5f9e9c5c23e9517fda282af3cffbee5be1b8bd))

### Behavioural changes

- a journaled set that swaps or chains renames, renames away from a path it later uses, renames onto a path it earlier used, flips a bit on a file it later replaces with a link, copies from a path it changes, or renames a symbolic link now fails with Error::Unreplayable before writing anything.

- a set that removes files or renames over them now costs one more durable directory flush when it lands, and leaves .name.fstx-aside-N siblings on disk while it applies.

- a rolled-back set restores removed and displaced files with their original permissions instead of the default mode.

- a journaled set that writes a path and later renames it is now refused with Error::Unreplayable.

## v0.3.0 — 2026-09-17

### Breaking

- **fs** — a strength below Ordered — Pushed, and a tier that pays one barrier ([`b023e28`](https://github.com/diaryx-org/fs-transaction/commit/b023e282326623a7e600596a766312ee8e8be2a6))

### Behavioural changes

- the sync requests a backend sees from an `OrderedBatch`
change. Each tier's files and directories arrive as `Pushed` requests, and
the tier is closed by a single `Ordered` (or, for the last tier, `Durable`)
request at the root, where before every debt was an `Ordered` request and
only the last tier's cap was `Durable`. `ChangeSet::apply` and `recover`
likewise push, rather than barrier, the name-stable debts they settle
before the one drain at the root; the per-op barriers `exec` issues as it
runs are unchanged.

- what a crash can leave of an interrupted tier. Nothing
orders the files of one tier against each other — that was always the
promise — but with a barrier per file the interrupted tier's files landed
in flush order, so a crash left at most the file in flight torn and every
earlier one whole. With pushes and one barrier, any number of the
interrupted tier's `create_new` files may be torn, independently. A
consumer whose names promise their contents must be able to recognise and
discard every torn file nothing names yet, not just one; the "nothing names
it yet" half — no later tier without an earlier one — is unchanged. Writes
through `replace` remain whole-or-nothing, since that barrier is the
protocol's own.

## v0.2.1 — 2026-08-25

### Added

- **change** — a set can expect what its caller read ([`96aa598`](https://github.com/diaryx-org/fs-transaction/commit/96aa598e8826da65786e5c10622f1344b25690ff))

## v0.2.0 — 2026-08-25

### Breaking

- **transaction** — invert the filesystem port onto prov-transaction ([`33dead6`](https://github.com/diaryx-org/fs-transaction/commit/33dead69e0b052586102c61e94b0119630cc4642))
- **transaction** — make the journal name configurable, defaulting generically ([`d76f22a`](https://github.com/diaryx-org/fs-transaction/commit/d76f22afda5fe3f23fa612f277424832b9f6ecae))
- stand up fs-transaction as its own crate ([`8d9db24`](https://github.com/diaryx-org/fs-transaction/commit/8d9db24b15c00dedb8a30e7f70c01f9770f50d91))
- **fs** — add exclusive create to the storage port ([`c33b20c`](https://github.com/diaryx-org/fs-transaction/commit/c33b20c4baaa8e5a88703a31d904388cf3e0b8ef))
- **change** — carry execute bits and symbolic links through a change set ([`ce3d493`](https://github.com/diaryx-org/fs-transaction/commit/ce3d493415694f8152ec7235960b82e5a2beb97b))
- bump version to 0.2.0 ([`1467919`](https://github.com/diaryx-org/fs-transaction/commit/14679192eae44e6691a9f8e80342a06787a46098))
- **memory** — replace an occupied file destination on rename, as the port promises ([`f4ee848`](https://github.com/diaryx-org/fs-transaction/commit/f4ee84879bf8582044ee359119d4e784149f7f39))
- **change** — make both of apply's answers durable, not merely consistent ([`04eaf6a`](https://github.com/diaryx-org/fs-transaction/commit/04eaf6a64c4b0089afbafb053429b053f71a8fa9))
- **change** — harden the certification protocol against its review ([`fc69e5d`](https://github.com/diaryx-org/fs-transaction/commit/fc69e5d321afb23a88e4ffdd503a7bc6da3fc0ad))

### Added

- **ordered** — add an ordered-batch protocol beside the journaled change set ([`4c8e0c0`](https://github.com/diaryx-org/fs-transaction/commit/4c8e0c0bd1535350be83608c10772b89bed6a107))
- **fs** — answer ordered syncs with a barrier on Apple platforms ([`a96cd4b`](https://github.com/diaryx-org/fs-transaction/commit/a96cd4b0ae953ea23223cac37c9dc99f41a493b1))
- **journal** — let a journal live outside the tree it applies to ([`006e365`](https://github.com/diaryx-org/fs-transaction/commit/006e365fe28cdea1e457e1de7af388acd4f125a5))
- **fs** — split replace out of write_atomic and batch every protocol's drains ([`1963994`](https://github.com/diaryx-org/fs-transaction/commit/1963994437c1f14d32e1debcca22bee79d4e169b))

### Fixed

- **store** — keep a document's permissions across an atomic write ([`1dbcb22`](https://github.com/diaryx-org/fs-transaction/commit/1dbcb2212f3ff139b05818d44dfa0f5c3539d6c9))
- flush the directory entries a creation chain mints ([`0a54344`](https://github.com/diaryx-org/fs-transaction/commit/0a543448073e1bc5a4eb75a07a880180642f9af3))
- **ordered** — land replaced writes through the backend's own write_atomic ([`719ac9a`](https://github.com/diaryx-org/fs-transaction/commit/719ac9af589539fd9482e3e474a62b299c385ff2))
- **journal** — refuse escaping paths and impossible op counts at replay ([`1698959`](https://github.com/diaryx-org/fs-transaction/commit/16989595a078801e16433545b982fedc46341d2d))
- **change** — roll a displaced link back as a link, never as a copy ([`6ad40c0`](https://github.com/diaryx-org/fs-transaction/commit/6ad40c04263eac123e438ae262cedbcc499e15c0))
- **change** — refuse to set the execute bit through a symbolic link ([`4441def`](https://github.com/diaryx-org/fs-transaction/commit/4441defd5c7449741e44cc0fd09effe24811be5c))
- **memory** — follow links on write, replace them on write_atomic, move them on rename ([`84de85f`](https://github.com/diaryx-org/fs-transaction/commit/84de85f771bea035cb8d8e8d6f0c216363cef19c))
- **journal** — a homed journal owns no path in the root ([`35c2922`](https://github.com/diaryx-org/fs-transaction/commit/35c292246235a1f0c9ffc1a5c0d6ae8ef3c50775))

### Changed

- extract prov-store crate for the write surface ([`9bfd35c`](https://github.com/diaryx-org/fs-transaction/commit/9bfd35c378cdf0778b5bb0c1c2ae690e2b67e8c1))

### Uncategorised — triage before release

- Extract transaction and journal recovery into `prov-transaction` ([`20f43d1`](https://github.com/diaryx-org/fs-transaction/commit/20f43d1184fb593fdede171fc389a482867ec4bb))
- update gitignore ([`cda3f14`](https://github.com/diaryx-org/fs-transaction/commit/cda3f14f23ed807f17225c27c49e254affa3232e))

### Behavioural changes

- replacing an existing file through `Storage::write_atomic`
— which is every document write, `ChangeSet` application, and journal write —
now leaves the file's access permissions as it found them instead of resetting
them to the process umask's default. A caller that relied on a save
normalizing a restrictive mode to a readable one will find the file still
restricted. Backends that wrap `StdFs` by forwarding each method individually
should forward `copy_permissions` too; without it they silently take the
no-op default and keep the old widening behaviour.

- `ChangeSet::apply` and `recover` now return
 `prov_transaction::Error` rather than `prov::Error`. A caller using `?`
 inside a function returning `prov::Result` is unaffected — the `From` impl
 converts — but one that matches the returned error directly must call
 `.into()` first. The variants map one-to-one, except that a corrupt
 journal, an unfinishable replay, and a non-UTF-8 staged path now arrive as
 `Error::Structure` with the same text rather than as themselves.

- `prov-transaction` no longer has `yaml`, `json`,
 `toml`, or `fig-lang` features. It never read a metadata format — the
 features only ever forwarded to `prov-graph` and `prov-store` — so a
 dependent that named one must drop it. Depending on `prov` is unaffected;
 its own format features no longer forward here.

- `prov_transaction::write_blob_atomic`, `discard_file`,
 and `write_probe` are gone, with no replacement. Each was a two-line
 wrapper over the `Storage` port; a caller that needs one can call
 `Storage::write_atomic`, `remove_file`, or `write` directly.

- the default journal is now `.fstx-journal` and the
 `write_atomic` staging sibling is `.<name>.fstx-tmp`, where both were
 `.prov-*`. A workspace opened through `prov` is unaffected — it configures
 `.prov-journal` explicitly — but a direct `prov-transaction` user who
 crashed mid-apply under a previous version must either recover with
 `Journal::named(".prov-journal")` or move the file before upgrading.

- `prov_transaction::JOURNAL_NAME` and `is_journal_path`
 are gone, replaced by `Journal::DEFAULT_NAME` and `Journal::owns_path`,
 which answer for the journal actually in use rather than for a global
 constant. `prov::journal::JOURNAL_NAME` still exists and still reads
 `.prov-journal`.

- `prov::recover` now returns `prov::Error` rather than
 `prov_transaction::Error`, so a caller matching its failure directly no
 longer needs `.into()`. `prov::journal::{decode, encode}` became public,
 having previously been a `pub(crate)` import nothing used.

- a replaced write in an OrderedBatch now flushes its
parent directory durable even under an Ordered finality, and an
Ordered-finality batch is only drain-free when it is create-only.

- recovering a journal that names paths outside the
root now fails with Error::Escape instead of writing them.

- removing a dangling symlink through a ChangeSet now
succeeds (the link itself is the undo) where it previously failed with
NotFound while capturing bytes through the link.

- a SetExecutable op whose path holds a symlink now
fails the set instead of silently flipping the referent's bit.

- over InMemoryFs, a write to a symlinked path now
lands in the target (previously it landed nowhere observable), and
write_atomic to one replaces the link with a regular file.

- InMemoryFs::rename onto an existing file now
succeeds and replaces it (previously AlreadyExists); onto an existing
symlink it replaces the link (previously AlreadyExists).

- applies that rename, remove, flip bits, or mint
directories now issue trailing syncs (and one durable flush) before
returning; sets over backends declaring SyncGuarantee::None are
unchanged, as every sync declines.

- a backend that overrides write_atomic but not the
new replace member is no longer reached by ChangeSet, journal replay, or
OrderedBatch writes — they call replace, whose default stages the
temp-then-rename dance against the backend's primitives. Such an adapter
must move (or copy) its override to replace; write_atomic's default then
composes on it.

- a failed final flush now rolls the set back instead
of returning with the ops applied; a rename op captures and restores a
displaced destination on rollback; abort and apply event sequences carry
the reordered barriers and anchored drains described above.

