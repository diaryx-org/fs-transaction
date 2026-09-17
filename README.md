# fs-transaction

Multi-file filesystem transactions that survive a crash.

This project was created for and is maintained by [Diaryx](https://github.com/diaryx-org),
and is directly used in [prov](https://github.com/diaryx-org/prov) and [historica](https://github.com/historica).
It is useful for people who need to maintain consistency across multiple files without a database.

`fs-transaction`'s `ChangeSet` stages writes, renames, removals, copies, execute-bit flips and symbolic links,
then applies them all-or-nothing:
an error unwinds every operation already applied,
and a write-ahead journal makes a committed set recoverable after a power cut.
Files stay ordinary files — nothing here changes how the tree is *read*, only how it is *written*.

```toml
[dependencies]
fs-transaction = "0.2"
```

```rust
use fs_transaction::{ChangeSet, Result, StdFs, exec::block_on, recover};
use std::path::Path;

fn rearrange(root: &Path) -> Result<()> {
    // Finish anything a previous crash left journaled, before reading the tree.
    block_on(recover(&StdFs, root))?;

    let mut change = ChangeSet::new();
    change.write("a.md", "hello");
    change.rename("old.md", "b.md");
    change.remove("stale.md");

    // All four land, or none of them do.
    block_on(change.apply(&StdFs, root))
}
```

## Expect what you read

A set is computed from a reading of the tree,
and the tree may move between that reading and the apply.
`expect` stages the reading itself — the bytes a path held,
or `expect_absent`, its absence —
and `apply` checks every expectation before writing anything:
one that no longer holds refuses the whole set with `Error::Drifted`,
nothing touched, nothing journaled.
Re-read, restage, retry — optimistic concurrency, without a lock.

```rust,ignore
change.expect("notes/a.md", bytes_i_read);   // refuse if someone else wrote it
change.expect_absent("notes/new.md");        // refuse if someone else created it
```

## When half-applied is legal

All-or-nothing is for trees where a half-applied change is illegal.
An append-only, content-addressed store is built the other way
— every partially-written batch is a state it already tolerates
— so a journal there pays to rule out states that were never wrong.
`OrderedBatch` gives such a tree what it actually needs:
durability and ordering, with no journal and no recovery step.
Tiers of writes separated by barriers;
a crash leaves some prefix of the tiers,
and nothing durable ever names anything that is not durable yet.

```rust
use fs_transaction::{OrderedBatch, StdFs, exec::block_on};
use fs_transaction::fs::Durability;
use std::path::Path;

fn record(store: &Path) -> fs_transaction::Result<()> {
    let mut batch = OrderedBatch::new();
    batch.create_new("blobs/9f86d081", "payload");     // exclusive, write-once
    batch.barrier();          // nothing below may be seen without everything above
    batch.create_new("revisions/50d858e0.rev", "the record naming it");
    block_on(batch.apply(&StdFs, store, Durability::Durable))
}
```

The final argument is the strength of the batch's own landing:
`Durable` survives a power cut once `apply` returns;
`Ordered` keeps the tree consistent but lets the tail go with the crash
—often enough, and one less drain of the drive's cache;
`Pushed` hands the last tier to the device and leaves the closing barrier to you,
for a store that lands its set one batch at a time and syncs once at the end.

A tier of `N` files in `D` directories costs `N + D` pushes and one barrier,
not `N + D` barriers: each file is handed to the device (`fsync(2)`),
and one barrier at the root orders the lot ahead of the next tier.
Nothing orders the files *within* a tier, so a crash can leave any number of an interrupted tier's
`create_new` files torn — a digest-named store must be able to recognise and discard every one of them.

## Backends

Everything is generic over a small async port whose method set mirrors `std::fs`.
`StdFs` and an `InMemoryFs` ship with the crate;
an adapter for OPFS, IndexedDB, or a network store is a few dozen mechanical lines.
A backend *declares* what it can keep through `Capabilities`,
and every member defaults to the pessimistic answer —
a forgotten override degrades to the defensive path, never to a false promise.

## The journal

Present only between a set's commit point and its completion.
`Journal::named` changes the filename of the journal, `.fstx-journal` by default.
`Journal::kept_in` changes the location of the journal, which is at the root by default.
It is good practice to always configure `Journal::named` so that it is easier to identify which application is responsible for it.
It may be desirable to configure `Journal::kept_in` if the folder is very frequently read---
for example, by a sync service such as iCloud or Dropbox.
Otherwise, a crash could transport a journal to other devices.

```rust,ignore
let journal = Journal::named(".myapp-journal")?.kept_in(app_support_dir)?;
block_on(journal.apply(&cs, &StdFs, root))?;   // ...and later:
block_on(journal.recover(&StdFs, root))?;       // the same pair, both halves
```

## Limits

- **Single writer.** No locking; concurrent appliers against one root will race. Serialize them yourself.
- **A set is bounded by memory.** Staged bytes and the undo buffer are held for the length of the apply;
  `FileOp::CopyFrom` is the escape hatch for a large immutable payload already on disk.
- **A root lives on one filesystem.** Barriers and drains prove nothing across a device boundary.
- **Symlinks are not resolved.** The guard keeping staged paths inside the root is purely lexical.
- **Futures are not required to be `Send`**, so an apply over a non-`Send` backend cannot be `tokio::spawn`ed.

## Zero dependencies (by default)

The `barrier-fsync` feature brings in `libc`:
on Apple platforms it answers `Durability::Ordered` with `F_BARRIERFSYNC`
instead of `F_FULLFSYNC`'s drain of the drive's whole write cache.
Without the feature every barrier and drain is the full flush,
which can be milliseconds instead of microseconds.
`Durability::Pushed` is plain `fsync(2)` on Apple platforms either way—
the standard library has no way to ask for it there, so the one symbol is declared by hand.
I recommend enabling the feature where performance is important on Apple platforms.

## License

MIT or Apache-2.0, at your option.
