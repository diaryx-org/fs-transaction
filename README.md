# fs-transaction

Multi-file filesystem transactions that survive a crash. Stage a set of writes,
renames, removals, copies, execute-bit flips and symbolic links; apply them
all-or-nothing; and if the power goes out halfway through, finish the job on
the next run.

The files stay ordinary files. This is not a virtual filesystem and not a
database — nothing here changes how your tree is *read*, only how it is
*written*.

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

## Why

Single-file atomic writes are a solved problem — `write` a temporary sibling,
`fsync` it, `rename` it over the target. What is *not* solved is a change that
touches several files at once. Rename a note in a linked set and every file
pointing at it has to be rewritten too; issue those one at a time and an I/O
error partway through leaves the tree torn, updated in the files already
written and stale in the ones never reached.

A `ChangeSet` closes that window from both sides:

- **On an error** — a full disk, a permission fault — every op already applied
  is unwound in reverse, and the tree ends up exactly as it was.
- **On a crash** — `kill -9`, a power cut — there is no error to catch and no
  chance to unwind, so a write-ahead journal written *before* the first file is
  touched survives instead. The next `recover` replays it forward to the
  fully-applied state.

Both endpoints are consistent. They are simply different consistent states, and
the crate does not pretend a lost-power change never happened when its intent
was already durably on disk.

## Ordered batches: the other crash discipline

All-or-nothing is the right guarantee when a half-applied set is *illegal*.
Some trees are built the other way: an append-only, content-addressed store
declares every partially-written batch legal — blobs that arrived without the
record naming them are exactly what any interrupted transfer leaves. Buying
atomicity there pays for a journal to rule out states that were never illegal.

`OrderedBatch` is what such a tree actually needs — durability and ordering,
without the journal. Tiers of writes separated by barriers: nothing durable
ever names anything that is not durable yet, a crash leaves some prefix of the
barriers, and there is no rollback and no recovery step, because every prefix
is a state the tree already tolerates.

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

`finality` is the strength of the batch's own landing: `Durable` means "this
returned, it survives a power cut"; `Ordered` means "consistent, but the tail
may go with the crash" — often enough for an append-only tree, and one less
drain of the drive's cache.

## What it does not do

Stated plainly, because a crate in this position should be:

- **Single writer.** There is no locking. Two processes applying sets against
  one root will race, and the stale-journal guard is a check-then-act, not a
  mutex. Serialize them yourself.
- **A set is bounded by memory.** Staged bytes and the undo buffer are both
  held for the length of the apply. `FileOp::CopyFrom` is the escape hatch for
  a large payload already on disk — it journals a *reference*, so restoring a
  captured tree costs O(files) of journal rather than a second copy of every
  byte. The source must be immutable for that to be sound; a content-addressed
  blob is, by construction.
- **Futures are not required to be `Send`.** The storage port uses native
  `async fn`, so a backend keeps its own future types — which also means an
  apply over a non-`Send` backend cannot be `tokio::spawn`ed.
- **Symlinks are not resolved.** The path guard that keeps a staged op inside
  the root is purely lexical.

## Any backend

Everything is generic over a small async port. `StdFs` and an `InMemoryFs` ship
with the crate; an adapter for OPFS, IndexedDB, or a network store is a few
dozen mechanical lines, since the method set mirrors `std::fs` exactly.

Durability is *declared*, never assumed. A backend says what it can keep
through `Capabilities`, and the apply path picks the strongest protocol that
backend actually supports — rather than assuming atomic rename and silently
lying on the backends that do not have one. Every durability member defaults to
the pessimistic answer, so an adapter that forgets to override one degrades to
the defensive path instead of to a false promise.

## Journal naming and placement

The journal is one transient dotfile, present only between a change set's
commit point and its completion. It defaults to `.fstx-journal` at the root;
`Journal::named` takes your own name.

Apply and recovery must agree about that name — if they disagree, nothing fails
loudly, recovery simply looks where no journal is and leaves the change
stranded. That is why both operations hang off `Journal` rather than taking the
name separately.

For a tree something *syncs* — an iCloud or Dropbox folder — the journal must
not live in the root at all: a sync service cannot tell crash state from
content, and would carry one machine's journal to machines that never crashed.
`Journal::kept_in` homes it in an absolute directory you own and nothing
syncs:

```rust,ignore
let journal = Journal::named(".myapp-journal")?.kept_in(app_support_dir)?;
block_on(journal.apply(&cs, &StdFs, root))?;   // ...and later:
block_on(journal.recover(&StdFs, root))?;       // the same pair, both halves
```

## Zero dependencies (by default)

A crate whose whole job is getting bytes onto disk correctly should not make
you audit anyone else's code to trust it, and should not drag a runtime into a
build that already has one. The checksum is hand-rolled FNV-1a; the error type
is a hand-written enum.

The one opt-in exception is the `barrier-fsync` feature (which brings in
`libc`): on Apple platforms it answers `Durability::Ordered` with
`F_BARRIERFSYNC` — a queue barrier — instead of `F_FULLFSYNC`'s drain of the
drive's whole write cache. That is the difference between microseconds and
milliseconds on exactly the calls both protocols make most, and without the
feature every sync stays the full flush: stronger than asked, never weaker.

## License

MIT or Apache-2.0, at your option.
