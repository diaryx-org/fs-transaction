---
title: A set can write its own journal
description: "A set that names the journal's path is applied like any other file: alone, it plants a file that wedges the root until someone deletes it by hand; beside other ops, it reports Ok and the file is gone"
status: open
created: 2026-11-08
updated: 2026-11-08
part_of: "[Tasks](tasks.md)"
---

# A set can write its own journal

`ChangeSet::apply` clamps every staged path to the root (`guard_ops`, then
`guard_in_root` on each expectation) and nothing else. A path equal to the
journal's own, `Journal::path_in(root)` (`.fstx-journal` by default, or the
name given to `Journal::named`), passes the clamp and is treated as an
ordinary file. The journal is the one path in the root the crate keeps for
itself, and a set built from data the caller did not write can name it as
easily as the `../../etc/passwd` the clamp was put there to refuse.

## Repro

Against `StdFs` on an empty root (on `InMemoryFs` the first apply succeeds
the same way):

```rust
use fs_transaction::{ChangeSet, Journal, StdFs, exec::block_on, recover};

let mut planted = ChangeSet::new();
planted.write(Journal::DEFAULT_NAME, "hello");
block_on(planted.apply(&StdFs, root))?;            // Ok(())

let mut next = ChangeSet::new();
next.write("b", "y");
block_on(next.apply(&StdFs, root));                 // Err(StaleJournal(".../.fstx-journal"))
block_on(recover(&StdFs, root));                    // Err(Corrupt("not a journal (bad header)"))
```

The root is now wedged: every apply refuses a stale journal, and recovery
refuses a file that is not one. Only deleting the file by hand frees it.

With a second op the set is journaled, and the result is different but no
better:

| set | `apply` returns | afterwards |
|---|---|---|
| `write(.fstx-journal, "x")` alone | `Ok(())` | `.fstx-journal` holds `x`; the root is wedged as above |
| `write(.fstx-journal, "x")`, `write(b, "y")` | `Ok(())` | `b` written; `.fstx-journal` is gone, retired as the set's own journal |
| `remove(.fstx-journal)`, `write(b, "y")` | `Err(Torn { … could not be retired: No such file or directory })` | `b` written; the set did land, and reports a torn apply |

In the second row a write that `apply` reports as done is not on disk. In
the third the set itself deleted the journal it was committing through, so
a crash between that op and the end of the set would have left nothing to
recover from.

## Done when

`apply` refuses, before it writes or journals anything, a set whose op names
the journal's path in the root, or its `write_atomic` staging sibling
(`Journal::owns_path` already recognizes both), with an error that names the
path. A homed journal (`Journal::kept_in`) keeps no file in the root, so a
same-named file there stays an ordinary file, as `owns_path` already
decides. A test holds each row of the table above.