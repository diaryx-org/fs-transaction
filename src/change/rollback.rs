//! The proof that a rollback gives back the tree the set began from.
//! Compiled only by Verus (`verus_keep_ghost`).
//!
//! Every step [`exec`](super::exec) records comes with the tree it undoes to
//! and the tree it undoes from, in a ghost [`Hist`]; [`fits`] says what
//! undoing the step does between the two. `exec` keeps the history true
//! after every op — whether the op lands or fails partway — and
//! [`unwind_durable`](super::unwind_durable) walks it back to its start.
//!
//! "Agree" is [`same`]: entry for entry, modes included, for a set that
//! flips no execute bit; contents only, for one that does, since
//! `set_executable` cannot promise to put a mode back bit for bit.

use vstd::prelude::*;

use super::Undo;
use crate::port::{Entry, Tree, content, ent, entry, fid, has_dir, has_entry, has_file, tid};

verus! {

pub tracked struct Hist {
    pub ghost s: Seq<Tree>,
}

/// `a` and `b` agree at `x`.
pub(crate) open spec fn same_at(exact: bool, a: Tree, b: Tree, x: int) -> bool {
    if exact {
        ent(a, x) == ent(b, x)
    } else {
        entry(content(a), x) == entry(content(b), x)
    }
}

pub(crate) open spec fn same(exact: bool, keys: Set<int>, a: Tree, b: Tree) -> bool {
    forall|x: int| keys.contains(x) ==> #[trigger] same_at(exact, a, b, x)
}

pub(crate) open spec fn same_but(exact: bool, keys: Set<int>, a: Tree, b: Tree, but: Set<int>) -> bool {
    forall|x: int| keys.contains(x) && !but.contains(x) ==> #[trigger] same_at(exact, a, b, x)
}

/// Undoing `step` takes a tree that agrees with `after` to one that agrees
/// with `before`.
pub(crate) open spec fn fits(exact: bool, keys: Set<int>, step: Undo, before: Tree, after: Tree) -> bool {
    match step {
        // A file that a replacement wrote over, put back into itself.
        Undo::Restore { path, bytes } => {
            let p = fid(path);
            &&& keys.contains(p)
            &&& same_but(exact, keys, after, before, set![p])
            &&& has_file(before, p) && before[p]->File_bytes == bytes@
            &&& has_file(after, p)
            &&& exact ==> after[p]->File_mode == before[p]->File_mode
        },
        // Something made where there was nothing.
        Undo::Delete { path } => {
            let p = fid(path);
            &&& keys.contains(p)
            &&& same_but(exact, keys, after, before, set![p])
            &&& !before.contains_key(p)
            &&& !has_dir(after, p)
        },
        // A link replaced.
        Undo::Relink { path, target } => {
            let p = fid(path);
            &&& keys.contains(p)
            &&& same_but(exact, keys, after, before, set![p])
            &&& ent(before, p) == Some(Entry::Link { target: tid(target) })
            &&& !has_dir(after, p)
        },
        // An entry moved from `to` to `from`: moved back.
        Undo::Rename { from, to } => {
            let (x, y) = (fid(from), fid(to));
            &&& keys.contains(x) && keys.contains(y) && x != y
            &&& same_but(exact, keys, after, before, set![x, y])
            &&& if exact {
                ent(after, x) == ent(before, y)
            } else {
                entry(content(after), x) == entry(content(before), y)
            }
            &&& before.contains_key(y)
            &&& !before.contains_key(x)
            &&& !has_dir(after, y)
        },
        // An execute bit flipped: what the file holds is unchanged.
        Undo::SetExecutable { path, .. } => {
            let p = fid(path);
            &&& !exact
            &&& keys.contains(p)
            &&& same_but(exact, keys, after, before, set![p])
            &&& entry(content(after), p) == entry(content(before), p)
            &&& has_entry(before, p)
        },
    }
}

/// The history is true of the log: one more tree than steps, each step
/// fitting the trees either side of it.
pub(crate) open spec fn logged(exact: bool, keys: Set<int>, steps: Seq<Undo>, hist: Seq<Tree>) -> bool {
    &&& hist.len() == steps.len() + 1
    &&& forall|i: int| 0 <= i < steps.len() ==> #[trigger] fits(exact, keys, steps[i], hist[i], hist[i + 1])
}

/// Away from what a step changed, a tree unchanged since it agreed with
/// `after` agrees with `before`.
pub(crate) proof fn lemma_frame(
    exact: bool,
    keys: Set<int>,
    t0: Tree,
    t1: Tree,
    after: Tree,
    before: Tree,
    changed: Set<int>,
)
    requires
        forall|x: int| keys.contains(x) && !changed.contains(x) ==> #[trigger] ent(t1, x) == ent(t0, x),
        same(exact, keys, t0, after),
        same_but(exact, keys, after, before, changed),
    ensures
        same_but(exact, keys, t1, before, changed),
{
    broadcast use crate::port::lemma_content;
    assert forall|x: int| keys.contains(x) && !changed.contains(x) implies #[trigger] same_at(exact, t1, before, x) by {
        assert(ent(t1, x) == ent(t0, x));
        assert(same_at(exact, t0, after, x));
        assert(same_at(exact, after, before, x));
    }
}

/// Agreeing everywhere but `changed`, and at each of `changed`, is agreeing.
pub(crate) proof fn lemma_close(exact: bool, keys: Set<int>, t: Tree, before: Tree, changed: Set<int>)
    requires
        same_but(exact, keys, t, before, changed),
        forall|x: int| changed.contains(x) && keys.contains(x) ==> #[trigger] same_at(exact, t, before, x),
    ensures
        same(exact, keys, t, before),
{
    assert forall|x: int| keys.contains(x) implies #[trigger] same_at(exact, t, before, x) by {
        if changed.contains(x) {
        } else {
            assert(same_at(exact, t, before, x));
        }
    }
}

} // verus!
