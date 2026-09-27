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

/// The path a step is about, and — for a move — the other.
pub(crate) open spec fn step_paths(step: Undo) -> Set<int> {
    match step {
        Undo::Restore { path, .. } | Undo::Delete { path } | Undo::Relink { path, .. }
        | Undo::SetExecutable { path, .. } => set![fid(path)],
        Undo::Rename { from, to } => set![fid(from), fid(to)],
    }
}

/// `fits` asks nothing of its trees that agreeing trees differ on.
pub(crate) proof fn lemma_fits_same(
    exact: bool,
    keys: Set<int>,
    step: Undo,
    before: Tree,
    after: Tree,
    before2: Tree,
    after2: Tree,
)
    requires
        fits(exact, keys, step, before, after),
        same(exact, keys, before, before2),
        same(exact, keys, after, after2),
    ensures
        fits(exact, keys, step, before2, after2),
{
    broadcast use crate::port::lemma_content;
    assert forall|x: int| keys.contains(x) implies #[trigger] same_at(exact, before, before2, x) by {}
    assert forall|x: int| keys.contains(x) implies #[trigger] same_at(exact, after, after2, x) by {}
    let but = step_paths(step);
    assert forall|x: int| keys.contains(x) && !but.contains(x) implies #[trigger] same_at(exact, after2, before2, x) by {
        assert(same_at(exact, after, before, x));
        assert(same_at(exact, before, before2, x));
        assert(same_at(exact, after, after2, x));
    }
    match step {
        Undo::Restore { path, .. } => {
            let p = fid(path);
            assert(same_at(exact, before, before2, p));
            assert(same_at(exact, after, after2, p));
        },
        Undo::Delete { path } => {
            let p = fid(path);
            assert(same_at(exact, before, before2, p));
            assert(same_at(exact, after, after2, p));
        },
        Undo::Relink { path, .. } => {
            let p = fid(path);
            assert(same_at(exact, before, before2, p));
            assert(same_at(exact, after, after2, p));
        },
        Undo::SetExecutable { path, .. } => {
            let p = fid(path);
            assert(same_at(exact, before, before2, p));
            assert(same_at(exact, after, after2, p));
        },
        Undo::Rename { from, to } => {
            let (x, y) = (fid(from), fid(to));
            assert(same_at(exact, before, before2, x));
            assert(same_at(exact, before, before2, y));
            assert(same_at(exact, after, after2, x));
            assert(same_at(exact, after, after2, y));
        },
    }
}

/// Extending a true log by a step that fits keeps it true.
pub(crate) proof fn lemma_log_push(exact: bool, keys: Set<int>, steps: Seq<Undo>, hist: Seq<Tree>, step: Undo, after: Tree)
    requires
        logged(exact, keys, steps, hist),
        fits(exact, keys, step, hist.last(), after),
    ensures
        logged(exact, keys, steps.push(step), hist.push(after)),
{
    assert forall|i: int| 0 <= i < steps.push(step).len() implies #[trigger] fits(exact, keys, steps.push(step)[i], hist.push(after)[i], hist.push(after)[i + 1]) by {
        if i < steps.len() {
            assert(steps.push(step)[i] == steps[i]);
            assert(hist.push(after)[i] == hist[i]);
            assert(hist.push(after)[i + 1] == hist[i + 1]);
        } else {
            assert(hist.push(after)[i] == hist.last());
        }
    }
}

/// Replacing the last tree of a true log with one the last step still fits
/// keeps it true.
pub(crate) proof fn lemma_log_update(exact: bool, keys: Set<int>, steps: Seq<Undo>, hist: Seq<Tree>, after: Tree)
    requires
        logged(exact, keys, steps, hist),
        steps.len() > 0,
        fits(exact, keys, steps.last(), hist[hist.len() - 2], after),
    ensures
        logged(exact, keys, steps, hist.update(hist.len() - 1, after)),
{
    let h2 = hist.update(hist.len() - 1, after);
    assert forall|i: int| 0 <= i < steps.len() implies #[trigger] fits(exact, keys, steps[i], h2[i], h2[i + 1]) by {
        if i < steps.len() - 1 {
            assert(h2[i] == hist[i]);
            assert(h2[i + 1] == hist[i + 1]);
        } else {
            assert(h2[i] == hist[hist.len() - 2]);
            assert(h2[i + 1] == after);
        }
    }
}

/// The log is true, and the tree agrees with its last state.
pub(crate) open spec fn holds(exact: bool, keys: Set<int>, steps: Seq<Undo>, hist: Seq<Tree>, t: Tree) -> bool {
    logged(exact, keys, steps, hist) && same(exact, keys, t, hist.last())
}

/// `t` differs from `pre` on `keys` at most at `but`.
pub(crate) open spec fn frame(keys: Set<int>, pre: Tree, t: Tree, but: Set<int>) -> bool {
    forall|z: int| keys.contains(z) && !but.contains(z) ==> #[trigger] ent(t, z) == ent(pre, z)
}

/// A move aside, or back, fits: `t` holds at `x` what `pre` held at `y`.
pub(crate) proof fn lemma_moved_fits(exact: bool, keys: Set<int>, step: Undo, l: Tree, pre: Tree, t: Tree)
    requires
        step is Rename,
        keys.contains(fid(move_from(step))),
        keys.contains(fid(move_to(step))),
        fid(move_from(step)) != fid(move_to(step)),
        same(exact, keys, pre, l),
        pre.contains_key(fid(move_to(step))),
        !pre.contains_key(fid(move_from(step))),
        ent(t, fid(move_from(step))) == ent(pre, fid(move_to(step))),
        !has_dir(t, fid(move_to(step))),
        frame(keys, pre, t, set![fid(move_from(step)), fid(move_to(step))]),
    ensures
        fits(exact, keys, step, l, t),
{
    broadcast use crate::port::lemma_content;
    let (x, y) = (fid(move_from(step)), fid(move_to(step)));
    assert forall|z: int| keys.contains(z) && !set![x, y].contains(z) implies #[trigger] same_at(exact, t, l, z) by {
        assert(ent(t, z) == ent(pre, z));
        assert(same_at(exact, pre, l, z));
    }
    assert(same_at(exact, pre, l, x));
    assert(same_at(exact, pre, l, y));
}

/// A capture before a replacing write — or the write after it — fits.
pub(crate) proof fn lemma_captured_fits(exact: bool, keys: Set<int>, step: Undo, l: Tree, pre: Tree, t: Tree)
    requires
        step is Restore || step is Delete || step is Relink,
        keys.contains(fid(capture_path(step))),
        same(exact, keys, pre, l),
        frame(keys, pre, t, set![fid(capture_path(step))]),
        step is Restore ==> has_file(pre, fid(capture_path(step)))
            && pre[fid(capture_path(step))]->File_bytes == restore_bytes(step)
            && has_file(t, fid(capture_path(step)))
            && (exact ==> t[fid(capture_path(step))]->File_mode == pre[fid(capture_path(step))]->File_mode),
        step is Delete ==> !pre.contains_key(fid(capture_path(step))) && !has_dir(t, fid(capture_path(step))),
        step is Relink ==> ent(pre, fid(capture_path(step))) == Some(Entry::Link { target: tid(relink_target(step)) })
            && !has_dir(t, fid(capture_path(step))),
    ensures
        fits(exact, keys, step, l, t),
{
    broadcast use crate::port::lemma_content;
    let p = fid(capture_path(step));
    assert forall|z: int| keys.contains(z) && !set![p].contains(z) implies #[trigger] same_at(exact, t, l, z) by {
        assert(ent(t, z) == ent(pre, z));
        assert(same_at(exact, pre, l, z));
    }
    assert(same_at(exact, pre, l, p));
}

/// A flip fits: what the file holds is unchanged.
pub(crate) proof fn lemma_flip_fits(exact: bool, keys: Set<int>, step: Undo, l: Tree, pre: Tree, t: Tree)
    requires
        step is SetExecutable,
        !exact,
        keys.contains(fid(capture_path(step))),
        same(exact, keys, pre, l),
        frame(keys, pre, t, set![fid(capture_path(step))]),
        has_entry(pre, fid(capture_path(step))),
        entry(content(t), fid(capture_path(step))) == entry(content(pre), fid(capture_path(step))),
    ensures
        fits(exact, keys, step, l, t),
{
    broadcast use crate::port::lemma_content;
    let p = fid(capture_path(step));
    assert forall|z: int| keys.contains(z) && !set![p].contains(z) implies #[trigger] same_at(exact, t, l, z) by {
        assert(ent(t, z) == ent(pre, z));
        assert(same_at(exact, pre, l, z));
    }
    assert(same_at(exact, pre, l, p));
}

pub(crate) open spec fn move_from(step: Undo) -> std::path::PathBuf {
    match step {
        Undo::Rename { from, .. } => from,
        _ => arbitrary(),
    }
}

pub(crate) open spec fn move_to(step: Undo) -> std::path::PathBuf {
    match step {
        Undo::Rename { to, .. } => to,
        _ => arbitrary(),
    }
}

pub(crate) open spec fn restore_bytes(step: Undo) -> Seq<u8> {
    match step {
        Undo::Restore { bytes, .. } => bytes@,
        _ => arbitrary(),
    }
}

pub(crate) open spec fn relink_target(step: Undo) -> std::path::PathBuf {
    match step {
        Undo::Relink { target, .. } => target,
        _ => arbitrary(),
    }
}

pub(crate) open spec fn capture_path(step: Undo) -> std::path::PathBuf {
    match step {
        Undo::Restore { path, .. } | Undo::Delete { path } | Undo::Relink { path, .. }
        | Undo::SetExecutable { path, .. } => path,
        Undo::Rename { to, .. } => to,
    }
}

/// A tree that changed only at `but` still agrees with the last state of a
/// true log, away from `but`.
pub(crate) proof fn lemma_same_frame(exact: bool, keys: Set<int>, pre: Tree, t: Tree, l: Tree)
    requires
        same(exact, keys, pre, l),
        frame(keys, pre, t, Set::empty()),
    ensures
        same(exact, keys, t, l),
{
    broadcast use crate::port::lemma_content;
    assert forall|z: int| keys.contains(z) implies #[trigger] same_at(exact, t, l, z) by {
        assert(ent(t, z) == ent(pre, z));
        assert(same_at(exact, pre, l, z));
    }
}

/// What a capture recorded about the path it captured, in the tree it
/// captured from.
pub(crate) open spec fn captured(step: Undo, pre: Tree, p: int) -> bool {
    &&& step is Restore || step is Delete || step is Relink
    &&& fid(capture_path(step)) == p
    &&& step is Restore ==> has_file(pre, p) && pre[p]->File_bytes == restore_bytes(step)
    &&& step is Delete ==> !pre.contains_key(p)
    &&& step is Relink ==> ent(pre, p) == Some(Entry::Link { target: tid(relink_target(step)) })
}

/// Where op `index` of a set rooted at `root` moves an entry aside, if it
/// does: a file of its own, empty, and none of the op's.
pub(crate) open spec fn aside_ok(root: &std::path::Path, op: crate::FileOp, index: int, keys: Set<int>, t: Tree) -> bool {
    let m = crate::port::model(root, op);
    let target = if m.act is Rename { m.other } else { m.path };
    let a = crate::port::aside_of(target, index);
    (m.act is Remove || m.act is Rename || m.act is SetLink) ==> {
        &&& keys.contains(a)
        &&& a != m.path && a != m.other
        &&& !t.contains_key(a)
    }
}

pub(crate) proof fn lemma_same_refl(exact: bool, keys: Set<int>, t: Tree)
    ensures
        same(exact, keys, t, t),
{
}

/// The path a step's effect overwrites: the one captured, or a move's
/// destination.
pub(crate) open spec fn overwritten(step: Undo) -> std::path::PathBuf {
    match step {
        Undo::Rename { to, .. } => to,
        _ => capture_path(step),
    }
}

/// What the effect may leave at the path it overwrites, for the step still
/// to fit.
pub(crate) open spec fn refits_at(exact: bool, step: Undo, p: Tree, t: Tree) -> bool {
    let y = fid(overwritten(step));
    match step {
        Undo::Restore { .. } => has_file(t, y) && (exact ==> t[y]->File_mode == p[y]->File_mode),
        Undo::SetExecutable { .. } => entry(content(t), y) == entry(content(p), y),
        _ => !has_dir(t, y),
    }
}

/// A step still fits once its effect has landed at the path it overwrites.
pub(crate) proof fn lemma_refit(exact: bool, keys: Set<int>, step: Undo, l: Tree, p: Tree, t: Tree)
    requires
        fits(exact, keys, step, l, p),
        same_but(exact, keys, t, p, set![fid(overwritten(step))]),
        refits_at(exact, step, p, t),
    ensures
        fits(exact, keys, step, l, t),
{
    broadcast use crate::port::lemma_content;
    let y = fid(overwritten(step));
    let but = step_paths(step);
    assert forall|z: int| keys.contains(z) && !but.contains(z) implies #[trigger] same_at(exact, t, l, z) by {
        assert(same_at(exact, t, p, z));
        assert(same_at(exact, p, l, z));
    }
    match step {
        Undo::Rename { from, to } => {
            let x = fid(from);
            assert(same_at(exact, t, p, x));
        },
        _ => {},
    }
}

/// Over a true log whose last step awaits its effect at `y`, and a tree
/// agreeing with the log's last state.
pub(crate) open spec fn pending(exact: bool, keys: Set<int>, steps: Seq<Undo>, hist: Seq<Tree>, t: Tree, y: int) -> bool {
    &&& holds(exact, keys, steps, hist, t)
    &&& steps.len() > 0
    &&& fid(overwritten(steps.last())) == y
}

/// After the pending effect, the log holds again with its last state moved on.
pub(crate) proof fn lemma_landed(exact: bool, keys: Set<int>, steps: Seq<Undo>, hist: Seq<Tree>, t0: Tree, t: Tree, y: int)
    requires
        pending(exact, keys, steps, hist, t0, y),
        keys.contains(y),
        forall|z: int| keys.contains(z) && z != y ==> #[trigger] ent(t, z) == ent(t0, z),
        refits_at(exact, steps.last(), hist.last(), t),
    ensures
        holds(exact, keys, steps, hist.update(hist.len() - 1, t), t),
{
    broadcast use crate::port::lemma_content;
    assert forall|z: int| keys.contains(z) && !set![y].contains(z) implies #[trigger] same_at(exact, t, hist.last(), z) by {
        assert(ent(t, z) == ent(t0, z));
        assert(same_at(exact, t0, hist.last(), z));
    }
    let i = steps.len() - 1;
    assert(fits(exact, keys, steps[i], hist[i], hist[i + 1]));
    assert(steps.last() == steps[i] && hist.last() == hist[i + 1] && hist[hist.len() - 2] == hist[i]);
    lemma_refit(exact, keys, steps.last(), hist[hist.len() - 2], hist.last(), t);
    lemma_log_update(exact, keys, steps, hist, t);
    let h2 = hist.update(hist.len() - 1, t);
    assert(h2.last() == t);
}

} // verus!
