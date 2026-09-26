//! Lexical path handling — normalization, and the guard that keeps a staged op
//! inside the root it was applied against.
//!
//! Purely lexical: nothing here touches the filesystem, so it holds for a path
//! naming something that does not exist yet, and it is the same answer on every
//! backend. Symlinks are consequently *not* resolved — a link inside the root
//! pointing out of it is not something this can see. A backend that must defend
//! against that has to refuse symlinks itself.

use std::path::{Component, Path, PathBuf};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
mod proof;

/// Lexically normalize a relative path: drop `.` components and fold
/// `parent/..` pairs. Leading `..` components (escaping the root) are kept —
/// the caller decides whether that is an error, which is what
/// [`escapes_root`] is for.
///
/// Proved (in `path/proof.rs`, by Verus) to reach a normal form — any root
/// first, then the surviving `..`s, then names — to be idempotent, and to
/// preserve the path's meaning: from any directory, the path and its
/// normalization reach the same place, or both climb above the root.
pub fn normalize(path: impl AsRef<Path>) -> PathBuf {
    let components: Vec<Component> = path.as_ref().components().collect();
    let kinds: Vec<Kind> = components.iter().map(kind).collect();
    fold(&kinds).into_iter().map(|i| components[i]).collect()
}

/// Whether `path`, resolved against a root, would land *outside* it.
///
/// Two ways a root-relative path can escape the tree it is joined onto: an
/// **absolute** path (or a Windows drive prefix), which `root.join(path)` jumps
/// to wholesale, ignoring the root entirely; and one whose [`normalize`]d form
/// still leads with `..`, a climb above the root that the `parent/..` folding
/// could not cancel.
///
/// [`ChangeSet::apply`](crate::ChangeSet::apply) refuses either before it
/// writes or journals anything, so a set assembled from untrusted input — a
/// link target authored by whoever wrote the document, a path out of a config
/// file — can never name a file outside the tree it was pointed at.
///
/// A path that stays within the root (`notes/a.md`, or `../sibling/b.md` where
/// the leading climb is cancelled by what precedes it) returns `false`.
///
/// Proved (in `path/proof.rs`, by Verus) to be `true` exactly when the path is
/// not relative, or its walk from the root climbs above the root at any point
/// — at its end or anywhere before — so a path this passes never leaves the
/// root, even transiently.
pub fn escapes_root(path: impl AsRef<Path>) -> bool {
    let kinds: Vec<Kind> = path.as_ref().components().map(|c| kind(&c)).collect();
    climbs_out(&kinds)
}

/// What [`fold`] needs to know about a component: which one it is, and not
/// what it is called.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub(crate) enum Kind {
    Prefix,
    Root,
    Cur,
    Parent,
    Normal,
}

fn kind(component: &Component) -> Kind {
    match component {
        Component::Prefix(_) => Kind::Prefix,
        Component::RootDir => Kind::Root,
        Component::CurDir => Kind::Cur,
        Component::ParentDir => Kind::Parent,
        Component::Normal(_) => Kind::Normal,
    }
}

/// The indices of the components [`normalize`] keeps: `.` dropped, and each
/// `..` either folded into the name before it or kept.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(kept =>
    ensures
        proof::kept_comps(kinds@, kept@) == proof::normalize(proof::comps(kinds@)),
        forall|k: int| 0 <= k < kept@.len() ==> kept@[k] < kinds@.len(),
))]
fn fold(kinds: &[Kind]) -> Vec<usize> {
    let mut kept: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= kinds@.len(),
            forall|k: int| 0 <= k < kept@.len() ==> kept@[k] < i,
            proof::kept_comps(kinds@, kept@) == proof::normalize(proof::comps(kinds@).take(i as int)),
        decreases kinds@.len() - i,
    ))]
    while i < kinds.len() {
        #[cfg(verus_keep_ghost)]
        proof! { proof::lemma_fold_turn(kinds@, kept@, i as int); }
        match kinds[i] {
            Kind::Cur => {}
            Kind::Parent => {
                if !kept.is_empty() && matches!(kinds[kept[kept.len() - 1]], Kind::Normal) {
                    kept.pop();
                } else {
                    kept.push(i);
                }
            }
            _ => kept.push(i),
        }
        i += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { proof::lemma_take_all(kinds@); }
    kept
}

/// Whether the normalized components lead with a climb or a root.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(b =>
    ensures
        b == proof::escapes(proof::comps(kinds@)),
))]
fn climbs_out(kinds: &[Kind]) -> bool {
    let kept = fold(kinds);
    !kept.is_empty() && matches!(kinds[kept[0]], Kind::Parent | Kind::Root | Kind::Prefix)
}

/// Refuse a staged path that would resolve outside the root — the guard both
/// [`ChangeSet::apply`](crate::ChangeSet::apply) and
/// [`OrderedBatch::apply`](crate::OrderedBatch::apply) clamp every op through.
/// Defers to [`escapes_root`], so a caller that guards its *reads* with the
/// same function clamps both directions to the exact same boundary.
pub(crate) fn guard_in_root(path: &Path) -> crate::error::Result<()> {
    if escapes_root(path) {
        return Err(crate::error::Error::Escape(path.to_path_buf()));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn folds_dot_and_parent_components() {
        assert_eq!(normalize("a/./b"), PathBuf::from("a/b"));
        assert_eq!(normalize("a/b/../c"), PathBuf::from("a/c"));
        assert_eq!(normalize("a/../../b"), PathBuf::from("../b"));
    }

    #[test]
    fn escapes_only_when_the_climb_survives_folding() {
        assert!(!escapes_root("notes/a.md"));
        assert!(!escapes_root("notes/../a.md"));
        assert!(escapes_root("../a.md"));
        assert!(escapes_root("a/../../etc/passwd"));
        assert!(escapes_root("/etc/passwd"));
    }
}
