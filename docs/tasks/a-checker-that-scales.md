---
title: A replay checker that scales with a set's size
description: The rule `Journal::apply` checks before its commit point compares every op with every other; group ops by path so only related pairs are compared, and keep the proof
status: open
created: 2026-09-27
updated: 2026-09-27
part_of: "[Tasks](tasks.md)"
---

# A replay checker that scales with a set's size

Before a set of more than one op is journaled, `replayable::check` decides
whether a crash in it could be recovered from. `first_refusal` does that by
calling `pair` on every ordered pair of ops, so a set of n ops costs n²
calls, whatever the ops touch.

## Measured

On an M3 Pro, in a release build, each op writing a 1 KB file in a nested
directory, `Journal::apply` on `InMemoryFs` took:

| ops    | time    |
|--------|---------|
| 1,000  | 6 ms    |
| 10,000 | 210 ms  |
| 30,000 | 1.6 s   |

A profile of the 40,000-op run was entirely `replayable::check`, at about
1.7 ns a pair. Extrapolated, 100,000 ops is about 17 s.

On `StdFs` the disk is still the larger cost at every size measured: each op
is made durable, at about 3.4 ms an op with the default flush and about
0.35 ms with `barrier-fsync`. So at 10,000 ops that is 4 to 34 s of disk
against 0.2 s of checking. The checker only dominates on a fast backend with
sets of tens of thousands of ops.

## Why it is deferred

The sets that must be one set are ones like a rename together with the link
rewrites that follow it. They run to hundreds of ops, or a few thousand,
where the check costs milliseconds. A tree-wide migration, such as rewriting
every file's frontmatter, does not need one set. It is better as many small
ones, provided the reader accepts both formats and the conversion skips files
already done. A crash then costs a rerun rather than a replay, and an error
costs no rollback. Nothing that uses the crate today needs a larger set.

## The change

`pair` only refuses a pair whose paths are the same or one inside the other.
Two ops that name unrelated paths always pass. So `first_refusal` can visit
only related pairs:

1. Order the ops' path keys: sort them, or build a trie of the interned
   components `key` already makes.
2. For each op, visit only the ops whose `path` or `other` is equal to one of
   its own, or nested with one of its own.

That makes the cost near-linear in the number of ops plus the number of
related pairs.

`pair` and `proof::admissible` stay as they are. The new proof obligation is
a lemma that `proof::pair_refusal` is `None` whenever neither path of one op
is equal to, or nested with, either path of the other. With that, the loop's
invariant can quantify over the related pairs alone. `first_refusal` must
still ensure `r is Ok <==> proof::admissible(proof::views(ops@))`, and must
still report the same first refusal: the lowest `i`, and for it the lowest
`k`.

## Done when

- `first_refusal`'s cost no longer grows with the number of unrelated pairs.
  10,000 ops on unrelated paths check in well under 10 ms on the setup above.
- Verus verifies it with the same `ensures`, and nothing new is trusted:
  `tests/trust_boundary.rs` still passes.
- `replayable`'s tests still pass, and a test pins that the refusal reported
  for a set with several bad pairs is the same one as before.
