---
title: "A strength below Ordered: handed over"
description: A third `Durability` — the bytes pushed to the device and ordered against nothing — so that a tier of N files costs N pushes and one barrier rather than N barriers, and a consumer landing a set can ask for the same
status: open
created: 2026-09-16
updated: 2026-09-16
part_of: "[Tasks](tasks.md)"
---

# A strength below Ordered: handed over

`Durability` names two strengths, and `Ordered` is the weaker: a barrier,
everything before it lands before anything after. On Apple platforms with
`barrier-fsync` that is `F_BARRIERFSYNC`, which does two things — pushes the
named file's dirty pages to the device, *and* issues a queue barrier. The
crate has no way to ask for the first without the second, and the second is
what costs: measured on an M3 Pro on APFS, a 200-byte file created, written,
renamed and flushed with its directory costs 0.14 ms per file with `fsync(2)`
on both and 0.44 ms with `F_BARRIERFSYNC` on both. `F_FULLFSYNC` on both is
6.4 ms, which is the drain and is not the subject here.

An `OrderedBatch` tier of N creates asks for N + D barriers — one per file,
one per directory that gained an entry — where the promise a tier makes
needs only N + D pushes and **one** barrier after the last of them. The
[module docs](../../src/ordered.rs) already say that within a tier nothing is
ordered; the barriers within a tier are therefore N − 1 more than the promise
requires. `flush_all_durable` is the same shape one level up: every path but
the anchor barriered, then the anchor drained, where every path but the last
could be pushed.

historica is the consumer that found it: a first capture lands thousands of
payloads, one `create_new`-shaped write each, and every one pays the barrier
pair. Its decision
[0075](https://github.com/diaryx-org/historica/blob/main/docs/decisions/0075-what-a-capture-owes-the-drive.md)
argues the shape this crate should offer and defers to this task for it.

## The shape

- **`Durability` gains a variant below `Ordered`** — *handed over*: the
  bytes reach the device before the call returns, ordered against nothing.
  `fsync(2)` on Apple (with or without `barrier-fsync`); `fsync` everywhere
  else, which is already the whole flush and is therefore stronger than
  asked, as ever. The name is open; `Pushed`, `Handed`, `Issued` have each
  been said out loud.
- **`SyncGuarantee` gains the matching level**, and `satisfies` says a
  backend answering only pushes can honour a push and nothing above it.
- **`apply_tier` uses it**: every file and directory in the tier pushed,
  then one `Ordered` on the last debt (or on the root, which needs an open
  handle either way) — N + D pushes and one barrier, for an `Ordered` tier;
  the same pushes and one `Durable` for the final tier, folding
  `flush_all_durable` into the same rule.
- **The variant is public**, so a consumer that lands its set one call at a
  time — which is how historica's store is shaped, since a streamed payload
  cannot be a slice in a batch — can ask for a push per file and issue the
  barrier itself once, through `Storage::sync(path, Durability::Ordered)`.

## What it costs

Both enums are exhaustive and public. A `match` on either in a consumer
breaks; so does a backend that implements `sync` by matching `need`. That is
a version somebody names, and it is why this is a task rather than a commit:
`dx deps fs-transaction --all` says who feels it, and the answer today is
historica and diaryx through it.

The crash state changes too, and the docs must say so: with a barrier per
file, at most one file in an interrupted tier is torn — the one in flight —
and the files before it are whole. With pushes and one barrier, any number of
files in the interrupted tail may be torn, because nothing orders them
against each other. For the trees `ordered` serves that is still legal — a
torn digest-named file is one the consumer already has to recognise and
discard — but "at most one" was a property somebody may have been counting
on, and it goes.

## Done when

- The variant exists on both enums, `satisfies` is right, and `StdFs::sync`
  answers it with a plain `fsync` on every platform the crate builds for.
- `apply_tier` and `flush_all_durable` issue N + D pushes and one barrier
  (or one drain) per tier, and a fault-injection test pins the count.
- The module docs for `ordered` state the new crash shape.
- The change carries a `Behavioural-change:` trailer for the crash shape,
  and the version bump is Adam's to name.
