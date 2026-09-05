# Merkle Mountain Range in Lean 4

A formally verified, minimal [Merkle Mountain Range (MMR)](https://docs.grin.mw/wiki/chain-state/merkle-mountain-range/) accumulator implemented in [Lean 4](https://lean-lang.org/).

## Overview

The accumulator stores only two pieces of state:

- `peaks : List α` — peak hashes, ordered by increasing height (newest/rightmost first), and
- `leafCount : Nat` — the number of leaves appended so far.

The hash function is abstract. All operations are parameterized by an arbitrary binary function `hash : α → α → α`, so the implementation and its structural proofs do not depend on a particular cryptographic hash. In a real deployment, `hash` would be a domain-separated hash of two child hashes.

## Features

- **Minimal state**: no internal tree storage; only peak hashes and the leaf count are retained.
- **Append-only core**: `appendPeak`, `append`, and `appendPeaks` support appending single leaves, aligned subtrees, and ordered chunks.
- **Aligned precondition**: `ValidChunk` is the machine-checkable alignment predicate for append-only structural semantics. It is distinct from the `Valid` peak-count invariant and is not needed to prove it.
- **Verified invariants**: the structural properties of peak counts and leaf counts are proved in Lean, independent of the concrete hash.

## Design

The main data structure and top-level API are defined in `MMR/Basic.lean`.

```lean
namespace MMR

universe u

structure Acc (α : Type u) where
  peaks : List α   -- smallest height (newest/rightmost) first
  leafCount : Nat

namespace Acc

def Valid (m : Acc α) : Prop
def appendPeak (hash : α → α → α) (height : Nat) (peak : α) (m : Acc α) : Acc α
def append (hash : α → α → α) (m : Acc α) (leaf : α) : Acc α :=
  appendPeak hash 0 leaf m
def appendPeaks (hash : α → α → α) (m : Acc α) (chunk : List (Nat × α)) : Acc α
def ValidChunk (hash : α → α → α) (m : Acc α) (chunk : List (Nat × α)) : Prop

end Acc
end MMR
```

Key points:

- `appendPeak` appends a complete subtree with `2^height` leaves and right-merges it into the existing peaks.
- `append` is `appendPeak` at height `0`, as shown in the one-liner above.
- `appendPeaks` folds `appendPeak` over an ordered chunk.
- `Valid` is the canonical peak-count invariant: `m.Valid` means `m.peaks.length = popcount m.leafCount`.
- `ValidChunk` is the alignment predicate for append-only structural semantics.

Although internal nodes are not stored, a canonical root can be computed on demand from the minimal state by “bagging the peaks”: fold the peaks from right to left with `hash`, optionally including `leafCount` as a domain-separation prefix. This needs only the already-available `peaks` and `leafCount`, so no full tree is required to derive a root.

## Verified properties

`MMR/Properties.lean` contains machine-checked proofs of the accumulator’s central structural invariants.

### Core invariants

These results hold without any alignment condition:

- **The empty accumulator satisfies the canonical invariant.**

  ```lean
  theorem empty_valid (α : Type u) : (empty α).Valid
  ```

- **Single-leaf append preserves the canonical invariant.**

  ```lean
  theorem append_peaks_length {α : Type u} (hash : α → α → α) (m : Acc α) (leaf : α)
      (h : m.Valid) :
      (append hash m leaf).Valid
  ```

- **Subtree append preserves the canonical invariant.**

  ```lean
  theorem appendPeak_peaks_length {α : Type u} (hash : α → α → α) (m : Acc α) (height : Nat) (peak : α)
      (h : m.Valid) :
      (appendPeak hash height peak m).Valid
  ```

- **Chunk append preserves the canonical invariant for any chunk.**

  ```lean
  theorem appendPeaks_peaks_length {α : Type u} (hash : α → α → α) (m : Acc α) (chunk : List (Nat × α))
      (h : m.Valid) :
      (appendPeaks hash m chunk).Valid
  ```

- **The leaf count tracks the number of appended leaves exactly.**

  ```lean
  theorem appendPeaks_leafCount {α : Type u} (hash : α → α → α) (m : Acc α) (chunk : List (Nat × α)) :
      (appendPeaks hash m chunk).leafCount =
        m.leafCount + chunk.foldl (fun acc hp => acc + 2 ^ hp.1) 0
  ```

- **Supporting binary-carry lemmas**, including the one-step peak-count recurrence and the length behavior of `mergeCarry`.

### Append-only semantics are not yet formalized

`ValidChunk` is the API-level precondition intended for aligned, append-only structural semantics: it records that every `(height, peak)` in a chunk is aligned when it is pushed. It is not needed for the core invariants above, and preservation of the append-only structural semantics is not currently proved in this repository.

All proofs in this section are independent of the concrete hash function.

## Repository layout

```text
MMR/
  Basic.lean       Data structures and MMR operations
  Properties.lean  Formal proofs of the structural invariants
Main.lean          Executable entry point
lakefile.toml      Lake project configuration
lean-toolchain     Pinned Lean toolchain
```

## Requirements

- [Lean 4](https://lean-lang.org/) (the toolchain is pinned in `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake) (included with Lean)

## Build

```sh
lake build
```

To run the entry point:

```sh
lake env lean --run Main.lean
```

To use the library in another Lean project, import `MMR`.

## References

- [Merkle Mountain Ranges — Grin Documentation](https://docs.grin.mw/wiki/chain-state/merkle-mountain-range/) — a general introduction to the MMR accumulator, its append/merge behavior, peaks, and bagging.
- [Minimizing Storage Using Merkle Mountain Ranges — Neptune](https://neptune.cash/articles/mmr) — describes storing only peaks and leaf count as a minimal MMR accumulator.
