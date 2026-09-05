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
- **Verified append-only semantics**: under aligned input, the accumulator is proved to be exactly the canonical MMR of the appended leaf history — see [`MMR/AppendOnly.lean`](MMR/AppendOnly.lean) and [Append-only semantics](#append-only-semantics-under-aligned-input).

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
- `ValidChunk` is the alignment predicate for append-only structural semantics; `validChunk?` is its computable validator.

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

All proofs in this section are independent of the concrete hash function.

### Append-only semantics under aligned input

`MMR/AppendOnly.lean` formalizes the append-only structural semantics and proves
that the implementation has them whenever the pushed input is aligned. The
statements are relative to a semantic model defined independently of the
implementation's evaluation order:

- `subtreeRoot hash base h f` — the root of the complete binary tree of height `h`
  covering leaves `f base, …, f (base + 2^h − 1)` of a leaf history `f`;
- `specPeaks hash n f` — the canonical MMR peaks (newest/smallest first) of the
  first `n` leaves of `f`, i.e. the forest given by the binary representation of `n`;
- `Represents hash m f` — the accumulator `m` is exactly the canonical MMR of
  the first `m.leafCount` leaves of `f`.

The main results are:

- **Aligned subtree append is canonical** — when `height` is aligned with `m`
  (`m.leafCount % 2^height = 0`), appending the genuine subtree root of the next
  `2^height` leaves extends the represented history:

  ```lean
  theorem appendPeak_spec (hash : α → α → α) (height : Nat) {m : Acc α} {f : Nat → α}
      (hrep : Represents hash m f) (halign : aligned m height) :
      Represents hash (appendPeak hash height (subtreeRoot hash m.leafCount height f) m) f
  ```

- **Single-leaf append is canonical** (height `0` is always aligned):

  ```lean
  theorem append_spec {m : Acc α} {f : Nat → α} (hrep : Represents hash m f) :
      Represents hash (append hash m (f m.leafCount)) f
  ```

- **Chunk append is canonical under aligned input**: an `AlignedRoots` chunk —
  every entry aligned at push time and carrying the genuine subtree root of the
  leaves it covers — preserves `Represents`:

  ```lean
  theorem appendPeaks_spec {m : Acc α} {f : Nat → α} {chunk : List (Nat × α)}
      (hrep : Represents hash m f) (hv : AlignedRoots hash m f chunk) :
      Represents hash (appendPeaks hash m chunk) f
  ```

  Together with `specPeaks_congr` (below) this is the append-only guarantee:
  the state at any point is the canonical MMR of exactly the leaves appended
  so far, and appending only ever extends that history, so leaf indices are
  stable and past leaf hashes are never rewritten.

- **The aligned step is exactly the implementation's carry-merge** (the key lemma
  behind the above):

  ```lean
  theorem specPeaks_aligned_step (hash : α → α → α) (q : Nat) :
      ∀ (h : Nat) (f : Nat → α),
        specPeaks hash (2 ^ h * (q + 1)) f
          = mergeCarry hash (trailingOnes q) (subtreeRoot hash (2 ^ h * q) h f)
              (specPeaks hash (2 ^ h * q) f)
  ```

- **Past leaves are never rewritten**: the canonical MMR of `n` leaves depends
  only on those `n` leaves, so future appends cannot change old leaf hashes:

  ```lean
  theorem specPeaks_congr (hash : α → α → α) (f g : Nat → α) :
      ∀ n, (∀ i, i < n → f i = g i) → specPeaks hash n f = specPeaks hash n g
  ```

- **Surviving peaks are untouched**: an append absorbs exactly the
  `trailingOnes (leafCount / 2^height)` trailing peaks and keeps every other
  peak verbatim:

  ```lean
  theorem appendPeak_peaks_prefix (hash : α → α → α) (m : Acc α) (height : Nat) (peak : α)
      (hvalid : m.Valid) :
      ∃ r, (appendPeak hash height peak m).peaks
        = r :: m.peaks.drop (trailingOnes (m.leafCount / 2 ^ height))
  ```

- **Bridges to the API**: `validChunk?` decides `ValidChunk`
  (`validChunk?_eq_validChunk`), the semantic chunk precondition `AlignedRoots`
  refines `ValidChunk` (`alignedRoots_validChunk`), and any representing state
  satisfies the canonical peak-count invariant (`represents_valid`, via
  `specPeaks_length : (specPeaks hash n f).length = popcount n`).

Without alignment the same operations remain safe — `Valid` still holds
unconditionally — but the resulting state is no longer the canonical MMR of any
leaf history, so stable leaf indices are not guaranteed. Alignment is exactly
the condition under which `appendPeak` coincides with the canonical MMR
extension (see `specPeaks_aligned_step`).

All proofs in this section are independent of the concrete hash function.

## Repository layout

```text
MMR/
  Basic.lean        Data structures and MMR operations
  Properties.lean   Formal proofs of the structural invariants
  AppendOnly.lean   Semantic model and proofs of append-only semantics
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
