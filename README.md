# MMR in Lean 4

A minimal Merkle Mountain Range (MMR) accumulator implemented in Lean 4.

The implementation stores only:

- `peaks : List α` — peak hashes, newest/rightmost first, and
- `leafCount : Nat` — number of leaves appended so far.

The hash algorithm is kept abstract: `append` is parameterized by an arbitrary
binary function `hash : α → α → α`.  For a real MMR this would be a hash of
the two children (with domain separation if desired), but all structural
properties are independent of the concrete hash.

## Structure and operations

The core data structure is defined in `MMR/Basic.lean`:

```lean
structure Acc (α : Type u) where
  peaks : List α   -- newest/rightmost peak first
  leafCount : Nat
```

The main operations are:

```lean
empty    (α : Type u) : Acc α
append   (hash : α → α → α) (m : Acc α) (leaf : α) : Acc α
appendList (hash : α → α → α) (initial : Acc α) (leaves : List α) : Acc α
```

Appending uses two auxiliary definitions:

- `trailingOnes n` — how many equal-height rightmost peaks must be merged
  when appending the leaf at index `n`;
- `mergeCarry hash c leaf peaks` — the carry-merge loop that consumes `c`
  rightmost peaks and produces the new peak list.

Only `peaks` and `leafCount` are consulted or updated by `append`; no full
tree storage is needed.

## Proved main theorems

The machine-checked properties in `MMR/Properties.lean` include:

- Peak-count invariant:

  ```lean
  theorem append_peaks_length {α : Type} (hash : α → α → α) (m : Acc α) (leaf : α)
      (h : m.peaks.length = popcount m.leafCount) :
      (append hash m leaf).peaks.length = popcount (m.leafCount + 1)
  ```

- From the empty accumulator, appending `n` leaves yields exactly `popcount n`
  peaks:

  ```lean
  theorem appendList_peaks_length_empty (α : Type) (hash : α → α → α) (leaves : List α) :
      (appendList hash (empty α) leaves).peaks.length = popcount leaves.length
  ```

- The one-step binary carry relation used by the merge loop:

  ```lean
  theorem popcount_succ_eq_sub (n : Nat) :
      popcount (n + 1) = popcount n - trailingOnes n + 1
  ```

- The merge loop removes `c` peaks and inserts one:

  ```lean
  theorem mergeCarry_length_eq {α : Type} (hash : α → α → α) (c : Nat) (x : α) (peaks : List α) :
      (mergeCarry hash c x peaks).length = if c ≤ peaks.length then peaks.length - c + 1 else 1
  ```

- `leafCount` always equals the number of appended leaves:

  ```lean
  theorem appendList_leafCount {α : Type} (hash : α → α → α) (m : Acc α) (leaves : List α) :
      (appendList hash m leaves).leafCount = m.leafCount + leaves.length
  ```

- `appendList` is compositional, so batching appends does not change the
  resulting accumulator:

  ```lean
  theorem appendList_append {α : Type} (hash : α → α → α) (m : Acc α) (as bs : List α) :
      appendList hash m (as ++ bs) = appendList hash (appendList hash m as) bs
  ```

All proofs are independent of the concrete hash function.

## References

- [Merkle Mountain Ranges - Grin Documentation](https://docs.grin.mw/wiki/chain-state/merkle-mountain-range/) — a general introduction to the MMR accumulator, its append/merge behavior, peaks, and bagging.
- [Minimizing Storage Using Merkle Mountain Ranges - Neptune](https://neptune.cash/articles/mmr) — describes storing only peaks and leaf count as a minimal MMR accumulator.

## Build

```sh
lake build
lake env lean Examples.lean   # or import MMR in your own Lean file
```
