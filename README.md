# MMR in Lean 4

A minimal Merkle Mountain Range (MMR) accumulator implemented in Lean 4.

The implementation stores only:

- `peaks : List α` — peak hashes, smallest height (newest/rightmost) first, and
- `leafCount : Nat` — number of leaves appended so far.

The hash algorithm is kept abstract: `append` is parameterized by an arbitrary
binary function `hash : α → α → α`.  For a real MMR this would be a hash of
the two children (with domain separation if desired), but all structural
properties are independent of the concrete hash.

## Structure and operations

The core data structure is defined in `MMR/Basic.lean`:

```lean
structure Acc (α : Type u) where
  peaks : List α   -- smallest height (newest/rightmost) first
  leafCount : Nat
```

The main operations are:

```lean
empty       (α : Type u) : Acc α
appendPeak  (hash : α → α → α) (height : Nat) (peak : α) (m : Acc α) : Acc α
appendPeaks (hash : α → α → α) (m : Acc α) : Chunk α → Acc α
append      (hash : α → α → α) (m : Acc α) (leaf : α) : Acc α
```

Key points:

- `appendPeak` is the core primitive: it appends a complete subtree with
  `2^height` leaves, right-merging it into existing peaks while preserving
  stable leaf indices.
- Single-leaf `append` is just `appendPeak height 0`.
- `appendPeaks` folds `appendPeak` over an ordered chunk.

Appending uses two auxiliary definitions:

- `trailingOnes n` — how many equal-height rightmost peaks must be merged
  when appending the leaf at index `n`;
- `mergeCarry hash c leaf peaks` — the carry-merge loop that consumes `c`
  rightmost peaks and produces the new peak list.

Only `peaks` and `leafCount` are consulted or updated; no full tree storage is
needed.

Although the accumulator does not store internal nodes, a single root can
still be computed on the fly from the minimal state by *bagging the peaks*:
fold the peaks from right to left with `hash`, optionally including
`leafCount` as a domain-separation prefix in the outer hash. This needs only
the already-available `peaks` and `leafCount`, so the root can be derived
whenever a verifier needs it without keeping the full tree around.

## Proved main theorems

The machine-checked properties in `MMR/Properties.lean` include:

- Peak-count invariant:

  ```lean
  theorem append_peaks_length {α : Type} (hash : α → α → α) (m : Acc α) (leaf : α)
      (h : m.peaks.length = popcount m.leafCount) :
      (append hash m leaf).peaks.length = popcount (m.leafCount + 1)
  ```

- `appendPeak` preserves the canonical invariant when the peak is aligned:

  ```lean
  theorem appendPeak_peaks_length {α : Type} (hash : α → α → α) (m : Acc α) (height : Nat) (peak : α)
      (halign : aligned m height)
      (h : m.peaks.length = popcount m.leafCount) :
      (appendPeak hash height peak m).peaks.length = popcount (m.leafCount + 2 ^ height)
  ```

- `appendPeaks` preserves append-only semantics under the aligned condition:

  ```lean
  theorem appendPeaks_peaks_length {α : Type} (hash : α → α → α) (m : Acc α) (chunk : Chunk α)
      (hvalid : ValidChunk hash m chunk)
      (h : m.peaks.length = popcount m.leafCount) :
      (appendPeaks hash m chunk).peaks.length =
        popcount (m.leafCount + chunk.foldl (fun acc hp => acc + 2 ^ hp.1) 0)
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

- `leafCount` always equals the number of leaves added by a chunk:

  ```lean
  theorem appendPeaks_leafCount {α : Type} (hash : α → α → α) (m : Acc α) :
      ∀ chunk : Chunk α,
        (appendPeaks hash m chunk).leafCount =
          m.leafCount + chunk.foldl (fun acc hp => acc + 2 ^ hp.1) 0
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
