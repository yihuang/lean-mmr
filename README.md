# MMR in Lean 4

A minimal Merkle Mountain Range (MMR) accumulator implemented in Lean 4.

The implementation stores only:

- `peaks : List α` — peak hashes, newest/rightmost first, and
- `leafCount : Nat` — number of leaves appended so far.

The hash algorithm is kept abstract: `append` is parameterized by an arbitrary
binary function `hash : α → α → α`.  For a real MMR this would be a hash of
the two children (with domain separation if desired), but all structural
properties are independent of the concrete hash.

## Files

- `MMR/Basic.lean` — the data structure and the append/merge algorithm:
  - `Acc` (peaks + leafCount)
  - `trailingOnes` (how many existing peaks are merged by the next append)
  - `popcount` (how many peaks a given leaf count has)
  - `mergeCarry` (the actual merge loop)
  - `append`, `appendList`

- `MMR/Properties.lean` — machine-checked properties:
  - the one-step binary carry relation
    `popcount (n+1) = popcount n - trailingOnes n + 1`,
  - `mergeCarry` removes `c` peaks and inserts one,
  - appending preserves `peaks.length = popcount leafCount`,
  - from empty, appending `n` leaves yields `popcount n` peaks,
  - `leafCount` always equals the number of appended leaves,
  - `appendList` is compositional: `appendList (as ++ bs) = appendList bs ∘ appendList as`.

## Build

```sh
lake build
lake env lean Examples.lean   # or import MMR in your own Lean file
```
