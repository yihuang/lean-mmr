namespace MMR

universe u

/-!
# Merkle Mountain Range accumulator with minimal state

This file gives an append-only Merkle Mountain Range (MMR) implementation
whose only stored state is:

* a list of peak hashes `peaks`, ordered by increasing height, i.e. from the
  smallest (newest/rightmost) peak to the largest (oldest/leftmost) peak; and
* the number of leaves `leafCount`.

The hash function is abstract: any binary function `hash : α → α → α` can be
used.  Structural properties (leaf-count/peak-count invariants and merge
behavior) do not depend on the actual cryptographic hash.
-/

/-- A minimal MMR accumulator: peaks (smallest height / newest first) and leaf count. -/
structure Acc (α : Type u) where
  peaks : List α
  leafCount : Nat
deriving Repr

namespace Acc

/-- The empty MMR. -/
def empty (α : Type u) : Acc α := ⟨[], 0⟩

/-- Number of trailing 1s in the binary representation of `n`.
This is exactly the number of equal-height peaks that will merge when the
leaf with index `n` is appended. -/
def trailingOnes : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then 0
    else trailingOnes ((n + 1) / 2) + 1
termination_by n => n
decreasing_by
  simp_wf
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- Number of 1-bits in `n`; the number of peaks of an MMR with `n` leaves. -/
def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)
termination_by n => n
decreasing_by
  simp_wf
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

set_option linter.unusedVariables false in
/-- Carry-merge:
  `mergeCarry hash c x peaks` takes the new leaf `x` and merges it with the
  first `c` entries of `peaks` (the rightmost peaks).  The first merge is
  `hash p x` because `p` is the older (left) peak and `x` is the newer
  (right) peak.  Subsequent merges hash the older peak with the previously
  computed parent. -/
def mergeCarry (hash : α → α → α) : Nat → α → List α → List α
  | 0, x, peaks => x :: peaks
  | n + 1, x, p :: peaks => mergeCarry hash n (hash p x) peaks
  | _c + 1, x, [] => [x] -- unreachable for valid states; keeps definition total

/-- Append a complete aligned subtree of `2^height` leaves whose root is `peak`.

This is the primitive MMR right-merge.  Appending a single leaf is the special
case `height = 0`.  When the input is valid (`aligned m height`), it preserves
the append-only semantics: the new subtree is placed immediately after the
current leaves and is right-merged with existing peaks of matching heights.

`mergeCarry` is reused with the carry starting at the given `height`: the number
of existing peaks consumed is the number of trailing 1s in `leafCount / 2^height`.
-/
def appendPeak (hash : α → α → α) (height : Nat) (peak : α) (m : Acc α) : Acc α :=
  { peaks := mergeCarry hash (trailingOnes (m.leafCount / 2 ^ height)) peak m.peaks,
    leafCount := m.leafCount + 2 ^ height }

/-- Append one leaf: `appendPeak` with height `0`. -/
def append (hash : α → α → α) (m : Acc α) (leaf : α) : Acc α :=
  appendPeak hash 0 leaf m

/-- Append many leaves in order.  It is derived from `appendPeak` by treating
each leaf as a height-0 aligned peak. -/
def appendList (hash : α → α → α) (initial : Acc α) (leaves : List α) : Acc α :=
  leaves.foldl (fun acc leaf => append hash acc leaf) initial

end Acc
end MMR
