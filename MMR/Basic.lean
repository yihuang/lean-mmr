namespace MMR

universe u

/-!
# Merkle Mountain Range accumulator with minimal state

This file gives an append-only Merkle Mountain Range (MMR) implementation
whose only stored state is:

* a list of peak hashes `peaks`, ordered from the newest/rightmost peak to
  the oldest/leftmost peak; and
* the number of leaves `leafCount`.

The hash function is abstract: any binary function `hash : α → α → α` can be
used.  Structural properties (leaf-count/peak-count invariants and merge
behavior) do not depend on the actual cryptographic hash.
-/

/-- A minimal MMR accumulator: peaks (newest/rightmost first) and leaf count. -/
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

/-- Append one leaf, updating only peaks and leaf count. -/
def append (hash : α → α → α) (m : Acc α) (leaf : α) : Acc α :=
  { peaks := mergeCarry hash (trailingOnes m.leafCount) leaf m.peaks,
    leafCount := m.leafCount + 1 }

/-- Append many leaves in order. -/
def appendList (hash : α → α → α) (initial : Acc α) (leaves : List α) : Acc α :=
  leaves.foldl (fun acc leaf => append hash acc leaf) initial

end Acc
end MMR
