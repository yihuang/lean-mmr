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

/-- An aligned chunk: each `(height, peak)` is a complete subtree with
`2^height` leaves, right-appended in list order. -/
abbrev Chunk (α : Type u) := List (Nat × α)

/-- A height is aligned with a leaf count when it is a multiple of the subtree
size `2^height`.  Equivalently, `height` does not exceed the smallest existing
peak height; the empty MMR accepts every height. -/
abbrev alignedAt (leafCount : Nat) (height : Nat) : Prop :=
  leafCount % 2 ^ height = 0

/-- A height is aligned with an accumulator when aligned at its `leafCount`. -/
def aligned (m : Acc α) (height : Nat) : Prop :=
  alignedAt m.leafCount height

/-- Computable version of `alignedAt`. -/
def alignedAt? (leafCount : Nat) (height : Nat) : Bool :=
  decide (alignedAt leafCount height)

/-- Computable version of `aligned`. -/
def aligned? (m : Acc α) (height : Nat) : Bool :=
  alignedAt? m.leafCount height

/-- Computably check that a chunk's peak heights are aligned with the current
`leafCount`, returning `true` iff every height is aligned at the moment it
would be pushed.  Only heights matter, so the peak hashes are ignored. -/
def validChunk? (leafCount : Nat) : Chunk α → Bool
  | [] => true
  | (height, _) :: rest =>
    if alignedAt? leafCount height then
      validChunk? (leafCount + 2 ^ height) rest
    else
      false

/-- Carry-merge:
  `mergeCarry hash c x peaks` takes the new leaf `x` and merges it with the
  first `c` entries of `peaks` (the rightmost peaks).  The first merge is
  `hash p x` because `p` is the older (left) peak and `x` is the newer
  (right) peak.  Subsequent merges hash the older peak with the previously
  computed parent. -/
def mergeCarry (hash : α → α → α) : Nat → α → List α → List α
  | 0, x, peaks => x :: peaks
  | n + 1, x, p :: peaks => mergeCarry hash n (hash p x) peaks
  | _, x, [] => [x] -- unreachable for valid states; keeps definition total

/-- Append a complete subtree of `2^height` leaves whose root is `peak`.

This is the primitive MMR right-merge and is deliberately total/permissive:
it does not check `aligned m height`.  `aligned` is only the condition under
which the append-only semantic (stable leaf indices and the canonical peak
count) is preserved.  Appending a single leaf is the special case `height = 0`.

`mergeCarry` is reused with the carry starting at the given `height`: the number
of existing peaks consumed is the number of trailing 1s in `leafCount / 2^height`.
-/
def appendPeak (hash : α → α → α) (height : Nat) (peak : α) (m : Acc α) : Acc α :=
  { peaks := mergeCarry hash (trailingOnes (m.leafCount / 2 ^ height)) peak m.peaks,
    leafCount := m.leafCount + 2 ^ height }

/-- Append one leaf: `appendPeak` with height `0`. -/
def append (hash : α → α → α) (m : Acc α) (leaf : α) : Acc α :=
  appendPeak hash 0 leaf m

/-- Fold a chunk into an accumulator in order.  Like `appendPeak`, this function
is permissive and does not enforce `ValidChunk`; callers wanting append-only
semantics should provide a `ValidChunk`. -/
def appendPeaks (hash : α → α → α) (m : Acc α) (chunk : Chunk α) : Acc α :=
  chunk.foldl (fun acc hp => appendPeak hash hp.1 hp.2 acc) m

/-- A chunk satisfies the aligned condition when every element is aligned at the
moment it is pushed.  This is the precondition for preserving append-only
semantics; it is not enforced by `appendPeaks`. -/
def ValidChunk (hash : α → α → α) (m : Acc α) : Chunk α → Prop
  | [] => True
  | (height, peak) :: rest =>
    aligned m height ∧ ValidChunk hash (appendPeak hash height peak m) rest

end Acc
end MMR
