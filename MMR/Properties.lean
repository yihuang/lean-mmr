import MMR.Basic

namespace MMR
namespace Acc

/-!
# Verified properties of the minimal MMR accumulator

The proofs below establish the two central structural invariants of the
accumulator:

1. Starting from the empty MMR, after appending `n` leaves the number of
   peaks is exactly the popcount of `n` (`popcount` counts the 1-bits in the
   binary representation of `n`).
2. Appending is compositional: `appendList` respects list concatenation, so
   the resulting MMR state is independent of how a batch of leaves is split
   across multiple `appendList` calls.
3. `leafCount` is always the number of leaves appended so far.

No assumptions about the hash function are needed.
-/

/-! ## Popcount / trailing-ones arithmetic -/

theorem popcount_succ (n : Nat) : popcount (n + 1) = (n + 1) % 2 + popcount ((n + 1) / 2) := by
  simp [popcount]

theorem popcount_even (k : Nat) : popcount (2 * k) = popcount k := by
  induction k with
  | zero => simp [popcount]
  | succ k ih =>
      have hmul : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [hmul]
      have hmod : (2 * k + 2) % 2 = 0 := by omega
      have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
      rw [popcount_succ (2 * k + 1)]
      simp [hmod, hdiv]

theorem popcount_odd (k : Nat) : popcount (2 * k + 1) = popcount k + 1 := by
  induction k with
  | zero => simp [popcount]
  | succ k ih =>
      have hmul : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [hmul]
      have hmod : (2 * k + 3) % 2 = 1 := by omega
      have hdiv : (2 * k + 3) / 2 = k + 1 := by omega
      rw [popcount_succ (2 * k + 2)]
      simp [hmod, hdiv]
      omega

theorem trailingOnes_succ (n : Nat) :
    trailingOnes (n + 1) =
      if (n + 1) % 2 = 0 then 0 else trailingOnes ((n + 1) / 2) + 1 := by
  simp [trailingOnes]

theorem trailingOnes_even (k : Nat) : trailingOnes (2 * k) = 0 := by
  induction k with
  | zero => simp [trailingOnes]
  | succ k ih =>
      have hmul : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [hmul]
      have hmod : (2 * k + 2) % 2 = 0 := by omega
      simp [trailingOnes, hmod]

theorem trailingOnes_odd (k : Nat) : trailingOnes (2 * k + 1) = trailingOnes k + 1 := by
  induction k with
  | zero => simp [trailingOnes]
  | succ k ih =>
      have hmul : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [hmul]
      have hmod : (2 * k + 3) % 2 = 1 := by omega
      have hdiv : (2 * k + 3) / 2 = k + 1 := by omega
      rw [trailingOnes_succ (2 * k + 2)]
      simp [hmod, hdiv]

/-- The merge count at `n` never exceeds the total number of peaks at `n`. -/
theorem trailingOnes_le_popcount (n : Nat) : trailingOnes n ≤ popcount n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [trailingOnes, popcount]
    | succ m =>
      by_cases hmod0 : (m+1) % 2 = 0
      · have hmul : m+1 = 2 * ((m+1)/2) := by omega
        rw [hmul]
        have hto : trailingOnes (2 * ((m+1)/2)) = 0 := trailingOnes_even _
        rw [hto]
        exact Nat.zero_le _
      · let k := (m+1) / 2
        have hmul : m+1 = 2 * k + 1 := by omega
        rw [hmul]
        have hto : trailingOnes (2*k+1) = trailingOnes k + 1 := trailingOnes_odd k
        rw [hto]
        have hpop : popcount (2*k+1) = popcount k + 1 := popcount_odd k
        rw [hpop]
        have ihk : trailingOnes k ≤ popcount k := ih k (by omega)
        omega

/-- The one-step peak-count recurrence:
`popcount (n+1) = popcount n - trailingOnes n + 1`.
This is exactly the binary carry used by `mergeCarry`. -/
theorem popcount_succ_eq_sub (n : Nat) :
    popcount (n + 1) = popcount n - trailingOnes n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [popcount, trailingOnes]
    | succ m =>
      by_cases hmod0 : (m+1) % 2 = 0
      · let k := (m+1) / 2
        have hmul : m + 1 = 2 * k := by omega
        have hto : trailingOnes (m+1) = 0 := by
          rw [hmul]; exact trailingOnes_even k
        have hpopm : popcount (m+1) = popcount k := by
          rw [hmul]; exact popcount_even k
        have hnext_mul : m + 1 + 1 = 2 * k + 1 := by omega
        have hpopnext : popcount (m + 1 + 1) = popcount k + 1 := by
          rw [hnext_mul]; exact popcount_odd k
        simp [hto, hpopm, hpopnext]
      · have hmod1 : (m+1) % 2 = 1 := (Nat.mod_two_eq_zero_or_one (m+1)).resolve_left hmod0
        let k := (m+1) / 2
        have hmul : m + 1 = 2 * k + 1 := by omega
        have hto : trailingOnes (m+1) = trailingOnes k + 1 := by
          rw [hmul]; exact trailingOnes_odd k
        have hpopm : popcount (m+1) = popcount k + 1 := by
          rw [hmul]; exact popcount_odd k
        have hnext_mul : m + 1 + 1 = 2 * (k + 1) := by omega
        have hpopnext : popcount (m + 1 + 1) = popcount (k + 1) := by
          rw [hnext_mul]; exact popcount_even (k+1)
        have ihk : popcount (k + 1) = popcount k - trailingOnes k + 1 := ih k (by omega)
        rw [hpopnext, ihk]
        simp [hto, hpopm]

/-! ## Core append/merge invariants -/

/-- `mergeCarry` removes exactly the `c` rightmost peaks and inserts one
merged/new peak (when enough peaks are present). -/
theorem mergeCarry_length_eq {α : Type} (hash : α → α → α) (c : Nat) (x : α) (peaks : List α) :
    (mergeCarry hash c x peaks).length = if c ≤ peaks.length then peaks.length - c + 1 else 1 := by
  induction c generalizing x peaks with
  | zero => simp [mergeCarry]
  | succ c ih =>
    cases peaks with
    | nil => simp [mergeCarry]
    | cons p ps =>
        simp [mergeCarry]
        exact ih (hash p x) ps

theorem append_leafCount (hash : α → α → α) (m : Acc α) (leaf : α) :
    (append hash m leaf).leafCount = m.leafCount + 1 := by
  simp [append, appendPeak]

/-- Appending preserves the invariant `peaks.length = popcount leafCount`. -/
theorem append_peaks_length {α : Type} (hash : α → α → α) (m : Acc α) (leaf : α)
    (h : m.peaks.length = popcount m.leafCount) :
    (append hash m leaf).peaks.length = popcount (m.leafCount + 1) := by
  have hle : trailingOnes m.leafCount ≤ m.peaks.length := by
    rw [h]
    exact trailingOnes_le_popcount m.leafCount
  have hpow : m.leafCount / 2 ^ 0 = m.leafCount := by simp
  change (mergeCarry hash (trailingOnes (m.leafCount / 2 ^ 0)) leaf m.peaks).length =
    popcount (m.leafCount + 1)
  rw [hpow]
  have hmerge := mergeCarry_length_eq hash (trailingOnes m.leafCount) leaf m.peaks
  rw [hmerge]
  rw [h]
  rw [popcount_succ_eq_sub]
  have hle' : trailingOnes m.leafCount ≤ popcount m.leafCount := by simpa [h] using hle
  simp [hle']

theorem appendPeak_leafCount (hash : α → α → α) (h : Nat) (peak : α) (m : Acc α) :
    (appendPeak hash h peak m).leafCount = m.leafCount + 2 ^ h := by
  simp [appendPeak]

theorem appendList_leafCount {α : Type} (hash : α → α → α) (m : Acc α) (leaves : List α) :
    (appendList hash m leaves).leafCount = m.leafCount + leaves.length := by
  induction leaves generalizing m with
  | nil => simp [appendList]
  | cons a as ih =>
      simp [appendList]
      change (appendList hash (append hash m a) as).leafCount =
        m.leafCount + (as.length + 1)
      have h := ih (append hash m a)
      rw [append_leafCount] at h
      omega

/-- Appending a whole list preserves the invariant, generalized to an
arbitrary starting state satisfying it. -/
theorem appendList_peaks_length {α : Type} (hash : α → α → α) (m : Acc α) (leaves : List α)
    (h : m.peaks.length = popcount m.leafCount) :
    (appendList hash m leaves).peaks.length = popcount (m.leafCount + leaves.length) := by
  induction leaves generalizing m with
  | nil => simpa [appendList] using h
  | cons a as ih =>
      simp [appendList]
      have h₁ : (append hash m a).peaks.length = popcount (m.leafCount + 1) := append_peaks_length hash m a h
      have h₂ : (appendList hash (append hash m a) as).peaks.length =
          popcount ((append hash m a).leafCount + as.length) := ih (append hash m a) h₁
      change (appendList hash (append hash m a) as).peaks.length =
        popcount (m.leafCount + (as.length + 1))
      rw [h₂]
      congr 1
      rw [append_leafCount]
      omega

/-- From the empty accumulator, `n` leaves produce exactly `popcount n`
peaks. -/
theorem appendList_peaks_length_empty (α : Type) (hash : α → α → α) (leaves : List α) :
    (appendList hash (empty α) leaves).peaks.length = popcount leaves.length := by
  have h := appendList_peaks_length hash (empty α) leaves (by simp [empty, popcount])
  simpa [empty] using h

/-- `appendList` is compositional: appending `as ++ bs` in one batch gives
the same state as appending `as` and then `bs`. -/
theorem appendList_append {α : Type} (hash : α → α → α) (m : Acc α) (as bs : List α) :
    appendList hash m (as ++ bs) = appendList hash (appendList hash m as) bs := by
  simp [appendList, List.foldl_append]

/-- Compositionality also preserves the peak-count invariant. -/
theorem appendList_peaks_length_append {α : Type} (hash : α → α → α) (m : Acc α) (as bs : List α)
    (h : m.peaks.length = popcount m.leafCount) :
    (appendList hash m (as ++ bs)).peaks.length =
      popcount (m.leafCount + (as ++ bs).length) := by
  rw [appendList_append]
  have h1 : (appendList hash m as).peaks.length = popcount (m.leafCount + as.length) :=
    appendList_peaks_length hash m as h
  have hcanon : (appendList hash m as).peaks.length = popcount (appendList hash m as).leafCount := by
    rw [appendList_leafCount]
    exact h1
  have h2 : (appendList hash (appendList hash m as) bs).peaks.length =
      popcount ((appendList hash m as).leafCount + bs.length) :=
    appendList_peaks_length hash (appendList hash m as) bs hcanon
  rw [h2]
  rw [appendList_leafCount]
  have hlen : (as ++ bs).length = as.length + bs.length := by simp
  rw [hlen]
  congr 1
  omega

end Acc
end MMR
