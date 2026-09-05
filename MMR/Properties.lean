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
2. Appending peaks preserves the canonical MMR invariant under the aligned
   condition: `ValidChunk` guarantees every peak is aligned when it is pushed.
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

theorem pow_pos (h : Nat) : 0 < 2 ^ h := by
  induction h with
  | zero => decide
  | succ h ih => omega

theorem popcount_shift (q h : Nat) : popcount (2 ^ h * q) = popcount q := by
  induction h with
  | zero => simp
  | succ h ih =>
      have hstep : popcount (2 ^ (h+1) * q) = popcount (2 ^ h * q) := by
        rw [Nat.pow_succ']
        rw [Nat.mul_assoc]
        have := popcount_even (2 ^ h * q)
        simpa using this
      rw [hstep, ih]

theorem appendPeak_peaks_length {α : Type} (hash : α → α → α) (m : Acc α) (height : Nat) (peak : α)
    (halign : aligned m height)
    (h : m.peaks.length = popcount m.leafCount) :
    (appendPeak hash height peak m).peaks.length = popcount (m.leafCount + 2 ^ height) := by
  let n := m.leafCount
  let q := n / 2 ^ height
  have hpowpos : 0 < 2 ^ height := pow_pos height
  have hmod : n % 2^height = 0 := halign
  have hnmul : n = 2^height * q := by
    dsimp [q]
    have hdm := Nat.div_add_mod n (2 ^ height)
    omega
  have hpopn : popcount n = popcount q := by
    rw [hnmul]
    rw [popcount_shift q height]
  have hc : trailingOnes q ≤ m.peaks.length := by
    rw [h, hpopn]
    exact trailingOnes_le_popcount q
  have hmerge := mergeCarry_length_eq hash (trailingOnes q) peak m.peaks
  change (mergeCarry hash (trailingOnes (m.leafCount / 2 ^ height)) peak m.peaks).length =
    popcount (m.leafCount + 2 ^ height)
  rw [hmerge]
  rw [if_pos hc]
  have hnext : m.leafCount + 2^height = 2^height * (q+1) := by
    change n + 2^height = 2^height * (q + 1)
    rw [hnmul]
    rw [Nat.mul_add, Nat.mul_one]
  rw [hnext]
  rw [popcount_shift (q+1) height]
  rw [popcount_succ_eq_sub]
  have hpeq : m.peaks.length = popcount q := by
    rw [h, hpopn]
  rw [hpeq]

theorem chunk_foldl_add {α : Type} (chunk : Chunk α) (x : Nat) :
    chunk.foldl (fun acc hp => acc + 2 ^ hp.1) x = x + chunk.foldl (fun acc hp => acc + 2 ^ hp.1) 0 := by
  induction chunk generalizing x with
  | nil => simp
  | cons hp rest ih =>
      cases hp with
      | mk h p =>
        simp only [List.foldl_cons, Nat.zero_add]
        have hfold : List.foldl (fun acc hp => acc + 2 ^ hp.fst) (2 ^ h) rest =
            2 ^ h + List.foldl (fun acc hp => acc + 2 ^ hp.fst) 0 rest := by
          simpa [Nat.add_comm] using (ih (2 ^ h))
        rw [ih (x + 2 ^ h), hfold]
        omega

theorem appendPeaks_leafCount {α : Type} (hash : α → α → α) (m : Acc α) :
    ∀ chunk : Chunk α,
      (appendPeaks hash m chunk).leafCount = m.leafCount + chunk.foldl (fun acc hp => acc + 2 ^ hp.1) 0 := by
  intro chunk
  induction chunk generalizing m with
  | nil => simp [appendPeaks]
  | cons hp rest ih =>
      cases hp with
      | mk h peak =>
        simp [appendPeaks]
        rw [show (List.foldl (fun acc hp => appendPeak hash hp.1 hp.2 acc) (appendPeak hash h peak m) rest) =
            appendPeaks hash (appendPeak hash h peak m) rest by rfl]
        rw [ih (appendPeak hash h peak m)]
        rw [appendPeak_leafCount]
        rw [chunk_foldl_add rest (2 ^ h)]
        omega

/-- `appendPeaks` preserves the canonical invariant when every peak is aligned. -/
theorem appendPeaks_peaks_length {α : Type} (hash : α → α → α) (m : Acc α) (chunk : Chunk α)
    (hvalid : ValidChunk hash m chunk)
    (h : m.peaks.length = popcount m.leafCount) :
    (appendPeaks hash m chunk).peaks.length =
      popcount (m.leafCount + chunk.foldl (fun acc hp => acc + 2 ^ hp.1) 0) := by
  induction chunk generalizing m with
  | nil =>
      simp [appendPeaks, ValidChunk] at hvalid ⊢
      exact h
  | cons hp rest ih =>
      cases hp with
      | mk height peak =>
        have hvalid' : ValidChunk hash (appendPeak hash height peak m) rest := hvalid.2
        have halign : aligned m height := hvalid.1
        have hstep : (appendPeak hash height peak m).peaks.length =
            popcount (m.leafCount + 2 ^ height) :=
          appendPeak_peaks_length hash m height peak halign h
        have hrest := ih (appendPeak hash height peak m) hvalid' hstep
        -- hrest gives the tail length in terms of the intermediate leafCount.
        simp only [appendPeaks, List.foldl_cons] at *
        rw [hrest]
        rw [appendPeak_leafCount]
        simp [chunk_foldl_add rest (2 ^ height), Nat.add_assoc]

end Acc
end MMR
