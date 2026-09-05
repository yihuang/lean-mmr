import MMR.Basic

namespace MMR
namespace Acc

universe u

/-!
# Verified properties of the minimal MMR accumulator

The proofs below establish the central structural invariants of the
accumulator:

1. Starting from the empty MMR, after appending `n` leaves the number of
   peaks is exactly the popcount of `n` (`popcount` counts the 1-bits in the
   binary representation of `n`).
2. Appending peaks preserves the canonical MMR invariant under the aligned
   condition: `ValidChunk` guarantees every peak is aligned when it is pushed.
3. `leafCount` is always the number of leaves appended so far.

No assumptions about the hash function are needed.

The file is organized in dependency order: first the pure bit arithmetic of
`popcount` and `trailingOnes`, then the length behavior of `mergeCarry`, and
finally the invariants of `append`, `appendPeak`, and `appendPeaks`.
-/

/-! ## Popcount / trailing-ones arithmetic

These lemmas are independent of the accumulator and describe the binary
carry behavior used by `mergeCarry`.
-/

section BitArithmetic

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

/-- Popcount is invariant under shifting in powers of two. -/
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

end BitArithmetic

/-! ## `mergeCarry`

Length behavior of the carry-merge helper.
-/

section MergeCarry

variable {α : Type u} (hash : α → α → α)

/-- `mergeCarry` removes exactly the `c` rightmost peaks and inserts one
merged/new peak (when enough peaks are present). -/
theorem mergeCarry_length_eq (c : Nat) (x : α) (peaks : List α) :
    (mergeCarry hash c x peaks).length = if c ≤ peaks.length then peaks.length - c + 1 else 1 := by
  induction c generalizing x peaks with
  | zero => simp [mergeCarry]
  | succ c ih =>
    cases peaks with
    | nil => simp [mergeCarry]
    | cons p ps =>
        simp [mergeCarry]
        exact ih (hash p x) ps

end MergeCarry

/-! ## Empty accumulator -/

section Empty

variable {α : Type u}

/-- The empty MMR satisfies the canonical peak-count invariant. -/
theorem empty_valid (α : Type u) : (empty α).Valid := by
  unfold Valid
  simp [empty, popcount]

end Empty

/-! ## Appending a single leaf -/

section Append

variable {α : Type u} (hash : α → α → α)

theorem append_leafCount (m : Acc α) (leaf : α) :
    (append hash m leaf).leafCount = m.leafCount + 1 := by
  simp [append, appendPeak]

/-- Appending preserves the canonical invariant `m.Valid`. -/
theorem append_peaks_length (m : Acc α) (leaf : α)
    (h : m.Valid) :
    (append hash m leaf).Valid := by
  unfold Valid
  rw [append_leafCount]
  have h' : m.peaks.length = popcount m.leafCount := by
    simpa [Valid] using h
  have hle : trailingOnes m.leafCount ≤ m.peaks.length := by
    rw [h']
    exact trailingOnes_le_popcount m.leafCount
  have hpow : m.leafCount / 2 ^ 0 = m.leafCount := by simp
  change (mergeCarry hash (trailingOnes (m.leafCount / 2 ^ 0)) leaf m.peaks).length =
    popcount (m.leafCount + 1)
  rw [hpow, mergeCarry_length_eq, if_pos hle, h', popcount_succ_eq_sub]

end Append

/-! ## Appending subtrees and chunks -/

section AppendPeaks

variable {α : Type u} (hash : α → α → α)

theorem appendPeak_leafCount (h : Nat) (peak : α) (m : Acc α) :
    (appendPeak hash h peak m).leafCount = m.leafCount + 2 ^ h := by
  simp [appendPeak]

/-- `appendPeak` preserves the canonical invariant when the peak is aligned. -/
theorem appendPeak_peaks_length (m : Acc α) (height : Nat) (peak : α)
    (halign : aligned m height)
    (h : m.Valid) :
    (appendPeak hash height peak m).Valid := by
  unfold Valid
  rw [appendPeak_leafCount]
  have h' : m.peaks.length = popcount m.leafCount := by
    simpa [Valid] using h
  let n := m.leafCount
  let q := n / 2 ^ height
  have hpowpos : 0 < 2 ^ height := Nat.two_pow_pos height
  have hmod : n % 2^height = 0 := halign
  have hnmul : n = 2^height * q := by
    dsimp [q]
    have hdm := Nat.div_add_mod n (2 ^ height)
    omega
  have hpopn : popcount n = popcount q := by
    rw [hnmul]
    rw [popcount_shift q height]
  have hc : trailingOnes q ≤ m.peaks.length := by
    rw [h', hpopn]
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
    rw [h', hpopn]
  rw [hpeq]

/-- Folding leaf contributions over a chunk commutes with adding a base. -/
theorem chunk_foldl_add (chunk : Chunk α) (x : Nat) :
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

theorem appendPeaks_leafCount (m : Acc α) (chunk : Chunk α) :
    (appendPeaks hash m chunk).leafCount = m.leafCount + chunk.foldl (fun acc hp => acc + 2 ^ hp.1) 0 := by
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
theorem appendPeaks_peaks_length (m : Acc α) (chunk : Chunk α)
    (hvalid : ValidChunk hash m chunk)
    (h : m.Valid) :
    (appendPeaks hash m chunk).Valid := by
  unfold Valid
  rw [appendPeaks_leafCount]
  induction chunk generalizing m with
  | nil =>
      simp [appendPeaks, ValidChunk] at hvalid ⊢
      simpa [Valid] using h
  | cons hp rest ih =>
      cases hp with
      | mk height peak =>
        have hvalid' : ValidChunk hash (appendPeak hash height peak m) rest := hvalid.2
        have halign : aligned m height := hvalid.1
        have hstep : (appendPeak hash height peak m).Valid :=
          appendPeak_peaks_length hash m height peak halign h
        have hrest := ih (appendPeak hash height peak m) hvalid' hstep
        -- hrest gives the tail length in terms of the intermediate leafCount.
        simp only [appendPeaks, List.foldl_cons] at *
        rw [hrest]
        rw [appendPeak_leafCount]
        simp [chunk_foldl_add rest (2 ^ height), Nat.add_assoc]

end AppendPeaks

end Acc
end MMR
