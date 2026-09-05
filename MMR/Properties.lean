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
2. `append`, `appendPeak`, and `appendPeaks` all preserve the canonical
   peak-count invariant `Valid`; no alignment condition is needed for this
   invariant.
3. `leafCount` is always the number of leaves appended so far.
4. `ValidChunk` is provided as the API-level precondition for aligned,
   append-only structural semantics; those semantics are formalized and proved
   in `MMR/AppendOnly.lean`, not in this file.

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

/-- Popcount of a shifted number plus a low remainder is the sum of the two
popcounts, as long as the remainder fits below the shift. -/
theorem popcount_shift_add (q r h : Nat) (hr : r < 2 ^ h) :
    popcount (2 ^ h * q + r) = popcount q + popcount r := by
  induction h generalizing r with
  | zero =>
      have hr0 : r = 0 := by omega
      simp [hr0, popcount]
  | succ h ih =>
      rcases Nat.mod_two_eq_zero_or_one r with hmod | hmod
      · let k := r / 2
        have hdm := Nat.div_add_mod r 2
        have hr_eq : r = 2 * k := by
          dsimp [k]
          omega
        have hpow : 2 ^ (h + 1) = 2 * 2 ^ h := by
          rw [Nat.pow_succ']
        have hr' : r < 2 * 2 ^ h := by
          simpa [hpow] using hr
        have hk_lt : k < 2 ^ h := by
          dsimp [k]
          omega
        have hmul : 2 ^ (h + 1) * q + r = 2 * (2 ^ h * q + k) := by
          rw [hpow, hr_eq]
          rw [Nat.mul_add, Nat.mul_assoc]
        rw [hmul, popcount_even]
        rw [ih k hk_lt]
        rw [hr_eq, popcount_even]
      · let k := r / 2
        have hdm := Nat.div_add_mod r 2
        have hr_eq : r = 2 * k + 1 := by
          dsimp [k]
          omega
        have hpow : 2 ^ (h + 1) = 2 * 2 ^ h := by
          rw [Nat.pow_succ']
        have hr' : r < 2 * 2 ^ h := by
          simpa [hpow] using hr
        have hk_lt : k < 2 ^ h := by
          dsimp [k]
          omega
        have hmul : 2 ^ (h + 1) * q + r = 2 * (2 ^ h * q + k) + 1 := by
          rw [hpow, hr_eq]
          rw [Nat.mul_add, Nat.mul_assoc]
          omega
        rw [hmul, popcount_odd]
        rw [ih k hk_lt]
        rw [hr_eq, popcount_odd]
        omega

/-- Adding `2^h` to `n` follows the same carry rule as adding one to
`n / 2^h`: the number of trailing ones of `n / 2^h` is the number of peaks
merged. -/
theorem popcount_add_pow (n h : Nat) :
    popcount (n + 2 ^ h) = popcount n - trailingOnes (n / 2 ^ h) + 1 := by
  let q := n / 2 ^ h
  let r := n % 2 ^ h
  have hr : r < 2 ^ h := by
    dsimp [r]
    exact Nat.mod_lt n (Nat.two_pow_pos h)
  have hdec : 2 ^ h * q + r = n := by
    dsimp [q, r]
    exact Nat.div_add_mod n (2 ^ h)
  have hpopn : popcount n = popcount q + popcount r := by
    have hp := popcount_shift_add q r h hr
    rwa [hdec] at hp
  have hnext : n + 2 ^ h = 2 ^ h * (q + 1) + r := by
    rw [← hdec]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hpopnext : popcount (n + 2 ^ h) = popcount (q + 1) + popcount r := by
    rw [hnext]
    exact popcount_shift_add (q + 1) r h hr
  rw [hpopnext]
  rw [hpopn]
  change popcount (q + 1) + popcount r =
    (popcount q + popcount r) - trailingOnes q + 1
  rw [popcount_succ_eq_sub q]
  have ht : trailingOnes q ≤ popcount q := trailingOnes_le_popcount q
  omega

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

/-- `appendPeak` preserves the canonical invariant, without requiring an aligned height. -/
theorem appendPeak_peaks_length (m : Acc α) (height : Nat) (peak : α)
    (h : m.Valid) :
    (appendPeak hash height peak m).Valid := by
  unfold Valid
  rw [appendPeak_leafCount]
  have h' : m.peaks.length = popcount m.leafCount := by
    simpa [Valid] using h
  let n := m.leafCount
  let q := n / 2 ^ height
  have hmod : n % 2 ^ height < 2 ^ height := Nat.mod_lt n (Nat.two_pow_pos height)
  have hdec : 2 ^ height * q + n % 2 ^ height = n := by
    dsimp [q]
    exact Nat.div_add_mod n (2 ^ height)
  have hpopn : popcount n = popcount q + popcount (n % 2 ^ height) := by
    have hp := popcount_shift_add q (n % 2 ^ height) height hmod
    rwa [hdec] at hp
  have hc : trailingOnes q ≤ m.peaks.length := by
    rw [h']
    change trailingOnes q ≤ popcount n
    have hle : trailingOnes q ≤ popcount q := trailingOnes_le_popcount q
    have hqle : popcount q ≤ popcount n := by
      rw [hpopn]
      omega
    omega
  have hmerge := mergeCarry_length_eq hash (trailingOnes q) peak m.peaks
  change (mergeCarry hash (trailingOnes (m.leafCount / 2 ^ height)) peak m.peaks).length =
    popcount (m.leafCount + 2 ^ height)
  rw [hmerge]
  rw [if_pos hc]
  rw [h']
  change popcount n - trailingOnes q + 1 = popcount (n + 2 ^ height)
  rw [popcount_add_pow n height]

/-- Folding leaf contributions over a chunk commutes with adding a base. -/
theorem chunk_foldl_add (chunk : List (Nat × α)) (x : Nat) :
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

theorem appendPeaks_leafCount (m : Acc α) (chunk : List (Nat × α)) :
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

/-- `appendPeaks` preserves the canonical invariant for any chunk. -/
theorem appendPeaks_peaks_length (m : Acc α) (chunk : List (Nat × α))
    (h : m.Valid) :
    (appendPeaks hash m chunk).Valid := by
  induction chunk generalizing m with
  | nil =>
      simpa [appendPeaks] using h
  | cons hp rest ih =>
      cases hp with
      | mk height peak =>
        change Valid (appendPeaks hash (appendPeak hash height peak m) rest)
        exact ih (appendPeak hash height peak m)
          (appendPeak_peaks_length hash m height peak h)

end AppendPeaks

end Acc
end MMR
