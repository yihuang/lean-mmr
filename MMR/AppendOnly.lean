import MMR.Properties

namespace MMR
namespace Acc

universe u

/-!
# Append-only semantics under aligned input

This file formalizes what *append-only* means for the minimal accumulator
and proves that the implementation enjoys it whenever the pushed input is
aligned (`ValidChunk` / `aligned`).

## Main discovery: `aligned` is exactly the right condition

The results below pin down the alignment condition
`m.leafCount % 2 ^ height = 0` as the *exact* boundary between mere safety
and append-only semantics, not a merely convenient sufficient side
condition:

* **Safety is unconditional.**  The peak-count invariant `Valid` and the
  carry count are correct for *every* height (`appendPeak_peaks_length`,
  `popcount_add_pow`), so unaligned appends never corrupt the accumulator.
* **Sufficiency.**  `specPeaks_aligned_step`: when `n = 2 ^ h * q` is
  aligned, the implementation's carry-merge *is* the canonical MMR
  extension, giving stable leaf indices (`appendPeak_spec`,
  `append_spec`, `appendPeaks_spec`).
* **Necessity.**  `unaligned_appendPeak_not_spec`: a machine-checked
  counterexample at the unaligned point `n = 1, h = 1` — the very same
  operation, fed the genuine subtree root, provably produces peaks that are
  not the canonical peaks of the extended history, so leaf indices shift.
* **Geometric reading.**  `alignedAt_iff_le_trailingZeros`: for a nonempty
  MMR, alignment is equivalent to `height ≤ trailingZeros n` — the appended
  subtree must be no taller than the newest (smallest) existing peak, i.e.
  its leaf range `[n, n + 2 ^ h)` starts at a clean subtree boundary.
  Unaligned appends would straddle existing mountains.

## Semantic model

The canonical MMR of a leaf history `f : Nat → α`, truncated to its first `n`
leaves, is defined independently of any evaluation order of the
implementation:

* `subtreeRoot hash base h f` is the root of the complete binary tree of
  height `h` covering the leaves `f base, …, f (base + 2 ^ h - 1)`;
* `specPeaks hash n f` lists the peaks of the forest of `n` leaves, newest
  (smallest height) first.

`Represents hash m f` states that the accumulator `m` is *exactly* the
canonical MMR of the first `m.leafCount` leaves of the history `f`.

## Append-only guarantees

* `appendPeak_spec`, `append_spec`, `appendPeaks_spec`: under the aligned
  precondition (and, for chunks, genuine subtree roots), appending produces
  the canonical MMR of the *extended* history.  Leaf indices are stable: the
  state after `n` leaves is the canonical MMR of the first `n` leaves, which
  depends only on those leaves (`specPeaks_congr`), so previously appended
  leaves are never rewritten — the log only grows.
* `appendPeak_peaks_prefix`: structurally, an append absorbs exactly the
  `trailingOnes (leafCount / 2 ^ height)` trailing peaks and leaves every
  surviving peak untouched.
* `validChunk?_eq_validChunk`, `alignedRoots_validChunk` and
  `represents_valid` connect the semantic precondition with the API-level
  `ValidChunk` predicate, its computable validator `validChunk?`, and the
  canonical peak-count invariant `Valid`.

No assumptions about the hash function are needed.
-/

section BitArithmetic

/-- Number of trailing 0s in the binary representation of `n`; for `n > 0`
this is the height of the newest (smallest) peak. -/
def trailingZeros : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then trailingZeros ((n + 1) / 2) + 1 else 0
termination_by n => n
decreasing_by
  simp_wf
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

theorem trailingZeros_succ (n : Nat) :
    trailingZeros (n + 1) =
      if (n + 1) % 2 = 0 then trailingZeros ((n + 1) / 2) + 1 else 0 := by
  simp [trailingZeros]

theorem trailingZeros_even (k : Nat) (hk : 0 < k) :
    trailingZeros (2 * k) = trailingZeros k + 1 := by
  cases k with
  | zero => omega
  | succ j =>
      have hmod : (2 * j + 1 + 1) % 2 = 0 := by omega
      have hdiv : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      have heq : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      rw [heq, trailingZeros_succ]
      simp [hmod, hdiv]

theorem trailingZeros_odd (k : Nat) : trailingZeros (2 * k + 1) = 0 := by
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  rw [trailingZeros_succ (2 * k)]
  simp [hmod]

/-- The newest peak of `2 ^ h * odd` leaves has height exactly `h`. -/
theorem trailingZeros_pow_mul_odd (h k : Nat) :
    trailingZeros (2 ^ h * (2 * k + 1)) = h := by
  induction h with
  | zero =>
      rw [Nat.pow_zero, Nat.one_mul]
      exact trailingZeros_odd k
  | succ h ih =>
      have hp : (2 : Nat) ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ']
      rw [hp, Nat.mul_assoc,
        trailingZeros_even (2 ^ h * (2 * k + 1))
          (Nat.mul_pos (Nat.two_pow_pos h) (by omega))]
      rw [ih]

/-- `a < a + 2 ^ h`, i.e. every peak covers at least one leaf. -/
theorem lt_add_pow (a h : Nat) : a < a + 2 ^ h := by
  have hp : 0 < 2 ^ h := Nat.two_pow_pos h
  omega

theorem two_pow_succ_mul (h k : Nat) : 2 ^ h * 2 * k = 2 ^ (h + 1) * k := by
  rw [Nat.pow_succ', Nat.mul_comm (2 ^ h) 2]

theorem two_pow_split_add (h k : Nat) :
    2 ^ h * 2 * k + 2 ^ h = 2 ^ h * (2 * k + 1) := by
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]

theorem two_pow_mul_div (h q : Nat) : 2 ^ h * q / 2 ^ h = q :=
  Nat.mul_div_cancel_left q (Nat.two_pow_pos h)

/-- **Exactness of the alignment condition.**  For a nonempty MMR, `n` is
aligned at height `h` exactly when `h` does not exceed `trailingZeros n`,
the height of the newest (smallest) peak: the appended subtree must be no
taller than every existing peak, i.e. its leaf range `[n, n + 2 ^ h)` must
start at a clean subtree boundary.  Together with `specPeaks_aligned_step`
(sufficiency) and `unaligned_appendPeak_not_spec` (necessity), this shows
`aligned` is exactly the right precondition, not a merely convenient
sufficient one. -/
theorem alignedAt_iff_le_trailingZeros (n h : Nat) (hn : 0 < n) :
    alignedAt n h ↔ h ≤ trailingZeros n := by
  have key : ∀ (n : Nat), 0 < n → ∀ h, alignedAt n h ↔ h ≤ trailingZeros n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn h
      cases n with
      | zero => omega
      | succ m =>
        rcases Nat.mod_two_eq_zero_or_one (m + 1) with hmod | hmod
        · -- even: n = 2 * k with 0 < k < n, and tz n = tz k + 1
          obtain ⟨k, hk⟩ : ∃ k, m + 1 = 2 * k := ⟨(m + 1) / 2, by omega⟩
          have hk0 : 0 < k := by omega
          have htz : trailingZeros (m + 1) = trailingZeros k + 1 := by
            rw [hk]
            exact trailingZeros_even k hk0
          constructor
          · intro hal
            have hal' : (m + 1) % 2 ^ h = 0 := hal
            rw [hk] at hal'
            cases h with
            | zero => omega
            | succ h =>
                have hpow : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ']
                rw [hpow, Nat.mul_mod_mul_left 2 k (2 ^ h)] at hal'
                have hkmod : k % 2 ^ h = 0 := by omega
                have hle : h ≤ trailingZeros k := (ih k (by omega) hk0 h).mp hkmod
                omega
          · intro hle
            show (m + 1) % 2 ^ h = 0
            cases h with
            | zero =>
                rw [Nat.pow_zero]
                exact Nat.mod_one _
            | succ h =>
                have hpow : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ']
                have hle' : h ≤ trailingZeros k := by omega
                have hkmod : k % 2 ^ h = 0 := (ih k (by omega) hk0 h).mpr hle'
                rw [hk, hpow, Nat.mul_mod_mul_left 2 k (2 ^ h), hkmod]
        · -- odd: tz n = 0, so alignment forces h = 0
          obtain ⟨j, hj⟩ : ∃ j, m + 1 = 2 * j + 1 := ⟨(m + 1) / 2, by omega⟩
          have htz : trailingZeros (m + 1) = 0 := by
            rw [hj]
            exact trailingZeros_odd j
          constructor
          · intro hal
            have hal' : (m + 1) % 2 ^ h = 0 := hal
            cases h with
            | zero => omega
            | succ h =>
                have hdvd : 2 ∣ 2 ^ (h + 1) := ⟨2 ^ h, by rw [Nat.pow_succ']⟩
                have hmm := Nat.mod_mod_of_dvd (m + 1) hdvd
                rw [hal'] at hmm
                simp only [Nat.zero_mod] at hmm
                omega
          · intro hle
            have h0 : h = 0 := by omega
            subst h0
            show (m + 1) % 2 ^ 0 = 0
            rw [Nat.pow_zero]
            exact Nat.mod_one _
  exact key n hn h

/-- Every positive number is a power of two times an odd number. -/
theorem exists_pow_two_mul_odd (n : Nat) (hn : 0 < n) :
    ∃ t k, n = 2 ^ t * (2 * k + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ m =>
      rcases Nat.mod_two_eq_zero_or_one (m + 1) with hmod | hmod
      · have hdiv : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
        have hpos : 0 < (m + 1) / 2 := by omega
        obtain ⟨t, k, hk⟩ := ih ((m + 1) / 2) hdiv hpos
        refine ⟨t + 1, k, ?_⟩
        rw [Nat.pow_succ']
        calc m + 1 = 2 * ((m + 1) / 2) := by omega
          _ = 2 * (2 ^ t * (2 * k + 1)) := by rw [hk]
          _ = 2 * 2 ^ t * (2 * k + 1) :=
              (Nat.mul_assoc 2 (2 ^ t) (2 * k + 1)).symm
      · refine ⟨0, (m + 1) / 2, ?_⟩
        rw [Nat.pow_zero, Nat.one_mul]
        have hdm := Nat.div_add_mod (m + 1) 2
        omega

/-- The popcount of the quotient never exceeds the popcount of the number. -/
theorem popcount_div_pow_le (n h : Nat) : popcount (n / 2 ^ h) ≤ popcount n := by
  have hmod : n % 2 ^ h < 2 ^ h := Nat.mod_lt n (Nat.two_pow_pos h)
  have hp := popcount_shift_add (n / 2 ^ h) (n % 2 ^ h) h hmod
  have hdec := Nat.div_add_mod n (2 ^ h)
  rw [hdec] at hp
  omega

end BitArithmetic

section Semantics
variable {α : Type u} (hash : α → α → α)

/-- Root of the complete subtree of height `h` covering the leaves
`f base, f (base + 1), …, f (base + 2 ^ h - 1)` of the leaf history `f`.
The left (older) child is always the first argument of `hash`, matching the
convention of `mergeCarry`. -/
def subtreeRoot (base : Nat) : Nat → (Nat → α) → α
  | 0, f => f base
  | h + 1, f => hash (subtreeRoot base h f) (subtreeRoot (base + 2 ^ h) h f)

/-- `subtreeRoot` only looks at the leaves it covers. -/
theorem subtreeRoot_congr (base hgt : Nat) (f g : Nat → α)
    (hfg : ∀ i, base ≤ i → i < base + 2 ^ hgt → f i = g i) :
    subtreeRoot hash base hgt f = subtreeRoot hash base hgt g := by
  induction hgt generalizing base with
  | zero =>
      simpa only [subtreeRoot] using
        hfg base (Nat.le_refl base) (by simp)
  | succ hgt ih =>
      have hmono : base + 2 ^ hgt ≤ base + 2 ^ (hgt + 1) := by
        rw [Nat.pow_succ']
        omega
      have hleft : ∀ i, base ≤ i → i < base + 2 ^ hgt → f i = g i := fun i h1 h2 =>
        hfg i h1 (Nat.lt_of_lt_of_le h2 hmono)
      have hright : ∀ i, base + 2 ^ hgt ≤ i → i < base + 2 ^ hgt + 2 ^ hgt → f i = g i := by
        intro i h1 h2
        refine hfg i (Nat.le_trans (Nat.le_add_right base (2 ^ hgt)) h1) ?_
        rw [Nat.pow_succ']
        omega
      simp only [subtreeRoot]
      rw [ih base hleft, ih (base + 2 ^ hgt) hright]

/-- Canonical MMR peaks (newest / smallest height first) of the leaf history
`f` truncated to its first `n` leaves: the forest given by the binary
representation of `n`.  The newest peak covers the last `2 ^ trailingZeros n`
leaves; the remaining peaks are those of the preceding leaves. -/
def specPeaks : Nat → (Nat → α) → List α
  | 0, _ => []
  | n + 1, f =>
      subtreeRoot hash (n + 1 - 2 ^ trailingZeros (n + 1)) (trailingZeros (n + 1)) f
        :: specPeaks (n + 1 - 2 ^ trailingZeros (n + 1)) f
termination_by n _ => n
decreasing_by
  all_goals
    have hp : 0 < 2 ^ trailingZeros (n + 1) := Nat.two_pow_pos _
    omega

theorem specPeaks_pos (n : Nat) (f : Nat → α) (hn : 0 < n) :
    specPeaks hash n f =
      subtreeRoot hash (n - 2 ^ trailingZeros n) (trailingZeros n) f
        :: specPeaks hash (n - 2 ^ trailingZeros n) f := by
  cases n with
  | zero => omega
  | succ m => rw [specPeaks]

/-- Peeling the newest peak off the canonical peaks of `2 ^ h * (2 * k + 1)`
leaves: the peak is the last `2 ^ h` leaves and `2 ^ h * 2 * k` leaves
remain. -/
theorem specPeaks_pow_mul_odd (h k : Nat) (f : Nat → α) :
    specPeaks hash (2 ^ h * (2 * k + 1)) f =
      subtreeRoot hash (2 ^ h * 2 * k) h f :: specPeaks hash (2 ^ h * 2 * k) f := by
  have hpos : 0 < 2 ^ h * (2 * k + 1) :=
    Nat.mul_pos (Nat.two_pow_pos h) (by omega)
  have hsub : 2 ^ h * (2 * k + 1) - 2 ^ h = 2 ^ h * 2 * k := by
    have hsplit : 2 ^ h * (2 * k + 1) = 2 ^ h * 2 * k + 2 ^ h :=
      (two_pow_split_add h k).symm
    rw [hsplit, Nat.add_sub_cancel]
  rw [specPeaks_pos _ _ _ hpos, trailingZeros_pow_mul_odd, hsub]

/-- The canonical forest has `popcount n` peaks. -/
theorem specPeaks_length (n : Nat) (f : Nat → α) :
    (specPeaks hash n f).length = popcount n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [specPeaks, popcount]
    | succ m =>
      obtain ⟨t, k, hk⟩ := exists_pow_two_mul_odd (m + 1) (Nat.succ_pos m)
      have h1 : popcount (2 ^ t * (2 * k + 1)) = popcount k + 1 := by
        rw [popcount_shift (2 * k + 1) t, popcount_odd k]
      have h2 : popcount (2 ^ t * 2 * k) = popcount k := by
        rw [two_pow_succ_mul t k]
        exact popcount_shift k (t + 1)
      have hlt : 2 ^ t * 2 * k < m + 1 := by
        rw [hk, ← two_pow_split_add t k]
        exact lt_add_pow (2 ^ t * 2 * k) t
      rw [hk, specPeaks_pow_mul_odd hash t k f, List.length_cons,
        ih (2 ^ t * 2 * k) hlt, h2, h1]

/-- The canonical MMR of the first `n` leaves depends only on those leaves:
future appends can never rewrite the hashes of past leaves. -/
theorem specPeaks_congr (f g : Nat → α) :
    ∀ n, (∀ i, i < n → f i = g i) → specPeaks hash n f = specPeaks hash n g := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h
    cases n with
    | zero => simp [specPeaks]
    | succ m =>
      obtain ⟨t, k, hk⟩ := exists_pow_two_mul_odd (m + 1) (Nat.succ_pos m)
      have h' : ∀ i, i < 2 ^ t * (2 * k + 1) → f i = g i := fun i hi =>
        h i (by rw [hk]; exact hi)
      have hmono : 2 ^ t * 2 * k ≤ 2 ^ t * (2 * k + 1) := by
        rw [← two_pow_split_add t k]
        exact Nat.le_add_right (2 ^ t * 2 * k) (2 ^ t)
      have hhead : subtreeRoot hash (2 ^ t * 2 * k) t f
          = subtreeRoot hash (2 ^ t * 2 * k) t g :=
        subtreeRoot_congr hash (2 ^ t * 2 * k) t f g
          (fun i _ h2 => h' i (by rw [two_pow_split_add t k] at h2; exact h2))
      have htail : specPeaks hash (2 ^ t * 2 * k) f = specPeaks hash (2 ^ t * 2 * k) g :=
        ih (2 ^ t * 2 * k)
          (by rw [hk, ← two_pow_split_add t k]; exact lt_add_pow (2 ^ t * 2 * k) t)
          (fun i hi => h' i (Nat.lt_of_lt_of_le hi hmono))
      rw [hk, specPeaks_pow_mul_odd hash t k f, specPeaks_pow_mul_odd hash t k g,
        hhead, htail]

/-- **The aligned append step.**  When `n = 2 ^ h * q` is aligned at height
`h`, the canonical peaks of the extended history `n + 2 ^ h` are obtained
from the canonical peaks of `n` by exactly the carry-merge performed by
`appendPeak`: merge `trailingOnes q` trailing peaks with the root of the
appended subtree.  This is the precise sense in which aligned appends are the
canonical MMR extension; without alignment the equation fails. -/
theorem specPeaks_aligned_step (q : Nat) :
    ∀ (h : Nat) (f : Nat → α),
      specPeaks hash (2 ^ h * (q + 1)) f
        = mergeCarry hash (trailingOnes q) (subtreeRoot hash (2 ^ h * q) h f)
            (specPeaks hash (2 ^ h * q) f) := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro h f
    rcases Nat.mod_two_eq_zero_or_one q with hmod | hmod
    · -- q is even (including q = 0): the appended subtree becomes the new
      -- smallest peak and nothing merges.
      have hj : q = 2 * (q / 2) := by omega
      rw [hj, specPeaks_pow_mul_odd hash h (q / 2) f, trailingOnes_even (q / 2)]
      simp only [mergeCarry]
      rw [Nat.mul_assoc]
    · -- q is odd: the appended subtree merges with the newest peak, and the
      -- remaining carries follow the induction hypothesis at height h + 1.
      obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
      have hL : 2 ^ h * (2 * k + 1 + 1) = 2 ^ (h + 1) * (k + 1) := by
        have h1 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [h1, ← Nat.mul_assoc, two_pow_succ_mul h (k + 1)]
      rw [hk, hL, ih k (by omega) (h + 1) f, trailingOnes_odd k,
        specPeaks_pow_mul_odd hash h k f]
      simp only [mergeCarry]
      simp only [subtreeRoot]
      rw [← two_pow_succ_mul h k, two_pow_split_add h k]

/-- Accumulator-level version of `alignedAt_iff_le_trailingZeros`: for a
nonempty MMR, `height` is aligned exactly when it does not exceed
`trailingZeros leafCount`, the height of the newest (smallest) peak. -/
theorem aligned_iff_le_trailingZeros (m : Acc α) (height : Nat)
    (hm : 0 < m.leafCount) :
    aligned m height ↔ height ≤ trailingZeros m.leafCount :=
  alignedAt_iff_le_trailingZeros m.leafCount height hm

/-! ### Necessity: the alignment condition cannot be dropped

`specPeaks_aligned_step` shows that `aligned` suffices for the append-only
canonical semantics, and `alignedAt_iff_le_trailingZeros` characterizes it
topologically.  A converse stated as a general equation between peak lists
cannot hold (degenerate hashes may collide), but the boundary is real: the
following machine-checked counterexample shows that at an unaligned point
the very same operation, fed the *genuine* subtree root, provably produces
a state that is not the canonical MMR of the extended history. -/

/-- A concrete injective hash for the counterexample below: `2 ^ a * 3 ^ b`
is injective by unique factorization. -/
private def tagHash (a b : Nat) : Nat := 2 ^ a * 3 ^ b

/-- A concrete leaf history for the counterexample below. -/
private def hist (i : Nat) : Nat := i

/-- **Alignment is necessary for append-only semantics.**  At the unaligned
point `leafCount = 1`, `height = 1` (indeed `1 % 2 ≠ 0`), appending the
*genuine* subtree root of the next two leaves produces peaks that are
provably *not* the canonical MMR peaks of the extended 3-leaf history:
the appended subtree straddles the existing single-leaf peak, so the leaf
indices shift.  Note that the peak-count invariant `Valid` still holds
(`appendPeak_peaks_length`), so safety and append-only semantics separate
exactly at the aligned condition. -/
theorem unaligned_appendPeak_not_spec :
    (appendPeak tagHash 1 (subtreeRoot tagHash 1 1 hist)
        { peaks := specPeaks tagHash 1 hist, leafCount := 1 }).peaks
      ≠ specPeaks tagHash 3 hist := by
  have htz2 : trailingZeros (1 + 1) = 1 := by
    have he := trailingZeros_even 1 (by omega)
    have h1 : trailingZeros 1 = 0 := trailingZeros_odd 0
    have h2 : (2 : Nat) * 1 = 1 + 1 := by omega
    rw [h2] at he
    omega
  have hsp1 : specPeaks tagHash 1 hist = [hist 0] := by
    show specPeaks tagHash (0 + 1) hist = _
    rw [specPeaks, show trailingZeros (0 + 1) = 0 from trailingZeros_odd 0,
      Nat.pow_zero]
    simp [subtreeRoot, specPeaks]
  have hsp2 : specPeaks tagHash 2 hist = [tagHash (hist 0) (hist 1)] := by
    show specPeaks tagHash (1 + 1) hist = _
    rw [specPeaks, htz2, Nat.pow_one]
    have hsub : (1 : Nat) + 1 - 2 = 0 := by omega
    rw [hsub]
    simp [subtreeRoot, specPeaks, Nat.pow_zero]
  have hsp3 : specPeaks tagHash 3 hist = [hist 2, tagHash (hist 0) (hist 1)] := by
    show specPeaks tagHash (2 + 1) hist = _
    rw [specPeaks, show trailingZeros (2 + 1) = 0 from trailingZeros_odd 1,
      Nat.pow_zero]
    have hsub : (2 : Nat) + 1 - 1 = 2 := by omega
    rw [hsub, hsp2]
    simp [subtreeRoot]
  have hdiv : (1 : Nat) / 2 ^ 1 = 0 := by decide
  show mergeCarry tagHash (trailingOnes (1 / 2 ^ 1))
      (subtreeRoot tagHash 1 1 hist) (specPeaks tagHash 1 hist) ≠ _
  rw [hdiv, hsp1, hsp3]
  simp only [trailingOnes, mergeCarry, subtreeRoot, Nat.pow_zero]
  decide

end Semantics

/-! ## Representation of a leaf history -/

section Represents
variable {α : Type u} (hash : α → α → α)

/-- The accumulator `m` *represents* the leaf history `f` when its peaks are
exactly the canonical MMR peaks of the first `m.leafCount` leaves of `f`.
Under this correspondence `f i` is the hash of the leaf with index `i` and
`m.leafCount` is the length of the history — so preserving `Represents`
while `leafCount` grows is precisely the append-only guarantee: old leaves
keep their indices and hashes, and only new leaves are added. -/
def Represents (m : Acc α) (f : Nat → α) : Prop :=
  m.peaks = specPeaks hash m.leafCount f

/-- The empty accumulator represents every (empty) history. -/
theorem empty_represents (f : Nat → α) : Represents hash (empty α) f := by
  simp [Represents, empty, specPeaks]

/-- A representing accumulator satisfies the canonical peak-count invariant. -/
theorem represents_valid {m : Acc α} {f : Nat → α} (hrep : Represents hash m f) :
    m.Valid := by
  have h := specPeaks_length hash m.leafCount f
  have hrep' : m.peaks = specPeaks hash m.leafCount f := hrep
  show m.peaks.length = popcount m.leafCount
  rw [hrep', h]

/-- **Aligned subtree append is canonical.**  If `m` represents the history
`f` and `height` is aligned with `m`, then appending the genuine subtree root
of the next `2 ^ height` leaves yields an accumulator that represents `f`
with the history extended by `2 ^ height` leaves. -/
theorem appendPeak_spec (height : Nat) {m : Acc α} {f : Nat → α}
    (hrep : Represents hash m f) (halign : aligned m height) :
    Represents hash
      (appendPeak hash height (subtreeRoot hash m.leafCount height f) m) f := by
  have h0 : m.leafCount % 2 ^ height = 0 := halign
  have hdm : 2 ^ height * (m.leafCount / 2 ^ height) + m.leafCount % 2 ^ height
      = m.leafCount := Nat.div_add_mod m.leafCount (2 ^ height)
  rw [h0, Nat.add_zero] at hdm
  have hnext : 2 ^ height * (m.leafCount / 2 ^ height) + 2 ^ height
      = 2 ^ height * (m.leafCount / 2 ^ height + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
  unfold Represents at hrep ⊢
  show mergeCarry hash (trailingOnes (m.leafCount / 2 ^ height))
      (subtreeRoot hash m.leafCount height f) m.peaks
    = specPeaks hash (m.leafCount + 2 ^ height) f
  rw [hrep, ← hdm, two_pow_mul_div height (m.leafCount / 2 ^ height), hnext]
  exact (specPeaks_aligned_step hash (m.leafCount / 2 ^ height) height f).symm

/-- **Single-leaf append is canonical** (height `0` is always aligned):
appending `f m.leafCount` extends the represented history by one leaf. -/
theorem append_spec {m : Acc α} {f : Nat → α} (hrep : Represents hash m f) :
    Represents hash (append hash m (f m.leafCount)) f :=
  appendPeak_spec hash 0 hrep (by
    show m.leafCount % 2 ^ 0 = 0
    rw [Nat.pow_zero]
    exact Nat.mod_one _)

/-- A chunk whose entries are aligned *and* carry the genuine subtree roots
of the leaves they cover.  This is the semantic refinement of `ValidChunk`
under which appending a chunk is append-only. -/
def AlignedRoots (m : Acc α) (f : Nat → α) : List (Nat × α) → Prop
  | [] => True
  | (height, peak) :: rest =>
      aligned m height ∧ peak = subtreeRoot hash m.leafCount height f ∧
        AlignedRoots (appendPeak hash height peak m) f rest

/-- The semantic chunk precondition refines the API-level `ValidChunk`. -/
theorem alignedRoots_validChunk {m : Acc α} {f : Nat → α}
    {chunk : List (Nat × α)} (hv : AlignedRoots hash m f chunk) :
    ValidChunk hash m chunk := by
  induction chunk generalizing m with
  | nil => simp only [ValidChunk]
  | cons hp rest ih =>
      obtain ⟨height, peak⟩ := hp
      simp only [AlignedRoots] at hv
      simp only [ValidChunk]
      exact ⟨hv.1, ih (m := appendPeak hash height peak m) hv.2.2⟩

/-- **Chunk append is canonical under aligned input.**  Folding an
`AlignedRoots` chunk into an accumulator that represents the history `f`
yields an accumulator that still represents `f`: the MMR of the extended
history.  Together with `specPeaks_congr` this is the append-only semantics:
the state at any point is the canonical MMR of the leaves appended so far,
and appending only ever extends that history. -/
theorem appendPeaks_spec {m : Acc α} {f : Nat → α} {chunk : List (Nat × α)}
    (hrep : Represents hash m f) (hv : AlignedRoots hash m f chunk) :
    Represents hash (appendPeaks hash m chunk) f := by
  induction chunk generalizing m with
  | nil => exact hrep
  | cons hp rest ih =>
      obtain ⟨height, peak⟩ := hp
      simp only [AlignedRoots] at hv
      obtain ⟨halign, hroot, hrest⟩ := hv
      subst hroot
      show Represents hash (appendPeaks hash (appendPeak hash height
        (subtreeRoot hash m.leafCount height f) m) rest) f
      exact ih (m := appendPeak hash height (subtreeRoot hash m.leafCount height f) m)
        (appendPeak_spec hash height hrep halign) hrest

/-- The computable validator `validChunk?` decides the API-level
precondition `ValidChunk`. -/
theorem validChunk?_eq_validChunk (m : Acc α) :
    ∀ chunk : List (Nat × α),
      validChunk? m.leafCount chunk = true ↔ ValidChunk hash m chunk := by
  intro chunk
  induction chunk generalizing m with
  | nil => simp [validChunk?, ValidChunk]
  | cons hp rest ih =>
      obtain ⟨height, peak⟩ := hp
      by_cases hal : m.leafCount % 2 ^ height = 0
      · have hc : alignedAt? m.leafCount height = true := by
          simpa [alignedAt?, alignedAt] using hal
        simp only [validChunk?, ValidChunk]
        rw [if_pos hc]
        have hstep := ih (appendPeak hash height peak m)
        rw [appendPeak_leafCount hash height peak m] at hstep
        exact ⟨fun h => ⟨hal, hstep.mp h⟩, fun h => hstep.mpr h.2⟩
      · have hc : ¬(alignedAt? m.leafCount height = true) := by
          intro hcon
          exact hal (by simpa [alignedAt?, alignedAt] using hcon)
        simp only [validChunk?, ValidChunk]
        rw [if_neg hc]
        refine Iff.intro ?_ ?_
        · intro hcon
          exact absurd hcon (by simp)
        · intro ⟨halign, _⟩
          exact absurd (show m.leafCount % 2 ^ height = 0 from halign) hal

end Represents

/-! ## Structural preservation of surviving peaks -/

section Preservation
variable {α : Type u} (hash : α → α → α)

/-- `mergeCarry` consumes exactly `c` trailing peaks, computes one new node,
and leaves every other peak untouched (`peaks.drop c` is a suffix of
`peaks`). -/
theorem mergeCarry_eq_cons_drop (c : Nat) (x : α) (peaks : List α)
    (hc : c ≤ peaks.length) :
    ∃ r : α, mergeCarry hash c x peaks = r :: peaks.drop c := by
  induction c generalizing x peaks with
  | zero =>
      refine ⟨x, ?_⟩
      simp [mergeCarry]
  | succ c ih =>
      cases peaks with
      | nil => exact absurd hc (by simp)
      | cons p ps =>
          have hc' : c ≤ ps.length := by
            simp only [List.length_cons] at hc
            omega
          obtain ⟨r, hr⟩ := ih (hash p x) ps hc'
          refine ⟨r, ?_⟩
          simp only [mergeCarry]
          rw [hr]
          simp [List.drop]

/-- Appending absorbs exactly the trailing peaks that the new subtree
subsumes and inserts one new node in front; every surviving peak of the old
state is kept verbatim. -/
theorem appendPeak_peaks_prefix (m : Acc α) (height : Nat) (peak : α)
    (hvalid : m.Valid) :
    ∃ r : α, (appendPeak hash height peak m).peaks
      = r :: m.peaks.drop (trailingOnes (m.leafCount / 2 ^ height)) := by
  have hlen : m.peaks.length = popcount m.leafCount := hvalid
  have hc : trailingOnes (m.leafCount / 2 ^ height) ≤ m.peaks.length := by
    rw [hlen]
    exact Nat.le_trans (trailingOnes_le_popcount _)
      (popcount_div_pow_le m.leafCount height)
  obtain ⟨r, hr⟩ :=
    mergeCarry_eq_cons_drop hash (trailingOnes (m.leafCount / 2 ^ height)) peak
      m.peaks hc
  refine ⟨r, ?_⟩
  show (mergeCarry hash (trailingOnes (m.leafCount / 2 ^ height)) peak m.peaks) = _
  exact hr

end Preservation

end Acc
end MMR
