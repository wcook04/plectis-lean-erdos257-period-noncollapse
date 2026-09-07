import Mathlib

/-!
# Sparse rationalisation: variable-alphabet core

Elementary core for the r5 ordinary sparse construction.  This file is **not**
a formalisation of the full sparse scheduling theorem (Theorem 2.1), the
block-law transfer, or the entropy bound.  Ordinary proofs live in
`SparseRationalisation.md`.  The namespace is deliberately separate from
registered flagship claims.

It extends the r4 finite pair mechanism (`PairedCongruenceRationalisation`)
to a variable digit range and supplies infinite variable-alphabet filling
under explicit capacity, overlap, and vanishing hypotheses.
-/

noncomputable section
open Filter Topology Finset

namespace ErdosProblems.Erdos251.SparseRationalisationDraft

/-- The unweighted total is independent of the free digit. -/
theorem pair_total (M D d : ℕ) (hd : d ≤ D) :
    M * d + M * (D - d) = M * D := by
  rw [← mul_add, Nat.add_comm d (D - d), Nat.sub_add_cancel hd]

/-- The same pair retains one free digit in the dyadic weighted total. -/
theorem pair_weighted (M D d n : ℕ) (hd : d ≤ D) :
    (M * d : ℚ) / 2 ^ (n + 1) +
      ((M : ℚ) * ((D - d : ℕ) : ℚ)) / 2 ^ (n + 2) =
        (M : ℚ) * (D + d) / 2 ^ (n + 2) := by
  rw [Nat.cast_sub hd]
  have hp : (2 : ℚ) ^ (n + 2) = 2 ^ (n + 1) * 2 := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  rw [hp]
  field_simp
  ring

/-- A deterministic repair to the next cumulative modulus. -/
def repairBuffer (C M : ℤ) : ℤ := (-C) % M

theorem repairBuffer_nonneg (C : ℤ) {M : ℤ} (hM : 0 < M) :
    0 ≤ repairBuffer C M :=
  Int.emod_nonneg _ hM.ne'

theorem repairBuffer_lt (C : ℤ) {M : ℤ} (hM : 0 < M) :
    repairBuffer C M < M :=
  Int.emod_lt_of_pos _ hM

theorem repairBuffer_repairs (C M : ℤ) : M ∣ C + repairBuffer C M := by
  refine ⟨-((-C) / M), ?_⟩
  have h := Int.emod_add_mul_ediv (-C) M
  dsimp [repairBuffer]
  nlinarith only [h]

/-- Repairing a larger modulus does not spoil previously imposed divisors. -/
theorem repairBuffer_preserves {q C M : ℤ} (hC : q ∣ C) (hM : q ∣ M) :
    q ∣ repairBuffer C M := by
  have hs : q ∣ C + repairBuffer C M := hM.trans (repairBuffer_repairs C M)
  have h := dvd_sub hs hC
  simpa using h

/-- The preceding spacing, not the following spacing, gives this telescope. -/
theorem capacity_telescope (M : ℚ) (n s : ℕ) :
    ((2 : ℚ) ^ s - 1) * M / 2 ^ (n + s + 2) =
      M / 2 ^ (n + 2) - M / 2 ^ (n + s + 2) := by
  have hp : (2 : ℚ) ^ (n + s + 2) = 2 ^ (n + 2) * 2 ^ s := by
    rw [show n + s + 2 = (n + 2) + s by omega, pow_add]
  rw [hp]
  field_simp

/-- A clipped greedy digit with a capacity that may vary with the index. -/
def variableDigit (D : ℕ) (w y : ℝ) : ℕ :=
  min D (Int.toNat ⌊y / w⌋)

theorem variableDigit_le (D : ℕ) (w y : ℝ) : variableDigit D w y ≤ D :=
  min_le_left _ _

/-- One-step interval filling with an arbitrary remaining-tail capacity S. -/
theorem variableDigit_spec {D : ℕ} {w S y : ℝ}
    (hw : 0 < w) (hy0 : 0 ≤ y) (hy1 : y ≤ (D : ℝ) * w + S)
    (hoverlap : w ≤ S) :
    0 ≤ y - (variableDigit D w y : ℝ) * w ∧
      y - (variableDigit D w y : ℝ) * w ≤ S := by
  have hx : 0 ≤ y / w := div_nonneg hy0 hw.le
  have hk0 : 0 ≤ ⌊y / w⌋ := Int.floor_nonneg.mpr hx
  have hfl : (⌊y / w⌋ : ℝ) * w ≤ y :=
    (le_div_iff₀ hw).mp (Int.floor_le _)
  have hfu : y < ((⌊y / w⌋ : ℝ) + 1) * w :=
    (div_lt_iff₀ hw).mp (Int.lt_floor_add_one _)
  unfold variableDigit
  by_cases hcase : Int.toNat ⌊y / w⌋ ≤ D
  · have hd : ((min D (Int.toNat ⌊y / w⌋) : ℕ) : ℝ) = (⌊y / w⌋ : ℝ) := by
      rw [min_eq_right hcase]
      have h : ((⌊y / w⌋).toNat : ℤ) = ⌊y / w⌋ := Int.toNat_of_nonneg hk0
      exact_mod_cast h
    constructor
    · rw [hd]
      linarith
    · rw [hd]
      nlinarith
  · have hge : D + 1 ≤ Int.toNat ⌊y / w⌋ := by omega
    have hDi : ((D + 1 : ℕ) : ℤ) ≤ ⌊y / w⌋ := by
      have h := Int.ofNat_le.mpr hge
      simpa [Int.toNat_of_nonneg hk0] using h
    have hDr : ((D + 1 : ℕ) : ℝ) ≤ (⌊y / w⌋ : ℝ) := by
      exact_mod_cast hDi
    have hd : min D (Int.toNat ⌊y / w⌋) = D :=
      min_eq_left (le_of_lt (Nat.not_le.mp hcase))
    rw [hd]
    constructor
    · push_cast at hDr
      nlinarith
    · linarith

/-- The remainder recursion is defined without assuming any invariant. -/
def greedyRemainder (w : ℕ → ℝ) (D : ℕ → ℕ) (y : ℝ) : ℕ → ℝ
  | 0 => y
  | n + 1 => greedyRemainder w D y n -
      (variableDigit (D n) (w n) (greedyRemainder w D y n) : ℝ) * w n

def greedyDigit (w : ℕ → ℝ) (D : ℕ → ℕ) (y : ℝ) (n : ℕ) : ℕ :=
  variableDigit (D n) (w n) (greedyRemainder w D y n)

theorem greedyDigit_le (w : ℕ → ℝ) (D : ℕ → ℕ) (y : ℝ) (n : ℕ) :
    greedyDigit w D y n ≤ D n :=
  variableDigit_le _ _ _

/-- Bounds for every remainder, including the full unprescribed infinite tail. -/
theorem greedyRemainder_bounds {w S : ℕ → ℝ} {D : ℕ → ℕ} {y : ℝ}
    (hw : ∀ n, 0 < w n)
    (hstep : ∀ n, S n = (D n : ℝ) * w n + S (n + 1))
    (hoverlap : ∀ n, w n ≤ S (n + 1))
    (hy0 : 0 ≤ y) (hy1 : y ≤ S 0) :
    ∀ n, 0 ≤ greedyRemainder w D y n ∧ greedyRemainder w D y n ≤ S n := by
  intro n
  induction n with
  | zero => exact ⟨hy0, hy1⟩
  | succ n ih =>
    have hup : greedyRemainder w D y n ≤ (D n : ℝ) * w n + S (n + 1) := by
      rw [← hstep n]
      exact ih.2
    exact variableDigit_spec (hw n) ih.1 hup (hoverlap n)

/-- The finite telescope used for the infinite-series endpoint. -/
theorem greedy_partial_sum (w : ℕ → ℝ) (D : ℕ → ℕ) (y : ℝ) (N : ℕ) :
    ∑ n ∈ range N, (greedyDigit w D y n : ℝ) * w n =
      y - greedyRemainder w D y N := by
  induction N with
  | zero => simp [greedyRemainder]
  | succ N ih =>
    rw [sum_range_succ, ih]
    simp only [greedyRemainder, greedyDigit]
    ring

/-- Infinite variable-alphabet interval filling from a given capacity sequence.
The actual sparse schedule must still establish these hypotheses separately. -/
theorem exists_digits_hasSum_of_capacity {w S : ℕ → ℝ} {D : ℕ → ℕ} {y : ℝ}
    (hw : ∀ n, 0 < w n)
    (hstep : ∀ n, S n = (D n : ℝ) * w n + S (n + 1))
    (hoverlap : ∀ n, w n ≤ S (n + 1))
    (hvanish : Tendsto S atTop (𝓝 0))
    (hy0 : 0 ≤ y) (hy1 : y ≤ S 0) :
    ∃ d : ℕ → ℕ, (∀ n, d n ≤ D n) ∧
      HasSum (fun n => (d n : ℝ) * w n) y := by
  refine ⟨greedyDigit w D y, greedyDigit_le w D y, ?_⟩
  have hb := greedyRemainder_bounds hw hstep hoverlap hy0 hy1
  have hr : Tendsto (greedyRemainder w D y) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvanish
      (fun n => (hb n).1) (fun n => (hb n).2)
  have hn : ∀ n, 0 ≤ (greedyDigit w D y n : ℝ) * w n := by
    intro n
    exact mul_nonneg (Nat.cast_nonneg _) (hw n).le
  rw [hasSum_iff_tendsto_nat_of_nonneg hn]
  have ht : Tendsto (fun N => y - greedyRemainder w D y N) atTop (𝓝 (y - 0)) :=
    tendsto_const_nhds.sub hr
  simpa only [greedy_partial_sum, sub_zero] using ht

#print axioms pair_total
#print axioms pair_weighted
#print axioms repairBuffer_repairs
#print axioms repairBuffer_preserves
#print axioms capacity_telescope
#print axioms variableDigit_spec
#print axioms exists_digits_hasSum_of_capacity

end ErdosProblems.Erdos251.SparseRationalisationDraft
