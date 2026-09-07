import Mathlib

/-!
# Finite certificates for the round-5 review of Erdős 269

Authored proof scripts, NOT compiled in the review environment.
No new axiom, `sorry`, registry change, or parent irrationality claim.

The accompanying ordinary proofs supply the infinite statements. These lemmas
isolate the finite rounding, scaled-window, and union-bound algebra.
-/

namespace ErdosProblems.Erdos269.R5

/-- Canonical columns of a sampled two-valued threshold matrix. -/
def cutVec (c : ℚ) (k i : ℕ) : ℚ := if i < k then 1 else c

/-- Differences of two cut columns have interval support. This is the
finite algebra behind Proposition 2.1 of the ordinary memorandum. -/
theorem cutVec_difference (c : ℚ) (k l i : ℕ) (hkl : k ≤ l) :
    cutVec c l i - cutVec c k i =
      if k ≤ i ∧ i < l then 1 - c else 0 := by
  by_cases hik : i < k
  · have hil : i < l := lt_of_lt_of_le hik hkl
    have hki : ¬ k ≤ i := by omega
    simp [cutVec, hik, hil, hki]
  · have hki : k ≤ i := by omega
    by_cases hil : i < l
    · simp [cutVec, hik, hil, hki]
    · simp [cutVec, hik, hil, hki]

/-- The sole exceptional pair of extreme cut columns is proportional. -/
theorem cutVec_extremes (c : ℚ) (m i : ℕ) (hi : i < m) :
    cutVec c 0 i = c * cutVec c m i := by
  simp [cutVec, hi]

/-- Any upper integer rounding of an affine orbit can be made exact by
increasing its integer digit by an integer between zero and `b - 1`.
The interval assumptions are satisfied by the ordinary ceiling function. -/
theorem upper_rounding_digit_bounds
    (b : ℕ) (hb : 1 ≤ b) (m C D : ℤ) (x y : ℝ)
    (hrec : y = (b : ℝ) * x - (m : ℝ))
    (hx : x ≤ (C : ℝ)) (hCx : (C : ℝ) < x + 1)
    (hy : y ≤ (D : ℝ)) (hDy : (D : ℝ) < y + 1) :
    0 ≤ (b : ℤ) * C - D - m ∧
      (b : ℤ) * C - D - m ≤ (b : ℤ) - 1 := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  have hnonneg : 0 ≤ (b : ℝ) * ((C : ℝ) - x) :=
    mul_nonneg (le_of_lt hbpos) (sub_nonneg.mpr hx)
  have hsmall : (b : ℝ) * ((C : ℝ) - x) < (b : ℝ) := by
    have hc : (C : ℝ) - x < 1 := by linarith
    nlinarith
  have hlow : (-1 : ℝ) <
      (((b : ℤ) * C - D - m : ℤ) : ℝ) := by
    push_cast
    nlinarith
  have hhigh : ((((b : ℤ) * C - D - m : ℤ) : ℝ)) < (b : ℝ) := by
    push_cast
    nlinarith
  have hlowZ : (-1 : ℤ) < (b : ℤ) * C - D - m := by exact_mod_cast hlow
  have hhighZ : (b : ℤ) * C - D - m < (b : ℤ) := by exact_mod_cast hhigh
  omega

/-- The corrected integer recurrence is exact. -/
theorem upper_rounding_step (b : ℕ) (m C D : ℤ) :
    D = (b : ℤ) * C - (m + ((b : ℤ) * C - D - m)) := by ring

/-- A digit perturbation by a multiple of M preserves its congruence class. -/
theorem correction_congruence (m M e : ℤ) : M ∣ (m + M * e) - m := by
  refine ⟨e, ?_⟩
  ring

/-- Multiplying a forcing phase multiplies its shadow error as well.
This exact identity applies to EVERY multiplier, not only multiplier one. -/
theorem scaled_window_shadow
    (q W F H S Z X Y : ℝ) (hW : W ≠ 0)
    (hX : X = H * S - Z) (hY : Y = W * X - F) :
    q * F / W - q * H * S + q * Z = -(q * Y / W) := by
  rw [hY, hX]
  field_simp [hW]
  <;> ring

/-- Common-modulus homogenisation preserves each normalised forcing phase. -/
theorem homogenised_phase (rho F W q : ℝ) (hrho : rho ≠ 0) (hW : W ≠ 0) :
    q * (rho * F) / (rho * W) = q * F / W := by
  field_simp [hrho, hW]
  <;> ring

/-- Distance numerator on the five-element circle. -/
def dist5 (a : ℕ) : ℕ := min (a % 5) (5 - a % 5)

/-- The two rows 1 and 2 attain spread 2/5 for every nonzero multiplier mod 5. -/
theorem two_rows_mod_five (q : ℕ) (hq : 1 ≤ q) (hq' : q ≤ 4) :
    max (dist5 q) (dist5 (2 * q)) = 2 := by
  interval_cases q <;> norm_num [dist5]

/-- With three bad labels out of four for each of four multipliers, the
union-bound sum is two, although the preceding good subset exists. -/
theorem union_bound_converse_witness :
    (4 : ℚ) * ((3 * 2) / (4 * 3)) = 2 := by norm_num

/-- The bad fraction 3/4 is larger than 1/sqrt(5), certified by squaring. -/
theorem bad_fraction_square_witness : (1 : ℚ) / 5 < (3 / 4 : ℚ) ^ 2 := by
  norm_num

end ErdosProblems.Erdos269.R5
