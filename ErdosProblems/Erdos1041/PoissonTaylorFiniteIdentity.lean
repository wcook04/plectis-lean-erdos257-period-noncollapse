import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Finite-coefficient Poisson/Taylor identity

Coefficient form of identity (1) in the round-four free-point return:

    ∑ |a_j|² - 2 ∑ j |a_j|² = |a₀|² - ∑_{j≥1} (2j-1)|a_j|²

This is the finite Taylor identity behind the Poisson average, not the
analytic Poisson integral on the circle, not the sharp `4s` hierarchy,
and not a path theorem.  The inequality `m²/(2m-1) ≤ m` is the local r3
radial-mean remainder.  Erdős #1041 remains open.
-/

namespace ErdosProblems.Erdos1041

open Complex Finset

/-- Local r3 radial-window remainder: `m²/(2m-1) ≤ m` for `m ≥ 1`. -/
theorem radialMean_coeff_weight_le {m : ℕ} (hm : 0 < m) :
    (m : ℝ) ^ 2 / (2 * m - 1) ≤ m := by
  have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
  have hden : (0 : ℝ) < 2 * m - 1 := by nlinarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- Coefficient form of identity (1): the diagonal Taylor combination
equals the Poisson/Fourier combination. -/
theorem poisson_taylor_coeff_identity (a : ℕ → ℂ) (deg : ℕ) :
    ∑ j ∈ range (deg + 1), Complex.normSq (a j) -
        2 * ∑ j ∈ range (deg + 1), (j : ℝ) * Complex.normSq (a j) =
      Complex.normSq (a 0) -
        ∑ j ∈ Icc 1 deg, (2 * (j : ℝ) - 1) * Complex.normSq (a j) := by
  have h0 : 0 ∈ range (deg + 1) := by simp
  have herase : (range (deg + 1)).erase 0 = Icc 1 deg := by
    ext j
    simp only [mem_erase, mem_range, mem_Icc]
    constructor
    · intro h
      exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h.1), Nat.lt_succ_iff.mp h.2⟩
    · intro h
      exact ⟨ne_of_gt (Nat.succ_le_iff.mp h.1), Nat.lt_succ_iff.mpr h.2⟩
  have hsplit :
      ∑ j ∈ range (deg + 1), Complex.normSq (a j) =
        Complex.normSq (a 0) + ∑ j ∈ Icc 1 deg, Complex.normSq (a j) := by
    rw [← Finset.sum_erase_add _ _ h0, herase, add_comm]
  have hsplitj :
      ∑ j ∈ range (deg + 1), (j : ℝ) * Complex.normSq (a j) =
        ∑ j ∈ Icc 1 deg, (j : ℝ) * Complex.normSq (a j) := by
    rw [← Finset.sum_erase_add _ _ h0, herase]
    simp
  have hsplitw :
      ∑ j ∈ Icc 1 deg, (2 * (j : ℝ) - 1) * Complex.normSq (a j) =
        2 * ∑ j ∈ Icc 1 deg, (j : ℝ) * Complex.normSq (a j) -
          ∑ j ∈ Icc 1 deg, Complex.normSq (a j) := by
    have hterm (j : ℕ) :
        (2 * (j : ℝ) - 1) * Complex.normSq (a j) =
          2 * ((j : ℝ) * Complex.normSq (a j)) - Complex.normSq (a j) := by
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib,
      Finset.mul_sum]
  rw [hsplit, hsplitj, hsplitw]
  ring

end ErdosProblems.Erdos1041
