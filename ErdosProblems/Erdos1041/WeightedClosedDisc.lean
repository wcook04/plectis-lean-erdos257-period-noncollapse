import ErdosProblems.Erdos1041.WeightedInteriorRadius
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

/-! Radial passage to the closed disc. Candidate pending compilation.
Zero weights use Real.rpow_zero, hence their factor is one even at a zero base.
No equality characterization is asserted. -/
open scoped BigOperators ComplexConjugate Topology
noncomputable section
namespace ErdosProblems.Erdos1041
open Filter

/-- The full closed-unit-disc weighted geometric-product inequality.
Nonnegative weights, including zero, are allowed. -/
theorem weighted_closed_disc_product_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, w j * (∏ k, ‖1 - conj (c k) * c j‖ ^ w k) ^ 2) ≤ 1 := by
  classical
  let F : ℝ → ℝ := fun r => ∑ j, w j *
    (∏ k, ‖1 - conj ((r : ℂ) * c k) * ((r : ℂ) * c j)‖ ^ w k) ^ 2
  have hF : Continuous F := by
    apply continuous_finset_sum
    intro j _
    apply continuous_const.mul
    apply Continuous.pow
    apply continuous_finset_prod
    intro k _
    apply (Real.continuous_rpow_const (hw0 k)).comp
    fun_prop
  let r : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ n
  have hr0 : ∀ n, 0 ≤ r n := by
    intro n
    dsimp [r]
    have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := n)
    linarith
  have hr1 : ∀ n, r n < 1 := by
    intro n
    dsimp [r]
    have h := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n
    linarith
  have hr : Tendsto r atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ n) atTop
        (𝓝 ((1 : ℝ) - 0)) := tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
    simpa only [sub_zero] using h
  have hbound : ∀ n, F (r n) ≤ 1 := by
    intro n
    apply weighted_open_disc_product_bound w (fun j => (r n : ℂ) * c j) hw0 hw
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n)]
    exact (mul_le_mul_of_nonneg_left (hc j) (hr0 n)).trans_lt
      (by simpa only [mul_one] using hr1 n)
  have hlim := le_of_tendsto (hF.continuousAt.tendsto.comp hr)
    (Filter.Eventually.of_forall hbound)
  simpa only [F, Complex.ofReal_one, one_mul] using hlim

end ErdosProblems.Erdos1041
end
