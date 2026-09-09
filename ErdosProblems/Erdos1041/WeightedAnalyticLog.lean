import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Tactic

/-! Actual finite weighted logarithmic function for the interior free-point
argument. Candidate pending compilation; no weighted inequality is assumed. -/
open scoped BigOperators ComplexConjugate NNReal
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Metric

/-- The analytic function whose modulus is the weighted geometric product. -/
def weightedAnalyticLog {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (∑ j, (w j : ℂ) * Complex.log (1 - conj (c j) * z))

theorem weightedAnalyticLog_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) : weightedAnalyticLog w c 0 = 1 := by
  simp [weightedAnalyticLog]

theorem weightedAnalyticLog_ne_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (z : ℂ) : weightedAnalyticLog w c z ≠ 0 :=
  Complex.exp_ne_zero _

/-- The literal logarithmic derivative from the finite analytic construction.
The product norm bound keeps every logarithm in its principal analytic branch. -/
theorem hasDerivAt_weightedAnalyticLog {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (z : ℂ)
    (hc : ∀ j, ‖c j‖ * ‖z‖ < 1) :
    HasDerivAt (weightedAnalyticLog w c)
      (weightedAnalyticLog w c z *
        ∑ j, (w j : ℂ) * (-conj (c j) / (1 - conj (c j) * z))) z := by
  have hterm : ∀ j, HasDerivAt
      (fun t : ℂ => (w j : ℂ) * Complex.log (1 - conj (c j) * t))
      ((w j : ℂ) * (-conj (c j) / (1 - conj (c j) * z))) z := by
    intro j
    have hslit : 1 - conj (c j) * z ∈ Complex.slitPlane := by
      have hh : ‖-(conj (c j) * z)‖ < 1 := by
        simpa only [norm_neg, norm_mul, Complex.norm_conj] using hc j
      simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hh
    have hlin : HasDerivAt (fun t : ℂ => 1 - conj (c j) * t) (-conj (c j)) z := by
      simpa only [mul_one, zero_sub] using
        ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (conj (c j))))
    exact (hlin.clog hslit).const_mul (w j : ℂ)
  simpa only [weightedAnalyticLog] using
    (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => hterm j)).cexp

/-- A concrete radius bound on the points supplies analyticity on a whole
closed disc. Positive weights and their normalization are not needed here. -/
theorem diffContOnCl_weightedAnalyticLog {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (R : ℝ)
    (hc : ∀ j, ‖c j‖ * R < 1) :
    DiffContOnCl ℂ (weightedAnalyticLog w c) (ball 0 R) := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  have hzR : ‖z‖ ≤ R := by
    have hz' := closure_ball_subset_closedBall hz
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hz'
  exact (hasDerivAt_weightedAnalyticLog w c z (fun j =>
    (mul_le_mul_of_nonneg_left hzR (norm_nonneg (c j))).trans_lt (hc j))).differentiableAt.differentiableWithinAt

end ErdosProblems.Erdos1041
end
