import ErdosProblems.Erdos1041.WeightedAnalyticLog
import ErdosProblems.Erdos1041.TaylorEnergyBound

/-! Actual normalized weighted logarithmic energy, pending compilation.
The rational expression is constructed from the points, not assumed to satisfy
an energy inequality. Its Poisson-kernel identification is a separate step. -/
open scoped BigOperators ComplexConjugate NNReal ENNReal
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Real Metric

/-- Pointwise conversion of the actual logarithmic derivative to the real
energy integrand. No normalization or positivity of weights is required. -/
theorem weightedAnalyticLog_energy_identity {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (z : ℂ)
    (hc : ∀ j, ‖c j‖ * ‖z‖ < 1) :
    ‖weightedAnalyticLog w c z‖ ^ 2 *
      (1 - 2 * (z * ∑ j, (w j : ℂ) *
        (-conj (c j) / (1 - conj (c j) * z))).re) =
    ‖weightedAnalyticLog w c z‖ ^ 2 -
      2 * (z * deriv (weightedAnalyticLog w c) z *
        conj (weightedAnalyticLog w c z)).re := by
  rw [(hasDerivAt_weightedAnalyticLog w c z hc).deriv]
  have hmul (g s : ℂ) : z * (g * s) * conj g = (z * s) * (g * conj g) := by ring
  rw [hmul, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.normSq_eq_norm_sq]
  ring

/-- The actual weighted logarithmic kernel has normalized average at most one.
The explicit radius condition supplies the analytic extension required by the
Taylor identity. This is not yet the finite weighted point-value inequality. -/
theorem circle_weightedAnalyticLog_energy_le_one {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (R : ℝ≥0) (hR : 1 < R)
    (hc : ∀ j, ‖c j‖ * (R : ℝ) < 1) :
    circleAverage (fun z => ‖weightedAnalyticLog w c z‖ ^ 2 *
      (1 - 2 * (z * ∑ j, (w j : ℂ) *
        (-conj (c j) / (1 - conj (c j) * z))).re)) 0 1 ≤ 1 := by
  have hg := diffContOnCl_weightedAnalyticLog w c R hc
  have he := circle_taylor_energy_le_value_zero hg hR
  have heq : circleAverage (fun z => ‖weightedAnalyticLog w c z‖ ^ 2 *
      (1 - 2 * (z * ∑ j, (w j : ℂ) *
        (-conj (c j) / (1 - conj (c j) * z))).re)) 0 1 =
      circleAverage (fun z => ‖weightedAnalyticLog w c z‖ ^ 2 -
        2 * (z * deriv (weightedAnalyticLog w c) z *
          conj (weightedAnalyticLog w c z)).re) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    apply weightedAnalyticLog_energy_identity
    intro j
    have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
    rw [hz1]
    exact (mul_le_mul_of_nonneg_left (le_of_lt (show (1 : ℝ) < R by exact_mod_cast hR))
      (norm_nonneg (c j))).trans_lt (hc j)
  rw [heq]
  simpa only [weightedAnalyticLog_zero, norm_one, one_pow] using he

end ErdosProblems.Erdos1041
end
