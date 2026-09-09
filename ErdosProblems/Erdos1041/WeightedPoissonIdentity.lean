import ErdosProblems.Erdos1041.PoissonKernelBridge
import ErdosProblems.Erdos1041.WeightedAnalyticEnergy

/-! Unit-circle Poisson mixture identification. Candidate pending compilation. -/
open scoped BigOperators ComplexConjugate NNReal ENNReal
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Real Metric

/-- The center is `c`, and the logarithmic factor uses `conj c * z`. -/
theorem poissonKernel_unit_fraction {c z : ℂ} (hz : ‖z‖ = 1) :
    poissonKernel 0 c z =
      (1 - ‖conj c * z‖ ^ 2) / ‖1 - conj c * z‖ ^ 2 := by
  have hzz : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have he : z * conj (1 - conj c * z) = z - c := by
    simp only [map_sub, map_one, map_mul, conj_conj]
    calc
      z * (1 - c * conj z) = z - c * (z * conj z) := by ring
      _ = z - c := by rw [hzz, mul_one]
  have hn := congrArg norm he
  simp only [norm_mul, Complex.norm_conj, hz, one_mul] at hn
  simp only [poissonKernel, sub_zero, hz, one_pow, norm_mul,
    Complex.norm_conj, mul_one, ← hn]

/-- The finite normalized Poisson mixture is exactly the rational expression
in the actual logarithmic energy. Nonnegative weights are unnecessary here. -/
theorem weighted_poisson_log_identity {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw : ∑ j, w j = 1)
    (hc : ∀ j, ‖c j‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j, w j * poissonKernel 0 (c j) z) =
      1 - 2 * (z * ∑ j, (w j : ℂ) *
        (-conj (c j) / (1 - conj (c j) * z))).re := by
  classical
  simp_rw [poissonKernel_unit_fraction hz]
  rw [weighted_poisson_fraction_identity w (fun j => conj (c j) * z) hw]
  · have ht : z * (∑ j, (w j : ℂ) *
        (-conj (c j) / (1 - conj (c j) * z))) =
        -(∑ j, (w j : ℂ) * ((conj (c j) * z) / (1 - conj (c j) * z))) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [ht]
    simp only [Complex.neg_re, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · intro j he
    have hn := congrArg norm he
    simp only [norm_mul, Complex.norm_conj, hz, mul_one, norm_one] at hn
    linarith [hc j]

/-- Actual normalized Poisson-weighted boundary energy is at most one. -/
theorem circle_weighted_poisson_energy_le_one {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw : ∑ j, w j = 1)
    (R : ℝ≥0) (hR : 1 < R) (hc : ∀ j, ‖c j‖ * (R : ℝ) < 1) :
    circleAverage (fun z => ‖weightedAnalyticLog w c z‖ ^ 2 *
      (∑ j, w j * poissonKernel 0 (c j) z)) 0 1 ≤ 1 := by
  have hc1 : ∀ j, ‖c j‖ < 1 := by
    intro j
    have h := (mul_le_mul_of_nonneg_left
      (le_of_lt (show (1 : ℝ) < R by exact_mod_cast hR)) (norm_nonneg (c j))).trans_lt (hc j)
    simpa only [mul_one] using h
  have heq : circleAverage (fun z => ‖weightedAnalyticLog w c z‖ ^ 2 *
      (∑ j, w j * poissonKernel 0 (c j) z)) 0 1 =
      circleAverage (fun z => ‖weightedAnalyticLog w c z‖ ^ 2 *
      (1 - 2 * (z * ∑ j, (w j : ℂ) *
        (-conj (c j) / (1 - conj (c j) * z))).re)) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    change ‖weightedAnalyticLog w c z‖ ^ 2 *
        (∑ j, w j * poissonKernel 0 (c j) z) =
      ‖weightedAnalyticLog w c z‖ ^ 2 *
        (1 - 2 * (z * ∑ j, (w j : ℂ) *
          (-conj (c j) / (1 - conj (c j) * z))).re)
    rw [weighted_poisson_log_identity w c hw hc1
      (by simpa [mem_sphere, dist_eq_norm] using hz)]
  rw [heq]
  exact circle_weightedAnalyticLog_energy_le_one w c R hR hc

end ErdosProblems.Erdos1041
end
