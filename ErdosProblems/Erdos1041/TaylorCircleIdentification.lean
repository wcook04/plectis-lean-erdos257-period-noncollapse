import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-! Scalar identification of an actual analytic function and its radial
logarithmic-derivative numerator with their Taylor series. These identities
supply the functions occurring in absolute circle-series transport.
Candidate pending focused compilation. -/
open scoped NNReal ENNReal

noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Metric

/-- Scalar Taylor evaluation, with coefficients evaluated at the unit vector. -/
theorem hasSum_scalar_taylor {g : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞}
    (hg : HasFPowerSeriesOnBall g p 0 r) {z : ℂ} (hz : z ∈ eball 0 r) :
    HasSum (fun n : ℕ => p.coeff n * z ^ n) (g z) := by
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    smul_eq_mul, zero_add, mul_comm] using hg.hasSum hz

/-- Applying the derivative series at the radial vector gives the original
Taylor coefficients weighted by their degrees; the degree-zero term is zero. -/
theorem hasSum_degree_scalar_taylor {g : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞}
    (hg : HasFPowerSeriesOnBall g p 0 r) {z : ℂ} (hz : z ∈ eball 0 r) :
    HasSum (fun n : ℕ => (n : ℂ) * p.coeff n * z ^ n)
      (z * deriv g z) := by
  have h := (ContinuousLinearMap.apply ℂ ℂ z).hasSum (hg.fderiv.hasSum hz)
  simp only [ContinuousLinearMap.apply_apply,
    FormalMultilinearSeries.derivSeries_apply_diag, zero_add] at h
  have hs : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) *
      p.coeff (n + 1) * z ^ (n + 1)) (z * deriv g z) := by
    simpa only [ContinuousLinearMap.apply_apply,
      FormalMultilinearSeries.derivSeries_apply_diag,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      nsmul_eq_mul, smul_eq_mul, zero_add,
      fderiv_eq_smul_deriv, mul_assoc, mul_left_comm, mul_comm] using h
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero] using hs

/-- Cauchy's coefficients identify the actual function at every unit-circle
point when the analytic disc has radius strictly larger than one. -/
theorem hasSum_cauchy_on_unit_circle {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R)
    {z : ℂ} (hz : z ∈ sphere 0 1) :
    HasSum (fun n : ℕ => cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ)) * z ^ n)
      (g z) := by
  have hseries := hg.hasFPowerSeriesOnBall (lt_trans (by norm_num) hR)
  apply hasSum_scalar_taylor hseries
  rw [Metric.eball_coe]
  have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
  simpa [mem_ball, dist_eq_norm, hz1] using (show (1 : ℝ) < R by exact_mod_cast hR)

/-- Cauchy's degree-weighted coefficients identify `z * g'(z)` on the same
unit circle. No derivative-series equality is assumed. -/
theorem hasSum_degree_cauchy_on_unit_circle {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R)
    {z : ℂ} (hz : z ∈ sphere 0 1) :
    HasSum (fun n : ℕ => (n : ℂ) * cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ)) * z ^ n)
      (z * deriv g z) := by
  have hseries := hg.hasFPowerSeriesOnBall (lt_trans (by norm_num) hR)
  apply hasSum_degree_scalar_taylor hseries
  rw [Metric.eball_coe]
  have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
  simpa [mem_ball, dist_eq_norm, hz1] using (show (1 : ℝ) < R by exact_mod_cast hR)

end ErdosProblems.Erdos1041
end
