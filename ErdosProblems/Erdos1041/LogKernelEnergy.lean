import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Logarithmic energy of points in the unit disk

The logarithmic kernel `-log ‖1 - conj z * w‖` has a convergent
power-series expansion. Summing over a finite configuration turns each
coefficient into the squared norm of a power sum. This gives the ENERGY
identity in the central free-point argument for actual disk points.
-/

open scoped BigOperators ComplexConjugate

namespace ErdosProblems.Erdos1041

/-- Each logarithmic interaction factor is positive inside the unit disk. -/
theorem log_kernel_factor_pos {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    0 < ‖1 - conj z * w‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hnorm : ‖conj z * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg z, norm_nonneg w]
  rw [← sub_eq_zero.mp hzero, norm_one] at hnorm
  exact lt_irrefl _ hnorm

/-- Real part of the convergent complex logarithm expansion. The term at
`n = 0` vanishes because division by zero is zero. -/
theorem hasSum_neg_log_norm_one_sub {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (z ^ n).re / n) (-Real.log ‖1 - z‖) := by
  simpa only [Complex.div_natCast_re, Complex.neg_re, Complex.log_re] using
    Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)

/-- The logarithmic kernel at two strictly interior points. -/
theorem hasSum_log_kernel {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => (conj (z ^ n) * w ^ n).re / n)
      (-Real.log ‖1 - conj z * w‖) := by
  have hzw : ‖conj z * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg z, norm_nonneg w]
  simpa only [mul_pow, map_pow] using hasSum_neg_log_norm_one_sub hzw

/-- Expansion of one interaction row against the configuration's power sums. -/
theorem hasSum_log_kernel_row {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (hc : ∀ i ∈ s, ‖c i‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (conj (z ^ n) * (∑ j ∈ s, c j ^ n)).re / n)
      (-∑ j ∈ s, Real.log ‖1 - conj z * c j‖) := by
  have h := hasSum_sum (s := s) (fun j hj => hasSum_log_kernel hz (hc j hj))
  simpa only [Finset.mul_sum, Complex.re_sum, Finset.sum_div,
    Finset.sum_neg_distrib] using h

/-- Summing the pair kernel produces the squared norm of the power sum. -/
theorem sum_re_conj_pow_mul_pow {ι : Type*} (s : Finset ι) (c : ι → ℂ) (n : ℕ) :
    (∑ i ∈ s, ∑ j ∈ s, (conj (c i ^ n) * c j ^ n).re) =
      ‖∑ i ∈ s, c i ^ n‖ ^ 2 := by
  have h : (∑ i ∈ s, ∑ j ∈ s, conj (c i ^ n) * c j ^ n) =
      conj (∑ i ∈ s, c i ^ n) * (∑ i ∈ s, c i ^ n) := by
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have hr := congrArg Complex.re h
  simpa only [Complex.re_sum, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hr

/-- Exact nonnegative energy expansion for an arbitrary finite configuration
in the open unit disk. No summability hypothesis is required. -/
theorem hasSum_log_kernel_energy {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (hc : ∀ i ∈ s, ‖c i‖ < 1) :
    HasSum (fun n : ℕ => ‖∑ i ∈ s, c i ^ n‖ ^ 2 / n)
      (-∑ i ∈ s, ∑ j ∈ s, Real.log ‖1 - conj (c i) * c j‖) := by
  have h := hasSum_sum (s := s) (fun i hi =>
    hasSum_sum (s := s) (fun j hj => hasSum_log_kernel (hc i hi) (hc j hj)))
  simp only [Finset.sum_neg_distrib] at h
  convert h using 1
  ext n
  simp_rw [← Finset.sum_div, sum_re_conj_pow_mul_pow]

/-- The total logarithmic interaction of points in the open unit disk is
nonpositive. -/
theorem sum_log_kernel_nonpos {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (hc : ∀ i ∈ s, ‖c i‖ < 1) :
    (∑ i ∈ s, ∑ j ∈ s, Real.log ‖1 - conj (c i) * c j‖) ≤ 0 := by
  have h := hasSum_log_kernel_energy s c hc
  have hnonneg : 0 ≤ -∑ i ∈ s, ∑ j ∈ s, Real.log ‖1 - conj (c i) * c j‖ := by
    rw [← h.tsum_eq]
    exact tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
  linarith

end ErdosProblems.Erdos1041
