import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The one-sided quadratic exponential bound

The central FP4 argument needs the normalized exponential remainder to be
increasing on the whole real line, including negative row logarithms.
Its integral representation gives that fact without a sign restriction.
This scalar input does not supply the geometric log-energy identities.
-/

namespace ErdosProblems.Erdos1041

open Set MeasureTheory

/-- Integral form of the normalized quadratic exponential remainder. -/
noncomputable def exponentialRemainder (t : ℝ) : ℝ :=
  ∫ s : ℝ in 0..1, (1 - s) * Real.exp (s * t)

private theorem remainder_integrable (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => (1 - s) * Real.exp (s * t)) volume 0 1 :=
  (by fun_prop : Continuous (fun s : ℝ => (1 - s) * Real.exp (s * t))).intervalIntegrable _ _

/-- The integral definition includes the removable value at zero. -/
theorem exponentialRemainder_zero : exponentialRemainder 0 = 1 / 2 := by
  simp only [exponentialRemainder, mul_zero, Real.exp_zero, mul_one]
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_const (c := (1 : ℝ)))
    ((show Continuous (fun s : ℝ => s) from continuous_id).intervalIntegrable 0 1)]
  norm_num

/-- Exact quadratic Taylor identity, with no division by the argument. -/
theorem exp_eq_one_add_add_sq_remainder (t : ℝ) :
    Real.exp t = 1 + t + t ^ 2 * exponentialRemainder t := by
  by_cases ht : t = 0
  · simp [ht]
  let F : ℝ → ℝ := fun s => ((t * (1 - s) + 1) * Real.exp (s * t)) / t ^ 2
  have hF (s : ℝ) : HasDerivAt F ((1 - s) * Real.exp (s * t)) s := by
    have hp : HasDerivAt (fun x : ℝ => t * (1 - x) + 1) (-t) s := by
      convert (((hasDerivAt_const s 1).sub (hasDerivAt_id s)).const_mul t).add_const 1 using 1 <;> ring
    have he : HasDerivAt (fun x : ℝ => Real.exp (x * t)) (Real.exp (s * t) * t) s := by
      simpa using ((hasDerivAt_id s).mul_const t).exp
    convert ((hp.mul he).div_const (t ^ 2)) using 1 <;>
      field_simp [ht] <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hF s) (remainder_integrable t)
  change exponentialRemainder t = F 1 - F 0 at hi
  dsimp [F] at hi
  simp only [sub_self, mul_zero, zero_add, one_mul, zero_mul, Real.exp_zero,
    sub_zero, mul_one] at hi
  field_simp [ht] at hi
  nlinarith

/-- Monotonicity holds on all of `ℝ`, not only for nonnegative arguments. -/
theorem exponentialRemainder_monotone : Monotone exponentialRemainder := by
  intro x y hxy
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (remainder_integrable x) (remainder_integrable y)
  intro s hs
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hs.1)) (sub_nonneg.mpr hs.2)

/-- The sharp quadratic coefficient at an upper bound controls every smaller
argument, including arbitrarily negative arguments. -/
theorem exp_le_one_add_add_sq_remainder {t M : ℝ} (ht : t ≤ M) :
    Real.exp t ≤ 1 + t + t ^ 2 * exponentialRemainder M := by
  rw [exp_eq_one_add_add_sq_remainder t]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (exponentialRemainder_monotone ht) (sq_nonneg t)) _

/-- The nonzero-argument formula used by the paper's exact central certificate. -/
theorem exponentialRemainder_eq_div {t : ℝ} (ht : t ≠ 0) :
    exponentialRemainder t = (Real.exp t - 1 - t) / t ^ 2 := by
  apply (eq_div_iff (pow_ne_zero _ ht)).2
  nlinarith [exp_eq_one_add_add_sq_remainder t]

end ErdosProblems.Erdos1041
