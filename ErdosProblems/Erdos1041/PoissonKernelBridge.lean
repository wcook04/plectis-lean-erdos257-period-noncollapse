import Mathlib.Analysis.Complex.Poisson
import Mathlib.Tactic

/-!
Pointwise algebra for the full-disc weighted free-point Poisson argument.
This supplies the kernel/logarithmic-derivative identity, not the analytic
norm-square majorization or the infinite Taylor energy identity. Uncompiled.
-/

namespace ErdosProblems.Erdos1041
open scoped BigOperators

/-- The elementary Poisson identity, before substitution on the unit circle. -/
theorem poisson_fraction_eq_log_derivative (u : ℂ) (hu : u ≠ 1) :
    (1 - ‖u‖ ^ 2) / ‖1 - u‖ ^ 2 = 1 + 2 * (u / (1 - u)).re := by
  have hd : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hn : Complex.normSq (1 - u) ≠ 0 :=
    (Complex.normSq_pos.mpr hd).ne'
  simp only [← Complex.normSq_eq_norm_sq, Complex.div_re]
  field_simp [hn]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  <;> ring

/-- Positive mixtures preserve the pointwise identity. The input `u` will
be `conj c * ζ`; no analytic derivative or boundary integral is assumed here. -/
theorem weighted_poisson_fraction_identity {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u : ι → ℂ) (hw : ∑ j, w j = 1)
    (hu : ∀ j, u j ≠ 1) :
    (∑ j, w j * ((1 - ‖u j‖ ^ 2) / ‖1 - u j‖ ^ 2)) =
      1 + 2 * ∑ j, w j * (u j / (1 - u j)).re := by
  simp_rw [poisson_fraction_eq_log_derivative _ (hu _), mul_add, mul_one]
  rw [Finset.sum_add_distrib, hw, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Inside the disc each kernel is nonnegative; mixture positivity is
separate from the logarithmic-derivative identity. -/
theorem poisson_fraction_nonneg {u : ℂ} (hu : ‖u‖ ≤ 1) :
    0 ≤ (1 - ‖u‖ ^ 2) / ‖1 - u‖ ^ 2 := by
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg u]

end ErdosProblems.Erdos1041
