import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Finite grouped-pole obstruction. Candidate pending compilation.
The variables `a` are the conjugated distinct nonzero centers. -/
open scoped BigOperators
noncomputable section
namespace ErdosProblems.Erdos1041
open Polynomial

/-- Numerator obtained by clearing distinct linear denominators in
`sum j, b j * a j / (1-a j*z)`. -/
def groupedPoleNumerator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) : ℂ[X] :=
  ∑ j, C (b j * a j) * ∏ k ∈ Finset.univ.erase j, (1 - C (a k) * X)

/-- Evaluation at one reciprocal center isolates precisely its own term. -/
theorem groupedPoleNumerator_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (i : ι) (hi : a i ≠ 0) :
    (groupedPoleNumerator a b).eval (a i)⁻¹ =
      b i * a i * ∏ k ∈ Finset.univ.erase i, (1 - a k * (a i)⁻¹) := by
  classical
  simp only [groupedPoleNumerator, eval_finset_sum, eval_mul, eval_C,
    eval_prod, eval_sub, eval_one, eval_X]
  apply Finset.sum_eq_single i
  · intro j hj hji
    have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ _⟩
    have hp : (∏ k ∈ Finset.univ.erase j, (1 - a k * (a i)⁻¹)) = 0 := by
      apply Finset.prod_eq_zero hmem
      simp [hi]
    rw [hp, mul_zero]
  · simp

/-- Distinct nonzero centers and a nonzero selected weight force the cleared
polynomial to be nonzero; no analytic or desired nonconstancy input is used. -/
theorem groupedPoleNumerator_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (ha : Function.Injective a) (i : ι)
    (hi : a i ≠ 0) (hb : b i ≠ 0) : groupedPoleNumerator a b ≠ 0 := by
  have hp : (∏ k ∈ Finset.univ.erase i, (1 - a k * (a i)⁻¹)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    intro he
    have he' : a k * (a i)⁻¹ = 1 := (sub_eq_zero.mp he).symm
    have hki : a k = a i := by
      have hh := congrArg (fun z : ℂ => z * a i) he'
      simpa only [mul_assoc, inv_mul_cancel₀ hi, mul_one, one_mul] using hh
    exact (Finset.mem_erase.mp hk).1 (ha hki)
  intro hz
  have he := groupedPoleNumerator_eval a b i hi
  rw [hz, eval_zero] at he
  exact (mul_ne_zero (mul_ne_zero hb hi) hp) he.symm

/-- In particular, strictly positive grouped real weights cannot cancel a
nonzero distinct pole in the cleared polynomial. -/
theorem groupedPoleNumerator_positive_weights_ne_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℂ) (w : ι → ℝ)
    (ha : Function.Injective a) (i : ι) (hi : a i ≠ 0) (hw : 0 < w i) :
    groupedPoleNumerator a (fun j => (w j : ℂ)) ≠ 0 := by
  apply groupedPoleNumerator_ne_zero a (fun j => (w j : ℂ)) ha i hi
  exact_mod_cast ne_of_gt hw

end ErdosProblems.Erdos1041
end
