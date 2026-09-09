import ErdosProblems.Erdos1041.WeightedAnalyticLog

/-! Exact radial identities of the explicit finite logarithmic construction.
Candidate pending compilation; no equality classification is asserted. -/
open scoped BigOperators ComplexConjugate
noncomputable section
namespace ErdosProblems.Erdos1041

/-- Contracting the centers by a real scalar composes the actual analytic
function with scalar multiplication. This identity is global and algebraic. -/
theorem weightedAnalyticLog_radial {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (r : ℝ) (z : ℂ) :
    weightedAnalyticLog w (fun j => (r : ℂ) * c j) z =
      weightedAnalyticLog w c ((r : ℂ) * z) := by
  unfold weightedAnalyticLog
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- At a contracted center, the original analytic function is sampled at the
square of the contraction factor. -/
theorem weightedAnalyticLog_radial_at_center {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (r : ℝ) (j : ι) :
    weightedAnalyticLog w (fun k => (r : ℂ) * c k) ((r : ℂ) * c j) =
      weightedAnalyticLog w c ((r : ℂ) ^ 2 * c j) := by
  rw [weightedAnalyticLog_radial]
  congr 1
  ring

/-- The first Taylor derivative is the negative conjugate weighted moment.
At zero no bound on the centers is needed to obtain the analytic derivative. -/
theorem deriv_weightedAnalyticLog_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) :
    deriv (weightedAnalyticLog w c) 0 =
      -(∑ j, (w j : ℂ) * conj (c j)) := by
  have h := (hasDerivAt_weightedAnalyticLog w c 0 (by intro j; simp)).deriv
  simpa only [weightedAnalyticLog_zero, norm_zero, mul_zero, sub_zero,
    div_one, one_mul, mul_neg, Finset.sum_neg_distrib] using h

/-- A nonzero weighted first moment is a concrete obstruction to constancy.
This sufficient obstruction does not cover symmetric configurations whose
first moment vanishes. -/
theorem weightedAnalyticLog_not_constant_of_first_moment {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ)
    (hm : (∑ j, (w j : ℂ) * conj (c j)) ≠ 0) :
    ¬ ∃ K : ℂ, weightedAnalyticLog w c = fun _ => K := by
  rintro ⟨K, hK⟩
  have hd := deriv_weightedAnalyticLog_zero w c
  rw [hK, deriv_const] at hd
  exact hm (neg_eq_zero.mp hd.symm)

end ErdosProblems.Erdos1041
end
