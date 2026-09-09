import ErdosProblems.Erdos1041.WeightedAnalyticLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Literal modulus identification for the finite analytic construction.
Candidate pending compilation. No sign or normalization of weights is assumed. -/
open scoped BigOperators ComplexConjugate
noncomputable section
namespace ErdosProblems.Erdos1041

/-- The analytic logarithmic construction has exactly the intended weighted
geometric modulus wherever its factors are nonzero, for arbitrary real weights. -/
theorem norm_weightedAnalyticLog {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (z : ℂ)
    (hc : ∀ j, 1 - conj (c j) * z ≠ 0) :
    ‖weightedAnalyticLog w c z‖ = ∏ j, ‖1 - conj (c j) * z‖ ^ w j := by
  classical
  rw [weightedAnalyticLog, Complex.norm_exp]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.log_re]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr (hc j))]
  congr 1
  ring

/-- The concrete norm bound used for analyticity also discharges every
nonzero-factor condition needed for the modulus identity. -/
theorem norm_weightedAnalyticLog_of_norm_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (z : ℂ)
    (hc : ∀ j, ‖c j‖ * ‖z‖ < 1) :
    ‖weightedAnalyticLog w c z‖ = ∏ j, ‖1 - conj (c j) * z‖ ^ w j := by
  apply norm_weightedAnalyticLog
  intro j hj
  have heq : conj (c j) * z = 1 := (sub_eq_zero.mp hj).symm
  have hn : ‖c j‖ * ‖z‖ = 1 := by
    simpa only [norm_mul, Complex.norm_conj, norm_one] using congrArg norm heq
  linarith [hc j]

end ErdosProblems.Erdos1041
end
