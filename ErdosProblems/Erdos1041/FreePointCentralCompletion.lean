import ErdosProblems.Erdos1041.FreePointHilbertCertificate
import ErdosProblems.Erdos1041.LogKernelCentralCertificate

/-!
# The central free-point inequality with its series inputs discharged

The logarithmic kernel energy and variance theorems supply the two analytic
inputs of the Hilbert certificate. Only the actual point-radius bound remains.
-/

open scoped BigOperators ComplexConjugate

namespace ErdosProblems.Erdos1041.FreePointHilbertCertificate

/-- Every finite configuration in the closed central disk satisfies the
geometric row-mean inequality. There are no additional series assumptions. -/
theorem freePointSum_central_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ centralRadius) :
    freePointSum c ≤ (m : ℝ) := by
  have hlt : ∀ j, ‖c j‖ < 1 := fun j => (hc j).trans_lt centralRadius_lt_one
  apply freePointSum_central_le_of_series hm c hc (logInteractionRow c)
  · intro j
    simp only [logInteractionRow, div_eq_mul_inv]
    ring
  · rw [sum_logInteractionRow]
    exact neg_nonpos.mpr (logInteractionEnergy_nonneg c hlt)
  · intro j
    have hdiag : logInteractionDiagonal c j = -Real.log (1 - ‖c j‖ ^ 2) := by
      have hpos : 0 < 1 - ‖c j‖ ^ 2 := by
        nlinarith [hlt j, norm_nonneg (c j)]
      unfold logInteractionDiagonal
      rw [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_one,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        Complex.normSq_eq_norm_sq, abs_of_pos hpos]
    simpa only [sum_logInteractionRow, neg_neg, hdiag] using
      logInteractionRow_sq_le hm c hlt j

/-- The same central theorem with the finite-point expression expanded. -/
theorem geometric_row_mean_central_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ Real.sqrt (1 - Real.exp (-2))) :
    (∑ j, (∏ k, ‖1 - conj (c j) * c k‖) ^ ((m : ℝ)⁻¹)) ≤ (m : ℝ) := by
  exact freePointSum_central_le hm c hc

end ErdosProblems.Erdos1041.FreePointHilbertCertificate
