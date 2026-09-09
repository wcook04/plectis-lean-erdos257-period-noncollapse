import ErdosProblems.Erdos1041.LogKernelVariance
import ErdosProblems.Erdos1041.ExponentialRemainderBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# An adaptive certificate for the free-point mean

For a finite configuration in the open unit disk, the mean logarithmic
interaction in each row has a controlled variance. The one-sided exponential
remainder then bounds the sum of the geometric row means. The input caps
are bounds on the actual logarithmic rows, not independent energy variables.
-/

open scoped BigOperators ComplexConjugate

namespace ErdosProblems.Erdos1041

noncomputable def logInteractionRow {m : ℕ} (c : Fin m → ℂ) (i : Fin m) : ℝ :=
  (∑ j, Real.log ‖1 - conj (c i) * c j‖) / m

noncomputable def logInteractionEnergy {m : ℕ} (c : Fin m → ℂ) : ℝ :=
  -(∑ i, ∑ j, Real.log ‖1 - conj (c i) * c j‖) / m

noncomputable def logInteractionDiagonal {m : ℕ} (c : Fin m → ℂ) (i : Fin m) : ℝ :=
  -Real.log ‖1 - conj (c i) * c i‖

theorem sum_logInteractionRow {m : ℕ} (c : Fin m → ℂ) :
    (∑ i, logInteractionRow c i) = -logInteractionEnergy c := by
  simp only [logInteractionRow, logInteractionEnergy, ← Finset.sum_div, neg_div, neg_neg]

theorem logInteractionEnergy_nonneg {m : ℕ} (c : Fin m → ℂ)
    (hc : ∀ i, ‖c i‖ < 1) : 0 ≤ logInteractionEnergy c := by
  exact div_nonneg (neg_nonneg.mpr
    (sum_log_kernel_nonpos Finset.univ c (fun i _ => hc i))) (Nat.cast_nonneg m)

theorem logInteractionRow_sq_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ i, ‖c i‖ < 1) (i : Fin m) :
    (logInteractionRow c i) ^ 2 ≤
      (logInteractionEnergy c / m) * logInteractionDiagonal c i := by
  have h := log_kernel_row_sq_le_energy Finset.univ c (fun j _ => hc j) (hc i)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold logInteractionRow logInteractionEnergy logInteractionDiagonal
  rw [div_pow]
  calc
    _ ≤ ((-Real.log ‖1 - conj (c i) * c i‖) *
        (-∑ j, ∑ k, Real.log ‖1 - conj (c j) * c k‖)) / (m : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right h (sq_nonneg _)
    _ = _ := by field_simp [hm0]

/-- The adaptive row certificate bounds the sum of the actual exponential
logarithmic means. The caps may vary from row to row. -/
theorem sum_exp_logInteractionRow_le_of_certificate
    {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ) (hc : ∀ i, ‖c i‖ < 1)
    (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hcap : ∀ i, logInteractionRow c i ≤ M i)
    (hcertificate : (∑ i, exponentialRemainder (M i) * logInteractionDiagonal c i) ≤ m) :
    (∑ i, Real.exp (logInteractionRow c i)) ≤ m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hE := logInteractionEnergy_nonneg c hc
  have hcoef : 0 ≤ logInteractionEnergy c / m := div_nonneg hE hmpos.le
  have hpoint (i : Fin m) :
      Real.exp (logInteractionRow c i) ≤ 1 + logInteractionRow c i +
        (logInteractionEnergy c / m) *
          (exponentialRemainder (M i) * logInteractionDiagonal c i) := by
    have hPhi : 0 ≤ exponentialRemainder (M i) := by
      have h := exponentialRemainder_monotone (hM i)
      rw [exponentialRemainder_zero] at h
      linarith
    have hv := mul_le_mul_of_nonneg_right (logInteractionRow_sq_le hm c hc i) hPhi
    have he := exp_le_one_add_add_sq_remainder (hcap i)
    nlinarith
  have hs := Finset.sum_le_sum (fun (i : Fin m) (_ : i ∈ Finset.univ) => hpoint i)
  have hsum : (∑ i, Real.exp (logInteractionRow c i)) ≤
      (m : ℝ) - logInteractionEnergy c + (logInteractionEnergy c / m) *
        (∑ i, exponentialRemainder (M i) * logInteractionDiagonal c i) := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, sum_logInteractionRow,
      ← Finset.mul_sum, sub_eq_add_neg] using hs
  have hb := mul_le_mul_of_nonneg_left hcertificate hcoef
  have hcancel : (logInteractionEnergy c / m) * m = logInteractionEnergy c :=
    div_mul_cancel₀ _ hmpos.ne'
  linarith

/-- The exponential logarithmic mean is the geometric mean of the row's
distance factors. -/
theorem exp_logInteractionRow_eq_rpow {m : ℕ} (c : Fin m → ℂ)
    (hc : ∀ i, ‖c i‖ < 1) (i : Fin m) :
    Real.exp (logInteractionRow c i) =
      (∏ j, ‖1 - conj (c i) * c j‖) ^ (1 / (m : ℝ)) := by
  have hfactor (j : Fin m) : 0 < ‖1 - conj (c i) * c j‖ :=
    log_kernel_factor_pos (hc i) (hc j)
  rw [Real.rpow_def_of_pos (Finset.prod_pos (fun j _ => hfactor j)),
    Real.log_prod (fun j _ => (hfactor j).ne')]
  congr 1
  simp only [logInteractionRow, div_eq_mul_inv, one_mul]

/-- Adaptive free-point inequality, stated directly for the geometric row
means appearing in the paper. -/
theorem freePointMean_le_of_log_certificate
    {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ) (hc : ∀ i, ‖c i‖ < 1)
    (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hcap : ∀ i, logInteractionRow c i ≤ M i)
    (hcertificate : (∑ i, exponentialRemainder (M i) * logInteractionDiagonal c i) ≤ m) :
    (∑ i, (∏ j, ‖1 - conj (c i) * c j‖) ^ (1 / (m : ℝ))) ≤ m := by
  simpa only [exp_logInteractionRow_eq_rpow c hc] using
    sum_exp_logInteractionRow_le_of_certificate hm c hc M hM hcap hcertificate

end ErdosProblems.Erdos1041
