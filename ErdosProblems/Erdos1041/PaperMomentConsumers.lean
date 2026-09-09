import ErdosProblems.Erdos1041.FreePointTorusPshReduction
import Mathlib

/-!
# Finite moment lowering, with the analytic supplier explicit

No reflected-derivative estimate, maximum principle, or Poisson formula is
postulated by this file. The norm-power sum entering the consumer is a
hypothesis. This is partial coverage only for the critical-value budget rows.

New source, not elaborated in this environment.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperMomentConsumers

open scoped BigOperators
open FreePointTorusPshReduction

/-- A cardinality-normalised nonnegative moment bound passes to lower powers. -/
theorem lower_moment {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβα : β ≤ α)
    (H : ∑ i, x i ^ α ≤ (Fintype.card ι : ℝ)) :
    ∑ i, x i ^ β ≤ (Fintype.card ι : ℝ) := by
  have hq0 : 0 ≤ β / α := div_nonneg hβ hα.le
  have hq1 : β / α ≤ 1 := (div_le_one hα).2 hβα
  have h := sum_rpow_le_card_of_sum_le_card hq0 hq1 (fun i => x i ^ α)
    (fun i => Real.rpow_nonneg (hx i) _) H
  have hp (i : ι) : (x i ^ α) ^ (β / α) = x i ^ β := by
    rw [← Real.rpow_mul (hx i)]
    congr 1
    field_simp [ne_of_gt hα]
  simpa only [hp] using h

/-- The squared free-point/critical-value moment implies the 1/n moment,
provided the polynomial has already supplied that squared moment. -/
theorem critical_moment_lowering {m : ℕ} (hm : 1 ≤ m)
    (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i)
    (H : ∑ i, x i ^ (2 / (m : ℝ)) ≤ (m : ℝ)) :
    ∑ i, x i ^ (1 / ((m : ℝ) + 1)) ≤ (m : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hα : (0 : ℝ) < 2 / m := div_pos (by norm_num) hmpos
  have hβ : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
  have hβα : 1 / ((m : ℝ) + 1) ≤ 2 / (m : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hmpos).2
    linarith
  simpa using lower_moment x hx hα hβ hβα (by simpa using H)

/-- Weighted quadratic control implies weighted first-moment control.
The argument is finite and uses the exact tangent inequality at one. -/
theorem weighted_first_of_second {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (H : ∑ i, w i * x i ^ 2 ≤ 1) : ∑ i, w i * x i ≤ 1 := by
  have hterm (i : ι) : w i * x i ≤ w i * ((x i ^ 2 + 1) / 2) := by
    apply mul_le_mul_of_nonneg_left _ (hw i)
    nlinarith [sq_nonneg (x i - 1)]
  calc
    ∑ i, w i * x i ≤ ∑ i, w i * ((x i ^ 2 + 1) / 2) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((∑ i, w i * x i ^ 2) + 1) / 2 := by
      have he : ∑ i, w i * ((x i ^ 2 + 1) / 2)
          = (∑ i, (w i * x i ^ 2 + w i)) / 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [he, Finset.sum_add_distrib, hwsum]
    _ ≤ 1 := by linarith

#print axioms critical_moment_lowering

end ErdosProblems.Erdos1041.PaperMomentConsumers
