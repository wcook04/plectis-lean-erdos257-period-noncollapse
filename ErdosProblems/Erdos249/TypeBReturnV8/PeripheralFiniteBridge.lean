import Erdos249257.FirstHarmonicPivot

/-!
# Finite bridge for the three peripheral first-harmonic pivot budgets

Authoring status: UNRUN in the Type-B environment.

This file contains no PNT or Schoenberg theorem.  It formalises the finite
last mile needed once arithmetic estimates have supplied:

* a cardinal bound for bad supplier bases;
* a cardinal bound for non-supplier bases; and
* a uniform norm bound on every good fibre mean.

It deliberately leaves the centred residual real-part estimate visible.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset
noncomputable section

@[simp] theorem norm_pivotPhaseAt (h N L s : ℕ) :
    ‖pivotPhaseAt h N L s‖ = 1 := by
  simp [pivotPhaseAt]

@[simp] theorem norm_pivotResidualAt_v8 (h N L s : ℕ) :
    ‖pivotResidualAt h N L s‖ = 1 := by
  rw [pivotResidualAt, norm_div, norm_windowFirstExp, norm_pivotPhaseAt]
  norm_num

/-- The bad contribution is bounded by the number of bad bases. -/
theorem norm_pivotBadContribution_le_card (h X L s : ℕ) (η : ℝ) :
    ‖pivotBadContribution h X L s η‖ ≤
      ((pivotBadBases X L s η).card : ℝ) := by
  rw [pivotBadContribution]
  calc
    ‖∑ N ∈ pivotBadBases X L s η, windowFirstExp h N L‖
        ≤ ∑ N ∈ pivotBadBases X L s η, ‖windowFirstExp h N L‖ := by
          exact norm_sum_le _ _
    _ = ((pivotBadBases X L s η).card : ℝ) := by simp

/-- The non-supplier contribution is bounded by the number of non-suppliers. -/
theorem norm_pivotNonSupplierContribution_le_card (h X L s : ℕ) :
    ‖pivotNonSupplierContribution h X L s‖ ≤
      ((pivotNonSupplierBases X L s).card : ℝ) := by
  rw [pivotNonSupplierContribution]
  calc
    ‖∑ N ∈ pivotNonSupplierBases X L s, windowFirstExp h N L‖
        ≤ ∑ N ∈ pivotNonSupplierBases X L s, ‖windowFirstExp h N L‖ := by
          exact norm_sum_le _ _
    _ = ((pivotNonSupplierBases X L s).card : ℝ) := by simp

/-- Good bases are a subset of the ambient dyadic block. -/
theorem pivotGoodBases_subset_Ico (X L s : ℕ) (η : ℝ) :
    pivotGoodBases X L s η ⊆ Finset.Ico X (2 * X) := by
  intro N hN
  have hSupplier : N ∈ pivotSupplierBases X L s :=
    (Finset.mem_filter.mp hN).1
  exact (Finset.mem_filter.mp hSupplier).1

/-- Hence there are at most `X` good bases. -/
theorem card_pivotGoodBases_le (X L s : ℕ) (η : ℝ) :
    (pivotGoodBases X L s η).card ≤ X := by
  calc
    (pivotGoodBases X L s η).card
        ≤ (Finset.Ico X (2 * X)).card :=
      Finset.card_le_card (pivotGoodBases_subset_Ico X L s η)
    _ = X := by
      rw [Nat.card_Ico]
      omega

/-- A uniform fibre-mean estimate immediately bounds the whole mean
contribution, because every residual has unit norm. -/
theorem norm_pivotFiberMeanContribution_le_of_uniform
    (h X L s : ℕ) (η ε : ℝ) (hε : 0 ≤ ε)
    (hmean : ∀ N ∈ pivotGoodBases X L s η,
      ‖pivotFiberMean h X L s (pivotCofactor N L s)‖ ≤ ε) :
    ‖pivotFiberMeanContribution h X L s η‖ ≤ ε * X := by
  rw [pivotFiberMeanContribution]
  calc
    ‖∑ N ∈ pivotGoodBases X L s η,
        pivotResidualAt h N L s *
          pivotFiberMean h X L s (pivotCofactor N L s)‖
        ≤ ∑ N ∈ pivotGoodBases X L s η,
            ‖pivotResidualAt h N L s *
              pivotFiberMean h X L s (pivotCofactor N L s)‖ := by
          exact norm_sum_le _ _
    _ = ∑ N ∈ pivotGoodBases X L s η,
          ‖pivotFiberMean h X L s (pivotCofactor N L s)‖ := by
          apply Finset.sum_congr rfl
          intro N hN
          simp [norm_mul]
    _ ≤ ∑ _N ∈ pivotGoodBases X L s η, ε :=
          Finset.sum_le_sum hmean
    _ = ((pivotGoodBases X L s η).card : ℝ) * ε := by simp
    _ ≤ (X : ℝ) * ε := by
          gcongr
          exact_mod_cast card_pivotGoodBases_le X L s η
    _ = ε * X := by ring

/-- Finite assembly: cardinal estimates plus a uniform fibre-mean estimate
supply the three peripheral clauses, leaving only the centred real part. -/
theorem pivotBudgetAt_of_peripheral_estimates
    (h X L s : ℕ) (η : ℝ)
    (hcentered :
      (pivotCenteredCorrelation h X L s η).re ≤ (14 / 25 : ℝ) * X)
    (hmean : ∀ N ∈ pivotGoodBases X L s η,
      ‖pivotFiberMean h X L s (pivotCofactor N L s)‖ ≤ (1 / 100 : ℝ))
    (hbad : ((pivotBadBases X L s η).card : ℝ) ≤ (1 / 100 : ℝ) * X)
    (hnon : ((pivotNonSupplierBases X L s).card : ℝ) ≤ (8 / 25 : ℝ) * X) :
    PivotBudgetAt h X L s η := by
  refine ⟨hcentered, ?_, ?_, ?_⟩
  · have h := norm_pivotFiberMeanContribution_le_of_uniform
      h X L s η (1 / 100 : ℝ) (by norm_num) hmean
    simpa [mul_comm] using h
  · exact (norm_pivotBadContribution_le_card h X L s η).trans hbad
  · exact (norm_pivotNonSupplierContribution_le_card h X L s).trans hnon

end
end TotientTailPeriodKiller
end Erdos249257
