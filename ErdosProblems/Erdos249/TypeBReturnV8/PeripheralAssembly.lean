import ErdosProblems.Erdos249.TypeBReturnV8.PeripheralFiniteBridge

/-! Complete candidate source; UNRUN. No prime-distribution theorem is supplied
by this finite/compositional module. The two analytic hypotheses remain visible.
The depth in the two hypotheses must be the SAME function. -/

namespace ErdosProblems.Erdos249.TypeBReturnV8
open Erdos249257.TotientTailPeriodKiller
open Finset
noncomputable section

theorem card_pivotFiber_eq_card_supplierPrimes
    {X L s m : ℕ} (hm : 0 < m) (hmsmall : m ≤ Nat.sqrt X / 2) :
    (pivotFiber X L s m).card = (pivotSupplierPrimes X L s m).card := by
  rw [← image_pivotSupplierPrimes_eq_pivotFiber hm hmsmall]
  apply Finset.card_image_iff.mpr
  intro p hp q hq heq
  exact pivotBaseOfPrime_injective_on_supplierPrimes hm hp hq heq

/-- Strong peripheral predicate used in the ordinary proof in this return. -/
def PeripheralAt (depth : ℕ → ℕ) (h X : ℕ) : Prop :=
  h ≤ depth X - 26 ∧
  16 * (2 * X + h + depth X + 2) ≤ 2 ^ depth X ∧
  (∀ N ∈ pivotGoodBases X (depth X) 26 (1 / 1000 : ℝ),
    ‖pivotFiberMean h X (depth X) 26 (pivotCofactor N (depth X) 26)‖ ≤
      (1 / 100 : ℝ)) ∧
  ((pivotBadBases X (depth X) 26 (1 / 1000 : ℝ)).card : ℝ) ≤
    (1 / 100 : ℝ) * X ∧
  ((pivotNonSupplierBases X (depth X) 26).card : ℝ) ≤ (8 / 25 : ℝ) * X

/-- Eventual peripheral estimates intersect a cofinal centred estimate at the
same depth. This is NOT a proof of either analytic hypothesis. -/
theorem dtw_of_eventual_peripheral_and_cofinal_centered
    (depth : ℕ → ℕ)
    (hperipheral : ∀ h : ℕ, 0 < h → ∃ A : ℕ, ∀ X : ℕ, A ≤ X →
      PeripheralAt depth h X)
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ,
      max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (depth X) 26 (1 / 1000 : ℝ)).re ≤
        (14 / 25 : ℝ) * X) :
    DTWPivotResidualDecorrelation := by
  intro h hh
  refine ⟨26, by decide, (1 / 1000 : ℝ), by norm_num, by norm_num, ?_⟩
  intro X₀
  obtain ⟨A, hA⟩ := hperipheral h hh
  obtain ⟨X, hX, hc⟩ := hcentered h hh (max X₀ A)
  have hAX : A ≤ X := by omega
  obtain ⟨hoverlap, hroom, hmean, hbad, hnon⟩ := hA X hAX
  refine ⟨X, depth X, by omega, hoverlap, hroom, ?_⟩
  exact pivotBudgetAt_of_peripheral_estimates h X (depth X) 26
    (1 / 1000 : ℝ) hc hmean hbad hnon

/-- The conditional arithmetic endpoint, with both missing inputs explicit. -/
theorem irrational_of_eventual_peripheral_and_cofinal_centered
    (depth : ℕ → ℕ)
    (hperipheral : ∀ h : ℕ, 0 < h → ∃ A : ℕ, ∀ X : ℕ, A ≤ X →
      PeripheralAt depth h X)
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ,
      max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (depth X) 26 (1 / 1000 : ℝ)).re ≤
        (14 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totient_series_of_pivotResidualDecorrelation
    (dtw_of_eventual_peripheral_and_cofinal_centered depth hperipheral hcentered)
end
end ErdosProblems.Erdos249.TypeBReturnV8
