import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! UNRUN candidate. A generic finite countermodel to an inference, not a
counterexample to the arithmetic totient-centred predicate. -/
namespace ErdosProblems.Erdos249.TypeBReturnV8
noncomputable section

def twoPhase (i : Fin 2) : ℂ := if i = 0 then 1 else -1
def twoMean : ℂ := (2 : ℂ)⁻¹ * ∑ i : Fin 2, twoPhase i
def twoCentered : ℂ := ∑ i : Fin 2, twoPhase i * (twoPhase i - twoMean)
def twoMeanContribution : ℂ := ∑ i : Fin 2, twoPhase i * twoMean

 theorem twoPhase_unit (i : Fin 2) : ‖twoPhase i‖ = 1 := by
  fin_cases i <;> norm_num [twoPhase]
 theorem twoMean_zero : twoMean = 0 := by
  norm_num [twoMean, Fin.sum_univ_two, twoPhase]
 theorem twoCentered_eq_two : twoCentered = 2 := by
  norm_num [twoCentered, twoMean_zero, Fin.sum_univ_two, twoPhase]
 theorem twoMeanContribution_zero : twoMeanContribution = 0 := by
  simp [twoMeanContribution, twoMean_zero]
 theorem three_peripheral_zero_do_not_force_centered_budget :
    twoMean = 0 ∧ twoMeanContribution = 0 ∧
    ¬ twoCentered.re ≤ (14 / 25 : ℝ) * 2 := by
  rw [twoMean_zero, twoMeanContribution_zero, twoCentered_eq_two]
  norm_num
end
end ErdosProblems.Erdos249.TypeBReturnV8
