import ErdosProblems.Erdos1041.ReturnV5.QuadraticBranch

/-!
# Exact residual of the constant-factor endpoint

AUTHORED / UNRUN. This file proves a REDUCTION, not the remaining analytic
construction. `HighDegreeFirstMergeResidual` is deliberately a proposition
definition; the equivalence below is not evidence that either side holds.
The repeated-root and degree-two branches have actual curve producers.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ReturnV5
open Polynomial Set PaperAnalyticTargets

/-- The exact two-part conclusion, without weakening open containment. -/
def CFConclusion (n : ℕ) (p : ℂ[X]) (z : Fin n → ℂ) (μ : ℝ) : Prop :=
  (∃ i j : Fin n, i ≠ j ∧
    ConnectedAtMost p.eval (2 * μ) ((71 / 10 : ℝ) * μ ^ (1 / (n : ℝ)))
      (z i) (z j) ∧ (Squarefree p → z i ≠ z j)) ∧
  (RootsInOpenUnitDisc p → μ ≤ 1 / 2 →
    ∃ i j : Fin n, i ≠ j ∧ ∃ γ : ℝ → ℂ,
      ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
      BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal (57 / 10))

/-- UNPROVED analytic residual, explicitly restricted to degree >= 3,
injective enumeration, and positive least critical modulus. -/
def HighDegreeFirstMergeResidual : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (z : Fin n → ℂ) (μ : ℝ), 3 ≤ n → p.Monic →
    p.natDegree = n → RootEnumeration p z → CriticalMinimum p μ →
    Function.Injective z → 0 < μ → CFConclusion n p z μ

/-- Every branch omitted by the residual is supplied by an actual curve.
This equivalence precisely identifies, but DOES NOT discharge, the gap. -/
theorem constantFactor_iff_highDegree_residual :
    ConstantFactorPath ↔ HighDegreeFirstMergeResidual := by
  constructor
  · intro H n p z μ hn hm hd hz hμ hinj hpos
    exact H n p z μ (by omega) hm hd hz hμ
  · intro H n p z μ hn hm hd hz hμ
    by_cases hn2 : n = 2
    · rcases hn2 with rfl
      obtain ⟨hclosed, hopen⟩ := constantFactor_quadratic_branch p z μ hz hμ
      exact ⟨hclosed, fun _ hsmall => hopen hsmall⟩
    · by_cases hinj : Function.Injective z
      · exact H n p z μ (by omega) hm hd hz hμ hinj
          (criticalMinimum_pos_of_injective hz hμ hinj)
      · have hr : ∃ i j, i ≠ j ∧ z i = z j := by
          by_contra h
          apply hinj
          intro i j he
          by_contra hij
          exact h ⟨i, j, hij, he⟩
        obtain ⟨hclosed, hopen⟩ := constantFactor_repeated_branch p z μ hz hμ hr
        exact ⟨hclosed, fun _ _ => hopen⟩

end ErdosProblems.Erdos1041.ReturnV5
