import ErdosProblems.Erdos1041.ReturnV5.FirstMergeReduction
import ErdosProblems.Erdos1041.ConnectorR18.CubicBranch

/-!
Cross-return composition candidate, UNRUN.
The V5 exact residual reduction and R18 cubic branch isolate degree at least four.
This equivalence does not prove the remaining analytic construction.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ReturnV5
open Polynomial Set PaperAnalyticTargets

/-- The exact residual after also supplying the cubic branch. -/
def DegreeFourFirstMergeResidual : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (z : Fin n → ℂ) (μ : ℝ), 4 ≤ n → p.Monic →
    p.natDegree = n → RootEnumeration p z → CriticalMinimum p μ →
    Function.Injective z → 0 < μ → CFConclusion n p z μ

/-- Compose the two returns without replacing the endpoint by a stronger supplier. -/
theorem constantFactor_iff_degreeFour_residual :
    ConstantFactorPath ↔ DegreeFourFirstMergeResidual := by
  constructor
  · intro H n p z μ hn hm hd hz hμ hinj hpos
    exact H n p z μ (by omega) hm hd hz hμ
  · intro H
    apply constantFactor_iff_highDegree_residual.mpr
    intro n p z μ hn hm hd hz hμ hinj hpos
    by_cases h3 : n = 3
    · rcases h3 with rfl
      exact ConnectorR18.cubic_complete (p := p) (z := z) (μ := μ) hz hμ
    · exact H n p z μ (by omega) hm hd hz hμ hinj hpos

end ErdosProblems.Erdos1041.ReturnV5
