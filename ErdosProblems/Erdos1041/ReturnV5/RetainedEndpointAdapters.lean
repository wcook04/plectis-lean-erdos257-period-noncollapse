import ErdosProblems.Erdos1041.ReturnV5.RootOccurrences
import ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10
import ErdosProblems.Erdos1041.PaperWeightedRefinementsR10
import ErdosProblems.Erdos1041.PaperCriticalValueMeanR10
import ErdosProblems.Erdos1041.PaperReflectedCompletion
import ErdosProblems.Erdos1041.PaperCubicSchur

/-!
# Exact type parity with the previously declared paper targets

AUTHORED / UNRUN. The weighted, reflected, cubic-count and moment proofs
already exist in the supplied source. The aliases below are TYPE CHECK targets,
not claims that these results are newly proved here. The primitive selector
adapter supplies its actual factorisation premise from RootEnumeration.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ReturnV5
open PaperAnalyticTargets
open scoped BigOperators

theorem weighted_free_point_exact_target : WeightedFreePoint :=
  paper_weighted_free_point

theorem critical_value_mean_exact_target : CriticalValueMean :=
  paper_critical_value_mean

theorem reflected_critical_value_exact_target : ReflectedCriticalValue :=
  PaperReflectedCompletion.reflected_critical_value

theorem cubic_root_count_exact_target : CubicRootCount :=
  PaperCubicSchur.cubic_root_count

/-- Exact primitive target, without an extra tail-selection assumption. -/
theorem primitive_quintic_selector_exact_target : PrimitiveQuinticSelector := by
  intro p a b c w hvalue henumeration hdisc
  apply PaperPrimitiveCompletionR10.two_tails_of_rootProduct (a := a) (b := b) (c := c) w _ hdisc
  intro x
  have he : PaperPrimitivePath.value a b c x = p.eval x := (hvalue x).symm
  rw [he, enumeration_eval henumeration]
  simp [PaperPrimitiveCompletionR10.rootProduct, Fin.prod_univ_succ, mul_assoc]

end ErdosProblems.Erdos1041.ReturnV5
