import ErdosProblems.Erdos249.TypeBReturnV8.FiniteArithmetic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Complete mathematical candidate, UNRUN. This proves one small finite
instance only. In particular it does not prove DTWFirstHarmonicNormGap. -/
namespace ErdosProblems.Erdos249.TypeBReturnV8
open Erdos249257.TotientTailPeriodKiller
open Finset
noncomputable section

private def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)
private theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := by simp [phase]
private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]
private theorem phase_pi : phase Real.pi = -1 := by
  simp [phase]

private theorem antipodal_pair_bound (a δ : ℝ) :
    ‖phase a + phase (a + Real.pi - δ)‖ ≤ |δ| := by
  have heq : phase a + phase (a + Real.pi - δ) =
      phase a * (1 - phase (-δ)) := by
    rw [sub_eq_add_neg, phase_add, phase_add, phase_pi]
    ring
  rw [heq, norm_mul, phase_norm, one_mul, norm_sub_rev]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -δ)
  simpa [phase, mul_comm, Real.norm_eq_abs] using h

private theorem phase_6 : windowFirstExp 1 6 9 = phase (67 * Real.pi / 64) := by
  have ha : windowFirstAngle 1 6 9 = 67 * Real.pi / 64 := by
    norm_num [windowFirstAngle, discrepancy_1_6_9]
    <;> ring
  simp only [windowFirstExp, phase, ha]
private theorem phase_7 : windowFirstExp 1 7 9 = phase (Real.pi / 8) := by
  have ha : windowFirstAngle 1 7 9 = Real.pi / 8 := by
    norm_num [windowFirstAngle, discrepancy_1_7_9]
    <;> ring
  simp only [windowFirstExp, phase, ha]

 theorem finite_first_harmonic_norm_gap :
    ‖∑ N ∈ Finset.Ico 4 (2 * 4), windowFirstExp 1 N 9‖ ≤ (21 / 25 : ℝ) * 4 := by
  have hpair : ‖windowFirstExp 1 7 9 + windowFirstExp 1 6 9‖ ≤
      5 * Real.pi / 64 := by
    rw [phase_7, phase_6]
    have heq : (67 * Real.pi / 64 : ℝ) =
        Real.pi / 8 + Real.pi - 5 * Real.pi / 64 := by ring
    rw [heq]
    have h := antipodal_pair_bound (Real.pi / 8) (5 * Real.pi / 64)
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 * Real.pi / 64)] using h
  have hfirst : ‖windowFirstExp 1 4 9 + windowFirstExp 1 5 9‖ ≤ 2 := by
    calc
      _ ≤ ‖windowFirstExp 1 4 9‖ + ‖windowFirstExp 1 5 9‖ := norm_add_le _ _
      _ = 2 := by norm_num
  have hset : Finset.Ico 4 (2 * 4) = {4, 5, 6, 7} := by decide
  have hsum : (∑ N ∈ Finset.Ico 4 (2 * 4), windowFirstExp 1 N 9) =
      (windowFirstExp 1 4 9 + windowFirstExp 1 5 9) +
      (windowFirstExp 1 7 9 + windowFirstExp 1 6 9) := by
    simp [hset, add_comm, add_left_comm, add_assoc]
  rw [hsum]
  have ht := norm_add_le (windowFirstExp 1 4 9 + windowFirstExp 1 5 9)
    (windowFirstExp 1 7 9 + windowFirstExp 1 6 9)
  have hpi := Real.pi_lt_four
  nlinarith

 theorem one_unconditional_norm_gap_instance :
    0 < (4 : ℕ) ∧ 16 * (2 * 4 + 1 + 9 + 2) ≤ 2 ^ 9 ∧
    ‖∑ N ∈ Finset.Ico 4 (2 * 4), windowFirstExp 1 N 9‖ ≤ (21 / 25 : ℝ) * 4 := by
  exact ⟨by decide, finite_room, finite_first_harmonic_norm_gap⟩
end
end ErdosProblems.Erdos249.TypeBReturnV8
