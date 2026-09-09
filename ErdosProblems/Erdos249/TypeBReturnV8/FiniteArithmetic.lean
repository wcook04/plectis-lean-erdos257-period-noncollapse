import Erdos249257.FirstHarmonicPivot
import Mathlib.Tactic

/-! UNRUN candidate. All arithmetic decisions below are intended to be kernel
reduction or proof-producing tactics; no native_decide and no custom axioms. -/
namespace ErdosProblems.Erdos249.TypeBReturnV8
open Erdos249257.TotientTailPeriodKiller

 theorem discrepancy_1_4_9 : windowDiscrepancy 1 4 9 = -62 := by decide
 theorem discrepancy_1_5_9 : windowDiscrepancy 1 5 9 = 902 := by decide
 theorem discrepancy_1_6_9 : windowDiscrepancy 1 6 9 = -244 := by decide
 theorem discrepancy_1_7_9 : windowDiscrepancy 1 7 9 = 544 := by decide
 theorem finite_room : 16 * (2 * 4 + 1 + 9 + 2) ≤ 2 ^ 9 := by decide
 theorem four_certified_kills : certifiedKill 1 4 9 ∧ certifiedKill 1 5 9 ∧
     certifiedKill 1 6 9 ∧ certifiedKill 1 7 9 := by decide

/-- The finite denominator lemma underlying both retained and new Farey
certificates. Positivity of s is a consequence, not an extra hypothesis. -/
theorem farey_denominator_bound (a b c d r s : ℤ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hdet : b * c - a * d = 1)
    (hl : 0 < r * b - a * s) (hu : 0 < c * s - r * d) :
    b + d ≤ s := by
  have hl' : 1 ≤ r * b - a * s := by omega
  have hu' : 1 ≤ c * s - r * d := by omega
  have hidentity : s = b * (c * s - r * d) + d * (r * b - a * s) := by
    calc
      s = (b * c - a * d) * s := by rw [hdet, one_mul]
      _ = _ := by ring
  have h₁ := mul_le_mul_of_nonneg_left hu' hb
  have h₂ := mul_le_mul_of_nonneg_left hl' hd
  nlinarith

/-- Exactly the finite run-threshold correction: X transitions use X+1 digits
and C+1 runs. The rounded constant 9.1 is not an equivalence. -/
theorem run_length_counterexample :
    (1001 / 110 : ℚ) = 91 / 10 ∧ (109 : ℚ) < (11 / 100) * 1000 := by
  norm_num

theorem run_threshold_iff (X C : ℝ) (hC : 0 ≤ C) (hX : 0 ≤ X) :
    (X + 1) / (C + 1) ≤ 100 * (X + 1) / (11 * X + 100) ↔
      11 * X ≤ 100 * C := by
  have hC1 : 0 < C + 1 := by linarith
  have hD : 0 < 11 * X + 100 := by linarith
  have hXp : 0 < X + 1 := by linarith
  rw [div_le_div_iff₀ hC1 hD]
  rw [show (100 * (X + 1)) * (C + 1) = (X + 1) * (100 * C + 100) by ring]
  rw [mul_le_mul_iff_of_pos_left hXp]
  constructor <;> intro h <;> linarith
end ErdosProblems.Erdos249.TypeBReturnV8
