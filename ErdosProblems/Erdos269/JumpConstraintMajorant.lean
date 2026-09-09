import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Erdős #269: the three-consecutive-2-jump obstruction and the Q̃ algebra

The merged ordered list of positive `{2,3,5}`-powers cannot contain three
consecutive powers of two: between `2^e` and `2^{e+2}` there is always a
power of three.  That unique-factorisation fact is the only new arithmetic
input in the improved carry majorant

    Q̃(n) = (1210 n² + 9130 n + 18847) / 11979

relative to the geometric majorant `Q(n) = (n² + 8n + 18)/9` obtained by
using only `multiplier ≥ 2`.  The rational identities below check the
generating-function moments of the constrained weights and the comparison
`Q − Q̃ > 0`.  They do not by themselves bound the actual tail `X_a`; that
assembly is an ordinary proof in the note, using the checked shell
multiplicity bound.  Neither majorant weakens the window-escape producer,
which is already equivalent to irrationality on the whole quadratic family.

Nothing here proves irrationality of the `{2,3,5}` series.
-/

namespace ErdosProblems.Erdos269

/-- Between `2^e` and `2^{e+2}` there is a power of three. -/
theorem exists_three_power_strictly_between_two_powers (e : ℕ) :
    ∃ v, 2 ^ e < 3 ^ v ∧ 3 ^ v < 2 ^ (e + 2) := by
  refine ⟨Nat.log 3 (2 ^ e) + 1, ?lt, ?gt⟩
  · have h3 : 1 < 3 := by norm_num
    exact Nat.lt_pow_succ_log_self h3 (2 ^ e)
  · have hn : 2 ^ e ≠ 0 := (Nat.pow_pos (by norm_num : (0 : ℕ) < 2)).ne'
    have hle : 3 ^ Nat.log 3 (2 ^ e) ≤ 2 ^ e := Nat.pow_log_le_self 3 hn
    have hmul : 3 ^ (Nat.log 3 (2 ^ e) + 1) ≤ 3 * 2 ^ e := by
      rw [pow_succ, Nat.mul_comm]
      exact Nat.mul_le_mul_left 3 hle
    have h3lt4 : 3 * 2 ^ e < 4 * 2 ^ e :=
      Nat.mul_lt_mul_of_pos_right (by norm_num : 3 < 4)
        (Nat.pow_pos (by norm_num : (0 : ℕ) < 2))
    have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by
      calc
        4 * 2 ^ e = 2 ^ 2 * 2 ^ e := by norm_num
        _ = 2 ^ (2 + e) := (pow_add 2 2 e).symm
        _ = 2 ^ (e + 2) := by rw [Nat.add_comm]
    exact lt_of_le_of_lt hmul (h4 ▸ h3lt4)

/-- Consequently `2^e`, `2^{e+1}`, `2^{e+2}` cannot be three consecutive
elements of the merged positive `{2,3,5}`-power list. -/
theorem not_three_consecutive_two_powers (e : ℕ) :
    ∃ t, 2 ^ e < t ∧ t < 2 ^ (e + 2) ∧ ∃ v, t = 3 ^ v := by
  obtain ⟨v, hlo, hhi⟩ := exists_three_power_strictly_between_two_powers e
  exact ⟨3 ^ v, hlo, hhi, ⟨v, rfl⟩⟩

/-- Geometric (unconstrained) quadratic majorant. -/
def carryMajorantQ (n : ℕ) : ℚ :=
  ((n : ℚ) ^ 2 + 8 * n + 18) / 9

/-- Jump-constrained quadratic majorant. -/
def carryMajorantQtilde (n : ℕ) : ℚ :=
  (1210 * (n : ℚ) ^ 2 + 9130 * n + 18847) / 11979

def jumpWeightMoment0 : ℚ := 20 / 11
def jumpWeightMoment1 : ℚ := 170 / 121
def jumpWeightMoment2 : ℚ := 4694 / 1331

/-- The generating function `A(z) = (1 + z/2 + z²/6)/(1 − z³/12)` at `z = 1`. -/
theorem jumpGenerating_eval_one :
    ((1 : ℚ) + 1 / 2 + 1 / 6) / (1 - 1 / 12) = jumpWeightMoment0 := by
  unfold jumpWeightMoment0
  norm_num

/-- Logarithmic-derivative evaluation `(z A'(z))_{z=1}`. -/
theorem jumpGenerating_first_moment :
    let N : ℚ := 1 + 1 / 2 + 1 / 6
    let D : ℚ := 1 - 1 / 12
    let Np : ℚ := 1 / 2 + 1 / 3
    let Dp : ℚ := -1 / 4
    (Np * D - N * Dp) / (D * D) = jumpWeightMoment1 := by
  unfold jumpWeightMoment1
  norm_num

/-- Second-moment evaluation `(z (z A')')_{z=1}`. -/
theorem jumpGenerating_second_moment :
    let N : ℚ := 1 + 1 / 2 + 1 / 6
    let D : ℚ := 1 - 1 / 12
    let Np : ℚ := 1 / 2 + 1 / 3
    let Dp : ℚ := -1 / 4
    let Npp : ℚ := 1 / 3
    let Dpp : ℚ := -1 / 2
    let P : ℚ := Np * D - N * Dp
    let Pp : ℚ := Npp * D - N * Dpp
    let Q : ℚ := D * D
    let Qp : ℚ := 2 * D * Dp
    let Ap : ℚ := P / Q
    let App : ℚ := (Pp * Q - P * Qp) / (Q * Q)
    Ap + App = jumpWeightMoment2 := by
  unfold jumpWeightMoment2
  norm_num

/-- The displayed Q̃ polynomial is the 1/18-moment form. -/
theorem carryMajorantQtilde_eq_moments (n : ℕ) :
    carryMajorantQtilde n =
      (jumpWeightMoment0 * ((n : ℚ) + 3) ^ 2
        + 2 * jumpWeightMoment1 * ((n : ℚ) + 3)
        + jumpWeightMoment2) / 18 := by
  unfold carryMajorantQtilde jumpWeightMoment0 jumpWeightMoment1 jumpWeightMoment2
  field_simp
  ring

/-- Strict improvement over the unconstrained geometric majorant. -/
theorem carryMajorantQ_sub_Qtilde (n : ℕ) :
    carryMajorantQ n - carryMajorantQtilde n =
      (121 * (n : ℚ) ^ 2 + 1518 * n + 5111) / 11979 := by
  unfold carryMajorantQ carryMajorantQtilde
  field_simp
  ring

theorem carryMajorantQtilde_lt_Q (n : ℕ) :
    carryMajorantQtilde n < carryMajorantQ n := by
  have hdiff := carryMajorantQ_sub_Qtilde n
  have hpos : (0 : ℚ) < (121 * (n : ℚ) ^ 2 + 1518 * n + 5111) / 11979 := by
    apply div_pos
    · have hsq : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
      have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
      nlinarith
    · norm_num
  linarith

end ErdosProblems.Erdos269
