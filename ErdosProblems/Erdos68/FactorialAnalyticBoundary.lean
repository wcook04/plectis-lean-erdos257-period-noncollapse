import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic growth boundaries for factorial-gap denominators

The denominators `n! - 1` do not have quadratic successive growth, and their
`2^n`-th roots tend to one. These are the two growth obstructions stated in
the short Erdős #68 paper when comparing external fast-series criteria.
Neither limit decides irrationality of the factorial-gap series.
-/

namespace Erdos68

open Filter
open scoped Topology

private theorem tendsto_one_div_factorial :
    Tendsto (fun n : ℕ => 1 / (n.factorial : ℝ)) atTop (𝓝 0) := by
  simpa only [one_div] using
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop :
        Tendsto (fun n : ℕ => (n.factorial : ℝ)) atTop atTop)

private theorem tendsto_succ_div_factorial :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n.factorial : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one] using
      tendsto_pow_const_div_const_pow_of_one_lt 1 (r := 2) (by norm_num)
  have hf := FloorSemiring.tendsto_pow_div_factorial_atTop (2 : ℝ)
  have hprod : Tendsto (fun n : ℕ => (n : ℝ) / (n.factorial : ℝ))
      atTop (𝓝 0) := by
    convert hn.mul hf using 1
    · ext n
      have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
      have hfac0 : (n.factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp [hpow, hfac0]
    · norm_num
  convert hprod.add tendsto_one_div_factorial using 1
  · ext n
    rw [add_div]
  · norm_num

/-- The next factorial-gap denominator is negligible relative to the square
of the current one, excluding a positive quadratic-growth lower bound. -/
theorem tendsto_factorialGap_succ_div_sq :
    Tendsto (fun n : ℕ =>
      ((n + 1).factorial - 1 : ℝ) / ((n.factorial : ℝ) - 1) ^ 2)
      atTop (𝓝 0) := by
  have h :=
    (tendsto_succ_div_factorial.sub (tendsto_one_div_factorial.pow 2)).div
      ((tendsto_const_nhds.sub tendsto_one_div_factorial).pow 2)
      (by norm_num : (1 - (0 : ℝ)) ^ 2 ≠ 0)
  have hzero : Tendsto (fun n : ℕ =>
      (((n : ℝ) + 1) / (n.factorial : ℝ) -
          (1 / (n.factorial : ℝ)) ^ 2) /
        (1 - 1 / (n.factorial : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using h
  apply hzero.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hfac : (2 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast (show 2 ≤ n.factorial from
      (by simpa using Nat.factorial_le hn))
  have hf0 : (n.factorial : ℝ) ≠ 0 := by linarith
  have hgap : (n.factorial : ℝ) - 1 ≠ 0 := by linarith
  have hinv : 1 - 1 / (n.factorial : ℝ) ≠ 0 := by
    intro heq
    have : (n.factorial : ℝ) = 1 := by
      field_simp [hf0] at heq
      linarith
    linarith
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hf0, hgap, hinv]
  <;> ring

/-- The summable-error hypothesis in the all-positive fast-series criterion
fails: the absolute quadratic-growth errors converge to one, not zero. -/
theorem not_summable_abs_factorialGap_succ_div_sq_sub_one :
    ¬ Summable (fun n : ℕ =>
      |((n + 1).factorial - 1 : ℝ) / ((n.factorial : ℝ) - 1) ^ 2 - 1|) := by
  intro hsum
  have hlimit : Tendsto (fun n : ℕ =>
      |((n + 1).factorial - 1 : ℝ) / ((n.factorial : ℝ) - 1) ^ 2 - 1|)
      atTop (𝓝 1) := by
    simpa only [Real.norm_eq_abs, zero_sub, abs_neg, abs_one] using
      (tendsto_factorialGap_succ_div_sq.sub_const 1).norm
  have hcontr : (1 : ℝ) = 0 :=
    tendsto_nhds_unique hlimit hsum.tendsto_atTop_zero
  exact one_ne_zero hcontr

private theorem log_factorialGap_le_sq {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ Real.log ((n.factorial : ℝ) - 1) ∧
      Real.log ((n.factorial : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by
  have hfac : (2 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast (show 2 ≤ n.factorial from
      (by simpa using Nat.factorial_le hn))
  have hgap : 0 < (n.factorial : ℝ) - 1 := by linarith
  have hpow : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  constructor
  · exact Real.log_nonneg (by linarith)
  · calc
      Real.log ((n.factorial : ℝ) - 1) ≤ Real.log ((n : ℝ) ^ n) :=
        Real.log_le_log hgap (by linarith)
      _ = (n : ℝ) * Real.log (n : ℝ) := Real.log_pow _ _
      _ ≤ (n : ℝ) ^ 2 := by
        have := Real.log_le_self (show (0 : ℝ) ≤ n by positivity)
        nlinarith [mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ n by positivity)]

/-- The logarithm of a factorial-gap denominator is negligible at dyadic
scale; the elementary bound `log(n! - 1) ≤ n²` suffices. -/
theorem tendsto_log_factorialGap_div_two_pow :
    Tendsto (fun n : ℕ => Real.log ((n.factorial : ℝ) - 1) / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (g := fun n : ℕ => (n : ℝ) ^ 2 / (2 : ℝ) ^ n)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (log_factorialGap_le_sq hn).1 (by positivity)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_le_div_of_nonneg_right (log_factorialGap_le_sq hn).2 (by positivity)
  · exact tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)

/-- Factorial-gap denominators fail the doubly exponential root-growth
hypothesis: their `2^n`-th roots converge to one. -/
theorem tendsto_factorialGap_rpow_one_div_two_pow :
    Tendsto (fun n : ℕ => ((n.factorial : ℝ) - 1) ^ (1 / (2 : ℝ) ^ n))
      atTop (𝓝 1) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    tendsto_log_factorialGap_div_two_pow
  have hexp : Tendsto (fun n : ℕ =>
      Real.exp (Real.log ((n.factorial : ℝ) - 1) / (2 : ℝ) ^ n))
      atTop (𝓝 1) := by simpa using h
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hfac : (2 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast (show 2 ≤ n.factorial from
      (by simpa using Nat.factorial_le hn))
  rw [Real.rpow_def_of_pos (by linarith : 0 < (n.factorial : ℝ) - 1)]
  simp only [div_eq_mul_inv, one_mul]

end Erdos68
