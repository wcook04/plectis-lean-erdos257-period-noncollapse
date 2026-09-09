import Mathlib

/-!
# Complete numerical specialization of the 71/10 and 57/10 budgets

AUTHORED / UNRUN. In particular, no logarithm inequality is accepted as a
hypothesis. The upper bound for log(40/3) uses ten elementary log bounds
and Mathlib's existing certified bound for log 2; it needs no new series API.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.ConnectorR18
open scoped BigOperators

def lowConstant : ℝ := (60 / 289) * (283 / 200)
def highConstant : ℝ := (161 / 100) + (1375 / 364)
def rationalConstant : ℝ := 66517563 / 9392500

theorem lowConstant_nonneg : 0 ≤ lowConstant := by norm_num [lowConstant]
theorem highConstant_nonneg : 0 ≤ highConstant := by norm_num [highConstant]
theorem lowConstant_value : lowConstant = 849 / 2890 := by norm_num [lowConstant]

theorem rationalConstant_identity :
    lowConstant + (63 / 50 : ℝ) * highConstant = rationalConstant := by
  norm_num [lowConstant, highConstant, rationalConstant]

theorem rationalConstant_lt : rationalConstant < (71 / 10 : ℝ) := by
  norm_num [rationalConstant]

theorem openConstant_identity :
    lowConstant + highConstant = (3735276 / 657475 : ℝ) := by
  norm_num [lowConstant, highConstant]

theorem openConstant_lt : lowConstant + highConstant < (57 / 10 : ℝ) := by
  norm_num [lowConstant, highConstant]

theorem sqrt_two_lt : Real.sqrt 2 < (283 / 200 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem log_two_lower : (104 / 125 : ℝ) ^ 2 < Real.log 2 := by
  exact lt_trans (by norm_num) Real.log_two_gt_d9

theorem sqrt_log_two_lower : (104 / 125 : ℝ) < Real.sqrt (Real.log 2) := by
  have hp : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (Real.log 2)
  nlinarith [log_two_lower]

theorem pi_upper : Real.pi < (22 / 7 : ℝ) := by
  exact lt_trans Real.pi_lt_d6 (by norm_num)

/-- A telescoping factorization bounds log(5/6) above by a rational sum.
The strict final comparison has positive rational slack. -/
theorem log_forty_thirds_upper : Real.log (40 / 3 : ℝ) < (161 / 100 : ℝ) ^ 2 := by
  have h50 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 50 / 51)
    (by norm_num : (50 / 51 : ℝ) ≠ 1)).le
  have h51 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 51 / 52)
    (by norm_num : (51 / 52 : ℝ) ≠ 1)).le
  have h52 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 52 / 53)
    (by norm_num : (52 / 53 : ℝ) ≠ 1)).le
  have h53 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 53 / 54)
    (by norm_num : (53 / 54 : ℝ) ≠ 1)).le
  have h54 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 54 / 55)
    (by norm_num : (54 / 55 : ℝ) ≠ 1)).le
  have h55 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 55 / 56)
    (by norm_num : (55 / 56 : ℝ) ≠ 1)).le
  have h56 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 56 / 57)
    (by norm_num : (56 / 57 : ℝ) ≠ 1)).le
  have h57 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 57 / 58)
    (by norm_num : (57 / 58 : ℝ) ≠ 1)).le
  have h58 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 58 / 59)
    (by norm_num : (58 / 59 : ℝ) ≠ 1)).le
  have h59 := (Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 59 / 60)
    (by norm_num : (59 / 60 : ℝ) ≠ 1)).le
  have hfactor : (5 / 6 : ℝ) = (50 / 51) * (51 / 52) * (52 / 53) * (53 / 54) * (54 / 55) * (55 / 56) * (56 / 57) * (57 / 58) * (58 / 59) * (59 / 60) := by norm_num
  have hsum : Real.log (5 / 6 : ℝ) =
      Real.log (50 / 51 : ℝ) + Real.log (51 / 52 : ℝ) + Real.log (52 / 53 : ℝ) + Real.log (53 / 54 : ℝ) + Real.log (54 / 55 : ℝ) + Real.log (55 / 56 : ℝ) + Real.log (56 / 57 : ℝ) + Real.log (57 / 58 : ℝ) + Real.log (58 / 59 : ℝ) + Real.log (59 / 60 : ℝ) := by
    rw [hfactor]
    repeat rw [Real.log_mul (by norm_num) (by norm_num)]
  have hid : Real.log (40 / 3 : ℝ) = 4 * Real.log 2 + Real.log (5 / 6 : ℝ) := by
    rw [show (40 / 3 : ℝ) = (2 : ℝ) ^ (4 : ℕ) * (5 / 6) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have htwo := Real.log_two_lt_d9
  rw [hid, hsum]
  norm_num at h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 ⊢
  linarith

theorem sqrt_log_forty_thirds_upper :
    Real.sqrt (Real.log (40 / 3 : ℝ)) < (161 / 100 : ℝ) := by
  have hp : 0 ≤ Real.log (40 / 3 : ℝ) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 40 / 3)).le
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (Real.log (40 / 3 : ℝ))
  nlinarith [log_forty_thirds_upper]

theorem boundary_squared_constant :
    Real.pi ^ 2 / Real.log 2 ≤ (1375 / 364 : ℝ) ^ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hl).mpr
  have hp : Real.pi ^ 2 ≤ (22 / 7 : ℝ) ^ 2 := by
    nlinarith [pi_upper, Real.pi_pos]
  have hh := mul_le_mul_of_nonneg_left log_two_lower.le
    (show (0 : ℝ) ≤ (1375 / 364 : ℝ) ^ 2 by positivity)
  nlinarith

theorem pi_div_sqrt_log_two_upper :
    Real.pi / Real.sqrt (Real.log 2) < (1375 / 364 : ℝ) := by
  have hd : 0 < Real.sqrt (Real.log 2) := by
    linarith [sqrt_log_two_lower]
  apply (div_lt_iff₀ hd).mpr
  nlinarith [pi_upper, sqrt_log_two_lower]

theorem two_rpow_one_third_lt : (2 : ℝ) ^ ((1 : ℝ) / 3) < 63 / 50 := by
  have hc : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = 2 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_natCast]
  apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 63 / 50)
  rw [hc]
  norm_num

theorem one_div_natCast_le_third {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) / (n : ℝ) ≤ 1 / 3 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ) := by linarith
  apply (div_le_iff₀ hp).mpr
  linarith

theorem two_rpow_degree_lt {n : ℕ} (hn : 3 ≤ n) :
    (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) < 63 / 50 := by
  exact lt_of_le_of_lt
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (one_div_natCast_le_third hn))
    two_rpow_one_third_lt

theorem top_scale_le {n : ℕ} {μ : ℝ} (hn : 3 ≤ n) (hμ : 0 ≤ μ) :
    (2 * μ) ^ ((1 : ℝ) / (n : ℝ)) ≤
      (63 / 50 : ℝ) * μ ^ ((1 : ℝ) / (n : ℝ)) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hμ]
  exact mul_le_mul_of_nonneg_right (two_rpow_degree_lt hn).le (Real.rpow_nonneg hμ _)

theorem small_scale_le_one {n : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hhalf : μ ≤ 1 / 2) :
    μ ^ ((1 : ℝ) / (n : ℝ)) ≤ 1 ∧ (2 * μ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 1 := by
  have he : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  constructor
  · exact Real.rpow_le_one hμ (by linarith) he
  · exact Real.rpow_le_one (by positivity) (by linarith) he

/-- The exact CF expression, not just its already-rationalized constant. -/
def cfCoefficient (n : ℕ) : ℝ :=
  Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 +
    (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) *
      (Real.sqrt (Real.log (40 / 3 : ℝ)) + Real.pi / Real.sqrt (Real.log 2))

theorem cfCoefficient_le_rational {n : ℕ} (hn : 3 ≤ n) :
    cfCoefficient n ≤ rationalConstant := by
  have hlo : Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 ≤ lowConstant := by
    norm_num [lowConstant]
    nlinarith [sqrt_two_lt]
  have hh : Real.sqrt (Real.log (40 / 3 : ℝ)) +
      Real.pi / Real.sqrt (Real.log 2) ≤ highConstant := by
    dsimp [highConstant]
    linarith [sqrt_log_forty_thirds_upper, pi_div_sqrt_log_two_upper]
  have hpow : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hprod := mul_le_mul_of_nonneg_left hh hpow
  have hprod' := mul_le_mul_of_nonneg_right (two_rpow_degree_lt hn).le
    highConstant_nonneg
  unfold cfCoefficient
  rw [← rationalConstant_identity]
  exact add_le_add hlo (hprod.trans hprod')

theorem cfCoefficient_lt_seventy_one_tenths {n : ℕ} (hn : 3 ≤ n) :
    cfCoefficient n < (71 / 10 : ℝ) :=
  (cfCoefficient_le_rational hn).trans_lt rationalConstant_lt

/-- The old coefficientwise single-saddle bound at S=4/3 is <9/2.
This is a numerical result, not an inverse-branch existence theorem. -/
theorem separatedCoefficient_four_thirds {n : ℕ} (hn : 3 ≤ n) :
    2 * (1 + (4 / 3 : ℝ)) ^ ((1 : ℝ) / (n : ℝ)) *
      Real.sqrt (Real.log ((4 / 3 : ℝ) / (4 / 3 - 1))) < 9 / 2 := by
  have hcube : ((7 / 3 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = 7 / 3 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 7 / 3)]
    norm_num [Real.rpow_natCast]
  have hthird : (7 / 3 : ℝ) ^ ((1 : ℝ) / 3) < 3 / 2 := by
    apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [hcube]
    norm_num
  have hpow : (7 / 3 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) < 3 / 2 :=
    lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (one_div_natCast_le_third hn)) hthird
  have hlog : Real.log 4 < (3 / 2 : ℝ) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hs : Real.sqrt (Real.log 4) < (3 / 2 : ℝ) := by
    have he := Real.sq_sqrt ((Real.log_pos (by norm_num : (1 : ℝ) < 4)).le)
    nlinarith [Real.sqrt_nonneg (Real.log 4)]
  have hnonneg : 0 ≤ (7 / 3 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_right hpow.le (Real.sqrt_nonneg (Real.log 4))
  have hmul0 := mul_lt_mul_of_pos_left hs (show (0 : ℝ) < 3 / 2 by norm_num)
  have hmul' : (3 / 2 : ℝ) * Real.sqrt (Real.log 4) < 9 / 4 := by
    convert hmul0 using 1 <;> norm_num
  have hprod : (7 / 3 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * Real.sqrt (Real.log 4) < 9 / 4 :=
    hmul.trans_lt hmul'
  rw [show 1 + (4 / 3 : ℝ) = 7 / 3 by norm_num,
    show (4 / 3 : ℝ) / (4 / 3 - 1) = 4 by norm_num]
  calc
    2 * (7 / 3 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * Real.sqrt (Real.log 4) =
        2 * ((7 / 3 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * Real.sqrt (Real.log 4)) := by ring
    _ < 2 * (9 / 4 : ℝ) := mul_lt_mul_of_pos_left hprod (by norm_num)
    _ = 9 / 2 := by norm_num

end ErdosProblems.Erdos1041.ConnectorR18
