import ErdosProblems.Erdos269.NormalizedStateWidth
import Mathlib.Tactic

/-!
# Round 7: the literal `8640 / 343` shell bound

Target: the bound in short-note `res:actual-orbit`.  The supplied bound `90`
does not prove this sharper displayed constant.  We retain the actual shell
mass, prove its `8^{-a}` estimate, and sum the resulting majorant exactly.
This is NOT a proof of the separate long-record `Q(n_a)` bound.

Validation: authored, not compiled in this return. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators

/-- The lower cubic height estimate uses all three actual prime channels. -/
theorem cube_lt_thirty_height235 (x : ℕ) :
    x ^ 3 < 30 * threePrimeHeight 2 3 5 x := by
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) x
  have h3 := Nat.lt_pow_succ_log_self (b := 3) (by norm_num) x
  have h5 := Nat.lt_pow_succ_log_self (b := 5) (by norm_num) x
  have h := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt h2 h3) h5
  calc
    x ^ 3 = (x * x) * x := by ring
    _ < (2 ^ (Nat.log 2 x + 1) * 3 ^ (Nat.log 3 x + 1)) *
        5 ^ (Nat.log 5 x + 1) := h
    _ = 30 * threePrimeHeight 2 3 5 x := by
      simp only [threePrimeHeight, pow_succ]
      ring

/-- A convenient exact power identity, kept on natural numbers. -/
theorem eight_pow_eq_two_pow_cube (a : ℕ) :
    (8 : ℕ) ^ a = ((2 : ℕ) ^ a) ^ 3 := by
  calc
    (8 : ℕ) ^ a = ((2 : ℕ) ^ 3) ^ a := by norm_num
    _ = 2 ^ (3 * a) := (pow_mul 2 3 a).symm
    _ = 2 ^ (a * 3) := by rw [Nat.mul_comm 3 a]
    _ = ((2 : ℕ) ^ a) ^ 3 := pow_mul 2 a 3

/-- Every summand in shell `a` is at most `30 / 8^a`. -/
theorem inverse_height_le_shell_geometric (a x : ℕ) (hx : 2 ^ a ≤ x) :
    ((threePrimeHeight 2 3 5 x : ℕ) : ℝ)⁻¹ ≤ 30 / (8 : ℝ) ^ a := by
  have hlow : (8 : ℕ) ^ a ≤ x ^ 3 := by
    rw [eight_pow_eq_two_pow_cube]
    exact Nat.pow_le_pow_left hx 3
  have hnat : (8 : ℕ) ^ a < 30 * threePrimeHeight 2 3 5 x :=
    lt_of_le_of_lt hlow (cube_lt_thirty_height235 x)
  have hreal : (8 : ℝ) ^ a < 30 * (threePrimeHeight 2 3 5 x : ℝ) := by
    exact_mod_cast hnat
  have hH : (0 : ℝ) < (threePrimeHeight 2 3 5 x : ℝ) :=
    threePrimeHeight235_cast_pos x
  have h8 : (0 : ℝ) < (8 : ℝ) ^ a := by positivity
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hH h8).mpr
  nlinarith

/-- Stronger geometric shell estimate than the coarse summability majorant. -/
theorem shellMass_le_thirty_square_div_eight_pow (a : ℕ) :
    dyadicShellMassR235 a ≤ 30 * ((a + 1 : ℕ) : ℝ) ^ 2 / (8 : ℝ) ^ a := by
  have hrepr : dyadicShellMassR235 a =
      ∑ e ∈ dyadicSmoothShell235 a,
        ((threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℕ) : ℝ)⁻¹ := by
    simp [dyadicShellMassR235, dyadicShellMassQ235]
  rw [hrepr]
  calc
    (∑ e ∈ dyadicSmoothShell235 a,
      ((threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℕ) : ℝ)⁻¹)
        ≤ ∑ _e ∈ dyadicSmoothShell235 a, 30 / (8 : ℝ) ^ a := by
          apply Finset.sum_le_sum
          intro e he
          exact inverse_height_le_shell_geometric a _
            (mem_dyadicSmoothShell235_iff.mp he).1
    _ = (dyadicSmoothShell235 a).card * (30 / (8 : ℝ) ^ a) := by simp
    _ ≤ (((a + 1 : ℕ) : ℝ) ^ 2) * (30 / (8 : ℝ) ^ a) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast dyadicSmoothShell235_card_le_square a
    _ = 30 * ((a + 1 : ℕ) : ℝ) ^ 2 / (8 : ℝ) ^ a := by ring

/-- The dyadic endpoint height has the complementary upper bound `8^a`. -/
theorem dyadic_height_le_eight_pow (a : ℕ) :
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) ≤ (8 : ℝ) ^ a := by
  have hnat := threePrimeHeight_le_cube 2 3 5 (2 ^ a) (by positivity)
  rw [← eight_pow_eq_two_pow_cube] at hnat
  exact_mod_cast hnat

/-- Termwise normalised-shell comparison; no limit argument is hidden here. -/
theorem normalised_shell_le_eighth_majorant (a n : ℕ) :
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * dyadicShellMassR235 (a + n) ≤
      15 * ((a + 1 : ℕ) : ℝ) ^ 2 *
        (((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 8 : ℝ) ^ n) := by
  have hsplit : ((a + n + 1 : ℕ) : ℝ) ≤
      ((a + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a),
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsq : ((a + n + 1 : ℕ) : ℝ) ^ 2 ≤
      (((a + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hsplit 2
  calc
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * dyadicShellMassR235 (a + n)
      ≤ ((8 : ℝ) ^ a / 2) *
          (30 * ((a + n + 1 : ℕ) : ℝ) ^ 2 / (8 : ℝ) ^ (a + n)) := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right (dyadic_height_le_eight_pow a) (by norm_num)
        · exact shellMass_le_thirty_square_div_eight_pow (a + n)
        · exact dyadicShellMassR235_nonneg _
        · positivity
    _ = 15 * ((a + n + 1 : ℕ) : ℝ) ^ 2 * (1 / 8 : ℝ) ^ n := by
      rw [pow_add, one_div_pow]
      field_simp <;> ring
    _ ≤ 15 * (((a + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2 *
        (1 / 8 : ℝ) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 15 * ((a + 1 : ℕ) : ℝ) ^ 2 *
        (((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 8 : ℝ) ^ n) := by ring

/-- Exact value of the geometric moment used on the page. -/
theorem hasSum_succ_square_eighth :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 8 : ℝ) ^ n)
      (576 / 343 : ℝ) := by
  have h := hasSum_succ_sq_mul_geometric (r := (1 / 8 : ℝ)) (by norm_num)
  convert h using 1 <;> norm_num

/-- The displayed sharper bound `8640/343`, for the actual infinite tail. -/
theorem trueNormalizedState_le_8640_div_343 (a : ℕ) :
    trueNormalizedState a ≤ (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 := by
  have hs : Summable (fun n : ℕ => dyadicShellMassR235 (a + n)) :=
    summable_dyadicShellMassR235.comp_injective fun _ _ h => Nat.add_left_cancel h
  have hl := hs.mul_left ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2)
  have hr := hasSum_succ_square_eighth.mul_left (15 * ((a + 1 : ℕ) : ℝ) ^ 2)
  have hstate : trueNormalizedState a =
      ∑' n : ℕ, (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 *
        dyadicShellMassR235 (a + n) := by
    unfold trueNormalizedState dyadicNormalizedTailStateR235 dyadicShellTsumTailR235
    rw [tsum_mul_left]
  rw [hstate]
  calc
    (∑' n : ℕ, (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 *
      dyadicShellMassR235 (a + n))
      ≤ ∑' n : ℕ, 15 * ((a + 1 : ℕ) : ℝ) ^ 2 *
          (((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 8 : ℝ) ^ n) :=
        hl.tsum_le_tsum (normalised_shell_le_eighth_majorant a) hr.summable
    _ = 15 * ((a + 1 : ℕ) : ℝ) ^ 2 * (576 / 343 : ℝ) := hr.tsum_eq
    _ = (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 := by ring

/-- Positivity and both exact constants as a single paper-facing statement. -/
theorem actual_state_sharp_bounds (a : ℕ) :
    0 < trueNormalizedState a ∧
    trueNormalizedState a ≤ (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 ∧
    (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 <
      90 * ((a + 1 : ℕ) : ℝ) ^ 2 := by
  refine ⟨trueNormalizedState_pos a, trueNormalizedState_le_8640_div_343 a, ?_⟩
  have hpos : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) ^ 2 := by positivity
  exact mul_lt_mul_of_pos_right (by norm_num) hpos

end ErdosProblems.Erdos269.PaperR7
