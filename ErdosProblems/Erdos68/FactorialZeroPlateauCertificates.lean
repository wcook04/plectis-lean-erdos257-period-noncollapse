import ErdosProblems.Erdos68.FactorialGapPlateauCore
import Mathlib.Tactic.NormNum

/-!
# Erdős #68: exact-index plateau certificates

Heavy `norm_num` certificates at indices `5`, `11`, `51`, `60`, `64`, and
`67`, together with the denominator lower bounds they support.  Kept separate
so launch entries that only need the carry recurrence avoid CI memory pressure.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- The first nontrivial exact missed-prime certificate. -/
theorem five_not_dvd_strictFacTop_factorialGapPrefix :
    ¬(5 : ℤ) ∣
      strictFacTop ((factorialGapPrefix 5 : ℚ) : ℝ) 5 := by
  have hprefix :
      factorialGapPrefix 5 = (17132 : ℚ) / 13685 := by
    norm_num [factorialGapPrefix, Finset.sum_Icc_succ_top]
  rw [strictFacTop_ratCast, hprefix]
  norm_num [strictFacTopRat, Rat.floor_def']

/-- An axiom-free exact certificate at the larger prime `11`. -/
theorem eleven_not_dvd_strictFacTop_factorialGapPrefix :
    ¬(11 : ℤ) ∣
      strictFacTop ((factorialGapPrefix 11 : ℚ) : ℝ) 11 := by
  have hprefix :
      factorialGapPrefix 11 =
        (14646288077549563211101117292014 : ℚ) /
          11684326001412031358992441685845 := by
    norm_num [factorialGapPrefix, Finset.sum_Icc_succ_top]
  rw [strictFacTop_ratCast, hprefix]
  norm_num [strictFacTopRat, Rat.floor_def']

/-- An exact composite-index certificate immediately before the first
observed unit carry. -/
theorem fifty_one_not_dvd_strictFacTop_factorialGapPrefix :
    ¬(51 : ℤ) ∣
      strictFacTop ((factorialGapPrefix 51 : ℚ) : ℝ) 51 := by
  rw [strictFacTop_ratCast]
  norm_num [strictFacTopRat, factorialGapPrefix,
    Finset.sum_Icc_succ_top, Rat.floor_def']

/-- A larger exact composite-index certificate; the corresponding carry at
index `60` is zero rather than one. -/
theorem sixty_not_dvd_strictFacTop_factorialGapPrefix :
    ¬(60 : ℤ) ∣
      strictFacTop ((factorialGapPrefix 60 : ℚ) : ℝ) 60 := by
  rw [strictFacTop_ratCast]
  norm_num [strictFacTopRat, factorialGapPrefix,
    Finset.sum_Icc_succ_top, Rat.floor_def']

/-- A larger direct certificate at index `64`; the exact carry there is
`51`, again excluding the unit-carry pattern forced by rationality. -/
theorem sixty_four_not_dvd_strictFacTop_factorialGapPrefix :
    ¬(64 : ℤ) ∣
      strictFacTop ((factorialGapPrefix 64 : ℚ) : ℝ) 64 := by
  rw [strictFacTop_ratCast]
  norm_num [strictFacTopRat, factorialGapPrefix,
    Finset.sum_Icc_succ_top, Rat.floor_def']

/-- Direct exact computation at the prime index `67` excludes the
excluding the prime-divisibility pattern forced by rationality there. -/
theorem sixty_seven_not_dvd_strictFacTop_factorialGapPrefix :
    ¬(67 : ℤ) ∣
      strictFacTop ((factorialGapPrefix 67 : ℚ) : ℝ) 67 := by
  rw [strictFacTop_ratCast]
  norm_num [strictFacTopRat, factorialGapPrefix,
    Finset.sum_Icc_succ_top, Rat.floor_def']

/-- Consequently, every displayed rational representation of the Erdős #68
series has denominator at least `11`. -/
theorem eleven_le_rational_denominator
    {q : ℕ} {a : ℤ}
    (hq : 0 < q)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    11 ≤ q :=
  rational_denominator_ge_of_prime_miss
    (by norm_num) hq
    eleven_not_dvd_strictFacTop_factorialGapPrefix hseries
/-- The exact prefix computation at index `51` is a non-unit carry. -/
theorem factorialGapStepCarry_fifty_one_ne_one :
    factorialGapStepCarry 51 ≠ 1 := by
  intro hcarry
  apply fifty_one_not_dvd_strictFacTop_factorialGapPrefix
  have hrec :=
    strictFacTop_factorialGapPrefix_step (m := 51) (by norm_num)
  rw [hcarry] at hrec
  use strictFacTop ((factorialGapPrefix 50 : ℚ) : ℝ) 50
  rw [hrec]
  ring

/-- The exact prefix computation at index `60` is also a non-unit carry. -/
theorem factorialGapStepCarry_sixty_ne_one :
    factorialGapStepCarry 60 ≠ 1 := by
  intro hcarry
  apply sixty_not_dvd_strictFacTop_factorialGapPrefix
  have hrec :=
    strictFacTop_factorialGapPrefix_step (m := 60) (by norm_num)
  rw [hcarry] at hrec
  use strictFacTop ((factorialGapPrefix 59 : ℚ) : ℝ) 59
  rw [hrec]
  ring

/-- Every displayed rational representation of the Erdős #68
series has denominator at least `51`. -/
theorem fifty_one_le_rational_denominator
    {q : ℕ} {a : ℤ}
    (hq : 0 < q)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    51 ≤ q :=
  rational_denominator_ge_of_nonunit_carry
    (by norm_num) factorialGapStepCarry_fifty_one_ne_one hq hseries

/-- The index-`60` certificate strengthens the universal lower bound for
every displayed rational denominator from `51` to `60`. -/
theorem sixty_le_rational_denominator
    {q : ℕ} {a : ℤ}
    (hq : 0 < q)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    60 ≤ q :=
  rational_denominator_ge_of_nonunit_carry
    (by norm_num) factorialGapStepCarry_sixty_ne_one hq hseries

/-- The prime-index certificate at `67` gives the largest universal lower
bound for a displayed rational denominator proved in this module. -/
theorem sixty_seven_le_rational_denominator
    {q : ℕ} {a : ℤ}
    (hq : 0 < q)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    67 ≤ q :=
  rational_denominator_ge_of_prime_miss
    (by norm_num) hq
    sixty_seven_not_dvd_strictFacTop_factorialGapPrefix hseries

/-- The index-`60` certificate in its divisibility form: no displayed
rational denominator of the series divides `59!`.

`sixty_le_rational_denominator` extracts only `60 ≤ q` from the same
certificate.  That leaves `59!` itself, and every other `59`-smooth
denominator, unexcluded; this statement removes all of them. -/
theorem rational_denominator_not_dvd_fiftynine_factorial
    {q : ℕ} {a : ℤ}
    (hq : 0 < q)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    ¬ (q ∣ Nat.factorial 59) := by
  have h :=
    rational_denominator_not_dvd_pred_factorial_of_nonunit_carry
      (m := 60) (by norm_num)
      factorialGapStepCarry_sixty_ne_one hq hseries
  simpa using h

end ErdosProblems.Erdos68
