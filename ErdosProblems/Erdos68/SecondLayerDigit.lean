import ErdosProblems.Erdos68.FactorialGapPlateauCore

/-!
# Erdős #68: the exact finite second-layer digit

The elementary split

`1 / (n! - 1) = 1 / n! + 1 / (n! * (n! - 1))`

separates the factorial-gap prefix into the factorial expansion of `e - 2`
and a faster-decaying second layer.  This file proves the exact digit law for
the *finite* second-layer prefix:

`digit_m(prefix₂ m) = m - 1 - factorialGapStepCarry m`.

Passing from that finite prefix to the infinite second-layer sum requires a
separate floor-stability hypothesis at scales `m!` and `(m-1)!`.  Keeping that
hypothesis explicit prevents the invalid inference that a positive tail of
scaled size less than one can never cross the next integer.

The file also records the correct rational factorial-digit boundary: rational
numbers have eventually zero canonical digits, so they cannot have an
eventually maximal canonical tail.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- Finite factorial-expansion prefix `sum_{2 <= n <= m} 1 / n!`. -/
def factorialExpPrefix (m : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 2 m, 1 / (n.factorial : ℚ)

/-- Finite second layer `sum_{2 <= n <= m} 1 / (n! (n! - 1))`. -/
def factorialGapSecondLayerPrefix (m : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 2 m,
    1 / ((n.factorial : ℚ) * ((n.factorial : ℚ) - 1))

/-- The factorial prefix scaled to an integer at level `m!`. -/
def factorialExpScaled (m : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 m, m.factorial / n.factorial

/-- The floor of the finite second layer at factorial scale `m!`. -/
def secondLayerPrefixFloor (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℚ) * factorialGapSecondLayerPrefix m⌋

/-- The mixed-radix digit made from two consecutive finite-prefix floors. -/
def secondLayerPrefixDigit (m : ℕ) : ℤ :=
  secondLayerPrefixFloor m - (m : ℤ) * secondLayerPrefixFloor (m - 1)

/-- Termwise elementary decomposition of a factorial-gap reciprocal. -/
theorem one_div_factorial_sub_one_eq_exp_add_second
    {n : ℕ} (hn : 2 ≤ n) :
    1 / ((n.factorial : ℚ) - 1) =
      1 / (n.factorial : ℚ) +
        1 / ((n.factorial : ℚ) * ((n.factorial : ℚ) - 1)) := by
  have hfac : (1 : ℕ) < n.factorial := Nat.one_lt_factorial.mpr hn
  have hn0 : (n.factorial : ℚ) ≠ 0 := by positivity
  have hn1 : (n.factorial : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < n.factorial := by exact_mod_cast hfac
    linarith
  field_simp [hn0, hn1]
  ring

/-- Exact decomposition of every finite factorial-gap prefix. -/
theorem factorialGapPrefix_eq_exp_add_second (m : ℕ) :
    factorialGapPrefix m =
      factorialExpPrefix m + factorialGapSecondLayerPrefix m := by
  unfold factorialGapPrefix factorialExpPrefix factorialGapSecondLayerPrefix
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  exact one_div_factorial_sub_one_eq_exp_add_second (Finset.mem_Icc.mp hn).1

/-- Scaling the finite factorial-expansion prefix by `m!` gives the displayed
natural-number sum of exact quotients. -/
theorem factorial_mul_expPrefix_eq_scaled (m : ℕ) :
    (m.factorial : ℚ) * factorialExpPrefix m = factorialExpScaled m := by
  unfold factorialExpPrefix factorialExpScaled
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
  have hdvd : n.factorial ∣ m.factorial := Nat.factorial_dvd_factorial hnm
  have hn0 : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [Nat.cast_div hdvd hn0]
  field_simp

/-- Adding the endpoint to the finite factorial-expansion prefix contributes
exactly `1 / m!`. -/
theorem factorialExpPrefix_eq_prev_add
    {m : ℕ} (hm : 2 ≤ m) :
    factorialExpPrefix m =
      factorialExpPrefix (m - 1) + 1 / (m.factorial : ℚ) := by
  have hset :
      Finset.Icc 2 m = insert m (Finset.Icc 2 (m - 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : m ∉ Finset.Icc 2 (m - 1) := by
    simp only [Finset.mem_Icc]
    omega
  rw [factorialExpPrefix, hset, Finset.sum_insert hnotmem,
    factorialExpPrefix]
  ring

/-- The integral factorial-expansion head satisfies its exact radix
recurrence. -/
theorem factorialExpScaled_step
    {m : ℕ} (hm : 2 ≤ m) :
    factorialExpScaled m = m * factorialExpScaled (m - 1) + 1 := by
  have hfac : m.factorial = m * (m - 1).factorial := by
    calc
      m.factorial = ((m - 1) + 1).factorial := by congr 1 <;> omega
      _ = ((m - 1) + 1) * (m - 1).factorial := Nat.factorial_succ _
      _ = m * (m - 1).factorial := by congr 1 <;> omega
  have hmfac0 : (m.factorial : ℚ) ≠ 0 := by positivity
  have hscaledQ :
      (factorialExpScaled m : ℚ) =
        (m : ℚ) * factorialExpScaled (m - 1) + 1 := by
    rw [← factorial_mul_expPrefix_eq_scaled,
      factorialExpPrefix_eq_prev_add hm, hfac]
    push_cast
    rw [← factorial_mul_expPrefix_eq_scaled]
    field_simp [hmfac0]
  exact_mod_cast hscaledQ

/-- The finite second-layer floor is the factorial-gap strict successor with
the integral `e - 2` head removed. -/
theorem secondLayerPrefixFloor_eq_strictFacTop_sub_exp (m : ℕ) :
    secondLayerPrefixFloor m =
      strictFacTopRat (factorialGapPrefix m) m -
        (factorialExpScaled m : ℤ) - 1 := by
  have hdecomp := factorialGapPrefix_eq_exp_add_second m
  have hexp := factorial_mul_expPrefix_eq_scaled m
  have hscaled :
      (m.factorial : ℚ) * factorialGapSecondLayerPrefix m =
        (m.factorial : ℚ) * factorialGapPrefix m -
          (factorialExpScaled m : ℚ) := by
    rw [hdecomp, mul_add, hexp]
    ring
  unfold secondLayerPrefixFloor strictFacTopRat
  rw [hscaled, Int.floor_sub_natCast]
  omega

/-- Exact finite second-layer digit law.  No infinite-tail stabilization is
used here. -/
theorem secondLayerPrefixDigit_eq_carry
    {m : ℕ} (hm : 2 ≤ m) :
    secondLayerPrefixDigit m =
      (m : ℤ) - 1 - factorialGapStepCarry m := by
  have hstep := strictFacTop_factorialGapPrefix_step hm
  rw [strictFacTop_ratCast, strictFacTop_ratCast] at hstep
  have hexp := factorialExpScaled_step hm
  have hexpZ :
      (factorialExpScaled m : ℤ) =
        (m : ℤ) * (factorialExpScaled (m - 1) : ℤ) + 1 := by
    exact_mod_cast hexp
  unfold secondLayerPrefixDigit
  rw [secondLayerPrefixFloor_eq_strictFacTop_sub_exp,
    secondLayerPrefixFloor_eq_strictFacTop_sub_exp, hstep, hexpZ]
  ring

/-- The explicit condition needed to replace a finite second-layer prefix
floor by the floor of an infinite target `x`. -/
def SecondLayerFloorStableAt (x : ℝ) (m : ℕ) : Prop :=
  facFloor x m = secondLayerPrefixFloor m

/-- Under floor stability at two consecutive scales, the canonical digit of
the infinite target is the finite digit `m - 1 - carry`. -/
theorem canonicalDigit_eq_carry_of_secondLayerFloorStable
    {x : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hmStable : SecondLayerFloorStableAt x m)
    (hprevStable : SecondLayerFloorStableAt x (m - 1)) :
    canonicalDigit x m =
      (m : ℤ) - 1 - factorialGapStepCarry m := by
  unfold canonicalDigit SecondLayerFloorStableAt at *
  rw [hmStable, hprevStable]
  exact secondLayerPrefixDigit_eq_carry hm

/-- A rational number cannot have an eventually maximal canonical
factorial-digit tail: rational tails are eventually zero. -/
theorem rational_not_eventually_canonicalDigit_eq_maximal
    (a : ℤ) {q : ℕ} (hq : 0 < q) :
    ¬ ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 2 ≤ m →
      canonicalDigit (((a : ℚ) / (q : ℚ)) : ℝ) m = (m : ℤ) - 1 := by
  rintro ⟨M, hM⟩
  let n := max q (max M 1)
  have hqn : q ≤ n := le_max_left _ _
  have hMn : M ≤ n := le_trans (le_max_left M 1) (le_max_right q (max M 1))
  have hn1 : 1 ≤ n :=
    le_trans (le_max_right M 1) (le_max_right q (max M 1))
  have hzero := canonicalDigit_eq_zero_of_rational a hq hqn
  have hmax := hM (n + 1) (by omega) (by omega)
  rw [hzero] at hmax
  push_cast at hmax
  omega

end ErdosProblems.Erdos68
