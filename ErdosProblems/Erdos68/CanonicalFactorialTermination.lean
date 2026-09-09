import ErdosProblems.Erdos68.CanonicalFactorialDigits

/-!
# Rationality and termination of canonical factorial digits

This completes the converse to rational termination in
`CanonicalFactorialDigits`: a zero digit tail forces its starting remainder
to vanish. A positive remainder would grow under every subsequent radix,
contradicting the canonical upper bound of one.

The result concerns the canonical expansion of an arbitrary real number. It
does not establish whether the factorial-gap series has a terminating tail.
-/

namespace ErdosProblems.Erdos68

private theorem canonicalRemainder_linear_growth_of_zero_digits
    (x : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hzero : ∀ n ≥ N, canonicalDigit x (n + 1) = 0) (k : ℕ) :
    ((k : ℝ) + 1) * canonicalRemainder x N ≤
      canonicalRemainder x (N + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hrec := canonicalRemainder_recurrence x (N + k)
      rw [hzero (N + k) (by omega), Int.cast_zero, sub_zero] at hrec
      have hradix : (2 : ℝ) ≤ ((N + k : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show 2 ≤ N + k + 1 by omega)
      have hdouble := mul_le_mul_of_nonneg_right hradix
        (canonicalRemainder_nonneg x (N + k))
      have hbase := canonicalRemainder_nonneg x N
      have hk : (0 : ℝ) ≤ k := by positivity
      simp only [Nat.add_succ, Nat.add_zero, Nat.cast_succ] at *
      nlinarith [mul_nonneg hk hbase]

/-- An eventually zero canonical digit sequence cannot conceal a positive
fractional remainder at the start of the tail. -/
theorem canonicalRemainder_eq_zero_of_zero_digit_tail
    (x : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hzero : ∀ n ≥ N, canonicalDigit x (n + 1) = 0) :
    canonicalRemainder x N = 0 := by
  apply le_antisymm _ (canonicalRemainder_nonneg x N)
  by_contra hnot
  have hpos : 0 < canonicalRemainder x N := lt_of_not_ge hnot
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / canonicalRemainder x N)
  have hlarge : 1 < (k : ℝ) * canonicalRemainder x N :=
    (div_lt_iff₀ hpos).mp hk
  have hgrowth := canonicalRemainder_linear_growth_of_zero_digits x hN hzero k
  have hupper := canonicalRemainder_lt_one x (N + k)
  nlinarith

/-- A zero canonical remainder gives the explicit rational value obtained by
dividing its factorial-scale floor by the corresponding factorial. -/
theorem exists_rat_eq_of_canonicalRemainder_eq_zero
    (x : ℝ) (N : ℕ) (hzero : canonicalRemainder x N = 0) :
    ∃ q : ℚ, (q : ℝ) = x := by
  refine ⟨(facFloor x N : ℚ) / (N.factorial : ℚ), ?_⟩
  push_cast
  have hfac : (N.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  apply (div_eq_iff hfac).2
  unfold canonicalRemainder at hzero
  nlinarith

/-- Termination of the canonical factorial digits implies rationality. -/
theorem exists_rat_eq_of_eventually_zero_canonicalDigit
    (x : ℝ) (hzero : ∃ N : ℕ, ∀ n ≥ N, canonicalDigit x (n + 1) = 0) :
    ∃ q : ℚ, (q : ℝ) = x := by
  obtain ⟨N, hN⟩ := hzero
  apply exists_rat_eq_of_canonicalRemainder_eq_zero x (max N 1)
  apply canonicalRemainder_eq_zero_of_zero_digit_tail x (le_max_right N 1)
  intro n hn
  exact hN n ((le_max_left N 1).trans hn)

/-- A real number is rational exactly when its canonical factorial digits
eventually vanish. The floor convention fixes the expansion, so there is no
ambiguity from alternative maximal-digit tails. -/
theorem exists_rat_eq_iff_eventually_zero_canonicalDigit (x : ℝ) :
    (∃ q : ℚ, (q : ℝ) = x) ↔
      ∃ N : ℕ, ∀ n ≥ N, canonicalDigit x (n + 1) = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨q.den, ?_⟩
    intro n hn
    have hq := canonicalDigit_eq_zero_of_rational q.num q.pos hn
    rw [Rat.cast_intCast, Rat.cast_natCast] at hq
    rw [Rat.cast_def]
    exact hq
  · exact exists_rat_eq_of_eventually_zero_canonicalDigit x

end ErdosProblems.Erdos68
