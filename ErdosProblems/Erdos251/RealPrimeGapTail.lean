import ErdosProblems.Erdos251.PrimeGapDyadicTail

/-!
# The actual real prime-gap tail

The convergent prime-gap series defines a real tail without a rationality
assumption. Its recurrence connects real small-mismatch certificates to the
actual prime-series endpoint. No cofinal supply of such certificates is proved.
-/

open scoped BigOperators

namespace ErdosProblems.Erdos251

/-- The genuine scaled tail after the first `N+1` prime-gap terms. -/
noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))

/-- The finite-prefix definition equals the convergent infinite tail. -/
theorem realPrimeGapTail_eq_scaled_tsum (N : ℕ) :
    realPrimeGapTail N =
      2 ^ (N + 1) * ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) := by
  rw [realPrimeGapTail, primeGapPartialSumQ_cast]
  have hsplit := summable_primeGapDyadicTerm.sum_add_tsum_nat_add (N + 1)
  rw [← hsplit]
  ring

/-- Exact agreement with the manuscript's shifted-gap series, with denominator
`2^(k+1)` and no rational-state hypothesis. -/
theorem realPrimeGapTail_eq_tsum_shifted_gaps (N : ℕ) :
    realPrimeGapTail N =
      ∑' k : ℕ, (primeGap0 (N + k + 1) : ℝ) / 2 ^ (k + 1) := by
  have hshift : Summable (fun k => primeGapDyadicTerm (k + (N + 1))) := by
    simpa [Nat.add_comm] using
      summable_primeGapDyadicTerm.comp_injective (add_left_injective (N + 1))
  rw [realPrimeGapTail_eq_scaled_tsum, ← (hshift.hasSum.mul_left (2 ^ (N + 1))).tsum_eq]
  apply tsum_congr
  intro k
  unfold primeGapDyadicTerm
  rw [show k + (N + 1) + 1 = (N + 1) + (k + 1) by omega, pow_add]
  rw [show k + (N + 1) = N + k + 1 by omega]
  field_simp
  simp only [pow_add, pow_succ]
  ring

/-- The actual real tail satisfies the integer-digit recurrence unconditionally. -/
theorem realPrimeGapTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) realPrimeGapTail := by
  intro N
  rw [realPrimeGapTail, realPrimeGapTail, primeGapPartialSumQ_succ]
  simp only [pow_succ]
  push_cast
  field_simp
  ring

@[simp] theorem realPrimeGapTail_zero :
    realPrimeGapTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 := by
  simp [realPrimeGapTail, primeGapPartialSumQ]
  ring

/-- The tail's initial value has exactly the arithmetic status of the gap sum. -/
theorem irrational_realPrimeGapTail_zero_iff :
    Irrational (realPrimeGapTail 0) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  rw [realPrimeGapTail_zero]
  simpa using
    (irrational_sub_natCast_iff (x := 2 * ∑' n : ℕ, primeGapDyadicTerm n) (n := 1)).trans
      (by simpa using
        (irrational_natCast_mul_iff (n := 2) (x := ∑' n : ℕ, primeGapDyadicTerm n)))

/-- Cofinal escape now refers to the actual real prime-gap tail. -/
theorem irrational_primeSeries_iff_realPrimeGapTail_escape :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      CofinalNonintegralTailShifts realPrimeGapTail := by
  exact (irrational_tsum_primeDyadicTerm_iff_primeGap summable_primeDyadicTerm).trans
    (irrational_realPrimeGapTail_zero_iff.symm.trans
      (irrational_initial_iff_cofinalNonintegralTailShifts realPrimeGapTail_recurrence))

/-- An integer in the open unit interval is zero, also in the real state space. -/
theorem realIntegral_eq_zero_of_small {x : ℝ}
    (hint : RealIntegral x) (hlo : -1 < x) (hhi : x < 1) : x = 0 := by
  obtain ⟨z, rfl⟩ := hint
  have hzlo : (-1 : ℤ) < z := by exact_mod_cast hlo
  have hzhi : z < (1 : ℤ) := by exact_mod_cast hhi
  have hz : z = 0 := by omega
  simp [hz]

/-- The real shift obeys the same difference recurrence as the rational shift. -/
theorem realTailShift_succ {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ) :
    realTailShift T h (N + 1) =
      2 * realTailShift T h N - ((g (N + h + 1) : ℝ) - g (N + 1)) := by
  unfold realTailShift
  rw [show N + 1 + h = N + h + 1 by omega, hrec (N + h), hrec N]
  ring

/-- Two adjacent small real shifts cannot both be integral when their digits differ. -/
theorem realTailShift_not_both_integral_of_small_pair_of_digit_ne
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (hsmall :
      (-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
      (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1))
    (hdigit : g (N + h + 1) ≠ g (N + 1)) :
    ¬ (RealIntegral (realTailShift T h N) ∧
      RealIntegral (realTailShift T h (N + 1))) := by
  rintro ⟨hN, hsucc⟩
  have hzN := realIntegral_eq_zero_of_small hN hsmall.1.1 hsmall.1.2
  have hzsucc := realIntegral_eq_zero_of_small hsucc hsmall.2.1 hsmall.2.2
  have hstep := realTailShift_succ hrec h N
  rw [hzN, hzsucc] at hstep
  apply hdigit
  have heq : (g (N + h + 1) : ℝ) = (g (N + 1) : ℝ) := by linarith
  exact_mod_cast heq

/-- The paper's real small-mismatch supply implies irrationality of the actual
prime series. The supply is an explicit unproved hypothesis, not a consequence
of nonperiodicity or of convergence. -/
theorem irrational_primeSeries_of_realPrimeGapTail_small_mismatch
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ((-1 < realTailShift realPrimeGapTail h N ∧
          realTailShift realPrimeGapTail h N < 1) ∧
       (-1 < realTailShift realPrimeGapTail h (N + 1) ∧
          realTailShift realPrimeGapTail h (N + 1) < 1)) ∧
      primeGap0 (N + h + 1) ≠ primeGap0 (N + 1)) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) := by
  apply irrational_primeSeries_iff_realPrimeGapTail_escape.mpr
  intro h hh N₀
  obtain ⟨N, hN, hsmall, hgap⟩ := hsupply h hh N₀
  have hcast : (primeGap0 (N + h + 1) : ℤ) ≠ (primeGap0 (N + 1) : ℤ) := by
    exact_mod_cast hgap
  have hnot := realTailShift_not_both_integral_of_small_pair_of_digit_ne
    realPrimeGapTail_recurrence h N hsmall hcast
  by_cases hint : RealIntegral (realTailShift realPrimeGapTail h N)
  · exact ⟨N + 1, by omega, fun hnext => hnot ⟨hint, hnext⟩⟩
  · exact ⟨N, hN, hint⟩

end ErdosProblems.Erdos251
