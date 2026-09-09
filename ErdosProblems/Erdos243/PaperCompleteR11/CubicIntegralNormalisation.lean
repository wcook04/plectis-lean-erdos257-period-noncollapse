import ErdosProblems.Erdos243.PaperCompleteR11.WindowIncidence
import Mathlib.Data.Nat.Choose.Basic

/-!
# Integral normalisation at the quarter-density threshold

Authored candidate; Lean and axiom audits UNRUN. The integral coefficients are
constructed from one clean four-window. In particular they are conclusions,
not hidden hypotheses in an arbitrary rational-profile statement.
- A non-integral constant or non-integral third difference gives density >= 1/4.
- The argument needs only an integer-valued sequence, not a recurrence.
- No claim that an integral constant must be +1 or -1 is made here.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- Integer-valued binomial basis for a rising cubic. -/
def risingBinomial (n : ℕ) : ℤ := ((n + 2).choose 3 : ℤ)

/-- The factor six is exact, including at the first two indices. -/
theorem six_mul_rising_choose (n : ℕ) :
    6 * (n + 2).choose 3 = n * (n + 1) * (n + 2) := by
  have h1 : (n + 1) * n = (n + 1).choose 2 * 2 := by
    simpa using Nat.add_one_mul_choose_eq n 1
  have h2 : (n + 2) * (n + 1).choose 2 = (n + 2).choose 3 * 3 := by
    simpa only [Nat.add_assoc] using Nat.add_one_mul_choose_eq (n + 1) 2
  have h3 := congrArg (fun t : ℕ ↦ t * (n + 2)) h1
  nlinarith

/-- The integer basis identity, without a truncated natural subtraction. -/
theorem six_mul_risingBinomial (n : ℕ) :
    6 * risingBinomial n = (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
  have h := six_mul_rising_choose n
  unfold risingBinomial
  exact_mod_cast h

/-- Four agreements determine an actual integer third difference and constant.
The conclusion describes the original profile at every index, not only the
four sampled values. -/
theorem cubic_integral_coefficients_of_four_agreements
    (C : ℕ → ℤ) (κ η : ℚ) (n : ℕ)
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) =
      κ * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) *
        (((n + j : ℕ) : ℚ) + 2) + η) :
    ∃ m c : ℤ, (m : ℚ) = 6 * κ ∧ (c : ℚ) = η ∧
      ∀ k : ℕ, κ * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + η =
        ((m * risingBinomial k + c : ℤ) : ℚ) := by
  let m : ℤ := C (n + 3) - 3 * C (n + 2) + 3 * C (n + 1) - C n
  have h0 := hagree 0 (by decide)
  have h1 := hagree 1 (by decide)
  have h2 := hagree 2 (by decide)
  have h3 := hagree 3 (by decide)
  simp only [Nat.add_zero] at h0
  push_cast at h1 h2 h3
  have hm : (m : ℚ) = 6 * κ := by
    dsimp [m]
    push_cast
    linear_combination h3 - 3 * h2 + 3 * h1 - h0
  let c : ℤ := C n - m * risingBinomial n
  have hc : (c : ℚ) = η := by
    have hb : (6 : ℚ) * (risingBinomial n : ℚ) =
        (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) := by
      exact_mod_cast six_mul_risingBinomial n
    dsimp [c]
    push_cast
    rw [hm]
    linear_combination h0 - κ * hb
  refine ⟨m, c, hm, hc, ?_⟩
  intro k
  have hb : (6 : ℚ) * (risingBinomial k : ℚ) =
      (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) := by
    exact_mod_cast six_mul_risingBinomial k
  push_cast
  rw [hm, hc]
  linear_combination -κ * hb

/-- The normalised integer leading coefficient is positive whenever the
original leading coefficient is positive. -/
theorem cubic_positive_integral_coefficients_of_four_agreements
    (C : ℕ → ℤ) (κ η : ℚ) (hκ : 0 < κ) (n : ℕ)
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) =
      κ * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) *
        (((n + j : ℕ) : ℚ) + 2) + η) :
    ∃ m c : ℤ, 0 < m ∧ (m : ℚ) = 6 * κ ∧ (c : ℚ) = η ∧
      ∀ k : ℕ, κ * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + η =
        ((m * risingBinomial k + c : ℤ) : ℚ) := by
  obtain ⟨m, c, hm, hc, heval⟩ :=
    cubic_integral_coefficients_of_four_agreements C κ η n hagree
  have hmpos : (0 : ℚ) < (m : ℚ) := by rw [hm]; positivity
  exact ⟨m, c, by exact_mod_cast hmpos, hm, hc, heval⟩

/-- At low exceptional density, the two integral coefficients are produced,
not assumed. This is valid even when there is no numerator recurrence. -/
theorem cubic_integral_coefficients_of_not_quarter_density
    (C : ℕ → ℤ) (κ η : ℚ)
    (hlow : ¬ LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
      (1 / 4)) :
    ∃ m c : ℤ, (m : ℚ) = 6 * κ ∧ (c : ℚ) = η ∧
      ∀ k : ℕ, κ * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + η =
        ((m * risingBinomial k + c : ℤ) : ℚ) := by
  obtain ⟨n, _hn, hclean⟩ := clean_windows_of_not_lower_density
    {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
    4 (by decide) hlow 0
  apply cubic_integral_coefficients_of_four_agreements C κ η n
  intro j hj
  exact not_ne_iff.mp (hclean j hj)

/-- Complete non-integral-profile branch, with the stronger constant 1/4. -/
theorem cubic_nonintegral_profile_quarter_density
    (C : ℕ → ℤ) (κ η : ℚ)
    (hbad : ¬ ∃ m c : ℤ, (m : ℚ) = 6 * κ ∧ (c : ℚ) = η) :
    LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
      (1 / 4) := by
  by_contra hlow
  obtain ⟨m, c, hm, hc, _⟩ :=
    cubic_integral_coefficients_of_not_quarter_density C κ η hlow
  exact hbad ⟨m, c, hm, hc⟩

/-- The same branch for the natural numerator sequence of the original paper. -/
theorem natural_cubic_nonintegral_profile_quarter_density
    (C : ℕ → ℕ) (κ η : ℚ)
    (hbad : ¬ ∃ m c : ℤ, (m : ℚ) = 6 * κ ∧ (c : ℚ) = η) :
    LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
      (1 / 4) := by
  simpa only [Int.cast_natCast] using
    cubic_nonintegral_profile_quarter_density (fun n ↦ (C n : ℤ)) κ η hbad

/-- A concrete infinite family excluded without any prime supplier. -/
theorem cubic_one_seventh_leading_quarter_density (C : ℕ → ℕ) (η : ℚ) :
    LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ (1 / 7 : ℚ) * (n : ℚ) * ((n : ℚ) + 1) *
        ((n : ℚ) + 2) + η} (1 / 4) := by
  apply natural_cubic_nonintegral_profile_quarter_density C (1 / 7) η
  rintro ⟨m, c, hm, _hc⟩
  have hmQ : (7 : ℚ) * (m : ℚ) = 6 := by linarith
  have hmZ : (7 : ℤ) * m = 6 := by exact_mod_cast hmQ
  omega

end ErdosProblems.Erdos243.PaperCompleteR11
