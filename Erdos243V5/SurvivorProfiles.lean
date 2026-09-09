import Erdos243V5.DensityQuantifiers

/-! Authored candidate, UNRUN. Stronger lower-density bounds for the two classified profiles;
only the correct phases are asserted to forbid four consecutive agreements. -/

namespace Erdos243V5

open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11

theorem twelve_binomial_plus (n : ℕ) :
    12 * risingBinomial n + 1 = plusCubic n := by
  have h := six_mul_risingBinomial n
  dsimp [plusCubic]
  linear_combination 2 * h

theorem twelve_binomial_minus (n : ℕ) :
    12 * risingBinomial n + (-1) = minusCubic n := by
  have h := six_mul_risingBinomial n
  dsimp [minusCubic]
  linear_combination 2 * h

theorem plus_profile_lower_density (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    LowerDensityAtLeast {n : ℕ | u n ≠ plusCubic n} (1 / 7) := by
  apply lowerDensityAtLeast_of_linear_bound _ 1 7 ((7 * T + 7 : ℕ) : ℝ)
    (by norm_num)
  intro X
  simp only [one_mul]
  exact_mod_cast plus_profile_one_seventh a u v T hnum hden X

theorem minus_profile_lower_density (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    LowerDensityAtLeast {n : ℕ | u n ≠ minusCubic n} (1 / 7) := by
  apply lowerDensityAtLeast_of_linear_bound _ 1 7 ((7 * T + 8 : ℕ) : ℝ)
    (by norm_num)
  intro X
  simp only [one_mul]
  exact_mod_cast minus_profile_one_seventh a u v T hnum hden X

theorem twelve_unit_profile_lower_density (a u v : ℕ → ℤ) (c : ℤ) (T : ℕ)
    (hc : c = 1 ∨ c = -1)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    LowerDensityAtLeast {n : ℕ | u n ≠ 12 * risingBinomial n + c} (1 / 7) := by
  rcases hc with rfl | rfl
  · simpa only [twelve_binomial_plus] using plus_profile_lower_density a u v T hnum hden
  · simpa only [twelve_binomial_minus] using minus_profile_lower_density a u v T hnum hden

/-- Correct literal replacement for the two local four-window clauses. -/
theorem classified_profile_phase_windows (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ k, T ≤ 7 * k → ∃ i, i < 4 ∧ u (7 * k + i) ≠ plusCubic (7 * k + i)) ∧
    (∀ k, T ≤ 1 + 7 * k → ∃ i, i < 4 ∧
      u (1 + 7 * k + i) ≠ minusCubic (1 + 7 * k + i)) := by
  exact ⟨fun k hk ↦ plus_phase_hit a u v T k hk hnum hden,
    fun k hk ↦ minus_phase_hit a u v T k hk hnum hden⟩

end Erdos243V5
