import ErdosProblems.Erdos269.PaperR7SharpShellBound
import ErdosProblems.Erdos269.IntegralBranchWidth
import ErdosProblems.Erdos269.DyadicRadixTailEscape

/-!
# Round 7: literal forcing, infinite digit expansion and scaled dichotomy

Targets: short-note `res:dyadic-alphabet`, the dynamical clauses of
`res:actual-orbit`, and long-record `res:actual-orbit`.
The total smooth-series reindexing is supplied separately in
`PaperR7SeriesIdentification`; nothing here silently identifies a formal tsum
with the smooth-number series without that bridge.

Validation: authored, not compiled. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators

/-- The forcing digit as printed in the short note, before any regrouping. -/
noncomputable def literalForcing235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) /
      (2 * (threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ))

/-- Exact identification with the existing natural-valued ordered digit. -/
theorem literalForcing235_eq_digit (a : ℕ) :
    literalForcing235 a = (dyadicOrderedBlockDigit235 a : ℚ) := by
  rw [← half_threePrimeHeight_mul_dyadicShellMassQ235 a]
  unfold literalForcing235 dyadicShellMassQ235
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Positivity of the integer digit, not merely nonnegativity of its formula. -/
theorem orderedDigit235_pos (a : ℕ) : 0 < dyadicOrderedBlockDigit235 a := by
  have hp : (0 : ℝ) <
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2 * dyadicShellMassR235 a :=
    mul_pos (div_pos (threePrimeHeight235_cast_pos _) (by norm_num))
      (dyadicShellMassR235_pos a)
  rw [half_threePrimeHeight_mul_dyadicShellMassR235 a] at hp
  exact_mod_cast hp

/-- Full short-note forcing/alphabet statement, with the actual printed sum. -/
theorem literal_integer_forcing_and_four_radices (a : ℕ) :
    (∃ m : ℕ, 0 < m ∧ literalForcing235 a = (m : ℚ)) ∧
    (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
      dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30) :=
  ⟨⟨dyadicOrderedBlockDigit235 a, orderedDigit235_pos a,
      literalForcing235_eq_digit a⟩, dyadicBlockBase235_cases a⟩

/-- The literal height ratio, in a field rather than natural truncated division. -/
theorem radix_eq_height_ratio (a : ℕ) :
    (dyadicBlockBase235 a : ℚ) =
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) /
        (threePrimeHeight 2 3 5 (2 ^ a) : ℚ) := by
  have hn : (threePrimeHeight 2 3 5 (2 ^ a) : ℚ) ≠ 0 := by
    exact_mod_cast (threePrimeHeightQ235_pos _).ne'
  apply (eq_div_iff hn).mpr
  exact_mod_cast (threePrimeHeight_dyadicBlock_succ a).symm

/-- The exact termwise identity that upgrades the finite telescope to a tsum. -/
theorem normalised_shell_eq_digit_over_product (a n : ℕ) :
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * dyadicShellMassR235 (a + n) =
      (dyadicOrderedBlockDigit235 (a + n) : ℝ) /
        ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (a + j) : ℝ) := by
  have hprodpos : (0 : ℝ) <
      ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (a + j) : ℝ) :=
    lt_of_lt_of_le (by positivity) (prod_dyadicBlockBase235_ge_two_pow a (n + 1))
  have hd := half_threePrimeHeight_mul_dyadicShellMassR235 (a + n)
  have hH := threePrimeHeight235_pow_add_eq_mul_prod a (n + 1)
  rw [eq_div_iff hprodpos.ne', ← hd]
  rw [show a + n + 1 = a + (n + 1) by omega, hH]
  ring

/-- Summability of the actual variable-base digit expansion. -/
theorem summable_actual_digit_expansion (a : ℕ) :
    Summable (fun n : ℕ => (dyadicOrderedBlockDigit235 (a + n) : ℝ) /
      ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (a + j) : ℝ)) := by
  have hs : Summable (fun n : ℕ => dyadicShellMassR235 (a + n)) :=
    summable_dyadicShellMassR235.comp_injective fun _ _ h => Nat.add_left_cancel h
  have hm := hs.mul_left ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2)
  exact hm.congr (normalised_shell_eq_digit_over_product a)

/-- Infinite digit expansion, including equality with the genuine tail. -/
theorem trueNormalizedState_eq_digit_tsum (a : ℕ) :
    trueNormalizedState a =
      ∑' n : ℕ, (dyadicOrderedBlockDigit235 (a + n) : ℝ) /
        ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (a + j) : ℝ) := by
  unfold trueNormalizedState dyadicNormalizedTailStateR235 dyadicShellTsumTailR235
  rw [← tsum_mul_left]
  exact tsum_congr (normalised_shell_eq_digit_over_product a)

/-- Every integer multiple follows an integer-digit recurrence. -/
theorem scaled_actual_recurrence (B : ℤ) (a : ℕ) :
    (B : ℝ) * trueNormalizedState (a + 1) =
      (dyadicBlockBase235 a : ℝ) * ((B : ℝ) * trueNormalizedState a) -
        ((B * (dyadicOrderedBlockDigit235 a : ℤ) : ℤ) : ℝ) := by
  have h := dyadicNormalizedShellTsumTailR235_succ a
  change trueNormalizedState (a + 1) =
    (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
      (dyadicOrderedBlockDigit235 a : ℝ) at h
  rw [h]
  push_cast
  ring

/-- Integral states propagate for any integer multiplier, not just multiplier one. -/
theorem scaled_integrality_propagates (B : ℤ) {a : ℕ} {z : ℤ}
    (hz : (B : ℝ) * trueNormalizedState a = (z : ℝ)) :
    ∀ n, a ≤ n → ∃ w : ℤ, (B : ℝ) * trueNormalizedState n = (w : ℝ) := by
  have hadd : ∀ k : ℕ, ∃ w : ℤ,
      (B : ℝ) * trueNormalizedState (a + k) = (w : ℝ) := by
    intro k
    induction k with
    | zero => exact ⟨z, by simpa using hz⟩
    | succ k ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨(dyadicBlockBase235 (a + k) : ℤ) * w -
        B * (dyadicOrderedBlockDigit235 (a + k) : ℤ), ?_⟩
      rw [show a + (k + 1) = (a + k) + 1 by omega,
        scaled_actual_recurrence, hw]
      push_cast
      ring
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact hadd k

/-- Full scaled dichotomy, with the eventual integrality clause included. -/
theorem scaled_integer_or_cofinal_separation (B : ℤ) :
    (∃ a : ℕ, ∀ n, a ≤ n →
      ∃ z : ℤ, (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
    (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
      FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31)) := by
  have h := dyadicBlockBase235_integer_or_cofinal_far
    (fun a => B * (dyadicOrderedBlockDigit235 a : ℤ))
    (fun a => (B : ℝ) * trueNormalizedState a) (scaled_actual_recurrence B)
  rcases h with ⟨a, z, hz⟩ | hfar
  · exact Or.inl ⟨a, scaled_integrality_propagates B hz⟩
  · exact Or.inr hfar

/-- All dynamical and numerical clauses of the short-note actual-orbit result.
The `Summable` clause for the original smooth series is assembled in the
separate identification module. The multiplier statement is stronger than
printed: every integer multiplier, not only the positive ones. -/
theorem actual_orbit_dynamics_and_bounds :
    (∀ a : ℕ,
      trueNormalizedState (a + 1) =
        (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
          (dyadicOrderedBlockDigit235 a : ℝ)) ∧
    (∀ a : ℕ, 0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 ∧
      (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 <
        90 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ B : ℤ,
      (∃ a : ℕ, ∀ n, a ≤ n → ∃ z : ℤ,
        (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
      (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
        FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31))) :=
  ⟨dyadicNormalizedShellTsumTailR235_succ,
    actual_state_sharp_bounds, scaled_integer_or_cofinal_separation⟩

end ErdosProblems.Erdos269.PaperR7
