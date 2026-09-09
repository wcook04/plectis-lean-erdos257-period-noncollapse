import ErdosProblems.Erdos269.PaperR7SeriesIdentification
import ErdosProblems.Erdos269.CofinalWindowEscapeEquivalence

/-!
# Round 7: the fixed denominator split and the literal original value

The existing bridge existentially chooses a split and a carry. The paper fixes
`D = 2^u 3^v 5^w B`, fixes the onset, and identifies that carry with `B X_a`.
This file proves those equality data rather than citing a nearby existential.
The long-record sharper `Q`-cap remains a separate obligation.

Validation: authored, not compiled. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators

/-- Account explicitly for the smooth integer `1`, absent from the source's tail-one bridge. -/
theorem tail_one_of_paperSeries_eq_rat {N : ℤ} {D : ℕ} (hD : 0 < D)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    dyadicShellTsumTailR235 1 = ((N - (D : ℤ) : ℤ) : ℝ) / (D : ℝ) := by
  have h := hval
  rw [paperSeries235_eq_shellTsum, dyadicShellTsumTailR235_zero_eq] at h
  have hDn : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  calc
    dyadicShellTsumTailR235 1 = (N : ℝ) / (D : ℝ) - 1 := by linarith
    _ = ((N - (D : ℤ) : ℤ) : ℝ) / (D : ℝ) := by
      push_cast
      field_simp <;> ring

/-- The stated smooth factor is absorbed at the stated onset. -/
theorem fixed_split_scaled_state_is_integer {N : ℤ} {D u v w B a : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ))
    (ha : u + 1 + 2 * v + 3 * w ≤ a) :
    ∃ z : ℤ, (B : ℝ) * trueNormalizedState a = (z : ℝ) := by
  let s : ℕ := 2 ^ u * 3 ^ v * 5 ^ w
  have hspos : 0 < s := by dsimp [s]; positivity
  have hDpos : 0 < D := by rw [hD]; positivity
  have htail := tail_one_of_paperSeries_eq_rat hDpos hval
  have hq : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hDpos
  have htail' : dyadicShellTsumTailR235 1 =
      ((N - (D : ℤ) : ℤ) : ℝ) / ((D : ℤ) : ℝ) := by simpa using htail
  obtain ⟨z, hz⟩ := qsmul_trueNormalizedState_eq_height_mul_sub hq htail'
    (a := a) (by omega)
  obtain ⟨t, ht⟩ := smooth_dvd_heightNormalizer235 (α := u) (β := v) (γ := w) ha
  have hDR : (D : ℝ) = (s : ℝ) * (B : ℝ) := by
    exact_mod_cast hD
  have hHR : (heightNormalizer235 a : ℝ) = (s : ℝ) * (t : ℝ) := by
    exact_mod_cast ht
  have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast hspos.ne'
  refine ⟨(t : ℤ) * (N - (D : ℤ)) - (B : ℤ) * z, ?_⟩
  apply mul_left_cancel₀ hsne
  calc
    (s : ℝ) * ((B : ℝ) * trueNormalizedState a) =
        (D : ℝ) * trueNormalizedState a := by rw [hDR]; ring
    _ = (heightNormalizer235 a : ℝ) * ((N - (D : ℤ) : ℤ) : ℝ) -
        (D : ℝ) * (z : ℝ) := by simpa using hz
    _ = (s : ℝ) * (((t : ℤ) * (N - (D : ℤ)) - (B : ℤ) * z : ℤ) : ℝ) := by
      rw [hHR, hDR]
      push_cast
      ring

/-- A canonical integer-valued representative; equality to the scaled state is proved below. -/
noncomputable def paperReducedCarry (B a : ℕ) : ℤ :=
  ⌊(B : ℝ) * trueNormalizedState a⌋

theorem paperReducedCarry_cast {N : ℤ} {D u v w B a : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ))
    (ha : u + 1 + 2 * v + 3 * w ≤ a) :
    (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a := by
  obtain ⟨z, hz⟩ := fixed_split_scaled_state_is_integer hB hD hval ha
  unfold paperReducedCarry
  rw [hz, Int.floor_intCast]

/-- Full short-note bridge at the GIVEN split and onset, with `d_a = B X_a`.
Reducedness and coprimality are not needed for this stronger assembly. -/
theorem short_fixed_split_bridge {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a : ℕ, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      0 < paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ ((90 * B * (a + 1) ^ 2 : ℕ) : ℤ) := by
  intro a ha
  have hc := paperReducedCarry_cast hB hD hval ha
  have hcn := paperReducedCarry_cast hB hD hval (a := a + 1) (by omega)
  have hposR : (0 : ℝ) < (B : ℝ) * trueNormalizedState a :=
    mul_pos (by exact_mod_cast hB) (trueNormalizedState_pos a)
  have hpos : 0 < paperReducedCarry B a := by
    rw [← hc] at hposR
    exact_mod_cast hposR
  refine ⟨hc, hpos, ?_, ?_⟩
  · have hr := scaled_actual_recurrence (B : ℤ) a
    have heq : (paperReducedCarry B (a + 1) : ℝ) =
        (((dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) : ℤ) : ℝ) := by
      rw [hcn]
      push_cast at hr ⊢
      rw [hc]
      exact hr
    exact_mod_cast heq
  · have hu := trueNormalizedState_mul_le a (q := (B : ℝ)) (Nat.cast_nonneg _)
    rw [← hc] at hu
    have hbound : (paperReducedCarry B a : ℝ) ≤
        (((90 * B * (a + 1) ^ 2 : ℕ) : ℤ) : ℝ) := by
      push_cast at hu ⊢
      nlinarith [hu]
    exact_mod_cast hbound

/-- Actual finite denominator clearing with the real half height, including the empty scale-zero case. -/
theorem finite_window_clears_real_half_height (u b : ℕ) (hub : u ≤ b) :
    ∃ z : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 *
        (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) = (z : ℝ) := by
  by_cases hb0 : b = 0
  · have hu0 : u = 0 := by omega
    subst b
    subst u
    exact ⟨0, by simp⟩
  · obtain ⟨z, hz⟩ := heightNormalizer235_mul_windowMass_eq_int u (b - u)
    have hidx : u + (b - u) = b := by omega
    rw [hidx] at hz
    have hpref : (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) =
        (dyadicSmoothWindowMassQ235 u (b - u) : ℝ) := by
      simp [dyadicSmoothWindowMassQ235, dyadicShellMassR235]
    have hh : (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 =
        (heightNormalizer235 b : ℝ) := by
      have h := two_mul_heightNormalizer235 b (by omega)
      have hR : 2 * (heightNormalizer235 b : ℝ) =
          (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) := by exact_mod_cast h
      linarith
    refine ⟨z, ?_⟩
    rw [hh, hpref]
    exact_mod_cast hz

/-- Full long-record all-scale lattice, with the existential collision made explicit. -/
theorem long_all_scale_lattice {N : ℤ} {D : ℕ} (hD : 0 < D)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    (∀ u b : ℕ, u ≤ b → ∃ z : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 *
        (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) = (z : ℝ)) ∧
    (∀ a : ℕ, 1 ≤ a → ∃ z : ℤ,
      (D : ℝ) * trueNormalizedState a = (z : ℝ)) ∧
    (∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ ∃ z : ℤ,
      trueNormalizedState j - trueNormalizedState i = (z : ℝ)) := by
  have hq : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have ht : dyadicShellTsumTailR235 1 =
      ((N - (D : ℤ) : ℤ) : ℝ) / ((D : ℤ) : ℝ) := by
    simpa using tail_one_of_paperSeries_eq_rat hD hval
  refine ⟨finite_window_clears_real_half_height, ?_, ?_⟩
  · intro a ha
    simpa [trueNormalizedState] using qsmul_normalizedTailState_eq_int_of_value_eq_rat hq ht ha
  · obtain ⟨i, j, hij, z, hz⟩ := exists_normalizedTailState_collision_of_value_eq_rat hq ht
    exact ⟨1 + i, 1 + j, by omega, by omega, z, hz⟩

/-- The exact all-denominator, all-start nonintegrality statement of the long record. -/
def AllReducedTailsNonintegral : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 → ∀ a : ℕ, 1 ≤ a →
    ∀ z : ℤ, (B : ℝ) * trueNormalizedState a ≠ (z : ℝ)

/-- Irrationality of the original value transfers to tail one without a hidden shift. -/
theorem irrational_tail_one_of_paperSeries (h : Irrational paperSeries235) :
    Irrational (dyadicShellTsumTailR235 1) := by
  rw [paperSeries235_eq_shellTsum, dyadicShellTsumTailR235_zero_eq, add_comm] at h
  simpa using h.sub_natCast 1

theorem allReducedTailsNonintegral_of_irrational (h : Irrational paperSeries235) :
    AllReducedTailsNonintegral := by
  intro B hB _ a ha z hz
  have hx := irrational_trueNormalizedState (irrational_tail_one_of_paperSeries h) a ha
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hy : Irrational ((B : ℝ) * trueNormalizedState a) := by
    simpa using hx.ratCast_mul hBq
  rw [hz] at hy
  rw [irrational_iff_ne_rational] at hy
  exact hy z 1 (by norm_num) (by simp)

/-- The converse uses the given split, not an unrelated abstract carry. -/
theorem irrational_of_allReducedTailsNonintegral (h : AllReducedTailsNonintegral) :
    Irrational paperSeries235 := by
  have hposden : ∀ N : ℤ, ∀ D : ℕ, 0 < D →
      paperSeries235 ≠ (N : ℝ) / (D : ℝ) := by
    intro N D hD hv
    obtain ⟨u, v, w, B, hsplit, hB, hcop⟩ := exists_smooth_coprime_split D hD
    obtain ⟨z, hz⟩ := fixed_split_scaled_state_is_integer hB hsplit hv
      (a := u + 1 + 2 * v + 3 * w) (le_refl _)
    exact h B hB hcop _ (by omega) z hz
  rw [irrational_iff_ne_rational]
  intro a b hb
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hbn : 0 < (-b).toNat := by omega
    have hcast : (((-b).toNat : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
    intro hv
    apply hposden (-a) (-b).toNat hbn
    rw [hv]
    have hR : (((-b).toNat : ℕ) : ℝ) = -(b : ℝ) := by exact_mod_cast hcast
    rw [hR]
    push_cast
    rw [neg_div_neg_eq]
  · have hbn : 0 < b.toNat := by omega
    have hcast : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hbpos.le
    intro hv
    apply hposden a b.toNat hbn
    have hR : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by exact_mod_cast hcast
    simpa [hR] using hv

/-- Full long-record `res:tails-equivalence`, at the literal smooth-number value. -/
theorem allReducedTailsNonintegral_iff :
    AllReducedTailsNonintegral ↔ Irrational paperSeries235 :=
  ⟨irrational_of_allReducedTailsNonintegral, allReducedTailsNonintegral_of_irrational⟩

end ErdosProblems.Erdos269.PaperR7
