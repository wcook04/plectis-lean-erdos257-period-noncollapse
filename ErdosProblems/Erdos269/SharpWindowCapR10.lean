import ErdosProblems.Erdos269.ActualSharpTailMajorantR10

/-! Endpoint composition of the actual constrained majorant. This is an
additional valid escape criterion, not an assertion that escape has been
produced. The original paper cap and its quantifiers are left unchanged.
All Lean builds and audits are UNRUN. -/
namespace ErdosProblems.Erdos269.PaperR10
open PaperR7 PaperR8

noncomputable def sharpPaperCap (B a : ℕ) : ℕ :=
  ⌊(B : ℚ) * carryMajorantQtilde (paperJumpIndex a)⌋₊

theorem carryMajorantQtilde_nonneg (n : ℕ) : 0 ≤ carryMajorantQtilde n := by
  unfold carryMajorantQtilde
  positivity

theorem paperJumpIndex_le_three_mul_r10 (a : ℕ) : paperJumpIndex a ≤ 3 * a := by
  have h := sorted_height_profile (pow_ne_zero a (by decide : (2 : ℕ) ≠ 0))
  rw [Nat.log_pow (by decide : 1 < (2 : ℕ))] at h
  unfold paperJumpIndex
  omega

theorem carryMajorantQtilde_jump_le_three_square (a : ℕ) :
    carryMajorantQtilde (paperJumpIndex a) ≤ 3 * ((a : ℚ) + 1) ^ 2 := by
  have hn : (paperJumpIndex a : ℚ) ≤ 3 * (a : ℚ) := by
    exact_mod_cast paperJumpIndex_le_three_mul_r10 a
  have hn0 : (0 : ℚ) ≤ paperJumpIndex a := Nat.cast_nonneg _
  have ha0 : (0 : ℚ) ≤ a := Nat.cast_nonneg _
  have hprod : (0 : ℚ) ≤
      (3 * (a : ℚ) - paperJumpIndex a) * (3 * (a : ℚ) + paperJumpIndex a) :=
    mul_nonneg (sub_nonneg.mpr hn) (by positivity)
  have hsq : (paperJumpIndex a : ℚ) ^ 2 ≤ 9 * (a : ℚ) ^ 2 := by
    nlinarith only [hprod]
  have ha2 : (0 : ℚ) ≤ (a : ℚ) ^ 2 := sq_nonneg _
  have hQ : carryMajorantQ (paperJumpIndex a) ≤ 3 * ((a : ℚ) + 1) ^ 2 := by
    unfold carryMajorantQ
    nlinarith only [hsq, hn, hn0, ha0, ha2]
  exact (carryMajorantQtilde_lt_Q (paperJumpIndex a)).le.trans hQ

theorem sharpPaperCap_le_three_square (B a : ℕ) :
    sharpPaperCap B a ≤ 3 * B * (a + 1) ^ 2 := by
  unfold sharpPaperCap
  apply Nat.floor_le_of_le
  have h := mul_le_mul_of_nonneg_left (carryMajorantQtilde_jump_le_three_square a)
    (Nat.cast_nonneg B : (0 : ℚ) ≤ B)
  push_cast
  nlinarith only [h]

theorem sharpPaperCap_le_short (B a : ℕ) :
    sharpPaperCap B a ≤ 90 * B * (a + 1) ^ 2 := by
  exact (sharpPaperCap_le_three_square B a).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right B (by decide : 3 ≤ 90)))

/-- Any integral scaled actual tail lies below the literal rational-floor cap. -/
theorem integral_scaled_tail_le_sharpPaperCap {B a : ℕ} {z : ℤ}
    (hz0 : 0 ≤ z) (hz : (z : ℝ) = (B : ℝ) * trueNormalizedState a) :
    z ≤ (sharpPaperCap B a : ℤ) := by
  have hzabs : ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg hz0
  have hzabsR : (z.natAbs : ℝ) = (z : ℝ) :=
    congrArg (fun t : ℤ => (t : ℝ)) hzabs
  have hboundR : (z.natAbs : ℝ) ≤
      ((B : ℚ) * carryMajorantQtilde (paperJumpIndex a) : ℚ) := by
    rw [hzabsR, hz]
    push_cast
    exact mul_le_mul_of_nonneg_left (trueNormalizedState_le_carryMajorantQtilde a)
      (Nat.cast_nonneg B)
  have hboundQ : (z.natAbs : ℚ) ≤ (B : ℚ) * carryMajorantQtilde (paperJumpIndex a) := by
    exact_mod_cast hboundR
  have hf : z.natAbs ≤ sharpPaperCap B a := by
    unfold sharpPaperCap
    -- Mathlib/Algebra/Order/Floor/Defs.lean: Nat.le_floor_iff.
    exact (Nat.le_floor_iff
      (mul_nonneg (Nat.cast_nonneg B) (carryMajorantQtilde_nonneg _))).mpr hboundQ
  have hfZ : ((z.natAbs : ℕ) : ℤ) ≤ (sharpPaperCap B a : ℤ) := by exact_mod_cast hf
  simpa only [hzabs] using hfZ

/-- Every equality, onset, positivity, recurrence and cap printed in the bridge.
The hypotheses do not need the numerator and denominator to be reduced. -/
theorem sharp_fixed_split_bridge {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a : ℕ, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      1 ≤ paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ (sharpPaperCap B a : ℤ) ∧
      sharpPaperCap B a ≤ 90 * B * (a + 1) ^ 2 := by
  intro a ha
  obtain ⟨hc, hp, hr, _⟩ := short_fixed_split_bridge hB hD hval a ha
  have hcap := integral_scaled_tail_le_sharpPaperCap hp.le hc
  exact ⟨hc, by omega, hr, hcap, sharpPaperCap_le_short B a⟩

/-- The recurrence plus the printed cap is an actual rationality consequence. -/
theorem actual_carry_at_sharp_cap {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∃ z : ℕ → ℤ, ∀ a, u + 1 + 2 * v + 3 * w ≤ a →
      (z a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      0 < z a ∧ z a ≤ (sharpPaperCap B a : ℤ) ∧
      z (a + 1) = (dyadicBlockBase235 a : ℤ) * z a -
        (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) := by
  refine ⟨paperReducedCarry B, ?_⟩
  intro a ha
  obtain ⟨hc, hp, hr, hcap, _⟩ := sharp_fixed_split_bridge hB hD hval a ha
  exact ⟨hc, by omega, hcap, hr⟩

/-- Any valid dominating cap has the rationality-to-contradiction direction. -/
theorem irrational_of_escape_dominating_sharp_cap (G : ℕ → ℕ → ℕ)
    (hdom : ∀ B a, 0 < B → sharpPaperCap B a ≤ G B a)
    (hesc : CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G) :
    Irrational paperSeries235 := by
  have hposden : ∀ N : ℤ, ∀ D : ℕ, 0 < D →
      paperSeries235 ≠ (N : ℝ) / (D : ℝ) := by
    intro N D hD hv
    obtain ⟨u, v, w, B, hsplit, hB, hcop⟩ := exists_smooth_coprime_split D hD
    have hbridge := sharp_fixed_split_bridge hB hsplit hv
    apply no_positive_reducedCarry_of_cofinalLocalWindowEscape_onset
      dyadicBlockBase235 dyadicOrderedBlockDigit235 G hesc B hB hcop
      (u + 1 + 2 * v + 3 * w) (paperReducedCarry B)
    · intro a ha
      exact (hbridge a ha).2.2.1
    · intro a ha
      have hp := (hbridge a ha).2.1
      omega
    · intro a ha
      have hp : 0 ≤ paperReducedCarry B a := by
        have := (hbridge a ha).2.1
        omega
      have hcast : ((Int.natAbs (paperReducedCarry B a) : ℕ) : ℤ) =
          paperReducedCarry B a := Int.natAbs_of_nonneg hp
      have huZ := (hbridge a ha).2.2.2.1
      rw [← hcast] at huZ
      have hu : Int.natAbs (paperReducedCarry B a) ≤ sharpPaperCap B a := by
        exact_mod_cast huZ
      exact hu.trans (hdom B a hB)
  -- Same positive-denominator normalisation as the compiled round-7 bridge.
  rw [irrational_iff_ne_rational]
  intro a b hb
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · intro hv
    have hbn : 0 < (-b).toNat := by omega
    have hcast : (((-b).toNat : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
    apply hposden (-a) (-b).toNat hbn
    have hR : (((-b).toNat : ℕ) : ℝ) = -(b : ℝ) := by exact_mod_cast hcast
    rw [hv, hR]
    push_cast
    rw [neg_div_neg_eq]
  · intro hv
    have hbn : 0 < b.toNat := by omega
    have hcast : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hbpos.le
    apply hposden a b.toNat hbn
    have hR : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by exact_mod_cast hcast
    simpa only [hR] using hv

/-- The long cap itself, with every original cofinal quantifier unchanged. -/
theorem sharp_cap_window_equivalence :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 sharpPaperCap ↔
      Irrational paperSeries235 := by
  constructor
  · exact irrational_of_escape_dominating_sharp_cap sharpPaperCap (fun _ _ _ => le_rfl)
  · intro h
    exact cofinalLocalWindowEscape_of_irrational_of_quadratic
      (irrational_tail_one_of_paperSeries h) sharpPaperCap (fun B => 3 * B)
      sharpPaperCap_le_three_square


end ErdosProblems.Erdos269.PaperR10
