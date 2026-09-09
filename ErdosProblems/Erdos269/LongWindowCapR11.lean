import ErdosProblems.Erdos269.SharpWindowCapR10

/-! Narrow long-cap endpoint composition. No historical broad bridge import,
no missing producer, and no alteration of the onset or window conventions. -/
namespace ErdosProblems.Erdos269.PaperR11
open PaperR7 PaperR8 PaperR10

theorem sharpPaperCap_le_longR11 (B a : ℕ) : sharpPaperCap B a ≤ longPaperCap B a := by
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left (carryMajorantQtilde_lt_Q (paperJumpIndex a)).le
    (Nat.cast_nonneg B : (0 : ℚ) ≤ B)

theorem carryMajorantQ_jump_le_three_squareR11 (a : ℕ) :
    carryMajorantQ (paperJumpIndex a) ≤ 3 * ((a : ℚ) + 1) ^ 2 := by
  have hn : (paperJumpIndex a : ℚ) ≤ 3 * (a : ℚ) := by
    exact_mod_cast paperJumpIndex_le_three_mul_r10 a
  have hn0 : (0 : ℚ) ≤ paperJumpIndex a := Nat.cast_nonneg _
  have ha0 : (0 : ℚ) ≤ a := Nat.cast_nonneg _
  have hprod : (0 : ℚ) ≤
      (3 * (a : ℚ) - paperJumpIndex a) * (3 * (a : ℚ) + paperJumpIndex a) :=
    mul_nonneg (sub_nonneg.mpr hn) (by positivity)
  have hsq : (paperJumpIndex a : ℚ) ^ 2 ≤ 9 * (a : ℚ) ^ 2 := by nlinarith only [hprod]
  unfold carryMajorantQ
  nlinarith only [hsq, hn, hn0, ha0, sq_nonneg (a : ℚ)]

theorem longPaperCap_le_three_squareR11 (B a : ℕ) :
    longPaperCap B a ≤ 3 * B * (a + 1) ^ 2 := by
  unfold longPaperCap
  apply Nat.floor_le_of_le
  have h := mul_le_mul_of_nonneg_left (carryMajorantQ_jump_le_three_squareR11 a)
    (Nat.cast_nonneg B : (0 : ℚ) ≤ B)
  push_cast
  nlinarith only [h]

/-- The printed long cap, including the canonical integer carry, positivity,
recurrence and the same fixed-split onset as the checked short bridge. -/
theorem long_fixed_split_bridgeR11 {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      1 ≤ paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ (longPaperCap B a : ℤ) := by
  intro a ha
  obtain ⟨hc, hp, hr, hu, _⟩ := sharp_fixed_split_bridge hB hD hval a ha
  refine ⟨hc, hp, hr, hu.trans ?_⟩
  exact_mod_cast sharpPaperCap_le_longR11 B a

/-- Closed-window endpoint at every permitted start, including length zero. -/
theorem long_fixed_split_windowR11 {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) (a len : ℕ)
    (ha : u + 1 + 2 * v + 3 * w ≤ a) :
    1 ≤ paperReducedCarry B (a + len) ∧
      paperReducedCarry B (a + len) ≤ (longPaperCap B (a + len) : ℤ) ∧
      paperReducedCarry B (a + len) = actualWindowBase a len * paperReducedCarry B a -
        (B : ℤ) * actualWindowForcing a len := by
  have hs := long_fixed_split_bridgeR11 hB hD hval a ha
  have hf := long_fixed_split_bridgeR11 hB hD hval (a + len) (by omega)
  refine ⟨hf.2.1, hf.2.2.2, ?_⟩
  have hr := trueNormalizedState_window a len
  change trueNormalizedState (a + len) =
    (actualWindowBase a len : ℝ) * trueNormalizedState a - (actualWindowForcing a len : ℝ) at hr
  have he : (paperReducedCarry B (a + len) : ℝ) =
      ((actualWindowBase a len * paperReducedCarry B a - (B : ℤ) * actualWindowForcing a len : ℤ) : ℝ) := by
    push_cast
    rw [hf.1, hs.1, hr]
    ring
  exact_mod_cast he

/-- The actual long-paper equivalence, not an asserted cofinal producer. -/
theorem long_cap_window_equivalenceR11 :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 longPaperCap ↔
      Irrational paperSeries235 := by
  constructor
  · exact irrational_of_escape_dominating_sharp_cap longPaperCap
      (fun B a _ => sharpPaperCap_le_longR11 B a)
  · intro h
    exact cofinalLocalWindowEscape_of_irrational_of_quadratic
      (irrational_tail_one_of_paperSeries h) longPaperCap (fun B => 3 * B)
      longPaperCap_le_three_squareR11

end ErdosProblems.Erdos269.PaperR11
