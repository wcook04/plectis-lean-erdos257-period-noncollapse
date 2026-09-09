import ErdosProblems.Erdos269.PaperR7RationalBridge
import ErdosProblems.Erdos269.PaperR7BasicAssembly
import ErdosProblems.Erdos269.JumpConstraintMajorant

/-!
# Round 7: exact window statements at the correct bounds

The short cap is `90 B (a+1)^2`. The long cap is `floor(B Q(n_a))`.
They are separately named. No validity claim about the latter is inferred from
the former. The bounded-length obstruction needs only growth of the long cap,
so it can be proved without assuming the unresolved `X_a <= Q(n_a)` bridge.

Validation: authored, not compiled. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators

noncomputable abbrev actualWindowBase (lo len : ℕ) : ℤ :=
  windowBase (fun a => (dyadicBlockBase235 a : ℤ)) lo len

noncomputable abbrev actualWindowForcing (lo len : ℕ) : ℤ :=
  windowForcing (fun a => (dyadicBlockBase235 a : ℤ))
    (fun a => (dyadicOrderedBlockDigit235 a : ℤ)) lo len

/-- The criterion as printed: positive starting thresholds and the literal cap. -/
def ShortPaperEscape : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 → ∀ a₀ : ℕ, 1 ≤ a₀ →
    ∃ lo len : ℕ, a₀ ≤ lo ∧ 0 < len ∧
      90 * B * (lo + len + 1) ^ 2 <
        leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
          (-((B : ℤ) * actualWindowForcing lo len))

theorem shortPaperEscape_iff_source :
    ShortPaperEscape ↔ ActualCofinalLocalWindowEscape := by
  constructor
  · intro h B hB hcop a₀
    obtain ⟨lo, len, hlo, hlen, hesc⟩ := h B hB hcop (max a₀ 1) (le_max_right _ _)
    refine ⟨lo, len, (le_max_left _ _).trans hlo, hlen, ?_, ?_⟩
    · have hp := windowBase235_pos lo len
      have hn : actualWindowBase lo len ≠ 0 := hp.ne'
      exact Int.natAbs_pos.mpr hn
    · simpa [bridgeWidth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hesc
  · intro h B hB hcop a₀ _
    obtain ⟨lo, len, hlo, hlen, _, hesc⟩ := h B hB hcop a₀
    refine ⟨lo, len, hlo, hlen, ?_⟩
    simpa [bridgeWidth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hesc

/-- Whole short-note `res:windowconsumer`, for the literal smooth-number sum. -/
theorem short_window_equivalence :
    Irrational paperSeries235 ↔ ShortPaperEscape := by
  rw [paperSeries235_eq_shellTsum, shortPaperEscape_iff_source]
  exact actualCofinalLocalWindowEscape_iff_irrational_value.symm

/-- Formalise the printed warning: escape against zero is automatic. -/
theorem escape_zero_cap :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235
      (fun _ _ => 0) := by
  intro B _ _ a₀
  have hp : 0 < Int.natAbs (actualWindowBase a₀ 1) :=
    Int.natAbs_pos.mpr (windowBase235_pos a₀ 1).ne'
  exact ⟨a₀, 1, le_refl _, by norm_num, hp,
    (leastPositiveResidue_pos_le hp (-((B : ℤ) * actualWindowForcing a₀ 1))).1⟩

/-- Natural-number product corresponding to the source's integral window base. -/
noncomputable def actualWindowProduct (lo len : ℕ) : ℕ :=
  ∏ j ∈ Finset.range len, dyadicBlockBase235 (lo + j)

theorem actualWindowBase_eq_product (lo len : ℕ) :
    actualWindowBase lo len = (actualWindowProduct lo len : ℤ) := by
  induction len with
  | zero => simp [actualWindowProduct, actualWindowBase, windowBase]
  | succ len ih =>
    simp only [actualWindowBase, windowBase] at ih ⊢
    rw [ih]
    simp only [actualWindowProduct, Finset.prod_range_succ, Nat.cast_mul]
    ring

theorem actualWindowProduct_pos (lo len : ℕ) : 0 < actualWindowProduct lo len := by
  have h : (0 : ℤ) < (actualWindowProduct lo len : ℤ) := by
    rw [← actualWindowBase_eq_product]
    exact windowBase235_pos lo len
  exact_mod_cast h

theorem height_windowProduct (lo len : ℕ) :
    threePrimeHeight 2 3 5 (2 ^ (lo + len)) =
      threePrimeHeight 2 3 5 (2 ^ lo) * actualWindowProduct lo len := by
  induction len with
  | zero => simp [actualWindowProduct]
  | succ len ih =>
    rw [show lo + (len + 1) = (lo + len) + 1 by omega,
      threePrimeHeight_dyadicBlock_succ, ih]
    simp only [actualWindowProduct, Finset.prod_range_succ]
    ring

/-- Exact integer-log growth law before converting the logarithms to real floors. -/
theorem actualWindowProduct_eq_log_monomial (lo len : ℕ) :
    actualWindowProduct lo len =
      2 ^ len *
        3 ^ (Nat.log 3 (2 ^ (lo + len)) - Nat.log 3 (2 ^ lo)) *
        5 ^ (Nat.log 5 (2 ^ (lo + len)) - Nat.log 5 (2 ^ lo)) := by
  have hpow : (2 : ℕ) ^ lo ≤ 2 ^ (lo + len) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := Nat.log_mono_right (b := 3) hpow
  have h5 := Nat.log_mono_right (b := 5) hpow
  have hHpos := threePrimeHeightQ235_pos (2 ^ lo)
  apply mul_left_cancel₀ hHpos.ne'
  rw [← height_windowProduct]
  unfold threePrimeHeight
  simp only [Nat.log_pow (by norm_num : 1 < (2 : ℕ))]
  -- Abstract the four integer logarithms so that `pow_add` below can only reach
  -- the leading power of two, never the arguments of the logarithms.
  set L3 := Nat.log 3 (2 ^ (lo + len)) with _hL3
  set L5 := Nat.log 5 (2 ^ (lo + len)) with _hL5
  set M3 := Nat.log 3 (2 ^ lo) with _hM3
  set M5 := Nat.log 5 (2 ^ lo) with _hM5
  have he3 : 3 ^ Nat.log 3 (2 ^ (lo + len)) =
      3 ^ Nat.log 3 (2 ^ lo) *
        3 ^ (Nat.log 3 (2 ^ (lo + len)) - Nat.log 3 (2 ^ lo)) := by
    rw [← pow_add, show Nat.log 3 (2 ^ lo) +
      (Nat.log 3 (2 ^ (lo + len)) - Nat.log 3 (2 ^ lo)) =
      Nat.log 3 (2 ^ (lo + len)) by omega]
  have he5 : 5 ^ Nat.log 5 (2 ^ (lo + len)) =
      5 ^ Nat.log 5 (2 ^ lo) *
        5 ^ (Nat.log 5 (2 ^ (lo + len)) - Nat.log 5 (2 ^ lo)) := by
    rw [← pow_add, show Nat.log 5 (2 ^ lo) +
      (Nat.log 5 (2 ^ (lo + len)) - Nat.log 5 (2 ^ lo)) =
      Nat.log 5 (2 ^ (lo + len)) by omega]
  rw [pow_add, he3, he5]
  ring

/-- The logarithmic floor used in the paper, with no numerical approximation. -/
theorem natLog_two_pow_eq_floor (b a : ℕ) :
    Nat.log b (2 ^ a) = ⌊(a : ℝ) * Real.logb b 2⌋₊ := by
  rw [← Real.natFloor_logb_natCast b (2 ^ a), Nat.cast_pow, Real.logb_pow]
  norm_num

/-- At a dyadic endpoint the leading two-factor is exact, giving `15`, not `30`. -/
theorem eight_pow_lt_fifteen_dyadic_height (a : ℕ) :
    (8 : ℝ) ^ a < 15 * (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) := by
  have h3 := Nat.lt_pow_succ_log_self (b := 3) (by norm_num) (2 ^ a)
  have h5 := Nat.lt_pow_succ_log_self (b := 5) (by norm_num) (2 ^ a)
  have h35 := Nat.mul_lt_mul_of_lt_of_lt h3 h5
  have hp : (0 : ℕ) < 2 ^ a := by positivity
  have hmul := Nat.mul_lt_mul_of_pos_left h35 hp
  have hnat : (8 : ℕ) ^ a < 15 * threePrimeHeight 2 3 5 (2 ^ a) := by
    calc
      (8 : ℕ) ^ a = 2 ^ a * (2 ^ a * 2 ^ a) := by
        rw [eight_pow_eq_two_pow_cube]
        ring
      _ < 2 ^ a * (3 ^ (Nat.log 3 (2 ^ a) + 1) *
          5 ^ (Nat.log 5 (2 ^ a) + 1)) := hmul
      _ = 15 * threePrimeHeight 2 3 5 (2 ^ a) := by
        simp only [threePrimeHeight, Nat.log_pow (by norm_num : 1 < (2 : ℕ)), pow_succ]
        ring
  exact_mod_cast hnat

/-- Both strict constants from long-record `res:window-growth`. -/
theorem actualWindowProduct_geometric_bounds (lo len : ℕ) :
    (8 : ℝ) ^ len / 15 < (actualWindowProduct lo len : ℝ) ∧
    (actualWindowProduct lo len : ℝ) < 15 * (8 : ℝ) ^ len := by
  -- Everything is kept at the exponent `lo + len`, and only the very last step
  -- splits `8 ^ (lo + len)`. Rewriting with `pow_add` earlier would also reach
  -- the `2 ^ (lo + len)` sitting inside the height, which must stay folded.
  have hW : (0 : ℝ) < (actualWindowProduct lo len : ℝ) := by
    exact_mod_cast actualWindowProduct_pos lo len
  have hpow : (0 : ℝ) < (8 : ℝ) ^ lo := by positivity
  have hZ : (threePrimeHeight 2 3 5 (2 ^ (lo + len)) : ℝ) =
      (threePrimeHeight 2 3 5 (2 ^ lo) : ℝ) * (actualWindowProduct lo len : ℝ) := by
    exact_mod_cast height_windowProduct lo len
  have hAL : (8 : ℝ) ^ lo < 15 * (threePrimeHeight 2 3 5 (2 ^ lo) : ℝ) :=
    eight_pow_lt_fifteen_dyadic_height lo
  have hAU : (threePrimeHeight 2 3 5 (2 ^ lo) : ℝ) ≤ (8 : ℝ) ^ lo :=
    dyadic_height_le_eight_pow lo
  have hZL : (8 : ℝ) ^ (lo + len) <
      15 * (threePrimeHeight 2 3 5 (2 ^ (lo + len)) : ℝ) :=
    eight_pow_lt_fifteen_dyadic_height (lo + len)
  have hZU : (threePrimeHeight 2 3 5 (2 ^ (lo + len)) : ℝ) ≤ (8 : ℝ) ^ (lo + len) :=
    dyadic_height_le_eight_pow (lo + len)
  have h8 : (8 : ℝ) ^ (lo + len) = (8 : ℝ) ^ lo * (8 : ℝ) ^ len := pow_add 8 lo len
  rw [hZ, h8] at hZL hZU
  constructor
  · apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 15)).mpr
    have hmul : (8 : ℝ) ^ lo * (8 : ℝ) ^ len <
        (8 : ℝ) ^ lo * ((actualWindowProduct lo len : ℝ) * 15) := by
      nlinarith [mul_le_mul_of_nonneg_right hAU hW.le]
    exact lt_of_mul_lt_mul_left hmul hpow.le
  · have hmul : (8 : ℝ) ^ lo * (actualWindowProduct lo len : ℝ) <
        (8 : ℝ) ^ lo * (15 * (8 : ℝ) ^ len) := by
      nlinarith [mul_lt_mul_of_pos_right hAL hW]
    exact lt_of_mul_lt_mul_left hmul hpow.le

/-- Whole growth law, with natural floors of nonnegative quantities.
Thus subtraction is the nonnegative floor difference appearing on the page. -/
theorem long_window_growth (lo len : ℕ) (_hlen : 1 ≤ len) :
    actualWindowBase lo len =
      ((2 ^ len *
        3 ^ (⌊((lo + len : ℕ) : ℝ) * Real.logb 3 2⌋₊ -
          ⌊(lo : ℝ) * Real.logb 3 2⌋₊) *
        5 ^ (⌊((lo + len : ℕ) : ℝ) * Real.logb 5 2⌋₊ -
          ⌊(lo : ℝ) * Real.logb 5 2⌋₊) : ℕ) : ℤ) ∧
    (8 : ℝ) ^ len / 15 < (actualWindowBase lo len : ℝ) ∧
    (actualWindowBase lo len : ℝ) < 15 * (8 : ℝ) ^ len := by
  refine ⟨?_, ?_⟩
  · rw [actualWindowBase_eq_product, actualWindowProduct_eq_log_monomial]
    simp only [natLog_two_pow_eq_floor]
    norm_num
  · simpa only [actualWindowBase_eq_product, Int.cast_natCast] using
      actualWindowProduct_geometric_bounds lo len

/-- The long record's actual jump index. -/
def paperJumpIndex (a : ℕ) : ℕ := a + Nat.log 3 (2 ^ a) + Nat.log 5 (2 ^ a)

/-- The long record's exact cap. It is NOT the short note's `90` cap. -/
noncomputable def longPaperCap (B a : ℕ) : ℕ :=
  ⌊(B : ℚ) * carryMajorantQ (paperJumpIndex a)⌋₊

/-- Only growth, not validity as a carry bound, is required for this lemma. -/
theorem start_le_longPaperCap {B a : ℕ} (hB : 0 < B) : a ≤ longPaperCap B a := by
  have hn : a ≤ paperJumpIndex a := by unfold paperJumpIndex; omega
  have hnon : (0 : ℚ) ≤ carryMajorantQ (paperJumpIndex a) := by
    unfold carryMajorantQ
    positivity
  have hsq : (paperJumpIndex a : ℚ) ≤ (paperJumpIndex a : ℚ) ^ 2 := by
    cases hidx : paperJumpIndex a with
    | zero => norm_num
    | succ n => push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
  have hQ : (paperJumpIndex a : ℚ) ≤ carryMajorantQ (paperJumpIndex a) := by
    unfold carryMajorantQ
    nlinarith
  have hBR : (1 : ℚ) ≤ B := by exact_mod_cast hB
  apply (Nat.le_floor_iff (mul_nonneg (Nat.cast_nonneg B) hnon)).mpr
  calc
    (a : ℚ) ≤ (paperJumpIndex a : ℚ) := by exact_mod_cast hn
    _ ≤ carryMajorantQ (paperJumpIndex a) := hQ
    _ ≤ (B : ℚ) * carryMajorantQ (paperJumpIndex a) := by nlinarith

/-- Crude but sufficient upper bound on a fixed-length window modulus. -/
theorem actualWindowProduct_le_thirty_pow (lo len : ℕ) :
    actualWindowProduct lo len ≤ 30 ^ len := by
  induction len with
  | zero => simp [actualWindowProduct]
  | succ len ih =>
    simp only [actualWindowProduct, Finset.prod_range_succ] at ih ⊢
    rw [pow_succ]
    exact Nat.mul_le_mul ih (dyadicBlockBase235_mem_interval (lo + len)).2

/-- An explicit finite box for every bounded-length escape against the exact long cap. -/
theorem escaping_start_lt_thirty_pow {B H lo len : ℕ}
    (hB : 0 < B) (hlen : len ≤ H)
    (hesc : longPaperCap B (lo + len) <
      leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
        (-((B : ℤ) * actualWindowForcing lo len))) : lo < 30 ^ H := by
  have hp : 0 < Int.natAbs (actualWindowBase lo len) :=
    Int.natAbs_pos.mpr (windowBase235_pos lo len).ne'
  have hres := (leastPositiveResidue_pos_le hp
    (-((B : ℤ) * actualWindowForcing lo len))).2
  have hcap := start_le_longPaperCap (a := lo + len) hB
  have hnat : Int.natAbs (actualWindowBase lo len) ≤ 30 ^ H := by
    rw [actualWindowBase_eq_product, Int.natAbs_natCast]
    exact (actualWindowProduct_le_thirty_pow lo len).trans
      (Nat.pow_le_pow_right (by norm_num) hlen)
  omega

/-- Full long-record `res:no-bounded-length`, with a stronger explicit finite enclosure. -/
theorem long_no_bounded_length {B H : ℕ} (hB : 0 < B)
    (_hcop : Nat.Coprime B 30) (_hH : 1 ≤ H) :
    Set.Finite {lo : ℕ | ∃ len : ℕ, 1 ≤ len ∧ len ≤ H ∧
      longPaperCap B (lo + len) <
        leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
          (-((B : ℤ) * actualWindowForcing lo len))} := by
  apply (Finset.finite_toSet (Finset.range (30 ^ H))).subset
  intro lo hlo
  obtain ⟨len, _, hlen, hesc⟩ := hlo
  exact Finset.mem_range.mpr (escaping_start_lt_thirty_pow hB hlen hesc)

end ErdosProblems.Erdos269.PaperR7
