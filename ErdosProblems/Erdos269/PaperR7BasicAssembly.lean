import ErdosProblems.Erdos269.KernelCarryRank
import ErdosProblems.Erdos269.IntegralBranchExtinction
import ErdosProblems.Erdos269.RestrictedFloorSum

/-!
# Round 7: whole displayed statements assembled from the supplied library

No replacement definitions of the underlying geometry are introduced. Each
assembly names every clause printed under its paper label. These conjunctions
are intentionally explicit: a nearby individual helper is not silently counted
as an end-to-end paper theorem.

Validation: authored, not compiled. Dependencies are copied unchanged from the
packet and retain their original evidence status. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators

/-- Both clauses of the flagship theorem, including the empty minor. -/
theorem paper_uniform_rank_and_nonseparation {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (_hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ, ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
      ∀ k : ℕ, (Matrix.det fun a b : Fin n =>
        threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
    (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
      ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k) :=
  ⟨exists_uniform_nonsingular_threePrimeKernel_minor_of_prime hp hq hr hpr hqr,
    not_finite_separable_threePrimeKernel hp hq hr hpr hqr⟩

/-- Long-record `res:cell`: cell constancy, kernel constancy and all three jump ratios. -/
theorem paper_cell_constancy_and_jumps {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ x y : ℕ, x ≠ 0 → y ≠ 0 → SameThreePrimeLogCell p q r x y →
      smoothPrefixLcm p q r x = smoothPrefixLcm p q r y) ∧
    (∀ i j k i' j' k' : ℕ,
      SameThreePrimeLogCell p q r (smooth3Val p q r i j k)
        (smooth3Val p q r i' j' k') →
      threePrimeKernelQ p q r i j k = threePrimeKernelQ p q r i' j' k') ∧
    (∀ x y : ℕ, x ≠ 0 → y ≠ 0 →
      Nat.log p y = Nat.log p x + 1 → Nat.log q y = Nat.log q x →
      Nat.log r y = Nat.log r x →
      smoothPrefixLcm p q r y = p * smoothPrefixLcm p q r x) ∧
    (∀ x y : ℕ, x ≠ 0 → y ≠ 0 →
      Nat.log p y = Nat.log p x → Nat.log q y = Nat.log q x + 1 →
      Nat.log r y = Nat.log r x →
      smoothPrefixLcm p q r y = q * smoothPrefixLcm p q r x) ∧
    (∀ x y : ℕ, x ≠ 0 → y ≠ 0 →
      Nat.log p y = Nat.log p x → Nat.log q y = Nat.log q x →
      Nat.log r y = Nat.log r x + 1 →
      smoothPrefixLcm p q r y = r * smoothPrefixLcm p q r x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy hc
    exact smoothPrefixLcm_eq_of_sameLogCell hp hq hr hpq hpr hqr hx hy hc
  · intro i j k i' j' k' hc
    exact threePrimeKernelQ_eq_of_sameLogCell hc
  · intro x y hx hy h1 h2 h3
    exact smoothPrefixLcm_firstLogStep hp hq hr hpq hpr hqr hx hy h1 h2 h3
  · intro x y hx hy h1 h2 h3
    exact smoothPrefixLcm_secondLogStep hp hq hr hpq hpr hqr hx hy h1 h2 h3
  · intro x y hx hy h1 h2 h3
    exact smoothPrefixLcm_thirdLogStep hp hq hr hpq hpr hqr hx hy h1 h2 h3

/-- Both cardinalities in long-record `res:count`, in one declaration. -/
theorem paper_jump_count {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) :
    (threePrimePositiveJumpSet p q r n).card = 3 * n ∧
    (threePrimeJumpSetWithOrigin p q r n).card = 3 * n + 1 :=
  ⟨threePrimePositiveJumpSet_card hp hq hr hpq hpr hqr,
    threePrimeJumpSetWithOrigin_card hp hq hr hpq hpr hqr⟩

/-- All three implications in long-record `res:drop` / `res:shell`. -/
theorem paper_shell_projection_and_quadratic
    {p q r lo hi hp hq hr : ℕ} (hpPos : 0 < p) (hrPos : 0 < r) :
    (hi ≤ r * lo → (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (hp + 1) * (hq + 1)) ∧
    (hi ≤ p * lo → (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (hq + 1) * (hr + 1)) ∧
    (∀ j : ℕ, hi ≤ r * lo → hp ≤ hq → hq ≤ hr → hp + hq + hr = j →
      9 * (smoothExponentShell p q r lo hi hp hq hr).card ≤ (j + 3) ^ 2) := by
  refine ⟨smoothExponentShell_card_le_dropThird hrPos,
    smoothExponentShell_card_le_dropFirst hpPos, ?_⟩
  intro j hw hpq hqr hj
  exact smoothExponentShell_card_quadratic hrPos hw hpq hqr hj

/-- The actual outer-product identity AND all two-by-two minors, not one alone. -/
theorem paper_two_prime_rank {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    (∀ i j : ℕ, twoPrimeKernelQ p q i j =
      ((p ^ i * q ^ Nat.log q (p ^ i) : ℕ) : ℚ)⁻¹ *
        ((p ^ Nat.log p (q ^ j) * q ^ j : ℕ) : ℚ)⁻¹) ∧
    (∀ i i' j j' : ℕ,
      twoPrimeKernelQ p q i j * twoPrimeKernelQ p q i' j' -
        twoPrimeKernelQ p q i j' * twoPrimeKernelQ p q i' j = 0) :=
  ⟨twoPrimeKernelQ_eq_outer_product hp hq, twoPrimeKernelQ_minor_two_eq_zero hp hq⟩

/-- Exact numerical determinant, with every displayed entry and nonvanishing. -/
theorem paper_two_by_two_fixture :
    threePrimeKernelQ 2 3 5 0 0 0 = 1 ∧
    threePrimeKernelQ 2 3 5 0 1 0 = 1 / 6 ∧
    threePrimeKernelQ 2 3 5 1 0 0 = 1 / 2 ∧
    threePrimeKernelQ 2 3 5 1 1 0 = 1 / 60 ∧
    (Matrix.det (fun i j : Fin 2 => threePrimeKernelQ 2 3 5 i j 0)) = -(1 / 15 : ℚ) ∧
    (Matrix.det (fun i j : Fin 2 => threePrimeKernelQ 2 3 5 i j 0)) ≠ 0 := by
  norm_num [Matrix.det_fin_two, threePrimeKernelQ, threePrimeHeight, smooth3Val]

/-- Supplemental displayed `res:cube`: both inequalities, for arbitrary bases > 1. -/
theorem paper_cubic_height_bounds {p q r x : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hx : x ≠ 0) :
    (x : ℝ) ^ 3 / ((p : ℝ) * q * r) < (threePrimeHeight p q r x : ℝ) ∧
    (threePrimeHeight p q r x : ℝ) ≤ (x : ℝ) ^ 3 := by
  have ha := Nat.lt_pow_succ_log_self hp x
  have hb := Nat.lt_pow_succ_log_self hq x
  have hc := Nat.lt_pow_succ_log_self hr x
  have hprod := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt ha hb) hc
  have hnat : x ^ 3 < (p * q * r) * threePrimeHeight p q r x := by
    calc
      x ^ 3 = (x * x) * x := by ring
      _ < (p ^ (Nat.log p x + 1) * q ^ (Nat.log q x + 1)) *
        r ^ (Nat.log r x + 1) := hprod
      _ = (p * q * r) * threePrimeHeight p q r x := by
        simp only [threePrimeHeight, pow_succ]
        ring
  constructor
  · have hden : (0 : ℝ) < (p : ℝ) * q * r := by positivity
    apply (div_lt_iff₀ hden).mpr
    have hR : (x : ℝ) ^ 3 < ((p : ℝ) * q * r) *
        (threePrimeHeight p q r x : ℝ) := by exact_mod_cast hnat
    simpa [mul_comm] using hR
  · exact_mod_cast threePrimeHeight_le_cube p q r x hx

/-- Short-note residue consumer with the ordinary integer upper bound. -/
theorem paper_finite_endpoint_obstruction {W K : ℕ} {d B F : ℤ}
    (hW : 0 < W) (hd : 0 < d) (hbound : d ≤ (K : ℤ))
    (hmod : Int.ModEq (W : ℤ) d (-B * F)) :
    leastPositiveResidue W (-B * F) ≤ K := by
  by_contra h
  have hesc : K < leastPositiveResidue W (-B * F) := by omega
  have habs : Int.natAbs d ≤ K := by omega
  exact no_bounded_positive_int_state_of_leastPositiveResidue hW hd habs hesc hmod

/-- Four-part generic denominator reduction, with all assumptions explicit. -/
theorem paper_generic_denominator_reduction
    (c d b m : ℕ → ℤ) (s B : ℤ) (K : ℕ → ℤ)
    (hs : 0 < s) (hfac : ∀ n, c n = s * d n)
    (hrec : ∀ n, c (n + 1) = b n * c n - (s * B) * m n)
    (hpos : ∀ n, 0 < c n) (hbound : ∀ n, c n ≤ s * (B * K n)) :
    (∀ n, d (n + 1) = b n * d n - B * m n) ∧
    (∀ n, 0 < d n) ∧
    (∀ n, d n ≤ B * K n) ∧
    (∀ lo len, d (lo + len) = windowBase b lo len * d lo -
      B * windowForcing b m lo len) := by
  refine ⟨integralCarry_cancel_commonFactor c d b m s B hs.ne' hfac hrec,
    ?_, ?_, reducedIntegralCarry_window c d b m s B hs.ne' hfac hrec⟩
  · intro n
    exact (reducedCarry_pos_le_of_commonFactor hs (hfac n) (hpos n) (hbound n)).1
  · intro n
    exact (reducedCarry_pos_le_of_commonFactor hs (hfac n) (hpos n) (hbound n)).2

/-- Long-record `res:pinning`: identity, positivity, upward closure and full rigidity.
The epsilon formulation of the limit is used exactly as in the source theorem. -/
theorem paper_pinning_and_rigidity :
    (∀ a : ℕ, trueNormalizedState a =
      ((dyadicOrderedBlockDigit235 a : ℝ) + trueNormalizedState (a + 1)) /
        (dyadicBlockBase235 a : ℝ) ∧ 0 < trueNormalizedState a) ∧
    (∀ a : ℕ, ∀ z : ℤ, trueNormalizedState a = (z : ℝ) →
      ∀ n, a ≤ n → ∃ w : ℤ, trueNormalizedState n = (w : ℝ)) ∧
    (∀ (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ),
      (∀ n, 0 < width n) →
      (∀ n, A ≤ n → y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ)) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 2 ^ k < ε) →
      y A = trueNormalizedState A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    refine ⟨?_, trueNormalizedState_pos a⟩
    simpa only [add_div] using trueNormalizedState_pinning a
  · intro a z hz
    exact integral_state_upward_closed hz
  · intro width A y _ hrec hwin hwidth hvanish
    exact surviving_window_orbit_eq_true_state width A y hrec hwin hwidth hvanish

end ErdosProblems.Erdos269.PaperR7
