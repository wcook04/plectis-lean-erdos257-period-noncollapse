import ErdosProblems.Erdos68.FactorialGapPlateauCore
import Mathlib.Tactic.NormNum

/-!
# Erdős #68: factorial-gap plateau supplement

Asymptotic coefficient bounds, generic coboundary lemmas, doubled-prime
criteria, rational first-crossing bounds, and the independent Type-2 interval
inequality.  The recurrence core and exact finite certificates live in their
own canonical modules; `FactorialZeroPlateau` re-exports the complete family.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-! ## Coefficient bounds and generic coboundary lemmas -/

/-- The ordinary-factorial-series coefficient `1 - factorialGapStepCarry m`
has at most linear growth.  This is the pointwise estimate needed for the
small-numerator hypothesis in the Erdős--Straus cumulative-product
rationality criterion. -/
theorem abs_one_sub_factorialGapStepCarry_le
    {m : ℕ} (hm : 3 ≤ m) :
    |(1 : ℤ) - factorialGapStepCarry m| ≤ (m : ℤ) := by
  obtain ⟨hlower, hupper⟩ := factorialGapStepCarry_bounds hm
  rw [abs_le]
  constructor <;> omega

/-- The carry-defect coefficients satisfy the exact asymptotic hypothesis
from Erdős--Straus Theorem 2.1 after taking the cumulative radices
`alpha_m = m`: `|1 - beta_m| / ((m-1)m)` tends to zero. -/
theorem tendsto_abs_one_sub_factorialGapStepCarry_div :
    Filter.Tendsto
      (fun m : ℕ =>
        ((|(1 : ℤ) - factorialGapStepCarry m| : ℤ) : ℝ) /
          ((((m - 1) * m : ℕ) : ℝ)))
      Filter.atTop
      (nhds 0) := by
  have hpredTopNat :
      Filter.Tendsto (fun m : ℕ => m - 1)
        Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b + 1, fun m hm => by omega⟩
  have hpredTopReal :
      Filter.Tendsto (fun m : ℕ => ((m - 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hpredTopNat
  have hinv :
      Filter.Tendsto (fun m : ℕ => 1 / ((m - 1 : ℕ) : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hpredTopReal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℕ => (0 : ℝ))
    (h := fun m : ℕ => 1 / ((m - 1 : ℕ) : ℝ))
    tendsto_const_nhds hinv ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with m hm
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with m hm
    have hcoeff := abs_one_sub_factorialGapStepCarry_le hm
    have hcoeffReal :
        ((|(1 : ℤ) - factorialGapStepCarry m| : ℤ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hcoeff
    have hmPos : (0 : ℝ) < m := by positivity
    have hpredPos : (0 : ℝ) < (m - 1 : ℕ) := by
      exact_mod_cast (show 0 < m - 1 by omega)
    calc
      ((|(1 : ℤ) - factorialGapStepCarry m| : ℤ) : ℝ) /
            ((((m - 1) * m : ℕ) : ℝ)) ≤
          (m : ℝ) / ((((m - 1) * m : ℕ) : ℝ)) := by
            apply div_le_div_of_nonneg_right hcoeffReal
            positivity
      _ = 1 / ((m - 1 : ℕ) : ℝ) := by
        push_cast
        field_simp

/-- A state bound for the Erdős--Straus coboundary recurrence.  If the
coefficient lies in the factorial-gap window `2 - m ≤ d m ≤ 2` and the next
state satisfies the assumed half-radix
window, then every sufficiently late state lies in the canonical interval
`(-B, 0]`.

The lower endpoint first follows weakly from the coefficient and half-radix
bounds.  Equality `c m = -B` would force `c (m + 1) ≤ -2B`, contradicting
that same weak bound at the next index. -/
theorem eventually_bounded_coboundary_state
    {B N : ℕ} (hB : 0 < B) {d c : ℕ → ℤ}
    (hrec : ∀ m : ℕ, N ≤ m →
      (B : ℤ) * d m = (m : ℤ) * c m - c (m + 1))
    (hcoeff : ∀ m : ℕ, N ≤ m →
      (2 : ℤ) - (m : ℤ) ≤ d m ∧ d m ≤ 2)
    (hhalf : ∀ m : ℕ, N ≤ m →
      2 * |c (m + 1)| < (m : ℤ)) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      -(B : ℤ) < c m ∧ c m ≤ 0 := by
  let M : ℕ := max N (4 * B)
  have hNM : N ≤ M := by
    dsimp [M]
    exact Nat.le_max_left _ _
  have hFourBM : 4 * B ≤ M := by
    dsimp [M]
    exact Nat.le_max_right _ _
  have hBInt : (0 : ℤ) < B := by
    exact_mod_cast hB
  have hclosedLower :
      ∀ {m : ℕ}, M ≤ m → -(B : ℤ) ≤ c m := by
    intro m hm
    have hNm : N ≤ m := hNM.trans hm
    have hmNonneg : (0 : ℤ) ≤ m := by positivity
    have hrecM := hrec m hNm
    have hdLower := (hcoeff m hNm).1
    have hhalfM := hhalf m hNm
    have hnegAbs : -((m : ℤ)) < 2 * c (m + 1) := by
      have hcNegAbs : -|c (m + 1)| ≤ c (m + 1) :=
        neg_abs_le (c (m + 1))
      nlinarith
    by_contra hnot
    have hcLow : c m ≤ -(B : ℤ) - 1 := by omega
    nlinarith
  have hclosedUpper :
      ∀ {m : ℕ}, M ≤ m → c m ≤ 0 := by
    intro m hm
    have hNm : N ≤ m := hNM.trans hm
    have hmFourNat : 4 * B ≤ m := hFourBM.trans hm
    have hmFourInt : 4 * (B : ℤ) ≤ (m : ℤ) := by
      exact_mod_cast hmFourNat
    have hmNonneg : (0 : ℤ) ≤ m := by positivity
    have hrecM := hrec m hNm
    have hdUpper := (hcoeff m hNm).2
    have hhalfM := hhalf m hNm
    have hposAbs : 2 * c (m + 1) < (m : ℤ) := by
      have hcLeAbs : c (m + 1) ≤ |c (m + 1)| :=
        le_abs_self (c (m + 1))
      nlinarith
    by_contra hnot
    have hcPos : 1 ≤ c m := by omega
    nlinarith
  refine ⟨M, ?_⟩
  intro m hm
  have hlower := hclosedLower hm
  have hupper := hclosedUpper hm
  refine ⟨?_, hupper⟩
  by_contra hnot
  have hcEq : c m = -(B : ℤ) := by omega
  have hNm : N ≤ m := hNM.trans hm
  have hrecM := hrec m hNm
  have hdLower := (hcoeff m hNm).1
  have hnextLower : -(B : ℤ) ≤ c (m + 1) :=
    hclosedLower (by omega)
  nlinarith

/-- Once an Erdős--Straus coboundary state lies in the canonical interval
`(-B, 0]`, its recurrence has no nonzero infinite trajectory.  At a large
index divisible by `B`, the next state is a multiple of `B` in that
interval and hence zero; zero then remains absorbing. -/
theorem eventually_zero_of_bounded_coboundary_core
    {B N : ℕ} (hB : 0 < B) {d c : ℕ → ℤ}
    (hrec : ∀ m : ℕ, N ≤ m →
      (B : ℤ) * d m = (m : ℤ) * c m - c (m + 1))
    (hstate : ∀ m : ℕ, N ≤ m →
      -(B : ℤ) < c m ∧ c m ≤ 0) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → d m = 0 := by
  have hBInt : (0 : ℤ) < B := by exact_mod_cast hB
  let q : ℕ := B * (N + 1)
  have hNq : N ≤ q := by
    have hBOne : 1 ≤ B := hB
    have hNq' : N + 1 ≤ q := by
      dsimp [q]
      simpa using Nat.mul_le_mul_right (N + 1) hBOne
    omega
  have hqCast :
      (q : ℤ) = (B : ℤ) * ((N + 1 : ℕ) : ℤ) := by
    dsimp [q]
  let k : ℤ := (((N + 1 : ℕ) : ℤ) * c q) - d q
  have hcNext : c (q + 1) = (B : ℤ) * k := by
    have hqRec := hrec q hNq
    rw [hqCast] at hqRec
    dsimp [k]
    calc
      c (q + 1) =
          (B : ℤ) * ((N + 1 : ℕ) : ℤ) * c q -
            (B : ℤ) * d q := by
              linarith
      _ = (B : ℤ) *
          (((N + 1 : ℕ) : ℤ) * c q - d q) := by ring
  have hqNextState := hstate (q + 1) (by omega)
  have hkLower : (-1 : ℤ) < k := by
    by_contra hnot
    have hk : k ≤ -1 := le_of_not_gt hnot
    have hmul :=
      mul_le_mul_of_nonneg_left hk hBInt.le
    rw [← hcNext] at hmul
    nlinarith [hqNextState.1]
  have hkUpper : k ≤ 0 := by
    by_contra hnot
    have hk : 1 ≤ k := by omega
    have hmul :=
      mul_le_mul_of_nonneg_left hk hBInt.le
    rw [← hcNext] at hmul
    nlinarith [hqNextState.2]
  have hkZero : k = 0 := by omega
  have hcBase : c (q + 1) = 0 := by
    rw [hcNext, hkZero, mul_zero]
  have hzeroStep :
      ∀ {m : ℕ}, q + 1 ≤ m → c m = 0 → c (m + 1) = 0 := by
    intro m hm hcm
    have hNm : N ≤ m := by omega
    have hmRec := hrec m hNm
    let r : ℤ := -d m
    have hcSucc : c (m + 1) = (B : ℤ) * r := by
      dsimp [r]
      rw [hcm] at hmRec
      calc
        c (m + 1) = -(B : ℤ) * d m := by linarith
        _ = (B : ℤ) * -d m := by ring
    have hmNextState := hstate (m + 1) (by omega)
    have hrLower : (-1 : ℤ) < r := by
      by_contra hnot
      have hr : r ≤ -1 := le_of_not_gt hnot
      have hmul :=
        mul_le_mul_of_nonneg_left hr hBInt.le
      rw [← hcSucc] at hmul
      nlinarith [hmNextState.1]
    have hrUpper : r ≤ 0 := by
      by_contra hnot
      have hr : 1 ≤ r := by omega
      have hmul :=
        mul_le_mul_of_nonneg_left hr hBInt.le
      rw [← hcSucc] at hmul
      nlinarith [hmNextState.2]
    have hrZero : r = 0 := by omega
    rw [hcSucc, hrZero, mul_zero]
  have hcZero :
      ∀ m : ℕ, q + 1 ≤ m → c m = 0 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hcBase
    | succ m hm ih => exact hzeroStep hm ih
  refine ⟨q + 1, ?_⟩
  intro m hm
  have hmRec := hrec m (by omega)
  have hcm := hcZero m hm
  have hcSucc := hcZero (m + 1) (by omega)
  have hmul : (B : ℤ) * d m = 0 := by
    simpa [hcm, hcSucc] using hmRec
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hBInt)

/-! ## Doubled-prime and single-power divisibility criteria -/

/-- At a doubled-prime index, a square divisibility hit has exactly two
surviving branches.  This is the exact series specialization
of the abstract two-stage strict-successor criterion: a proof of
irrationality may now rule out either a unit carry together with a
predecessor multiple, or the exceptional carry `1 + p` together with its
shifted predecessor residue. -/
theorem sq_dvd_double_strictFacTop_factorialGapPrefix_iff
    {p : ℕ} (hp : p.Prime) (hpTwo : p ≠ 2) :
    (p : ℤ) ^ 2 ∣
        strictFacTop
          ((factorialGapPrefix (2 * p) : ℚ) : ℝ) (2 * p) ↔
      (factorialGapStepCarry (2 * p) = 1 ∧
          (p : ℤ) ∣
            strictFacTop
              ((factorialGapPrefix (2 * p - 1) : ℚ) : ℝ)
              (2 * p - 1)) ∨
        (factorialGapStepCarry (2 * p) = 1 + (p : ℤ) ∧
          (p : ℤ) ∣
            2 *
                strictFacTop
                  ((factorialGapPrefix (2 * p - 1) : ℚ) : ℝ)
                  (2 * p - 1) -
              1) := by
  have hpThree : 3 ≤ p := by
    have hpTwoLe := hp.two_le
    omega
  have hm : 3 ≤ 2 * p := by omega
  have hrec :=
    strictFacTop_factorialGapPrefix_step
      (m := 2 * p) (show 2 ≤ 2 * p by omega)
  obtain ⟨hbLower, hbUpper⟩ :=
    factorialGapStepCarry_bounds hm
  exact
    sq_dvd_double_strictSuccessor_prime_iff
      hp hpTwo
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hrec)
      hbLower
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbUpper)

/-- A cofinal family of odd primes at which both doubled-index
square-hit branches fail proves the original Erdős #68 series irrational.
The hypothesis is stated entirely in terms of the actual carry and
predecessor strict successor; no such cofinal family is constructed here. -/
theorem
    irrational_factorialGapSeries_of_cofinal_double_prime_branch_failures
    (hmiss : ∀ B : ℕ, ∃ p : ℕ,
      p.Prime ∧ p ≠ 2 ∧ B < p ∧
        ¬((factorialGapStepCarry (2 * p) = 1 ∧
              (p : ℤ) ∣
                strictFacTop
                  ((factorialGapPrefix (2 * p - 1) : ℚ) : ℝ)
                  (2 * p - 1)) ∨
            (factorialGapStepCarry (2 * p) = 1 + (p : ℤ) ∧
              (p : ℤ) ∣
                2 *
                    strictFacTop
                      ((factorialGapPrefix (2 * p - 1) : ℚ) : ℝ)
                      (2 * p - 1) -
                  1))) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_prime_power_misses
      (k := 2)
  intro B
  obtain ⟨p, hp, hpTwo, hBp, hbranches⟩ := hmiss B
  refine ⟨p, hp, hBp, ?_⟩
  rw [sq_dvd_double_strictFacTop_factorialGapPrefix_iff hp hpTwo]
  exact hbranches

/-- Divisibility at an index `m` is equivalent to the predecessor gap lying
in one explicit short interval.  This removes the floor and carry from the
single-power (`k = 1`) condition. -/
theorem dvd_strictFacTop_factorialGapPrefix_iff_predecessorGap_window
    {m : ℕ} (hm : 3 ≤ m) :
    (m : ℤ) ∣
        strictFacTop ((factorialGapPrefix m : ℚ) : ℝ) m ↔
      1 + 1 / ((m.factorial : ℝ) - 1) <
          (m : ℝ) * factorialGapPredecessorGap m ∧
        (m : ℝ) * factorialGapPredecessorGap m ≤
          2 + 1 / ((m.factorial : ℝ) - 1) := by
  have hrec := strictFacTop_factorialGapPrefix_step (show 2 ≤ m by omega)
  obtain ⟨hbLower, hbUpper⟩ := factorialGapStepCarry_bounds hm
  have hmInt : (3 : ℤ) ≤ m := by exact_mod_cast hm
  rw [dvd_strictSuccessor_iff_roundingDigit_eq_one
    hmInt (by simpa using hrec) hbLower hbUpper]
  unfold factorialGapStepCarry
  simp only [one_div]
  constructor
  · intro hb
    have hfloor :
        ⌊1 + (((m.factorial : ℝ) - 1)⁻¹) -
            (m : ℝ) * factorialGapPredecessorGap m⌋ = (-1 : ℤ) := by
      omega
    obtain ⟨hminus, hzero⟩ := Int.floor_eq_iff.mp hfloor
    norm_num at hminus hzero
    constructor <;> linarith
  · rintro ⟨hlower, hupper⟩
    have hfloor :
        ⌊1 + (((m.factorial : ℝ) - 1)⁻¹) -
            (m : ℝ) * factorialGapPredecessorGap m⌋ = (-1 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        linarith
      · norm_num
        linarith
    omega

/-! ## Rational first crossings -/

/-- At any genuine first crossing of a rational grid level by the actual
Erdős #68 prefixes, the exit gap is positive and at most the newly added
factorial-gap term. -/
theorem actualFirstCrossing_gap_bounds
    {τ : ℕ} (hτ : 2 ≤ τ) {G : ℚ}
    (hbefore : factorialGapPrefix (τ - 1) < G)
    (hcross : G ≤ factorialGapPrefix τ) :
    0 < G - factorialGapPrefix (τ - 1) ∧
      G - factorialGapPrefix (τ - 1) ≤
        1 / ((τ.factorial : ℚ) - 1) := by
  constructor
  · linarith
  · rw [factorialGapPrefix_eq_prev_add hτ] at hcross
    linarith

/-- The normalized offset at a first crossing of the factorial grid.
For the actual Erdős #68 prefix this is
`τ! * (H_τ - G) = 1 + 1 / (τ! - 1) - τ! * (G - H_{τ-1})`. -/
noncomputable def firstExitDelta (τ : ℕ) (V : ℝ) : ℝ :=
  1 + 1 / ((τ.factorial : ℝ) - 1) - (τ.factorial : ℝ) * V

/-- The scaled distance from the crossing level to the new actual prefix is
the normalized first-exit offset expressed in terms of the preceding gap. -/
theorem actualFirstCrossing_scaledOffset_eq
    {τ : ℕ} (hτ : 2 ≤ τ) (G : ℚ) :
    (τ.factorial : ℝ) *
        (((factorialGapPrefix τ - G : ℚ) : ℝ)) =
      firstExitDelta τ
        (((G - factorialGapPrefix (τ - 1) : ℚ) : ℝ)) := by
  have hfac : 1 < τ.factorial := Nat.one_lt_factorial.mpr hτ
  have hdenQ : ((τ.factorial : ℚ) - 1) ≠ 0 := by
    intro hzero
    have hone : (τ.factorial : ℚ) = 1 := sub_eq_zero.mp hzero
    exact (Nat.ne_of_gt hfac) (by exact_mod_cast hone)
  have hRat :
      (τ.factorial : ℚ) * (factorialGapPrefix τ - G) =
        1 + 1 / ((τ.factorial : ℚ) - 1) -
          (τ.factorial : ℚ) *
            (G - factorialGapPrefix (τ - 1)) := by
    rw [factorialGapPrefix_eq_prev_add hτ]
    field_simp [hdenQ]
    ring
  unfold firstExitDelta
  exact_mod_cast hRat

/-- A genuine crossing starts above the preceding prefix, so its normalized
offset is strictly below two. -/
theorem actualFirstCrossing_delta_lt_two
    {τ : ℕ} (hτ : 2 ≤ τ) {G : ℚ}
    (hbefore : factorialGapPrefix (τ - 1) < G) :
    firstExitDelta τ
        (((G - factorialGapPrefix (τ - 1) : ℚ) : ℝ)) < 2 := by
  have hfacNat : 1 < τ.factorial := Nat.one_lt_factorial.mpr hτ
  have hfac : (1 : ℝ) < τ.factorial := by exact_mod_cast hfacNat
  have hfacTwo : (2 : ℝ) ≤ τ.factorial := by
    exact_mod_cast (show 2 ≤ τ.factorial by omega)
  have hgapOne : (1 : ℝ) ≤ (τ.factorial : ℝ) - 1 := by
    linarith
  have hgapPos : (0 : ℝ) < (τ.factorial : ℝ) - 1 := by linarith
  have hinv : 1 / ((τ.factorial : ℝ) - 1) ≤ 1 :=
    (div_le_one hgapPos).2 hgapOne
  have hV :
      (0 : ℝ) <
        (((G - factorialGapPrefix (τ - 1) : ℚ) : ℝ)) := by
    exact_mod_cast (sub_pos.mpr hbefore)
  unfold firstExitDelta
  nlinarith [mul_pos (by positivity : (0 : ℝ) < τ.factorial) hV]

/-- The `δ ≥ 1` exit branch is exactly the exceptionally small-gap branch.
This is the algebraic threshold behind the stronger first-crossing
denominator obstruction. -/
theorem firstExitDelta_ge_one_iff
    {τ : ℕ} (hτ : 2 ≤ τ) (V : ℝ) :
    1 ≤ firstExitDelta τ V ↔
      V ≤ 1 / ((τ.factorial : ℝ) * ((τ.factorial : ℝ) - 1)) := by
  have hfac : (1 : ℝ) < τ.factorial := by
    exact_mod_cast Nat.one_lt_factorial.mpr hτ
  have hfacPos : (0 : ℝ) < τ.factorial := by positivity
  have hgapPos : (0 : ℝ) < (τ.factorial : ℝ) - 1 := by linarith
  have hrecip :
      1 / ((τ.factorial : ℝ) * ((τ.factorial : ℝ) - 1)) =
        (1 / ((τ.factorial : ℝ) - 1)) / (τ.factorial : ℝ) := by
    field_simp [ne_of_gt hfacPos, ne_of_gt hgapPos]
  unfold firstExitDelta
  rw [hrecip]
  constructor
  · intro h
    apply (le_div_iff₀ hfacPos).2
    nlinarith
  · intro h
    have hmul := (le_div_iff₀ hfacPos).1 h
    nlinarith

/-- If the normalized first-exit offset lies in `[0,2)`, then the negative
unit carry occurs exactly when the exit gap is at most
`1 / (τ! (τ! - 1))`. -/
theorem firstExit_carry_eq_neg_one_iff
    {τ : ℕ} (hτ : 2 ≤ τ) {V : ℝ} {b : ℤ}
    (hδ2 : firstExitDelta τ V < 2)
    (hb : b = -⌊firstExitDelta τ V⌋) :
    b = -1 ↔
      V ≤ 1 / ((τ.factorial : ℝ) * ((τ.factorial : ℝ) - 1)) := by
  rw [← firstExitDelta_ge_one_iff hτ V]
  constructor
  · intro hbneg
    have hfloor : ⌊firstExitDelta τ V⌋ = 1 := by omega
    have hlower := Int.floor_le (firstExitDelta τ V)
    rw [hfloor] at hlower
    simpa using hlower
  · intro hδ1
    have hfloor1 : (1 : ℤ) ≤ ⌊firstExitDelta τ V⌋ :=
      Int.le_floor.mpr (by simpa using hδ1)
    have hfloor2 : ⌊firstExitDelta τ V⌋ < 2 :=
      Int.floor_lt.mpr hδ2
    omega

/-- A positive rational fraction bounded above by `1 / N` must have
denominator at least `N`.  No coprimality hypothesis is needed, so this
applies directly to any displayed first-crossing gap representation. -/
theorem positive_fraction_denominator_ge
    {a v N : ℕ} (ha : 0 < a) (hv : 0 < v) (hN : 0 < N)
    (hbound : (a : ℚ) / (v : ℚ) ≤ 1 / (N : ℚ)) :
    N ≤ v := by
  have hvQ : (0 : ℚ) < v := by exact_mod_cast hv
  have hNQ : (0 : ℚ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ hvQ hNQ] at hbound
  norm_num at hbound
  have hmul : a * N ≤ v := by exact_mod_cast hbound
  calc
    N = 1 * N := by simp
    _ ≤ a * N := Nat.mul_le_mul_right N ha
    _ ≤ v := hmul

/-- Real-cast version of the elementary positive-fraction denominator
bound, convenient after applying the first-exit floor criterion. -/
theorem positive_real_fraction_denominator_ge
    {a v N : ℕ} (ha : 0 < a) (hv : 0 < v) (hN : 0 < N)
    (hbound : (a : ℝ) / (v : ℝ) ≤ 1 / (N : ℝ)) :
    N ≤ v := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ hvR hNR] at hbound
  norm_num at hbound
  have hmul : a * N ≤ v := by exact_mod_cast hbound
  calc
    N = 1 * N := by simp
    _ ≤ a * N := Nat.mul_le_mul_right N ha
    _ ≤ v := hmul

/-- The actual first-crossing gap bound immediately forces the displayed
rational denominator to be at least `τ! - 1`. -/
theorem actualFirstCrossing_denominator_ge
    {τ a v : ℕ} (hτ : 2 ≤ τ) (ha : 0 < a) (hv : 0 < v)
    {G : ℚ}
    (hgap :
      G - factorialGapPrefix (τ - 1) = (a : ℚ) / (v : ℚ))
    (hbefore : factorialGapPrefix (τ - 1) < G)
    (hcross : G ≤ factorialGapPrefix τ) :
    τ.factorial - 1 ≤ v := by
  have hfac : 1 < τ.factorial := Nat.one_lt_factorial.mpr hτ
  have hbounds := actualFirstCrossing_gap_bounds hτ hbefore hcross
  apply positive_fraction_denominator_ge ha hv (Nat.sub_pos_of_lt hfac)
  rw [← hgap]
  simpa [Nat.cast_sub hfac.le] using hbounds.2

/-- On the actual negative-unit exit branch, the first-crossing gap has the
strong denominator lower bound `τ! (τ! - 1)`. -/
theorem actualFirstCrossing_negCarry_denominator_ge
    {τ a v : ℕ} (hτ : 2 ≤ τ) (ha : 0 < a) (hv : 0 < v)
    {G : ℚ} {b : ℤ}
    (hgap :
      G - factorialGapPrefix (τ - 1) = (a : ℚ) / (v : ℚ))
    (hbefore : factorialGapPrefix (τ - 1) < G)
    (hcross : G ≤ factorialGapPrefix τ)
    (hb :
      b = -⌊(τ.factorial : ℝ) *
        (((factorialGapPrefix τ - G : ℚ) : ℝ))⌋)
    (hbneg : b = -1) :
    τ.factorial * (τ.factorial - 1) ≤ v := by
  have hfac : 1 < τ.factorial := Nat.one_lt_factorial.mpr hτ
  have hbounds := actualFirstCrossing_gap_bounds hτ hbefore hcross
  have hbefore' : factorialGapPrefix (τ - 1) < G := by
    linarith [hbounds.1]
  have hδeq := actualFirstCrossing_scaledOffset_eq hτ G
  have hδ2 := actualFirstCrossing_delta_lt_two hτ hbefore'
  have hb' :
      b = -⌊firstExitDelta τ
        (((G - factorialGapPrefix (τ - 1) : ℚ) : ℝ))⌋ := by
    rw [← hδeq]
    exact hb
  have hsmall :=
    (firstExit_carry_eq_neg_one_iff hτ hδ2 hb').mp hbneg
  have hgapReal :
      (((G - factorialGapPrefix (τ - 1) : ℚ) : ℝ)) =
        (a : ℝ) / (v : ℝ) := by
    rw [hgap]
    push_cast
    rfl
  apply positive_real_fraction_denominator_ge ha hv
    (Nat.mul_pos (Nat.factorial_pos τ) (Nat.sub_pos_of_lt hfac))
  rw [← hgapReal]
  simpa [Nat.cast_mul, Nat.cast_sub hfac.le] using hsmall

/-! ## An independent factorial interval inequality -/

/-- For `n ≥ 8`, the factorial already dominates the exact polynomial
coefficient that appears when one specializes the Kovač--Tao Type-2 interval
overlap test to the factorial gaps `n! - 1` with width `n^2 + 1`. -/
theorem typeTwoOverlapCoefficient_lt_factorial
    {n : ℕ} (hn : 8 ≤ n) :
    2 * n ^ 4 + 3 * n ^ 3 + 4 * n ^ 2 + 2 < n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hpoly :
          2 * (n + 1) ^ 4 + 3 * (n + 1) ^ 3 + 4 * (n + 1) ^ 2 + 2 <
            (n + 1) * (2 * n ^ 4 + 3 * n ^ 3 + 4 * n ^ 2 + 2) := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        let R : ℕ :=
          2 * m ^ 5 + 83 * m ^ 4 + 1372 * m ^ 3 +
            11275 * m ^ 2 + 45977 * m + 74239
        have hR : 0 < R := by
          dsimp [R]
          positivity
        have hid :
            (8 + m + 1) *
                (2 * (8 + m) ^ 4 + 3 * (8 + m) ^ 3 +
                  4 * (8 + m) ^ 2 + 2) =
              2 * (8 + m + 1) ^ 4 + 3 * (8 + m + 1) ^ 3 +
                4 * (8 + m + 1) ^ 2 + 2 + R := by
          dsimp [R]
          ring
        rw [hid]
        omega
      calc
        2 * (n + 1) ^ 4 + 3 * (n + 1) ^ 3 + 4 * (n + 1) ^ 2 + 2
            < (n + 1) * (2 * n ^ 4 + 3 * n ^ 3 + 4 * n ^ 2 + 2) := hpoly
        _ < (n + 1) * n.factorial :=
          Nat.mul_lt_mul_of_pos_left ih (Nat.succ_pos n)
        _ = (n + 1).factorial := by
          rw [Nat.factorial_succ]

/-- Exact next-interval overlap for the factorial-gap specialization of
Kovač--Tao, Lemma 5.1.  At stage `n`, take the positive-integer interval
whose upper endpoint is `n! - 1` and whose width is `n^2 + 1`.  For every
`n ≥ 8`, the single interval at stage `n+1` already contributes more tail
length than the largest reciprocal gap at stage `n`.

Together with the analytic hypotheses of Kovač--Tao, Lemma 5.1, this is the
elementary interval inequality used to construct a rational reciprocal series
with denominators between `n! - n^2 - 2` and `n! - 1`.  The theorem below is
only that inequality: it proves neither the existence statement nor the
rationality or irrationality of the unperturbed Erdős #68 series. -/
theorem factorialGap_typeTwo_nextInterval_overlap
    {n : ℕ} (hn : 8 ≤ n) :
    (((n + 1).factorial : ℤ) - ((n + 1 : ℤ) ^ 2 + 2)) *
          (((n + 1).factorial : ℤ) - 1) <
      (((n + 1 : ℤ) ^ 2 + 1)) *
        (((n.factorial : ℤ) - ((n : ℤ) ^ 2 + 2)) *
          ((n.factorial : ℤ) - ((n : ℤ) ^ 2 + 1))) := by
  let x : ℤ := n.factorial
  let N : ℤ := n
  let B : ℤ := 2 * N ^ 4 + 3 * N ^ 3 + 4 * N ^ 2 + 2
  let P : ℤ :=
    N ^ 6 + 2 * N ^ 5 + 5 * N ^ 4 + 6 * N ^ 3 +
      7 * N ^ 2 + 2 * N + 1
  have hcoeffNat := typeTwoOverlapCoefficient_lt_factorial hn
  have hcoeff : B < x := by
    dsimp [B, x, N]
    exact_mod_cast hcoeffNat
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast Nat.factorial_pos n
  have hP : 0 < P := by
    dsimp [P, N]
    positivity
  have hprod : 0 < x * (x - B) :=
    mul_pos hx (sub_pos.mpr hcoeff)
  have hidentity :
      (((N + 1) ^ 2 + 1) *
            ((x - (N ^ 2 + 2)) * (x - (N ^ 2 + 1))) -
          ((((N + 1) * x) - ((N + 1) ^ 2 + 2)) *
            (((N + 1) * x) - 1))) =
        x * (x - B) + P := by
    dsimp [B, P]
    ring
  rw [← sub_pos]
  rw [show ((n + 1).factorial : ℤ) = (N + 1) * x by
    dsimp [N, x]
    rw [Nat.factorial_succ]
    push_cast
    rfl]
  change
    0 <
      ((N + 1) ^ 2 + 1) * ((x - (N ^ 2 + 2)) * (x - (N ^ 2 + 1))) -
        ((((N + 1) * x) - ((N + 1) ^ 2 + 2)) *
          (((N + 1) * x) - 1))
  rw [hidentity]
  exact add_pos hprod hP

end ErdosProblems.Erdos68
