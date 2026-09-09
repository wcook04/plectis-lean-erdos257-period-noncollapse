import ErdosProblems.Erdos1049.ZudilinHeightRegion
import ErdosProblems.Erdos1049.HermitePadeNoGo
import ErdosProblems.Erdos1049.ZudilinConeArithmetic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Erdős #1049: one integer certificate controls four separate obstructions

The single two-sided bracket

`2 ^ 64 < 3 ^ 41 < 2 ^ 65`

sharpens every parameter obstruction already recorded for `3 / 2`.

* The Archimedean height deficit against the Bundschuh--Väänänen frontier is
  bigger than `3 / 13`, uniformly over the whole admissible rectangular
  Hermite--Padé cone (`threeHalves_rectangular_hp_gap_gt_threeThirteenths`).
  The previous certificate `3 ^ 81 < 2 ^ 200` only gave `81 / 200` for the
  ratio itself and no cone-uniform gap at all.
* The four-jet counting threshold at bottom depth `41` drops from the
  `4 R + 2 S = 164 + 2 S` of `exists_distinct_binary_selectors_same_fourJet_of_rank`
  to `130 + 2 S`, and `130` is *exactly* optimal
  (`fourJet_card_gt_two_pow_of_rank_41`).
* The cubic Hankel producer must remove more than `39 / 41` of its raw
  denominator charge (`threeHalves_hankelChargeThreshold_lt_eightFortyOne`).
* The scalar cone misses by a fixed relative margin `17 / 41`
  (`three_two_scalar_margin_lt_explicit`).

The final section adds a general **bounded-fibre escape** pigeonhole.  Once an
analytic remainder is supplied as `g` together with a fibre bound, the generic
theorem yields a four-jet collision separated by `g`; no such concrete
remainder instantiation is formalized here.

No theorem here decides the arithmetic nature of the Lambert value at `3 / 2`.
-/

namespace ErdosProblems.Erdos1049

/-! ## The exact two-sided power certificate -/

/-- Upper half of the certificate. -/
theorem threePow_fortyOne_lt_twoPow_sixtyFive : 3 ^ 41 < 2 ^ 65 := by norm_num

/-- Lower half of the certificate: `65` cannot be replaced by `64`. -/
theorem twoPow_sixtyFour_lt_threePow_fortyOne : 2 ^ 64 < 3 ^ 41 := by norm_num

/-- The sharp rational upper bound on the logarithmic height ratio. -/
theorem logThree_div_logTwo_lt_sixtyFive_fortyOne :
    Real.log 3 / Real.log 2 < (65 : ℝ) / 41 := by
  have hpows : (3 : ℝ) ^ 41 < (2 : ℝ) ^ 65 := by
    exact_mod_cast threePow_fortyOne_lt_twoPow_sixtyFive
  have hlogs : Real.log ((3 : ℝ) ^ 41) < Real.log ((2 : ℝ) ^ 65) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) hpows
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  apply (div_lt_iff₀ hlog2).2
  nlinarith

/-- The sharp rational lower bound for the reciprocal ratio. -/
theorem fortyOne_sixtyFive_lt_logTwo_div_logThree :
    (41 : ℝ) / 65 < Real.log 2 / Real.log 3 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have h := logThree_div_logTwo_lt_sixtyFive_fortyOne
  rw [div_lt_iff₀ hlog2] at h
  apply (lt_div_iff₀ hlog3).2
  nlinarith

/-! ## The Archimedean deficit -/

/-- **Strict certificate gap above the Bundschuh--Väänänen frontier.**  The
displayed certificates give the threshold `41/65 - 2/5 = 3/13`; the theorem
proves a strict lower bound above that threshold, not an exact value for the
actual gap. -/
theorem threeHalves_bv_height_gap_gt_threeThirteenths :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - (1 / 2 - 1 / Real.pi ^ 2) := by
  have hratio := fortyOne_sixtyFive_lt_logTwo_div_logThree
  have hmargin := bundschuhVaananenMargin_lt_twoFifths
  nlinarith

/-- **The rectangular Hermite--Padé cone misses `3 / 2` uniformly.**  No
parameter choice inside the admissible region recovers even the first
`3 / 13` of the missing logarithmic height. -/
theorem threeHalves_rectangular_hp_gap_gt_threeThirteenths (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma := by
  have hgap := threeHalves_bv_height_gap_gt_threeThirteenths
  have hrect := rectangular_hp_threshold_le_classical rho sigma hrho hsigma
  linarith

/-! ## The cubic Hankel and scalar-cone deficits -/

/-- **Exact rational ceiling for the cubic Hankel charge.**  Starting from a
raw charge `4`, more than `39 / 41` of it must be removed. -/
theorem threeHalves_hankelChargeThreshold_lt_eightFortyOne :
    (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := by
  have h := logThree_div_logTwo_lt_sixtyFive_fortyOne
  linarith

/-! ## Zudilin scalar-content ceiling -/

/-- **Abstract scalar-ceiling comparison.**  For positive `N`, the polynomial
ceiling `N^3-N` is strictly below the `39/41` fraction of the raw charge
`4N^3-3N^2` used in the `p=3/2` bookkeeping.  This theorem proves that exact
integer inequality only; it does not itself establish that a source scalar
factor has degree at most `N^3-N`.  The source-facing factor derivation and any
application of this ceiling are separate, explicit premises. -/
theorem zudilinScalarContent_ceiling_lt_required (N : ℤ) (hN : 0 < N) :
    41 * (N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  have hsq : 0 ≤ (230 * N - 117) ^ 2 := sq_nonneg (230 * N - 117)
  have hquad : 0 < 115 * N ^ 2 - 117 * N + 41 := by
    nlinarith
  have hproduct : 0 < N * (115 * N ^ 2 - 117 * N + 41) :=
    mul_pos hN hquad
  nlinarith

/-- Any extracted degree satisfying the explicit bound `extractedDegree ≤ N^3-N`
misses the required `39/41` raw-charge threshold.  A source application must
establish that bound separately; further divisibility of the primitive
residual Hankel matrix would then be needed to close the charge gap. -/
theorem zudilinScalarContent_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 0 < N)
    (hextracted : extractedDegree ≤ N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  have hceiling := zudilinScalarContent_ceiling_lt_required N hN
  linarith

/-! ## Zudilin scalar-plus-border ceiling -/

/-- **Abstract scalar-plus-border ceiling comparison.**  For `N ≥ 2`, the
deliberately overgenerous combined polynomial ceiling `2 * N^3 - N` misses the
explicit `39/41` charge threshold.  This theorem checks that integer
comparison only; it does not prove that scalar content and southeast `Phi_d`
border factors in the source attain those individual ceilings.  The
source-facing residual and border-factor derivation, and any use of this
combined ceiling, are separate premises. -/
theorem zudilinScalarPlusBorder_ceiling_lt_required (N : ℤ) (hN : 2 ≤ N) :
    41 * (2 * N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  have hx : 0 ≤ N - 2 := by omega
  have hquad : 0 < 74 * N ^ 2 - 117 * N + 41 := by
    nlinarith [sq_nonneg (N - 2)]
  have hproduct : 0 < N * (74 * N ^ 2 - 117 * N + 41) := by
    nlinarith
  nlinarith

/-- Any extraction satisfying the explicit bound `extractedDegree ≤ 2 * N^3-N`
still misses the required charge.  A source application must establish that
combined bound separately; higher residual valuations, genuine determinant
cancellation, or another integral model would then be needed to close the
remaining gap. -/
theorem zudilinScalarPlusBorder_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 2 ≤ N)
    (hextracted : extractedDegree ≤ 2 * N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  have hceiling := zudilinScalarPlusBorder_ceiling_lt_required N hN
  linarith

/-! ## Associated-graded Hankel row coefficients -/

/-- The source backward-shift induction on a hypergeometric tail has this
associated-graded transition.  A positive tail state moves down with sign
`-1`; state zero can emit state `s` with coefficient `a (s+1)`.  This finite
recurrence isolates the only coefficient data needed to sharpen Zudilin's
Hankel `q`-order lower bound to an equality. -/
def hankelAssociatedCoeff (a : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, 0 => ∑ s ∈ Finset.range (j + 1),
      a (s + 1) * hankelAssociatedCoeff a j s
  | j + 1, t + 1 => -hankelAssociatedCoeff a j t

/-- **Associated-graded reciprocal law.**  Suppose `h` is the coefficient
sequence reciprocal to `1 + sum_(r>=1) a_r X^r`, expressed through its exact
coefficient recurrence.  After `j` source row transformations, the leading
coefficient contributed by tail state `t` is
`(-1)^j h_(j-t)` for `t ≤ j`, and zero otherwise.

This kernel-checks the all-depth combinatorial induction used by the
source-facing proof in `HankelQOrderComputationalLab.md`; it is not a finite
rank calculation. -/
theorem hankelAssociatedCoeff_eq_reciprocal
    (a h : ℕ → ℤ) (hzero : h 0 = 1)
    (hrec : ∀ j, h (j + 1) =
      -(∑ s ∈ Finset.range (j + 1), a (s + 1) * h (j - s))) :
    ∀ j t, hankelAssociatedCoeff a j t =
      if t ≤ j then (-1 : ℤ) ^ j * h (j - t) else 0 := by
  intro j
  induction j with
  | zero =>
      intro t
      cases t with
      | zero => simp [hankelAssociatedCoeff, hzero]
      | succ t => simp [hankelAssociatedCoeff]
  | succ j ih =>
      intro t
      cases t with
      | zero =>
          rw [hankelAssociatedCoeff, if_pos (Nat.zero_le (j + 1))]
          calc
            ∑ s ∈ Finset.range (j + 1),
                a (s + 1) * hankelAssociatedCoeff a j s =
                ∑ s ∈ Finset.range (j + 1),
                  a (s + 1) * ((-1 : ℤ) ^ j * h (j - s)) := by
                    apply Finset.sum_congr rfl
                    intro s hs
                    rw [ih, if_pos]
                    exact Nat.le_of_lt_succ (Finset.mem_range.mp hs)
            _ = (-1 : ℤ) ^ j *
                (∑ s ∈ Finset.range (j + 1), a (s + 1) * h (j - s)) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro s _
                  ring
            _ = (-1 : ℤ) ^ (j + 1) * h (j + 1) := by
                  rw [hrec]
                  ring
      | succ t =>
          rw [hankelAssociatedCoeff]
          by_cases ht : t ≤ j
          · rw [ih, if_pos ht, if_pos (Nat.succ_le_succ ht)]
            have hsub : j + 1 - (t + 1) = j - t := by omega
            rw [hsub, pow_succ]
            ring
          · have hsucc : ¬t + 1 ≤ j + 1 :=
              fun h => ht (Nat.le_of_succ_le_succ h)
            rw [ih, if_neg ht, if_neg hsucc]
            norm_num

/-! ### The two source-tail reciprocal specializations -/

/-- Coefficients of any genuine inverse power series satisfy exactly the
recurrence consumed by `hankelAssociatedCoeff_eq_reciprocal`.  Writing this
once keeps the two Zudilin tail specializations tied to multiplication in
`ℤ⟦X⟧`, rather than to separately asserted coefficient formulas. -/
theorem coeff_recurrence_of_mul_eq_one
    (H G : PowerSeries ℤ)
    (hH0 : PowerSeries.coeff 0 H = 1)
    (hmul : H * G = 1) (j : ℕ) :
    PowerSeries.coeff (j + 1) G =
      -(∑ s ∈ Finset.range (j + 1),
          PowerSeries.coeff (s + 1) H * PowerSeries.coeff (j - s) G) := by
  have hcoeff := congrArg (PowerSeries.coeff (j + 1)) hmul
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  simp only [PowerSeries.coeff_one, hH0, one_mul,
    if_neg (show j + 1 ≠ 0 by omega)] at hcoeff
  linarith

/-- The associated-grade ratio for every positive source-tail state is
`(1-X)^3`. -/
noncomputable def zudilinPositiveTailAssociatedH : PowerSeries ℤ :=
  (1 - PowerSeries.X) ^ 3

/-- Its reciprocal is `(1-X)^(-3)`. -/
noncomputable def zudilinPositiveTailAssociatedReciprocal : PowerSeries ℤ :=
  (PowerSeries.invOneSubPow ℤ 3).val

/-- The associated-grade ratio for the zero source-tail state is
`(1-X)^4/(1+X)`. -/
noncomputable def zudilinZeroTailAssociatedH : PowerSeries ℤ :=
  (1 - PowerSeries.X) ^ 4 *
    PowerSeries.invOfUnit (1 + PowerSeries.X) 1

/-- Its reciprocal is `(1+X)/(1-X)^4`. -/
noncomputable def zudilinZeroTailAssociatedReciprocal : PowerSeries ℤ :=
  (1 + PowerSeries.X) * (PowerSeries.invOneSubPow ℤ 4).val

@[simp] theorem coeff_zero_zudilinPositiveTailAssociatedH :
    PowerSeries.coeff 0 zudilinPositiveTailAssociatedH = 1 := by
  simp [zudilinPositiveTailAssociatedH,
    PowerSeries.coeff_zero_eq_constantCoeff]

@[simp] theorem coeff_zero_zudilinZeroTailAssociatedH :
    PowerSeries.coeff 0 zudilinZeroTailAssociatedH = 1 := by
  simp [zudilinZeroTailAssociatedH,
    PowerSeries.coeff_zero_eq_constantCoeff]

@[simp] theorem coeff_zero_zudilinPositiveTailAssociatedReciprocal :
    PowerSeries.coeff 0 zudilinPositiveTailAssociatedReciprocal = 1 := by
  change PowerSeries.coeff 0
      (PowerSeries.invOneSubPow ℤ (2 + 1)).val = 1
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp

@[simp] theorem coeff_zero_zudilinZeroTailAssociatedReciprocal :
    PowerSeries.coeff 0 zudilinZeroTailAssociatedReciprocal = 1 := by
  rw [zudilinZeroTailAssociatedReciprocal,
    PowerSeries.coeff_zero_eq_constantCoeff]
  change PowerSeries.constantCoeff
    ((1 + PowerSeries.X) *
      (PowerSeries.invOneSubPow ℤ (3 + 1)).val) = 1
  rw [map_mul, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp

theorem zudilinPositiveTailAssociatedH_mul_reciprocal :
    zudilinPositiveTailAssociatedH *
        zudilinPositiveTailAssociatedReciprocal = 1 := by
  simpa [zudilinPositiveTailAssociatedH,
    zudilinPositiveTailAssociatedReciprocal] using
      (PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow
        ℤ 0 3)

theorem zudilinZeroTailAssociatedH_mul_reciprocal :
    zudilinZeroTailAssociatedH * zudilinZeroTailAssociatedReciprocal = 1 := by
  have hplus : PowerSeries.invOfUnit
        (1 + PowerSeries.X : PowerSeries ℤ) 1 * (1 + PowerSeries.X) = 1 := by
    apply PowerSeries.invOfUnit_mul
    simp
  have hminus :
      (1 - PowerSeries.X : PowerSeries ℤ) ^ 4 *
          (PowerSeries.invOneSubPow ℤ 4).val = 1 := by
    simpa using
      (PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow
        ℤ 0 4)
  rw [zudilinZeroTailAssociatedH, zudilinZeroTailAssociatedReciprocal]
  calc
    ((1 - PowerSeries.X) ^ 4 *
          PowerSeries.invOfUnit (1 + PowerSeries.X) 1) *
        ((1 + PowerSeries.X) * (PowerSeries.invOneSubPow ℤ 4).val) =
        ((1 - PowerSeries.X) ^ 4 *
          (PowerSeries.invOneSubPow ℤ 4).val) *
        (PowerSeries.invOfUnit (1 + PowerSeries.X) 1 *
          (1 + PowerSeries.X)) := by ring
    _ = 1 := by rw [hminus, hplus, one_mul]

/-- Coefficients of `(1-X)^(-3)` are the triangular numbers occurring in
every positive source-tail contribution. -/
@[simp] theorem coeff_zudilinPositiveTailAssociatedReciprocal (r : ℕ) :
    PowerSeries.coeff r zudilinPositiveTailAssociatedReciprocal =
      ((r + 2).choose 2 : ℤ) := by
  change PowerSeries.coeff r
      (PowerSeries.invOneSubPow ℤ (2 + 1)).val = ((r + 2).choose 2 : ℤ)
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp [Nat.add_comm]

private theorem coeff_invOneSubPow_four (r : ℕ) :
    PowerSeries.coeff r (PowerSeries.invOneSubPow ℤ 4).val =
      ((r + 3).choose 3 : ℤ) := by
  change PowerSeries.coeff r
      (PowerSeries.invOneSubPow ℤ (3 + 1)).val = ((r + 3).choose 3 : ℤ)
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp [Nat.add_comm]

/-- Coefficients of `(1+X)/(1-X)^4` are the two adjacent tetrahedral
numbers in the zero-tail contribution. -/
@[simp] theorem coeff_zudilinZeroTailAssociatedReciprocal (r : ℕ) :
    PowerSeries.coeff r zudilinZeroTailAssociatedReciprocal =
      ((r + 3).choose 3 : ℤ) + ((r + 2).choose 3 : ℤ) := by
  rw [zudilinZeroTailAssociatedReciprocal, add_mul, one_mul,
    map_add, coeff_invOneSubPow_four]
  cases r with
  | zero => simp
  | succ r =>
      have hshift :
          PowerSeries.coeff (r + 1)
              (PowerSeries.X * (PowerSeries.invOneSubPow ℤ 4).val) =
            PowerSeries.coeff r (PowerSeries.invOneSubPow ℤ 4).val := by
        simpa [Nat.add_comm] using
          (PowerSeries.coeff_X_pow_mul
            (PowerSeries.invOneSubPow ℤ 4).val 1 r)
      rw [hshift, coeff_invOneSubPow_four]

/-- The positive-tail associated recurrence is now specialized to the actual
source ratio, at every depth and tail state. -/
theorem hankelAssociatedCoeff_zudilinPositiveTail (j t : ℕ) :
    hankelAssociatedCoeff
        (fun r => PowerSeries.coeff r zudilinPositiveTailAssociatedH) j t =
      if t ≤ j then
        (-1 : ℤ) ^ j * PowerSeries.coeff (j - t)
          zudilinPositiveTailAssociatedReciprocal
      else 0 := by
  exact hankelAssociatedCoeff_eq_reciprocal
    (fun r => PowerSeries.coeff r zudilinPositiveTailAssociatedH)
    (fun r => PowerSeries.coeff r zudilinPositiveTailAssociatedReciprocal)
    coeff_zero_zudilinPositiveTailAssociatedReciprocal
    (fun r => coeff_recurrence_of_mul_eq_one
      zudilinPositiveTailAssociatedH
      zudilinPositiveTailAssociatedReciprocal
      coeff_zero_zudilinPositiveTailAssociatedH
      zudilinPositiveTailAssociatedH_mul_reciprocal r)
    j t

/-- Closed form of every positive-tail associated contribution. -/
theorem hankelAssociatedCoeff_zudilinPositiveTail_closed (j t : ℕ) :
    hankelAssociatedCoeff
        (fun r => PowerSeries.coeff r zudilinPositiveTailAssociatedH) j t =
      if t ≤ j then
        (-1 : ℤ) ^ j * (((j - t + 2).choose 2 : ℕ) : ℤ)
      else 0 := by
  rw [hankelAssociatedCoeff_zudilinPositiveTail]
  split_ifs <;> simp

/-- The zero-tail associated recurrence is likewise specialized to its
distinct source ratio `(1-X)^4/(1+X)`. -/
theorem hankelAssociatedCoeff_zudilinZeroTail (j t : ℕ) :
    hankelAssociatedCoeff
        (fun r => PowerSeries.coeff r zudilinZeroTailAssociatedH) j t =
      if t ≤ j then
        (-1 : ℤ) ^ j * PowerSeries.coeff (j - t)
          zudilinZeroTailAssociatedReciprocal
      else 0 := by
  exact hankelAssociatedCoeff_eq_reciprocal
    (fun r => PowerSeries.coeff r zudilinZeroTailAssociatedH)
    (fun r => PowerSeries.coeff r zudilinZeroTailAssociatedReciprocal)
    coeff_zero_zudilinZeroTailAssociatedReciprocal
    (fun r => coeff_recurrence_of_mul_eq_one
      zudilinZeroTailAssociatedH
      zudilinZeroTailAssociatedReciprocal
      coeff_zero_zudilinZeroTailAssociatedH
      zudilinZeroTailAssociatedH_mul_reciprocal r)
    j t

/-- Closed form of the zero-tail contribution after every number of source
row transforms. -/
theorem hankelAssociatedCoeff_zudilinZeroTail_zero (j : ℕ) :
    hankelAssociatedCoeff
        (fun r => PowerSeries.coeff r zudilinZeroTailAssociatedH) j 0 =
      (-1 : ℤ) ^ j *
        ((((j + 3).choose 3 : ℕ) : ℤ) +
          (((j + 2).choose 3 : ℕ) : ℤ)) := by
  rw [hankelAssociatedCoeff_zudilinZeroTail, if_pos (Nat.zero_le j)]
  simp

private theorem sum_range_choose_add_two_two (j : ℕ) :
    (∑ r ∈ Finset.range j, (r + 2).choose 2) = (j + 2).choose 3 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.choose_succ_succ (j + 2) 2).symm

/-- The positive-tail states `1,…,j`, read in reverse order, contribute one
tetrahedral number. -/
theorem sum_coeff_zudilinPositiveTailAssociatedReciprocal (j : ℕ) :
    (∑ r ∈ Finset.range j,
        PowerSeries.coeff r zudilinPositiveTailAssociatedReciprocal) =
      (((j + 2).choose 3 : ℕ) : ℤ) := by
  simp_rw [coeff_zudilinPositiveTailAssociatedReciprocal]
  norm_cast
  exact sum_range_choose_add_two_two j

private theorem six_mul_choose_add_three_three (j : ℕ) :
    6 * (j + 3).choose 3 = (j + 1) * (j + 2) * (j + 3) := by
  induction j with
  | zero => decide
  | succ j ih =>
      have htwo : 2 * (j + 3).choose 2 = (j + 3) * (j + 2) := by
        have h := Nat.add_one_mul_choose_eq (j + 2) 1
        simpa [Nat.choose_one_right, mul_comm, Nat.add_assoc] using h.symm
      rw [show j + 1 + 3 = (j + 3) + 1 by omega,
        Nat.choose_succ_succ, mul_add]
      calc
        6 * (j + 3).choose 2 + 6 * (j + 3).choose 3 =
            3 * (2 * (j + 3).choose 2) +
              6 * (j + 3).choose 3 := by ring
        _ = 3 * ((j + 3) * (j + 2)) +
              ((j + 1) * (j + 2) * (j + 3)) := by rw [htwo, ih]
        _ = (j + 1 + 1) * (j + 1 + 2) * (j + 1 + 3) := by ring

private theorem six_mul_choose_add_two_three (j : ℕ) :
    6 * (j + 2).choose 3 = j * (j + 1) * (j + 2) := by
  cases j with
  | zero => decide
  | succ j =>
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        six_mul_choose_add_three_three j

/-- The two source-tail families have reciprocal-coefficient numerators which
add to the claimed transformed-row coefficient.  This is the exact algebraic
fan-in after the associated-graded reciprocal law: the `t=0` contribution and
the sum of `1 ≤ t ≤ j` contributions combine without cancellation. -/
theorem zudilinTransformedTailNumerators_add (j : ℤ) :
    (j + 1) * (j + 2) * (2 * j + 3) + j * (j + 1) * (j + 2) =
      3 * (j + 1) ^ 2 * (j + 2) := by
  ring

/-! ## Determinant-preserving source backward shifts -/

/-- Gaussian binomial coefficients as integer power series, using the standard
Pascal recurrence.  This is the coefficient occurring in Zudilin's displayed
operator `D_j=(N;q)_j`. -/
noncomputable def zudilinQBinomialPS : ℕ → ℕ → PowerSeries ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => zudilinQBinomialPS n (k + 1) +
      PowerSeries.X ^ (n - k) * zudilinQBinomialPS n k

@[simp] theorem zudilinQBinomialPS_zero (n : ℕ) :
    zudilinQBinomialPS n 0 = 1 := by
  cases n <;> rfl

theorem zudilinQBinomialPS_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    zudilinQBinomialPS n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [zudilinQBinomialPS, ih (by omega), ih (by omega)]
          simp

/-- Coefficient of the `k`th backward shift in the source operator
`D_j=(N;q)_j`: `(-1)^k q^(k(k-1)/2) [j choose k]_q`. -/
noncomputable def zudilinBackwardShiftCoeff (j k : ℕ) : PowerSeries ℤ :=
  PowerSeries.C ((-1 : ℤ) ^ k) *
    PowerSeries.X ^ (k * (k - 1) / 2) * zudilinQBinomialPS j k

@[simp] theorem zudilinBackwardShiftCoeff_zero (j : ℕ) :
    zudilinBackwardShiftCoeff j 0 = 1 := by
  simp [zudilinBackwardShiftCoeff]

theorem zudilinBackwardShiftCoeff_eq_zero_of_lt {j k : ℕ} (h : j < k) :
    zudilinBackwardShiftCoeff j k = 0 := by
  rw [zudilinBackwardShiftCoeff, zudilinQBinomialPS_eq_zero_of_lt h, mul_zero]

/-- Exact coefficient recurrence for the source operators
`D_(j+1) = (1-X^j N)D_j`.  The side condition is precisely the range in
which both consecutive Gaussian-binomial rows participate. -/
theorem zudilinBackwardShiftCoeff_succ (j k : ℕ) (hk : k ≤ j) :
    zudilinBackwardShiftCoeff (j + 1) (k + 1) =
      zudilinBackwardShiftCoeff j (k + 1) -
        PowerSeries.X ^ j * zudilinBackwardShiftCoeff j k := by
  have htri : (k + 1) * ((k + 1) - 1) / 2 =
      k * (k - 1) / 2 + k := Nat.triangle_succ k
  have hexp : (k + 1) * ((k + 1) - 1) / 2 + (j - k) =
      j + k * (k - 1) / 2 := by rw [htri]; omega
  have hsign : PowerSeries.C ((-1 : ℤ) ^ (k + 1)) =
      -PowerSeries.C ((-1 : ℤ) ^ k) := by
    rw [pow_succ, map_mul]
    norm_num
  have hpow :
      (PowerSeries.X : PowerSeries ℤ) ^
            ((k + 1) * ((k + 1) - 1) / 2) *
          PowerSeries.X ^ (j - k) =
        PowerSeries.X ^ (j + k * (k - 1) / 2) := by
    rw [← pow_add, hexp]
  have hsecond :
      PowerSeries.C ((-1 : ℤ) ^ (k + 1)) *
          PowerSeries.X ^ ((k + 1) * ((k + 1) - 1) / 2) *
          (PowerSeries.X ^ (j - k) * zudilinQBinomialPS j k) =
        -(PowerSeries.X ^ j *
          (PowerSeries.C ((-1 : ℤ) ^ k) *
            PowerSeries.X ^ (k * (k - 1) / 2) *
            zudilinQBinomialPS j k)) := by
    rw [hsign]
    calc
      (-PowerSeries.C ((-1 : ℤ) ^ k)) *
            PowerSeries.X ^ ((k + 1) * ((k + 1) - 1) / 2) *
            (PowerSeries.X ^ (j - k) * zudilinQBinomialPS j k) =
          -PowerSeries.C ((-1 : ℤ) ^ k) *
            (PowerSeries.X ^ ((k + 1) * ((k + 1) - 1) / 2) *
              PowerSeries.X ^ (j - k)) * zudilinQBinomialPS j k := by ring
      _ = -PowerSeries.C ((-1 : ℤ) ^ k) *
            PowerSeries.X ^ (j + k * (k - 1) / 2) *
              zudilinQBinomialPS j k := by rw [hpow]
      _ = -(PowerSeries.X ^ j *
          (PowerSeries.C ((-1 : ℤ) ^ k) *
            PowerSeries.X ^ (k * (k - 1) / 2) *
            zudilinQBinomialPS j k)) := by rw [pow_add]; ring
  rw [zudilinBackwardShiftCoeff, zudilinBackwardShiftCoeff,
    zudilinBackwardShiftCoeff, zudilinQBinomialPS, mul_add, hsecond]
  ring

/-- Apply the source operator `D_j` to the `n`th term of an arbitrary
power-series sequence.  The range is finite and agrees literally with the
displayed Gaussian-binomial expansion in Zudilin's source. -/
noncomputable def zudilinBackwardShiftApply
    (j n : ℕ) (v : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range (j + 1),
    zudilinBackwardShiftCoeff j k * v (n - k)

@[simp] theorem zudilinBackwardShiftApply_zero
    (n : ℕ) (v : ℕ → PowerSeries ℤ) :
    zudilinBackwardShiftApply 0 n v = v n := by
  simp [zudilinBackwardShiftApply]

set_option maxHeartbeats 800000 in
/-- Exact operator recurrence on arbitrary sequences.  This is the
source-facing bridge from the Gaussian-binomial row formula to the filtered
induction used for the initial monomial. -/
theorem zudilinBackwardShiftApply_succ
    (j n : ℕ) (v : ℕ → PowerSeries ℤ) (hjn : j < n) :
    zudilinBackwardShiftApply (j + 1) n v =
      zudilinBackwardShiftApply j n v -
        PowerSeries.X ^ j * zudilinBackwardShiftApply j (n - 1) v := by
  have hfirst :
      (∑ k ∈ Finset.range (j + 1),
          zudilinBackwardShiftCoeff j (k + 1) * v (n - (k + 1))) =
        ∑ k ∈ Finset.range j,
          zudilinBackwardShiftCoeff j (k + 1) * v (n - (k + 1)) := by
    rw [Finset.sum_range_succ]
    simp [zudilinBackwardShiftCoeff_eq_zero_of_lt (Nat.lt_succ_self j)]
  have hindex :
      (∑ k ∈ Finset.range (j + 1),
          zudilinBackwardShiftCoeff j k * v (n - (k + 1))) =
        ∑ k ∈ Finset.range (j + 1),
          zudilinBackwardShiftCoeff j k * v ((n - 1) - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [show n - (k + 1) = (n - 1) - k by
      have hk' : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      omega]
  have hdecomp :
      (∑ k ∈ Finset.range (j + 1),
          zudilinBackwardShiftCoeff j k * v (n - k)) =
        (∑ k ∈ Finset.range j,
          zudilinBackwardShiftCoeff j (k + 1) * v (n - (k + 1))) + v n := by
    rw [Finset.sum_range_succ']
    simp
  rw [zudilinBackwardShiftApply, zudilinBackwardShiftApply,
    zudilinBackwardShiftApply]
  rw [show j + 1 + 1 = (j + 1) + 1 by omega,
    Finset.sum_range_succ']
  simp only [zudilinBackwardShiftCoeff_zero, one_mul, Nat.sub_zero]
  calc
    (∑ k ∈ Finset.range (j + 1),
        zudilinBackwardShiftCoeff (j + 1) (k + 1) * v (n - (k + 1))) + v n =
      v n +
        ∑ k ∈ Finset.range (j + 1),
          (zudilinBackwardShiftCoeff j (k + 1) -
            PowerSeries.X ^ j * zudilinBackwardShiftCoeff j k) *
              v (n - (k + 1)) := by
        rw [add_comm]
        apply congrArg (fun z => v n + z)
        apply Finset.sum_congr rfl
        intro k hk
        rw [zudilinBackwardShiftCoeff_succ j k
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = v n +
        (∑ k ∈ Finset.range (j + 1),
          zudilinBackwardShiftCoeff j (k + 1) * v (n - (k + 1))) -
        PowerSeries.X ^ j *
          (∑ k ∈ Finset.range (j + 1),
            zudilinBackwardShiftCoeff j k * v (n - (k + 1))) := by
              simp_rw [sub_mul]
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
              simp_rw [mul_assoc]
              ring
    _ = (v n +
        ∑ k ∈ Finset.range j,
          zudilinBackwardShiftCoeff j (k + 1) * v (n - (k + 1))) -
        PowerSeries.X ^ j *
          (∑ k ∈ Finset.range (j + 1),
            zudilinBackwardShiftCoeff j k * v ((n - 1) - k)) := by
              rw [hfirst, hindex]
    _ = (∑ k ∈ Finset.range (j + 1),
          zudilinBackwardShiftCoeff j k * v (n - k)) -
        PowerSeries.X ^ j *
          (∑ k ∈ Finset.range (j + 1),
            zudilinBackwardShiftCoeff j k * v ((n - 1) - k)) := by
              rw [hdecomp]
              ring

/-- Lower-unitriangular matrix implementing the rowwise source operators.
Row `j` combines source row `r≤j` with backward-shift index `j-r`. -/
noncomputable def zudilinBackwardShiftMatrix (N : ℕ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  fun j r => if (r : ℕ) ≤ (j : ℕ) then
    zudilinBackwardShiftCoeff (j : ℕ) ((j : ℕ) - (r : ℕ)) else 0

theorem zudilinBackwardShiftMatrix_lowerTriangular (N : ℕ) :
    Matrix.BlockTriangular (zudilinBackwardShiftMatrix N)
      (fun i : Fin N => OrderDual.toDual i) := by
  intro i j hij
  rw [OrderDual.toDual_lt_toDual] at hij
  rw [zudilinBackwardShiftMatrix, if_neg]
  exact_mod_cast (not_le_of_gt hij)

theorem det_zudilinBackwardShiftMatrix (N : ℕ) :
    (zudilinBackwardShiftMatrix N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _
    (zudilinBackwardShiftMatrix_lowerTriangular N)]
  simp [zudilinBackwardShiftMatrix]

/-- Hankel matrix of an arbitrary power-series moment sequence. -/
noncomputable def zudilinMomentMatrix (N : ℕ) (v : ℕ → PowerSeries ℤ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  fun j l => v ((j : ℕ) + (l : ℕ))

/-- Apply exactly the source `D_j` operator to row `j`. -/
noncomputable def zudilinBackwardShiftedMomentMatrix
    (N : ℕ) (v : ℕ → PowerSeries ℤ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  zudilinBackwardShiftMatrix N * zudilinMomentMatrix N v

/-- **The source backward shifts preserve every Hankel determinant.**  This
kernel-checks the row-operation passage for the exact displayed
`(-1)^k q^(k(k-1)/2)[j choose k]_q` coefficients, independently of any
leading-term estimate for the particular normalized moments. -/
theorem det_zudilinBackwardShiftedMomentMatrix
    (N : ℕ) (v : ℕ → PowerSeries ℤ) :
    (zudilinBackwardShiftedMomentMatrix N v).det =
      (zudilinMomentMatrix N v).det := by
  rw [zudilinBackwardShiftedMomentMatrix, Matrix.det_mul,
    det_zudilinBackwardShiftMatrix, one_mul]

/-! ## Unique-minimum determinant order principle -/

/-- A finite sum of power series has the order of its unique lowest-order
summand.  This is the filtered algebra needed to pass from entrywise initial
terms to a determinant order without assuming that the full matrix equals its
associated grade. -/
theorem order_sum_eq_of_unique_lowest
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → PowerSeries ℤ) (a : ι) (B : ℕ)
    (ha : PowerSeries.order (f a) = B)
    (hother : ∀ b, b ≠ a → (B : ℕ∞) < PowerSeries.order (f b)) :
    PowerSeries.order (∑ b, f b) = B := by
  have hrest : (B : ℕ∞) <
      PowerSeries.order (∑ b ∈ (Finset.univ.erase a), f b) := by
    have hle : ((B + 1 : ℕ) : ℕ∞) ≤
        PowerSeries.order (∑ b ∈ (Finset.univ.erase a), f b) := by
      apply PowerSeries.nat_le_order
      intro n hn
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro b hb
      apply PowerSeries.coeff_of_lt_order
      have hbne : b ≠ a := (Finset.mem_erase.mp hb).1
      have hnB : n ≤ B := Nat.le_of_lt_succ hn
      exact lt_of_le_of_lt (by exact_mod_cast hnB) (hother b hbne)
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self B) hle
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ a),
    PowerSeries.order_add_of_order_ne]
  · rw [ha, inf_eq_left.2 hrest.le]
  · rw [ha]
    exact ne_of_lt hrest

/-- The signed Leibniz summand of a power-series matrix. -/
noncomputable def zudilinDetTerm {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (PowerSeries ℤ))
    (σ : Equiv.Perm (Fin N)) : PowerSeries ℤ :=
  PowerSeries.C (Equiv.Perm.sign σ : ℤ) * ∏ i, M (σ i) i

theorem det_eq_sum_zudilinDetTerm {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (PowerSeries ℤ)) :
    M.det = ∑ σ : Equiv.Perm (Fin N), zudilinDetTerm M σ := by
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  simp [zudilinDetTerm]

theorem order_zudilinDetTerm {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (PowerSeries ℤ))
    (e : Fin N → Fin N → ℕ)
    (hentry : ∀ i j, PowerSeries.order (M i j) = e i j)
    (σ : Equiv.Perm (Fin N)) :
    PowerSeries.order (zudilinDetTerm M σ) =
      ((∑ i, e (σ i) i : ℕ) : ℕ∞) := by
  have hsign : (Equiv.Perm.sign σ : ℤ) ≠ 0 := Units.ne_zero _
  rw [zudilinDetTerm, PowerSeries.order_mul,
    ← PowerSeries.monomial_zero_eq_C_apply,
    PowerSeries.order_monomial_of_ne_zero _ _ hsign,
    PowerSeries.order_prod]
  simp [hentry]

/-- **Unique-minimum Leibniz bridge.**  If the exact entry orders make one
permutation uniquely minimal, then the determinant has precisely that order.
The hypotheses concern only entrywise orders and a finite combinatorial
minimum; no determinant-level conclusion is smuggled into them. -/
theorem order_det_eq_of_unique_minimizing_permutation {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (PowerSeries ℤ))
    (e : Fin N → Fin N → ℕ) (σ₀ : Equiv.Perm (Fin N)) (B : ℕ)
    (hentry : ∀ i j, PowerSeries.order (M i j) = e i j)
    (hmain : ∑ i, e (σ₀ i) i = B)
    (hother : ∀ σ : Equiv.Perm (Fin N), σ ≠ σ₀ →
      B < ∑ i, e (σ i) i) :
    PowerSeries.order M.det = B := by
  rw [det_eq_sum_zudilinDetTerm]
  apply order_sum_eq_of_unique_lowest
      (fun σ : Equiv.Perm (Fin N) => zudilinDetTerm M σ) σ₀ B
  · rw [order_zudilinDetTerm M e hentry, hmain]
  · intro σ hσ
    rw [order_zudilinDetTerm M e hentry]
    exact_mod_cast hother σ hσ

/-! ## The concrete normalized source moments at `x=z=1` -/

/-- Finite `q`-Pochhammer product `(q^start;q)_len`, represented as an
integer formal power series. -/
noncomputable def zudilinPochhammerPS (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)

theorem constantCoeff_zudilinPochhammerPS (start len : ℕ) (hstart : 0 < start) :
    PowerSeries.constantCoeff (zudilinPochhammerPS start len) = 1 := by
  simp only [zudilinPochhammerPS, map_prod, map_sub, map_one, map_pow,
    PowerSeries.constantCoeff_X]
  apply Finset.prod_eq_one
  intro r hr
  rw [zero_pow (by omega)]
  norm_num

theorem zudilinPochhammerPS_succ (start len : ℕ) :
    zudilinPochhammerPS start (len + 1) =
      zudilinPochhammerPS start len *
        (1 - PowerSeries.X ^ (start + len)) := by
  simp [zudilinPochhammerPS, Finset.prod_range_succ]

theorem zudilinPochhammerPS_succ_start (start len : ℕ) :
    zudilinPochhammerPS start (len + 1) =
      (1 - PowerSeries.X ^ start) *
        zudilinPochhammerPS (start + 1) len := by
  induction len with
  | zero => simp [zudilinPochhammerPS]
  | succ len ih =>
      rw [show len + 1 + 1 = (len + 1) + 1 by omega,
        zudilinPochhammerPS_succ, ih,
        zudilinPochhammerPS_succ]
      ring_nf

/-- `invOfUnit` at constant coefficient one respects products.  This local
lemma is the exact cancellation device used to compare consecutive normalized
source tails. -/
theorem invOfUnit_mul_one
    (φ ψ : PowerSeries ℤ)
    (hφ : PowerSeries.constantCoeff φ = 1)
    (hψ : PowerSeries.constantCoeff ψ = 1) :
    PowerSeries.invOfUnit (φ * ψ) 1 =
      PowerSeries.invOfUnit φ 1 * PowerSeries.invOfUnit ψ 1 := by
  have hφψ : PowerSeries.constantCoeff (φ * ψ) = (1 : ℤˣ) := by
    simp [hφ, hψ]
  have hleft :
      (φ * ψ) * PowerSeries.invOfUnit (φ * ψ) 1 = 1 :=
    PowerSeries.mul_invOfUnit (φ * ψ) 1 hφψ
  have hφinv : φ * PowerSeries.invOfUnit φ 1 = 1 := by
    exact PowerSeries.mul_invOfUnit φ 1 (by simpa using hφ)
  have hψinv : ψ * PowerSeries.invOfUnit ψ 1 = 1 := by
    exact PowerSeries.mul_invOfUnit ψ 1 (by simpa using hψ)
  have hright :
      (φ * ψ) *
          (PowerSeries.invOfUnit φ 1 * PowerSeries.invOfUnit ψ 1) = 1 := by
    calc
      (φ * ψ) *
          (PowerSeries.invOfUnit φ 1 * PowerSeries.invOfUnit ψ 1) =
          (φ * PowerSeries.invOfUnit φ 1) *
            (ψ * PowerSeries.invOfUnit ψ 1) := by ring
      _ = 1 := by rw [hφinv, hψinv, one_mul]
  calc
    PowerSeries.invOfUnit (φ * ψ) 1 =
        PowerSeries.invOfUnit (φ * ψ) 1 * 1 := by ring
    _ = PowerSeries.invOfUnit (φ * ψ) 1 *
        ((φ * ψ) *
          (PowerSeries.invOfUnit φ 1 * PowerSeries.invOfUnit ψ 1)) := by
            rw [hright]
    _ = (PowerSeries.invOfUnit φ 1 * PowerSeries.invOfUnit ψ 1) *
        ((φ * ψ) * PowerSeries.invOfUnit (φ * ψ) 1) := by ring
    _ = PowerSeries.invOfUnit φ 1 * PowerSeries.invOfUnit ψ 1 := by
          rw [hleft]
          ring

/-- The exact unit multiplying a normalized tail when its moment index moves
from `n` to `n+1`. -/
noncomputable def zudilinNormalizedTailStepUnit (n t : ℕ) : PowerSeries ℤ :=
  (1 - PowerSeries.X ^ (n + 1)) ^ 3 *
    (1 - PowerSeries.X ^ (n + t + 1)) ^ 2 *
    PowerSeries.invOfUnit (1 - PowerSeries.X ^ (2 * n + t + 2)) 1 *
    PowerSeries.invOfUnit (1 - PowerSeries.X ^ (2 * n + t + 3)) 1

@[simp] theorem constantCoeff_zudilinNormalizedTailStepUnit (n t : ℕ) :
    PowerSeries.constantCoeff (zudilinNormalizedTailStepUnit n t) = 1 := by
  simp [zudilinNormalizedTailStepUnit]

private theorem coeff_one_sub_X_pow_cube_at (d : ℕ) (hd : 0 < d) :
    PowerSeries.coeff d
        ((1 - PowerSeries.X ^ d : PowerSeries ℤ) ^ 3) = -3 := by
  ring_nf
  simp only [map_sub, map_add]
  change PowerSeries.coeff d 1 -
        PowerSeries.coeff d (PowerSeries.X ^ d * PowerSeries.C (3 : ℤ)) +
        PowerSeries.coeff d (PowerSeries.X ^ (d * 2) * PowerSeries.C (3 : ℤ)) -
        PowerSeries.coeff d (PowerSeries.X ^ (d * 3)) = -3
  rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_C]
  simp [PowerSeries.coeff_X_pow, hd.ne']

private theorem coeff_one_sub_X_pow_fifth_at (d : ℕ) (hd : 0 < d) :
    PowerSeries.coeff d
        ((1 - PowerSeries.X ^ d : PowerSeries ℤ) ^ 5) = -5 := by
  ring_nf
  simp only [map_sub, map_add]
  change PowerSeries.coeff d 1 -
        PowerSeries.coeff d (PowerSeries.X ^ d * PowerSeries.C (5 : ℤ)) +
        PowerSeries.coeff d (PowerSeries.X ^ (d * 2) * PowerSeries.C (10 : ℤ)) -
        PowerSeries.coeff d (PowerSeries.X ^ (d * 3) * PowerSeries.C (10 : ℤ)) +
        PowerSeries.coeff d (PowerSeries.X ^ (d * 4) * PowerSeries.C (5 : ℤ)) -
        PowerSeries.coeff d (PowerSeries.X ^ (d * 5)) = -5
  rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_C]
  simp [PowerSeries.coeff_X_pow, hd.ne']

/-- Clearing the two moving denominator factors from one exact tail step
recovers the finite numerator ratio. -/
theorem zudilinNormalizedTailStepUnit_mul_denominators (n t : ℕ) :
    zudilinNormalizedTailStepUnit n t *
        (1 - PowerSeries.X ^ (2 * n + t + 2)) *
        (1 - PowerSeries.X ^ (2 * n + t + 3)) =
      (1 - PowerSeries.X ^ (n + 1)) ^ 3 *
        (1 - PowerSeries.X ^ (n + t + 1)) ^ 2 := by
  let A : PowerSeries ℤ := 1 - PowerSeries.X ^ (n + 1)
  let B : PowerSeries ℤ := 1 - PowerSeries.X ^ (n + t + 1)
  let C : PowerSeries ℤ := 1 - PowerSeries.X ^ (2 * n + t + 2)
  let D : PowerSeries ℤ := 1 - PowerSeries.X ^ (2 * n + t + 3)
  have hC : PowerSeries.constantCoeff C = 1 := by simp [C]
  have hD : PowerSeries.constantCoeff D = 1 := by simp [D]
  have hCinv : PowerSeries.invOfUnit C 1 * C = 1 := by
    exact PowerSeries.invOfUnit_mul C 1 (by simpa using hC)
  have hDinv : PowerSeries.invOfUnit D 1 * D = 1 := by
    exact PowerSeries.invOfUnit_mul D 1 (by simpa using hD)
  change (A ^ 3 * B ^ 2 * PowerSeries.invOfUnit C 1 *
      PowerSeries.invOfUnit D 1) * C * D = A ^ 3 * B ^ 2
  calc
    (A ^ 3 * B ^ 2 * PowerSeries.invOfUnit C 1 *
        PowerSeries.invOfUnit D 1) * C * D =
      A ^ 3 * B ^ 2 * (PowerSeries.invOfUnit C 1 * C) *
        (PowerSeries.invOfUnit D 1 * D) := by ac_rfl
    _ = _ := by rw [hCinv, hDinv, mul_one, mul_one]

/-- The first associated-grade coefficient of the literal source-tail step is
`-5` in the zero state and `-3` in every positive state. -/
theorem coeff_zudilinNormalizedTailStepUnit_first (n t : ℕ) :
    PowerSeries.coeff (n + 1) (zudilinNormalizedTailStepUnit n t) =
      if t = 0 then -5 else -3 := by
  let C : PowerSeries ℤ := 1 - PowerSeries.X ^ (2 * n + t + 2)
  let D : PowerSeries ℤ := 1 - PowerSeries.X ^ (2 * n + t + 3)
  have hCorder : ((n + 1 : ℕ) : ℕ∞) <
      PowerSeries.order (PowerSeries.X ^ (2 * n + t + 2) : PowerSeries ℤ) := by
    rw [PowerSeries.order_X_pow]
    exact_mod_cast (show n + 1 < 2 * n + t + 2 by omega)
  have hDorder : ((n + 1 : ℕ) : ℕ∞) <
      PowerSeries.order (PowerSeries.X ^ (2 * n + t + 3) : PowerSeries ℤ) := by
    rw [PowerSeries.order_X_pow]
    exact_mod_cast (show n + 1 < 2 * n + t + 3 by omega)
  have hclear :
      PowerSeries.coeff (n + 1)
          (zudilinNormalizedTailStepUnit n t * C * D) =
        PowerSeries.coeff (n + 1) (zudilinNormalizedTailStepUnit n t) := by
    rw [show zudilinNormalizedTailStepUnit n t * C * D =
        (zudilinNormalizedTailStepUnit n t * C) * D by ring]
    rw [show C = 1 - PowerSeries.X ^ (2 * n + t + 2) by rfl,
      show D = 1 - PowerSeries.X ^ (2 * n + t + 3) by rfl,
      PowerSeries.coeff_mul_one_sub_of_lt_order (n + 1) hDorder,
      PowerSeries.coeff_mul_one_sub_of_lt_order (n + 1) hCorder]
  have hnum := congrArg (PowerSeries.coeff (n + 1))
    (zudilinNormalizedTailStepUnit_mul_denominators n t)
  change PowerSeries.coeff (n + 1)
      (zudilinNormalizedTailStepUnit n t * C * D) = _ at hnum
  rw [hclear] at hnum
  by_cases ht : t = 0
  · subst t
    rw [if_pos rfl]
    have hpow :
        (1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3 *
            (1 - PowerSeries.X ^ (n + 0 + 1)) ^ 2 =
          (1 - PowerSeries.X ^ (n + 1)) ^ 5 := by
      simp only [Nat.add_zero]
      ring
    rw [hpow, coeff_one_sub_X_pow_fifth_at (n + 1) (by omega)] at hnum
    exact hnum
  · rw [if_neg ht]
    have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hBOrder : ((n + 1 : ℕ) : ℕ∞) <
        PowerSeries.order
          (PowerSeries.X ^ (n + t + 1) : PowerSeries ℤ) := by
      rw [PowerSeries.order_X_pow]
      exact_mod_cast (show n + 1 < n + t + 1 by omega)
    have hnumcoeff :
        PowerSeries.coeff (n + 1)
            ((1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3 *
              (1 - PowerSeries.X ^ (n + t + 1)) ^ 2) =
          PowerSeries.coeff (n + 1)
            ((1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3) := by
      rw [pow_two]
      calc
        PowerSeries.coeff (n + 1)
            ((1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3 *
              ((1 - PowerSeries.X ^ (n + t + 1)) *
                (1 - PowerSeries.X ^ (n + t + 1)))) =
          PowerSeries.coeff (n + 1)
            (((1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3 *
              (1 - PowerSeries.X ^ (n + t + 1))) *
                (1 - PowerSeries.X ^ (n + t + 1))) := by rw [mul_assoc]
        _ = PowerSeries.coeff (n + 1)
            ((1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3 *
              (1 - PowerSeries.X ^ (n + t + 1))) := by
          rw [PowerSeries.coeff_mul_one_sub_of_lt_order (n + 1) hBOrder]
        _ = PowerSeries.coeff (n + 1)
            ((1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3) := by
          rw [PowerSeries.coeff_mul_one_sub_of_lt_order (n + 1) hBOrder]
    rw [hnumcoeff,
      coeff_one_sub_X_pow_cube_at (n + 1) (by omega)] at hnum
    exact hnum

/-- Below its first associated grade, the literal tail-step unit is exactly
the constant series. -/
theorem coeff_zudilinNormalizedTailStepUnit_eq_zero_of_pos_lt
    (n t d : ℕ) (hdpos : 0 < d) (hd : d < n + 1) :
    PowerSeries.coeff d (zudilinNormalizedTailStepUnit n t) = 0 := by
  let A : PowerSeries ℤ := 1 - PowerSeries.X ^ (n + 1)
  let B : PowerSeries ℤ := 1 - PowerSeries.X ^ (n + t + 1)
  let C : PowerSeries ℤ := 1 - PowerSeries.X ^ (2 * n + t + 2)
  let D : PowerSeries ℤ := 1 - PowerSeries.X ^ (2 * n + t + 3)
  have hAorder : (d : ℕ∞) <
      PowerSeries.order (PowerSeries.X ^ (n + 1) : PowerSeries ℤ) := by
    rw [PowerSeries.order_X_pow]
    exact_mod_cast hd
  have hBorder : (d : ℕ∞) <
      PowerSeries.order (PowerSeries.X ^ (n + t + 1) : PowerSeries ℤ) := by
    rw [PowerSeries.order_X_pow]
    exact_mod_cast (show d < n + t + 1 by omega)
  have hCorder : (d : ℕ∞) <
      PowerSeries.order (PowerSeries.X ^ (2 * n + t + 2) : PowerSeries ℤ) := by
    rw [PowerSeries.order_X_pow]
    exact_mod_cast (show d < 2 * n + t + 2 by omega)
  have hDorder : (d : ℕ∞) <
      PowerSeries.order (PowerSeries.X ^ (2 * n + t + 3) : PowerSeries ℤ) := by
    rw [PowerSeries.order_X_pow]
    exact_mod_cast (show d < 2 * n + t + 3 by omega)
  have hclear :
      PowerSeries.coeff d
          (zudilinNormalizedTailStepUnit n t * C * D) =
        PowerSeries.coeff d (zudilinNormalizedTailStepUnit n t) := by
    rw [show C = 1 - PowerSeries.X ^ (2 * n + t + 2) by rfl,
      show D = 1 - PowerSeries.X ^ (2 * n + t + 3) by rfl,
      PowerSeries.coeff_mul_one_sub_of_lt_order d hDorder,
      PowerSeries.coeff_mul_one_sub_of_lt_order d hCorder]
  have hnum := congrArg (PowerSeries.coeff d)
    (zudilinNormalizedTailStepUnit_mul_denominators n t)
  change PowerSeries.coeff d
      (zudilinNormalizedTailStepUnit n t * C * D) = _ at hnum
  rw [hclear] at hnum
  rw [show
      (1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3 *
          (1 - PowerSeries.X ^ (n + t + 1)) ^ 2 =
        (((((1 : PowerSeries ℤ) * A) * A) * A) * B) * B by
      simp only [A, B, one_mul]
      ring] at hnum
  rw [show B = 1 - PowerSeries.X ^ (n + t + 1) by rfl,
    PowerSeries.coeff_mul_one_sub_of_lt_order d hBorder,
    PowerSeries.coeff_mul_one_sub_of_lt_order d hBorder,
    show A = 1 - PowerSeries.X ^ (n + 1) by rfl,
    PowerSeries.coeff_mul_one_sub_of_lt_order d hAorder,
    PowerSeries.coeff_mul_one_sub_of_lt_order d hAorder,
    PowerSeries.coeff_mul_one_sub_of_lt_order d hAorder] at hnum
  simpa [PowerSeries.coeff_one, hdpos.ne'] using hnum

/-- The tail-step unit differs from `1` only from associated degree `n+1`
onward. -/
theorem natCast_succ_le_order_zudilinNormalizedTailStepUnit_sub_one
    (n t : ℕ) :
    (((n + 1 : ℕ) : ℕ∞) : ℕ∞) ≤
      PowerSeries.order (zudilinNormalizedTailStepUnit n t - 1) := by
  apply PowerSeries.nat_le_order
  intro d hd
  rw [map_sub]
  cases d with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ d =>
      rw [coeff_zudilinNormalizedTailStepUnit_eq_zero_of_pos_lt
        n t (d + 1) (by omega) hd]
      simp [PowerSeries.coeff_one]

/-- The unit factor in the `t`th normalized summand
`(q;q)_n^3(q^(t+1);q)_n/(q^(n+1+t);q)_(n+1)`. -/
noncomputable def zudilinNormalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  zudilinPochhammerPS 1 n ^ 3 * zudilinPochhammerPS (t + 1) n *
    PowerSeries.invOfUnit (zudilinPochhammerPS (n + 1 + t) (n + 1)) 1

/-- **Exact consecutive-index source-tail identity.**  This is the literal
hypergeometric ratio behind the filtered associated-grade transition; no
truncation or asymptotic notation is used. -/
theorem zudilinNormalizedTailUnit_succ (n t : ℕ) :
    zudilinNormalizedTailUnit (n + 1) t =
      zudilinNormalizedTailUnit n t *
        zudilinNormalizedTailStepUnit n t := by
  let A : PowerSeries ℤ := 1 - PowerSeries.X ^ (n + 1)
  let B : PowerSeries ℤ := 1 - PowerSeries.X ^ (n + t + 1)
  let O : PowerSeries ℤ := zudilinPochhammerPS (n + t + 2) n
  let C : PowerSeries ℤ := 1 - PowerSeries.X ^ (2 * n + t + 2)
  let D : PowerSeries ℤ := 1 - PowerSeries.X ^ (2 * n + t + 3)
  have hA : PowerSeries.constantCoeff A = 1 := by simp [A]
  have hB : PowerSeries.constantCoeff B = 1 := by simp [B]
  have hO : PowerSeries.constantCoeff O = 1 := by
    exact constantCoeff_zudilinPochhammerPS _ _ (by omega)
  have hC : PowerSeries.constantCoeff C = 1 := by simp [C]
  have hD : PowerSeries.constantCoeff D = 1 := by simp [D]
  have hdenN :
      zudilinPochhammerPS (n + 1 + t) (n + 1) = B * O := by
    simpa [B, O, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      zudilinPochhammerPS_succ_start (n + 1 + t) n
  have hdenSucc :
      zudilinPochhammerPS (n + 1 + 1 + t) (n + 1 + 1) =
        O * C * D := by
    rw [show n + 1 + 1 = (n + 1) + 1 by omega,
      zudilinPochhammerPS_succ,
      zudilinPochhammerPS_succ]
    simp only [O, C, D]
    have hbase : n + 1 + 1 + t = n + t + 2 := by omega
    have hCexp : n + t + 2 + n = 2 * n + t + 2 := by omega
    have hDexp : n + t + 2 + (n + 1) = 2 * n + t + 3 := by omega
    rw [hbase, hCexp, hDexp]
  have hPochOne :
      zudilinPochhammerPS 1 (n + 1) =
        zudilinPochhammerPS 1 n * A := by
    simpa [A, Nat.add_comm] using zudilinPochhammerPS_succ 1 n
  have hPochTail :
      zudilinPochhammerPS (t + 1) (n + 1) =
        zudilinPochhammerPS (t + 1) n * B := by
    simpa [B, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      zudilinPochhammerPS_succ (t + 1) n
  have hinvN :
      PowerSeries.invOfUnit
          (zudilinPochhammerPS (n + 1 + t) (n + 1)) 1 =
        PowerSeries.invOfUnit B 1 * PowerSeries.invOfUnit O 1 := by
    rw [hdenN]
    exact invOfUnit_mul_one B O hB hO
  have hinvSucc :
      PowerSeries.invOfUnit
          (zudilinPochhammerPS (n + 1 + 1 + t) (n + 1 + 1)) 1 =
        PowerSeries.invOfUnit O 1 *
          PowerSeries.invOfUnit C 1 * PowerSeries.invOfUnit D 1 := by
    rw [hdenSucc, invOfUnit_mul_one (O * C) D (by simp [hO, hC]) hD,
      invOfUnit_mul_one O C hO hC]
  have hBinv : PowerSeries.invOfUnit B 1 * B = 1 := by
    exact PowerSeries.invOfUnit_mul B 1 (by simpa using hB)
  rw [zudilinNormalizedTailUnit, zudilinNormalizedTailUnit,
    zudilinNormalizedTailStepUnit, hPochOne, hPochTail, hinvN, hinvSucc]
  change
    (zudilinPochhammerPS 1 n * A) ^ 3 *
        (zudilinPochhammerPS (t + 1) n * B) *
          (PowerSeries.invOfUnit O 1 * PowerSeries.invOfUnit C 1 *
            PowerSeries.invOfUnit D 1) =
      (zudilinPochhammerPS 1 n ^ 3 *
          zudilinPochhammerPS (t + 1) n *
            (PowerSeries.invOfUnit B 1 * PowerSeries.invOfUnit O 1)) *
        (A ^ 3 * B ^ 2 * PowerSeries.invOfUnit C 1 *
          PowerSeries.invOfUnit D 1)
  calc
    (zudilinPochhammerPS 1 n * A) ^ 3 *
        (zudilinPochhammerPS (t + 1) n * B) *
          (PowerSeries.invOfUnit O 1 * PowerSeries.invOfUnit C 1 *
            PowerSeries.invOfUnit D 1) =
      (zudilinPochhammerPS 1 n ^ 3 *
          zudilinPochhammerPS (t + 1) n *
            PowerSeries.invOfUnit O 1) *
        (A ^ 3 * B * PowerSeries.invOfUnit C 1 *
          PowerSeries.invOfUnit D 1) := by ring
    _ =
      (zudilinPochhammerPS 1 n ^ 3 *
          zudilinPochhammerPS (t + 1) n *
            (PowerSeries.invOfUnit B 1 * PowerSeries.invOfUnit O 1)) *
        (A ^ 3 * B ^ 2 * PowerSeries.invOfUnit C 1 *
          PowerSeries.invOfUnit D 1) := by
      rw [show
        (zudilinPochhammerPS 1 n ^ 3 *
            zudilinPochhammerPS (t + 1) n *
              (PowerSeries.invOfUnit B 1 * PowerSeries.invOfUnit O 1)) *
          (A ^ 3 * B ^ 2 * PowerSeries.invOfUnit C 1 *
            PowerSeries.invOfUnit D 1) =
          (zudilinPochhammerPS 1 n ^ 3 *
            zudilinPochhammerPS (t + 1) n *
              PowerSeries.invOfUnit O 1) *
          (A ^ 3 * B * PowerSeries.invOfUnit C 1 *
            PowerSeries.invOfUnit D 1) by
        calc
          _ = (PowerSeries.invOfUnit B 1 * B) *
              ((zudilinPochhammerPS 1 n ^ 3 *
                  zudilinPochhammerPS (t + 1) n *
                    PowerSeries.invOfUnit O 1) *
                (A ^ 3 * B * PowerSeries.invOfUnit C 1 *
                  PowerSeries.invOfUnit D 1)) := by ring
          _ = _ := by rw [hBinv, one_mul]]

@[simp] theorem constantCoeff_zudilinNormalizedTailUnit (n t : ℕ) :
    PowerSeries.constantCoeff (zudilinNormalizedTailUnit n t) = 1 := by
  simp only [zudilinNormalizedTailUnit, map_mul, map_pow,
    constantCoeff_zudilinPochhammerPS 1 n (by omega),
    constantCoeff_zudilinPochhammerPS (t + 1) n (by omega),
    PowerSeries.constantCoeff_invOfUnit]
  norm_num

theorem order_zudilinNormalizedTailUnit (n t : ℕ) :
    PowerSeries.order (zudilinNormalizedTailUnit n t) = 0 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · simp [PowerSeries.coeff_zero_eq_constantCoeff]
  · intro i hi
    omega

/-- The exact `t`th summand of Zudilin's normalized moment `v_n^*` at
`x=z=1`. -/
noncomputable def zudilinNormalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * zudilinNormalizedTailUnit n t

/-- The exact normalized source summand inherits the consecutive-index unit
recurrence, with the expected additional shift `X^t`. -/
theorem zudilinNormalizedTail_succ (n t : ℕ) :
    zudilinNormalizedTail (n + 1) t =
      PowerSeries.X ^ t * zudilinNormalizedTail n t *
        zudilinNormalizedTailStepUnit n t := by
  rw [zudilinNormalizedTail, zudilinNormalizedTail,
    zudilinNormalizedTailUnit_succ]
  have hexp : (n + 1 + 1) * t = t + (n + 1) * t := by ring
  rw [hexp, pow_add]
  ring

/-- The zero-tail source difference has first coefficient `-5` at every
index.  This is the zero-state emission entering the first transformed row. -/
theorem coeff_zudilinNormalizedTail_succ_zero_sub_first (n : ℕ) :
    PowerSeries.coeff (n + 1)
        (zudilinNormalizedTail (n + 1) 0 -
          zudilinNormalizedTail n 0) = -5 := by
  let ψ : PowerSeries ℤ := zudilinNormalizedTailStepUnit n 0 - 1
  have hrewrite :
      zudilinNormalizedTail (n + 1) 0 - zudilinNormalizedTail n 0 =
        zudilinNormalizedTail n 0 * ψ := by
    rw [zudilinNormalizedTail_succ]
    simp only [pow_zero, one_mul, ψ]
    ring
  have hψzero : PowerSeries.coeff 0 ψ = 0 := by
    simp [ψ, PowerSeries.coeff_zero_eq_constantCoeff]
  have hψlt : ∀ d, d < n + 1 → PowerSeries.coeff d ψ = 0 := by
    intro d hd
    cases d with
    | zero => exact hψzero
    | succ d =>
        change PowerSeries.coeff (d + 1)
            (zudilinNormalizedTailStepUnit n 0 - 1) = 0
        rw [map_sub,
          coeff_zudilinNormalizedTailStepUnit_eq_zero_of_pos_lt
            n 0 (d + 1) (by omega) hd]
        simp [PowerSeries.coeff_one]
  have hψfirst : PowerSeries.coeff (n + 1) ψ = -5 := by
    change PowerSeries.coeff (n + 1)
        (zudilinNormalizedTailStepUnit n 0 - 1) = -5
    rw [map_sub, coeff_zudilinNormalizedTailStepUnit_first]
    simp [PowerSeries.coeff_one]
  rw [hrewrite, PowerSeries.coeff_mul,
    Finset.sum_eq_single_of_mem (0, n + 1) (by simp)]
  · simp [PowerSeries.coeff_zero_eq_constantCoeff,
      zudilinNormalizedTail, hψfirst]
  · intro ij hij hne
    have hadd : ij.1 + ij.2 = n + 1 :=
      Finset.mem_antidiagonal.mp hij
    have hsecond : ij.2 < n + 1 := by
      have hle : ij.2 ≤ n + 1 := by omega
      exact lt_of_le_of_ne hle (fun heq => hne (by
        apply Prod.ext
        · omega
        · exact heq))
    rw [hψlt ij.2 hsecond, mul_zero]

/-- Every coefficient below the first zero-tail source difference vanishes. -/
theorem coeff_zudilinNormalizedTail_succ_zero_sub_eq_zero_of_lt
    (n d : ℕ) (hd : d < n + 1) :
    PowerSeries.coeff d
        (zudilinNormalizedTail (n + 1) 0 -
          zudilinNormalizedTail n 0) = 0 := by
  have hrewrite :
      zudilinNormalizedTail (n + 1) 0 - zudilinNormalizedTail n 0 =
        zudilinNormalizedTail n 0 *
          (zudilinNormalizedTailStepUnit n 0 - 1) := by
    rw [zudilinNormalizedTail_succ]
    simp only [pow_zero, one_mul]
    ring
  rw [hrewrite]
  apply PowerSeries.coeff_mul_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hd)
    (natCast_succ_le_order_zudilinNormalizedTailStepUnit_sub_one n 0)

theorem order_zudilinNormalizedTail (n t : ℕ) :
    PowerSeries.order (zudilinNormalizedTail n t) = (n + 1) * t := by
  rw [zudilinNormalizedTail, PowerSeries.order_mul,
    PowerSeries.order_X_pow, order_zudilinNormalizedTailUnit]
  simp

/-- Every coefficient below the exact shift of a normalized tail vanishes. -/
theorem coeff_zudilinNormalizedTail_eq_zero_of_lt (n t d : ℕ)
    (hd : d < (n + 1) * t) :
    PowerSeries.coeff d (zudilinNormalizedTail n t) = 0 := by
  rw [zudilinNormalizedTail, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hd]

/-- The first nonzero coefficient of every normalized tail is exactly one. -/
@[simp] theorem coeff_zudilinNormalizedTail_leading (n t : ℕ) :
    PowerSeries.coeff ((n + 1) * t) (zudilinNormalizedTail n t) = 1 := by
  rw [zudilinNormalizedTail]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using
    (PowerSeries.coeff_X_pow_mul
      (zudilinNormalizedTailUnit n t) ((n + 1) * t) 0)

/-- Zudilin's normalized moment `v_n^*` as a genuine formal power series.
For each coefficient `q^d`, only tails `t≤d/(n+1)` can contribute, so the
source infinite sum is defined coefficientwise by this exact finite sum. -/
noncomputable def zudilinNormalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (zudilinNormalizedTail n t)

@[simp] theorem coeff_zudilinNormalizedMoment (n d : ℕ) :
    PowerSeries.coeff d (zudilinNormalizedMoment n) =
      ∑ t ∈ Finset.range (d / (n + 1) + 1),
        PowerSeries.coeff d (zudilinNormalizedTail n t) := by
  simp [zudilinNormalizedMoment]

@[simp] theorem constantCoeff_zudilinNormalizedMoment (n : ℕ) :
    PowerSeries.constantCoeff (zudilinNormalizedMoment n) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    coeff_zudilinNormalizedMoment]
  simp [zudilinNormalizedTail, constantCoeff_zudilinNormalizedTailUnit]

/-- The exact source-transformed normalized moment in row `j`, column `l`:
`D_j v_(j+l)^*`. -/
noncomputable def zudilinTransformedNormalizedMoment (j l : ℕ) :
    PowerSeries ℤ :=
  zudilinBackwardShiftApply j (j + l) zudilinNormalizedMoment

@[simp] theorem zudilinTransformedNormalizedMoment_zero (l : ℕ) :
    zudilinTransformedNormalizedMoment 0 l =
      zudilinNormalizedMoment l := by
  simp [zudilinTransformedNormalizedMoment]

/-- Consecutive transformed rows satisfy the literal source recurrence
`D_(j+1)v_(j+1+l)^* = D_jv_(j+l+1)^* - X^jD_jv_(j+l)^*`.
This is the exact filtered recurrence whose first nonzero coefficient remains
to be identified at all `j,l`. -/
theorem zudilinTransformedNormalizedMoment_succ (j l : ℕ) :
    zudilinTransformedNormalizedMoment (j + 1) l =
      zudilinTransformedNormalizedMoment j (l + 1) -
        PowerSeries.X ^ j * zudilinTransformedNormalizedMoment j l := by
  rw [zudilinTransformedNormalizedMoment,
    zudilinBackwardShiftApply_succ j (j + 1 + l)
      zudilinNormalizedMoment (by omega)]
  simp only [zudilinTransformedNormalizedMoment]
  rw [show j + 1 + l = j + (l + 1) by omega,
    show j + (l + 1) - 1 = j + l by omega]

/-- Below degree `n+1`, the zero-tail summand is the only possible
contribution to the exact normalized moment. -/
theorem coeff_zudilinNormalizedMoment_of_lt (n d : ℕ) (hd : d < n + 1) :
    PowerSeries.coeff d (zudilinNormalizedMoment n) =
      PowerSeries.coeff d (zudilinNormalizedTail n 0) := by
  rw [coeff_zudilinNormalizedMoment, Nat.div_eq_of_lt hd]
  simp

/-- **First nontrivial transformed row, uniformly in the column.**  The exact
coefficient of `X^(l+1)` in `D_1 v_(l+1)^*` is `-6`, matching the all-rank
row scalar `(-1)^1 (2^2·3/2)`. -/
theorem coeff_zudilinTransformedNormalizedMoment_one_first (l : ℕ) :
    PowerSeries.coeff (l + 1)
        (zudilinTransformedNormalizedMoment 1 l) = -6 := by
  have hrow := zudilinTransformedNormalizedMoment_succ 0 l
  simp only [Nat.zero_add, pow_zero, one_mul,
    zudilinTransformedNormalizedMoment_zero] at hrow
  rw [hrow, map_sub,
    coeff_zudilinNormalizedMoment_of_lt (l + 1) (l + 1) (by omega)]
  have hsecond :
      PowerSeries.coeff (l + 1) (zudilinNormalizedMoment l) =
        PowerSeries.coeff (l + 1) (zudilinNormalizedTail l 0) + 1 := by
    rw [coeff_zudilinNormalizedMoment,
      show (l + 1) / (l + 1) = 1 by exact Nat.div_self (by omega)]
    norm_num [Finset.sum_range_succ]
    simpa using (coeff_zudilinNormalizedTail_leading l 1)
  rw [hsecond]
  have hzero := coeff_zudilinNormalizedTail_succ_zero_sub_first l
  rw [map_sub] at hzero
  linarith

theorem coeff_zudilinTransformedNormalizedMoment_one_eq_zero_of_lt
    (l d : ℕ) (hd : d < l + 1) :
    PowerSeries.coeff d (zudilinTransformedNormalizedMoment 1 l) = 0 := by
  have hrow := zudilinTransformedNormalizedMoment_succ 0 l
  simp only [Nat.zero_add, pow_zero, one_mul,
    zudilinTransformedNormalizedMoment_zero] at hrow
  rw [hrow, map_sub,
    coeff_zudilinNormalizedMoment_of_lt (l + 1) d (by omega),
    coeff_zudilinNormalizedMoment_of_lt l d hd]
  have hzero :=
    coeff_zudilinNormalizedTail_succ_zero_sub_eq_zero_of_lt l d hd
  rw [map_sub] at hzero
  exact hzero

/-- The complete initial-monomial theorem for source row `1`, in every
column: exact order `l+1` and coefficient `-6`. -/
theorem order_zudilinTransformedNormalizedMoment_one (l : ℕ) :
    PowerSeries.order (zudilinTransformedNormalizedMoment 1 l) = l + 1 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · rw [coeff_zudilinTransformedNormalizedMoment_one_first]
    norm_num
  · intro d hd
    exact coeff_zudilinTransformedNormalizedMoment_one_eq_zero_of_lt l d hd

/-- **Complete first transformed-row initial monomial, in every column.**
The exact order and its nonzero leading coefficient are packaged together so
that downstream verification surfaces expose the substantive partial result
as one theorem.  Rows `j ≥ 2` are not claimed here. -/
theorem zudilinTransformedNormalizedMoment_one_initialMonomial (l : ℕ) :
    PowerSeries.order (zudilinTransformedNormalizedMoment 1 l) = l + 1 ∧
      PowerSeries.coeff (l + 1)
        (zudilinTransformedNormalizedMoment 1 l) = -6 := by
  exact ⟨order_zudilinTransformedNormalizedMoment_one l,
    coeff_zudilinTransformedNormalizedMoment_one_first l⟩

/-- The exact exponent left after the transformed-row factors and the
Vandermonde leading monomial are combined.  Writing it as a sum of squares
keeps the assembly independent of any division convention. -/
def zudilinSharpHankelQOrder (N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N, (j : ℤ) ^ 2

/-- **Closed form for the sharp all-rank exponent.**  This is the exact
integer identity behind
`ord_q V_N^* = N(N-1)(2N-1)/6`; division by six is postponed so that the
statement is valid in an integral domain without side conditions. -/
theorem six_mul_zudilinSharpHankelQOrder (N : ℕ) :
    6 * zudilinSharpHankelQOrder N =
      (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1) := by
  induction N with
  | zero => simp [zudilinSharpHankelQOrder]
  | succ N ih =>
      rw [zudilinSharpHankelQOrder, Finset.sum_range_succ]
      change 6 * (zudilinSharpHankelQOrder N + (N : ℤ) ^ 2) =
        ((N + 1 : ℕ) : ℤ) * (((N + 1 : ℕ) : ℤ) - 1) *
          (2 * ((N + 1 : ℕ) : ℤ) - 1)
      rw [mul_add, ih]
      push_cast
      ring

/-- Positive magnitude of the leading coefficient contributed by transformed
row `j`.  The numerator is even because `(j+1)(j+2)` is a product of
consecutive integers. -/
def zudilinTransformedRowCoeff (j : ℕ) : ℕ :=
  ((j + 1) ^ 2 * (j + 2)) / 2

theorem two_mul_zudilinTransformedRowCoeff (j : ℕ) :
    2 * zudilinTransformedRowCoeff j = (j + 1) ^ 2 * (j + 2) := by
  rw [zudilinTransformedRowCoeff]
  apply Nat.mul_div_cancel'
  have hconsecutive : 2 ∣ (j + 1) * (j + 2) :=
    (Nat.even_mul_succ_self (j + 1)).two_dvd
  simpa [pow_two, mul_assoc] using dvd_mul_of_dvd_right hconsecutive (j + 1)

/-- The zero tail plus every positive tail has precisely the positive row
coefficient used in the associated Vandermonde matrix. -/
theorem zudilinAssociatedTailRowCoeff_eq (j : ℕ) :
    PowerSeries.coeff j zudilinZeroTailAssociatedReciprocal +
        ∑ r ∈ Finset.range j,
          PowerSeries.coeff r zudilinPositiveTailAssociatedReciprocal =
      (zudilinTransformedRowCoeff j : ℤ) := by
  rw [coeff_zudilinZeroTailAssociatedReciprocal,
    sum_coeff_zudilinPositiveTailAssociatedReciprocal]
  have hscaled :
      6 * ((j + 3).choose 3 + (j + 2).choose 3 + (j + 2).choose 3) =
        3 * ((j + 1) ^ 2 * (j + 2)) := by
    rw [mul_add, mul_add, six_mul_choose_add_three_three,
      six_mul_choose_add_two_three]
    ring
  have htwo :
      2 * ((j + 3).choose 3 + (j + 2).choose 3 + (j + 2).choose 3) =
        (j + 1) ^ 2 * (j + 2) := by
    omega
  have hrow := two_mul_zudilinTransformedRowCoeff j
  have hnat :
      (j + 3).choose 3 + (j + 2).choose 3 + (j + 2).choose 3 =
        zudilinTransformedRowCoeff j := by
    omega
  exact_mod_cast hnat

theorem zudilinTransformedRowCoeff_pos (j : ℕ) :
    0 < zudilinTransformedRowCoeff j := by
  have hdouble := two_mul_zudilinTransformedRowCoeff j
  have hrhs : 0 < (j + 1) ^ 2 * (j + 2) := by positivity
  omega

/-- **Closed form for the first nonzero coefficient magnitude.**  The theorem
avoids natural-number division on the right: equivalently, the product of the
row coefficients is `(N!)^2 (N+1)! / 2^N`. -/
theorem twoPow_mul_prod_zudilinTransformedRowCoeff (N : ℕ) :
    2 ^ N * (∏ j ∈ Finset.range N, zudilinTransformedRowCoeff j) =
      (N.factorial) ^ 2 * (N + 1).factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, pow_succ]
      calc
        2 ^ N * 2 *
              ((∏ j ∈ Finset.range N, zudilinTransformedRowCoeff j) *
                zudilinTransformedRowCoeff N) =
            (2 ^ N * (∏ j ∈ Finset.range N, zudilinTransformedRowCoeff j)) *
              (2 * zudilinTransformedRowCoeff N) := by ring
        _ = (N.factorial ^ 2 * (N + 1).factorial) *
              ((N + 1) ^ 2 * (N + 2)) := by
                rw [ih, two_mul_zudilinTransformedRowCoeff]
        _ = ((N + 1).factorial) ^ 2 * (N + 2).factorial := by
              rw [Nat.factorial_succ (N + 1), Nat.factorial_succ N]
              ring

/-! ## Exact determinant of the associated-graded leading matrix -/

/-- The signed monomial factored from transformed row `j`.  Its sign is the
one produced by the source backward-shift recurrence; retaining it here makes
the later cancellation with the Vandermonde leading sign explicit rather than
passing only to absolute values. -/
noncomputable def zudilinAssociatedLeadingRowScale {N : ℕ} (j : Fin N) :
    PowerSeries ℤ :=
  PowerSeries.C
      (((-1 : ℤ) ^ (j : ℕ)) * (zudilinTransformedRowCoeff (j : ℕ) : ℤ)) *
    PowerSeries.X ^ ((j : ℕ) * ((j : ℕ) + 1) / 2)

theorem zudilinAssociatedLeadingRowScale_ne_zero {N : ℕ} (j : Fin N) :
    zudilinAssociatedLeadingRowScale j ≠ 0 := by
  rw [zudilinAssociatedLeadingRowScale]
  apply mul_ne_zero
  · have hsign : ((-1 : ℤ) ^ (j : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hcoeff : (zudilinTransformedRowCoeff (j : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (zudilinTransformedRowCoeff_pos (j : ℕ)).ne'
    simpa only [map_zero] using
      PowerSeries.C_injective.ne (mul_ne_zero hsign hcoeff)
  · exact pow_ne_zero _ PowerSeries.X_ne_zero

theorem order_zudilinAssociatedLeadingRowScale {N : ℕ} (j : Fin N) :
    PowerSeries.order (zudilinAssociatedLeadingRowScale j) =
      ((j : ℕ) * ((j : ℕ) + 1) / 2 : ℕ) := by
  have hsign : ((-1 : ℤ) ^ (j : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcoeff : (zudilinTransformedRowCoeff (j : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (zudilinTransformedRowCoeff_pos (j : ℕ)).ne'
  rw [zudilinAssociatedLeadingRowScale, PowerSeries.order_mul,
    ← PowerSeries.monomial_zero_eq_C_apply,
    PowerSeries.order_monomial_of_ne_zero _ _ (mul_ne_zero hsign hcoeff),
    PowerSeries.order_X_pow]
  simp

/-- The exact associated-graded matrix after the source row transformations:
row `j` has its signed scalar and triangular `q`-power factored against the
Vandermonde row `1,q^j,q^(2j),...`. -/
noncomputable def zudilinAssociatedLeadingMatrix (N : ℕ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  fun j l => zudilinAssociatedLeadingRowScale j *
    (PowerSeries.X ^ (j : ℕ)) ^ (l : ℕ)

/-- The pointwise leading-term description is exactly a diagonal row scaling
of the power-series Vandermonde matrix.  This is the matrix identity needed to
turn the transformed-row statement into a determinant statement. -/
theorem zudilinAssociatedLeadingMatrix_eq_diagonal_mul_vandermonde (N : ℕ) :
    zudilinAssociatedLeadingMatrix N =
      Matrix.diagonal (fun j => zudilinAssociatedLeadingRowScale j) *
        Matrix.vandermonde (fun j : Fin N =>
          PowerSeries.X ^ (j : ℕ)) := by
  ext j l
  simp [zudilinAssociatedLeadingMatrix]

/-- **Exact associated-graded determinant product.**  The determinant algebra
is now kernel checked at every rank: the transformed row scales multiply, and
the residual determinant is precisely the product of power-series differences
in the Vandermonde formula.  What remains outside Lean is identifying the
source normalized moment determinant with this associated-graded leading
matrix by Zudilin's row operations. -/
theorem det_zudilinAssociatedLeadingMatrix (N : ℕ) :
    (zudilinAssociatedLeadingMatrix N).det =
      (∏ j : Fin N, zudilinAssociatedLeadingRowScale j) *
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (PowerSeries.X ^ (j : ℕ) - PowerSeries.X ^ (i : ℕ)) := by
  rw [zudilinAssociatedLeadingMatrix_eq_diagonal_mul_vandermonde,
    Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]

/-- Distinct transformed rows give distinct power-series Vandermonde nodes.
The proof reads off their exact `X`-orders, so it works uniformly at every
rank rather than by finite determinant expansion. -/
theorem zudilinAssociatedLeadingNode_injective (N : ℕ) :
    Function.Injective (fun j : Fin N =>
      (PowerSeries.X : PowerSeries ℤ) ^ (j : ℕ)) := by
  intro i j hij
  apply Fin.ext
  have horder := congrArg PowerSeries.order hij
  simpa [PowerSeries.order_X_pow] using horder

/-- A Vandermonde factor `X^j-X^i` has exact order `i` when `i<j`.
This is the coefficient-level reason no higher-order cancellation is hidden
inside an individual factor. -/
theorem order_X_pow_sub_X_pow {i j : ℕ} (hij : i < j) :
    PowerSeries.order
        ((PowerSeries.X : PowerSeries ℤ) ^ j - PowerSeries.X ^ i) = i := by
  rw [sub_eq_add_neg, PowerSeries.order_add_of_order_ne]
  · simp [PowerSeries.order_X_pow, PowerSeries.order_neg, hij.le]
  · simp only [PowerSeries.order_X_pow, PowerSeries.order_neg]
    exact_mod_cast hij.ne'

/-- **All-rank noncancellation of the associated-graded determinant.**  Every
signed row scale is nonzero and the residual power-series nodes are distinct;
hence the exact leading matrix has nonzero determinant for every rank.  This
kernel-checks the determinant noncancellation step which previously survived
only in the ordinary Vandermonde argument. -/
theorem det_zudilinAssociatedLeadingMatrix_ne_zero (N : ℕ) :
    (zudilinAssociatedLeadingMatrix N).det ≠ 0 := by
  rw [zudilinAssociatedLeadingMatrix_eq_diagonal_mul_vandermonde,
    Matrix.det_mul]
  apply mul_ne_zero
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      zudilinAssociatedLeadingRowScale_ne_zero j
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (zudilinAssociatedLeadingNode_injective N)

/-- The exact order of the associated-graded determinant, before simplifying
the two finite sums to the sum-of-squares closed form.  The first sum is the
triangular row shift and the second is the full Vandermonde contribution. -/
theorem order_det_zudilinAssociatedLeadingMatrix (N : ℕ) :
    PowerSeries.order (zudilinAssociatedLeadingMatrix N).det =
      (∑ j : Fin N,
          (((j : ℕ) * ((j : ℕ) + 1) / 2 : ℕ) : ℕ∞)) +
        ∑ i : Fin N, ∑ _j ∈ Finset.Ioi i, (((i : ℕ) : ℕ∞)) := by
  rw [det_zudilinAssociatedLeadingMatrix, PowerSeries.order_mul,
    PowerSeries.order_prod]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact order_zudilinAssociatedLeadingRowScale j
  · rw [PowerSeries.order_prod]
    apply Finset.sum_congr rfl
    intro i _
    rw [PowerSeries.order_prod]
    apply Finset.sum_congr rfl
    intro j hj
    apply order_X_pow_sub_X_pow (i := (i : ℕ)) (j := (j : ℕ))
    exact_mod_cast (Finset.mem_Ioi.mp hj)

/-- Natural-number form of the two exact contributions to the transformed
determinant order. -/
def zudilinAssociatedLeadingOrderNat (N : ℕ) : ℕ :=
  (∑ j ∈ Finset.range N, j * (j + 1) / 2) +
    ∑ i ∈ Finset.range N, i * (N - 1 - i)

theorem zudilinVandermondeOrderNat_succ (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), i * ((N + 1) - 1 - i)) =
      (∑ i ∈ Finset.range N, i * (N - 1 - i)) +
        ∑ i ∈ Finset.range N, i := by
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, mul_zero, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  have hsub : N - i = (N - 1 - i) + 1 := by omega
  rw [hsub, mul_add, mul_one]

theorem zudilinAssociatedLeadingOrderNat_succ (N : ℕ) :
    zudilinAssociatedLeadingOrderNat (N + 1) =
      zudilinAssociatedLeadingOrderNat N + N ^ 2 := by
  have htri : N * (N + 1) / 2 = ∑ i ∈ Finset.range (N + 1), i := by
    simpa [mul_comm] using (Finset.sum_range_id (N + 1)).symm
  have hsum : N * (N + 1) / 2 + (∑ i ∈ Finset.range N, i) = N ^ 2 := by
    rw [htri, Finset.sum_range_succ]
    calc
      ((∑ i ∈ Finset.range N, i) + N) + (∑ i ∈ Finset.range N, i) =
          (∑ i ∈ Finset.range N, i) * 2 + N := by omega
      _ = N * (N - 1) + N := by rw [Finset.sum_range_id_mul_two]
      _ = N ^ 2 := by
        cases N with
        | zero => simp
        | succ N => simp; ring
  rw [zudilinAssociatedLeadingOrderNat, Finset.sum_range_succ,
    zudilinVandermondeOrderNat_succ, zudilinAssociatedLeadingOrderNat]
  omega

/-- The triangular row shifts and Vandermonde shifts add to the exact
sum-of-squares order. -/
theorem zudilinAssociatedLeadingOrderNat_eq_sum_sq (N : ℕ) :
    zudilinAssociatedLeadingOrderNat N =
      ∑ j ∈ Finset.range N, j ^ 2 := by
  induction N with
  | zero => simp [zudilinAssociatedLeadingOrderNat]
  | succ N ih =>
      rw [show N + 1 = Nat.succ N by omega,
        zudilinAssociatedLeadingOrderNat_succ, Finset.sum_range_succ, ih]

/-- The power-series determinant order is the natural sum of squares. -/
theorem order_det_zudilinAssociatedLeadingMatrix_eq_sum_sq (N : ℕ) :
    PowerSeries.order (zudilinAssociatedLeadingMatrix N).det =
      ((∑ j ∈ Finset.range N, j ^ 2 : ℕ) : ℕ∞) := by
  rw [order_det_zudilinAssociatedLeadingMatrix,
    ← zudilinAssociatedLeadingOrderNat_eq_sum_sq]
  have hrow :
      (∑ j : Fin N,
          (((j : ℕ) * ((j : ℕ) + 1) / 2 : ℕ) : ℕ∞)) =
        ((∑ j ∈ Finset.range N, j * (j + 1) / 2 : ℕ) : ℕ∞) := by
    norm_cast
    simpa using (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => j * (j + 1) / 2) N)
  have hvander :
      (∑ i : Fin N, ∑ _j ∈ Finset.Ioi i, (((i : ℕ) : ℕ∞))) =
        ((∑ i ∈ Finset.range N, i * (N - 1 - i) : ℕ) : ℕ∞) := by
    norm_cast
    simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi]
    simpa [mul_comm] using (Fin.sum_univ_eq_sum_range
      (fun i : ℕ => i * (N - 1 - i)) N)
  rw [hrow, hvander, ← ENat.coe_add]
  rfl

theorem six_mul_sum_range_sq (N : ℕ) :
    6 * (∑ j ∈ Finset.range N, j ^ 2) =
      N * (N - 1) * (2 * N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      cases N with
      | zero => simp
      | succ N =>
          simp
          have h₁ : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
          have h₂ : 2 * (N + 1 + 1) - 1 = 2 * N + 3 := by omega
          rw [h₁, h₂]
          ring

/-- **Closed exact order of the kernel-checked leading determinant.**  This
joins the power-series determinant calculation to the same division-free
closed form used by the source-facing all-rank theorem. -/
theorem six_mul_order_det_zudilinAssociatedLeadingMatrix (N : ℕ) :
    6 * PowerSeries.order (zudilinAssociatedLeadingMatrix N).det =
      (N * (N - 1) * (2 * N - 1) : ℕ) := by
  rw [order_det_zudilinAssociatedLeadingMatrix_eq_sum_sq]
  exact_mod_cast six_mul_sum_range_sq N

/-- The two exact algebraic outputs used by the ordinary determinant proof:
the sharp exponent and the positive first-coefficient magnitude.  This theorem
assembles the closed forms, but it deliberately does not identify a formal
power-series determinant with these data; that source-facing row-operation
bridge remains the end-to-end formalisation boundary. -/
theorem zudilinSharpHankelOrderAndCoeff_algebraicAssembly (N : ℕ) :
    6 * zudilinSharpHankelQOrder N =
        (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1) ∧
      2 ^ N * (∏ j ∈ Finset.range N, zudilinTransformedRowCoeff j) =
        (N.factorial) ^ 2 * (N + 1).factorial :=
  ⟨six_mul_zudilinSharpHankelQOrder N,
    twoPow_mul_prod_zudilinTransformedRowCoeff N⟩


/-- **Quantitative scalar-cone deficit.**  The positive-`C₀` scalar ray does
not merely have the wrong sign; it misses by a fixed relative margin. -/
theorem three_two_scalar_margin_lt_explicit {C0 C1 : ℝ}
    (hC0 : 0 < C0) (hsource : 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 < -((17 : ℝ) / 41) * C0 * Real.log 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h := logThree_div_logTwo_lt_sixtyFive_fortyOne
  rw [div_lt_iff₀ hlog2] at h
  nlinarith

/-! ## The four-jet rank threshold -/

/-- **Power-certificate compiler.**  Any certified binary upper bound
`3 ^ p < 2 ^ q` improves the four-jet rank threshold from the generic
`4 R + 2 S` to `2 q T + 2 S` at bottom depth `R = p T`. -/
theorem exists_distinct_binary_selectors_same_fourJet_of_power_certificate
    {n p q T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (hpq : 3 ^ p < 2 ^ q) (hT : 0 < T)
    (hrank : 2 * q * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (p * T) S W forms ε = selectedFourJetSum (p * T) S W forms η := by
  apply exists_distinct_binary_selectors_same_fourJet forms
  rw [fourJetSignature_card]
  have hpow : ((3 : ℕ) ^ p) ^ (2 * T) < ((2 : ℕ) ^ q) ^ (2 * T) :=
    Nat.pow_lt_pow_left hpq (by omega)
  have hleft : (3 ^ (p * T)) ^ 2 = ((3 : ℕ) ^ p) ^ (2 * T) := by
    rw [← pow_mul, ← pow_mul]; ring_nf
  have hright : ((2 : ℕ) ^ q) ^ (2 * T) * (2 ^ S) ^ 2 = 2 ^ (2 * q * T + 2 * S) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  calc (3 ^ (p * T)) ^ 2 * (2 ^ S) ^ 2
      = ((3 : ℕ) ^ p) ^ (2 * T) * (2 ^ S) ^ 2 := by rw [hleft]
    _ < ((2 : ℕ) ^ q) ^ (2 * T) * (2 ^ S) ^ 2 :=
        Nat.mul_lt_mul_of_lt_of_le hpow (le_refl _) (by positivity)
    _ = 2 ^ (2 * q * T + 2 * S) := hright
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hrank

/-- **The `R = 41` instance.**  The threshold drops from `164 T + 2 S` to
`130 T + 2 S`. -/
theorem exists_distinct_binary_selectors_same_fourJet_of_rank_41
    {n T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ) (hT : 0 < T)
    (hrank : 130 * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (41 * T) S W forms ε = selectedFourJetSum (41 * T) S W forms η := by
  apply exists_distinct_binary_selectors_same_fourJet_of_power_certificate
    (p := 41) (q := 65) (T := T) forms threePow_fortyOne_lt_twoPow_sixtyFive hT
  omega

/-- **`130` is exactly optimal.**  With only `129 + 2 S` binary forms the
four-jet target is still strictly larger than the selector space, so the
counting argument genuinely cannot fire one row earlier. -/
theorem fourJet_card_gt_two_pow_of_rank_41 (S : ℕ) :
    2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) := by
  rw [fourJetSignature_card]
  have hlow : (2 : ℕ) ^ 129 < (3 ^ 41) ^ 2 := by norm_num
  calc (2 : ℕ) ^ (129 + 2 * S) = 2 ^ 129 * (2 ^ S) ^ 2 := by
        rw [pow_add, ← pow_mul]; ring_nf
    _ < (3 ^ 41) ^ 2 * (2 ^ S) ^ 2 := by
        exact Nat.mul_lt_mul_of_lt_of_le hlow (le_refl _) (by positivity)

/-! ## Bounded-fibre escape -/

/-- **Bounded-fibre escape.**  If every fibre of `g` has at most `k` points
and the domain is larger than `card β * k`, then some `f`-collision is
separated by `g`.

Applied with `f` the four-jet signature and `g` the selected analytic
remainder, this converts a bound `k` on remainder multiplicity into a jet
collision outside the remainder nullspace: each extra binary form beyond the
exact entropy threshold doubles the tolerated degeneracy. -/
theorem exists_ne_map_eq_map_ne_of_card_mul_lt {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ) (k : ℕ)
    (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k)
    (hcard : Fintype.card β * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧ g x ≠ g y := by
  by_contra hbad
  push_neg at hbad
  have hfactor : ∀ x y : α, f x = f y → g x = g y := by
    intro x y hxy
    by_cases hne : x = y
    · rw [hne]
    · exact hbad x y hne hxy
  have hfiber : ∀ b : β, (Finset.univ.filter fun x => f x = b).card ≤ k := by
    intro b
    by_cases hemp : (Finset.univ.filter fun x => f x = b).Nonempty
    · obtain ⟨x0, hx0⟩ := hemp
      have hsub : (Finset.univ.filter fun x => f x = b)
          ⊆ (Finset.univ.filter fun y => g y = g x0) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx0 ⊢
        exact hfactor x x0 (hx.trans hx0.symm)
      exact le_trans (Finset.card_le_card hsub) (hg x0)
    · rw [Finset.not_nonempty_iff_eq_empty] at hemp
      simp [hemp]
  have hcount : Fintype.card α ≤ Fintype.card β * k := by
    have hpart := Finset.card_eq_sum_card_fiberwise
      (f := f) (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
      (fun x _ => Finset.mem_univ (f x))
    rw [← Finset.card_univ, ← Finset.card_univ, hpart]
    calc ∑ b ∈ (Finset.univ : Finset β), (Finset.univ.filter fun x => f x = b).card
        ≤ ∑ _b ∈ (Finset.univ : Finset β), k := Finset.sum_le_sum fun b _ => hfiber b
      _ = (Finset.univ : Finset β).card * k := by
          rw [Finset.sum_const, smul_eq_mul]
  omega

end ErdosProblems.Erdos1049
