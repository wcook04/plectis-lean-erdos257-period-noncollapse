import ErdosProblems.Erdos269.IntegralBranchExtinction
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Erdős #269: an explicit all-scale width for the normalized tail state

The genuine half-height normalized tail state
`X_a = trueNormalizedState a = (H(2^a)/2) · Σ_{h ≥ 2^a} 1/H(h)`
is the state whose integrality the `B = 1` corner asks about, and whose
`q`-multiples the rationality lattice makes integral.  Every consumer of the
integral branch (`IntegralRigidity`, the local-window residue consumer of
`RestrictedFloorSum`) needs an explicit all-scale enclosure `0 < X_a ≤ W(a)`.
Positivity is `trueNormalizedState_pos`; this module supplies the width.

The bound is the poly-geometric tsum estimate.  Writing the tail from scale
`m` shell by shell,

`X_m = Σ_{n ≥ 0} d_(m+n) / (b_m ⋯ b_(m+n))`

with the ordered digit `d_a = dyadicOrderedBlockDigit235 a ≤ 15 (a+1)^2` and
every radix `b ≥ 2`, so

`X_m ≤ Σ_{n ≥ 0} 15 (m+n+1)^2 / 2^(n+1) ≤ 15 (m+1)^2 Σ_{n ≥ 0} (n+1)^2 / 2^(n+1)
     = 90 (m+1)^2`,

using `(m+n+1) ≤ (m+1)(n+1)` and the exact value
`Σ_{n ≥ 0} (n+1)^2 r^n = 2/(1-r)^3 - 1/(1-r)^2`, which at `r = 1/2` is `12`.

The main theorem is `trueNormalizedState_le_quadratic`; the cubic corollary
`trueNormalizedState_le_cubic` is the form recorded in the longitudinal record.
The measured constant is `sup_a X_a/(a+1)^2 ≈ 0.91` (attained at `a = 0`), so
the bound is crude by about two orders of magnitude and can be sharpened with a
sharper digit majorant; nothing downstream needs more than an explicit
polynomial.

No rationality hypothesis is used.  Erdős #269 remains open.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- The dyadic endpoint heights telescope along the radix word. -/
theorem threePrimeHeight235_pow_add_eq_mul_prod (m n : ℕ) :
    (threePrimeHeight 2 3 5 (2 ^ (m + n)) : ℝ)
      = (threePrimeHeight 2 3 5 (2 ^ m) : ℝ)
        * ∏ j ∈ Finset.range n, (dyadicBlockBase235 (m + j) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (threePrimeHeight 2 3 5 (2 ^ (m + (n + 1))) : ℝ)
        = (dyadicBlockBase235 (m + n) : ℝ)
          * (threePrimeHeight 2 3 5 (2 ^ (m + n)) : ℝ) :=
      mod_cast threePrimeHeight_dyadicBlock_succ (m + n)
    rw [Finset.prod_range_succ, hstep, ih]
    ring

/-- Every radix product over `n` shells is at least `2^n`. -/
theorem prod_dyadicBlockBase235_ge_two_pow (m n : ℕ) :
    (2 : ℝ) ^ n ≤ ∏ j ∈ Finset.range n, (dyadicBlockBase235 (m + j) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ]
    have hb2 : (2 : ℝ) ≤ (dyadicBlockBase235 (m + n) : ℝ) :=
      mod_cast (dyadicBlockBase235_mem_interval (m + n)).1
    have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
    have hPnonneg : (0 : ℝ) ≤ ∏ j ∈ Finset.range n, (dyadicBlockBase235 (m + j) : ℝ) :=
      le_trans hnonneg ih
    calc (2 : ℝ) ^ n * 2 ≤ (∏ j ∈ Finset.range n, (dyadicBlockBase235 (m + j) : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
      _ ≤ (∏ j ∈ Finset.range n, (dyadicBlockBase235 (m + j) : ℝ))
            * (dyadicBlockBase235 (m + n) : ℝ) :=
          mul_le_mul_of_nonneg_left hb2 hPnonneg

/-- One shell of the tail from scale `m`, normalized by the scale-`m` half
height, is the shell digit over the radix product, hence at most the digit
over `2^(n+1)`. -/
theorem half_height_mul_shellMass_le (m n : ℕ) :
    (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n)
      ≤ (dyadicOrderedBlockDigit235 (m + n) : ℝ) / 2 ^ (n + 1) := by
  have hdigit : (threePrimeHeight 2 3 5 (2 ^ (m + n + 1)) : ℝ) / 2
      * dyadicShellMassR235 (m + n) = (dyadicOrderedBlockDigit235 (m + n) : ℝ) :=
    half_threePrimeHeight_mul_dyadicShellMassR235 (m + n)
  have hH : (threePrimeHeight 2 3 5 (2 ^ (m + (n + 1))) : ℝ)
      = (threePrimeHeight 2 3 5 (2 ^ m) : ℝ)
        * ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (m + j) : ℝ) :=
    threePrimeHeight235_pow_add_eq_mul_prod m (n + 1)
  have hP : (2 : ℝ) ^ (n + 1)
      ≤ ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (m + j) : ℝ) :=
    prod_dyadicBlockBase235_ge_two_pow m (n + 1)
  have hPpos : (0 : ℝ) < ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (m + j) : ℝ) :=
    lt_of_lt_of_le (by positivity) hP
  have hHm : (0 : ℝ) < (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) :=
    threePrimeHeight235_cast_pos _
  have hmass : 0 ≤ dyadicShellMassR235 (m + n) := dyadicShellMassR235_nonneg _
  have hidx : m + n + 1 = m + (n + 1) := Nat.add_assoc m n 1
  rw [hidx] at hdigit
  -- `(H_m/2) · mass = digit / P` with `P ≥ 2^(n+1)`
  have hkey : (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n)
      = (dyadicOrderedBlockDigit235 (m + n) : ℝ)
        / ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (m + j) : ℝ) := by
    rw [eq_div_iff hPpos.ne', ← hdigit, hH]
    ring
  rw [hkey]
  have hd : (0 : ℝ) ≤ (dyadicOrderedBlockDigit235 (m + n) : ℝ) := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_left hd (by positivity) hP

/-- `Σ_{n ≥ 0} (n+1)^2 r^n = 2/(1-r)^3 - 1/(1-r)^2` for `|r| < 1`, via
`(n+1)^2 = 2·C(n+2,2) - C(n+1,1)`. -/
theorem hasSum_succ_sq_mul_geometric {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ 2 * r ^ n)
      (2 * (1 / (1 - r) ^ 3) - 1 / (1 - r) ^ 2) := by
  have hr' : ‖r‖ < 1 := by simpa [Real.norm_eq_abs] using hr
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hr'
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hr'
  have hcomb := (h2.mul_left 2).sub h1
  refine hcomb.congr_fun ?_
  intro n
  have hc2 : ((n + 2).choose 2 : ℝ) * 2 = ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    have h := Nat.succ_mul_choose_eq (n + 1) 1
    rw [Nat.choose_one_right] at h
    have h' : (n + 2) * (n + 1) = (n + 2).choose 2 * 2 := by simpa using h
    exact_mod_cast h'.symm
  have hc1 : ((n + 1).choose 1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    rw [Nat.choose_one_right]
  rw [hc1]
  push_cast at hc2 ⊢
  linear_combination (-(r ^ n)) * hc2

/-- The exact value at `r = 1/2`: `Σ (n+1)^2 / 2^n = 12`. -/
theorem hasSum_succ_sq_div_two_pow :
    HasSum (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n) 12 := by
  have h := hasSum_succ_sq_mul_geometric (r := (1 / 2 : ℝ)) (by norm_num)
  convert h using 1
  norm_num

/-- **Quadratic width.**  The genuine normalized tail state is at most
`90 (m+1)^2` at every scale. -/
theorem trueNormalizedState_le_quadratic (m : ℕ) :
    trueNormalizedState m ≤ 90 * ((m + 1 : ℕ) : ℝ) ^ 2 := by
  -- the state is the tsum of the half-height-normalized shells
  have hsum : Summable (fun n : ℕ => dyadicShellMassR235 (m + n)) :=
    summable_dyadicShellMassR235.comp_injective fun _ _ h => Nat.add_left_cancel h
  have hstate : trueNormalizedState m
      = ∑' n : ℕ, (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n) := by
    unfold trueNormalizedState dyadicNormalizedTailStateR235 dyadicShellTsumTailR235
    rw [tsum_mul_left]
  -- the majorant `15 (m+1)^2 (n+1)^2 / 2^(n+1)` and its exact sum
  have hmaj : HasSum
      (fun n : ℕ => 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n)
        / 2)
      (15 * ((m + 1 : ℕ) : ℝ) ^ 2 * 12 / 2) := by
    have := (hasSum_succ_sq_div_two_pow.mul_left (15 * ((m + 1 : ℕ) : ℝ) ^ 2)).div_const 2
    simpa using this
  have hle : ∀ n : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n)
        ≤ 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n) / 2 := by
    intro n
    refine (half_height_mul_shellMass_le m n).trans ?_
    have hd : (dyadicOrderedBlockDigit235 (m + n) : ℝ) ≤ 15 * ((m + n + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast dyadicOrderedBlockDigit235_le_quadratic (m + n)
    have hsplit : ((m + n + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsq : ((m + n + 1 : ℕ) : ℝ) ^ 2 ≤ (((m + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hsplit 2
    have hR : 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n) / 2
        = 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 / 2 ^ (n + 1) := by
      rw [one_div_pow, pow_succ]
      field_simp
      ring
    rw [hR]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc (dyadicOrderedBlockDigit235 (m + n) : ℝ) ≤ 15 * ((m + n + 1 : ℕ) : ℝ) ^ 2 := hd
      _ ≤ 15 * (((m + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2 := by nlinarith [hsq]
      _ = 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 := by ring
  have hnonneg : ∀ n : ℕ,
      0 ≤ (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n) := by
    intro n
    exact mul_nonneg (by positivity) (dyadicShellMassR235_nonneg _)
  have hsumL : Summable (fun n : ℕ =>
      (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n)) :=
    hsum.mul_left _
  rw [hstate]
  calc (∑' n : ℕ, (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n))
      ≤ ∑' n : ℕ, 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n) / 2 :=
        hsumL.tsum_le_tsum hle hmaj.summable
    _ = 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * 12 / 2 := hmaj.tsum_eq
    _ = 90 * ((m + 1 : ℕ) : ℝ) ^ 2 := by ring

/-- The cubic form recorded in the longitudinal record: `X_m ≤ 40 (m+4)^3`. -/
theorem trueNormalizedState_le_cubic (m : ℕ) :
    trueNormalizedState m ≤ 40 * ((m + 4 : ℕ) : ℝ) ^ 3 := by
  refine (trueNormalizedState_le_quadratic m).trans ?_
  push_cast
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- Integer-cast form for the carry consumers: every `q`-multiple of a true
state is bounded by `q · 90 (m+1)^2`. -/
theorem trueNormalizedState_mul_le (m : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    q * trueNormalizedState m ≤ q * (90 * ((m + 1 : ℕ) : ℝ) ^ 2) :=
  mul_le_mul_of_nonneg_left (trueNormalizedState_le_quadratic m) hq

end ErdosProblems.Erdos269
