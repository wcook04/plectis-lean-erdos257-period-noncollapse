import ErdosProblems.Erdos251.PrimeGapDyadicTail
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Erdős #251: the polynomial-gap countermodel series has the rational value `32`

`PrimeGapDyadicTail` records the exact infinite countermodel
`g_n = 2(n^2 + 4n + 2)`, `T_n = 2(n+4)^2` to coarse prime-gap arguments, and
`PolynomialGapTailCountermodel.md` states that the positive even gap series
`Σ_{j ≥ 1} g_j / 2^j` has the rational value `T_0 = 32`.  Until now that value
was a Python receipt (`scripts/erdos251_polynomial_gap_countermodel.py`).

This module proves it in Lean.  The finite telescope
`Σ_{j ≤ N} g_j / 2^j = 32 - T_N / 2^N` is exact rational algebra from the
recurrence; the terminal term `2(N+4)^2 / 2^N` tends to zero by polynomial
against exponential growth; the terms are nonnegative, so the partial-sum
limit is the `HasSum`.  No ratio bound is needed.

The countermodel is not the actual prime-gap word and nothing here bears on
Erdős #251 itself.
-/

open Filter Topology

namespace ErdosProblems.Erdos251

/-- The real dyadic term of the polynomial countermodel series, indexed so
that `n = 0` carries the gap `g_1 / 2`.  The zero-index gap `g_0` is the initial
carry and is not part of the series. -/
noncomputable def polynomialGapDyadicTerm (n : ℕ) : ℝ :=
  (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)

@[simp] theorem polynomialTailOrbit_zero : polynomialTailOrbit 0 = 32 := by
  simp [polynomialTailOrbit]

/-- Exact finite telescope for the countermodel: the partial sum of the gap
series is `32` minus the scaled terminal state. -/
theorem polynomialGap_partialSum_eq (N : ℕ) :
    ∑ j ∈ Finset.range N, (polynomialGapWord (j + 1) : ℚ) / 2 ^ (j + 1) =
      32 - polynomialTailOrbit N / 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, polynomialTailOrbit_recurrence N]
      simp only [pow_succ]
      field_simp
      ring

/-- Real cast of the finite telescope. -/
theorem polynomialGapDyadicTerm_partialSum_eq (N : ℕ) :
    ∑ j ∈ Finset.range N, polynomialGapDyadicTerm j =
      32 - ((polynomialTailOrbit N : ℚ) : ℝ) / 2 ^ N := by
  have h := congrArg ((↑) : ℚ → ℝ) (polynomialGap_partialSum_eq N)
  push_cast at h
  simpa [polynomialGapDyadicTerm] using h

/-- The scaled terminal state `2(N+4)^2 / 2^N` tends to zero. -/
theorem tendsto_polynomialTailOrbit_div_two_pow :
    Tendsto (fun N : ℕ => ((polynomialTailOrbit N : ℚ) : ℝ) / 2 ^ N) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have hshift : Tendsto (fun n : ℕ => ((n + 4 : ℕ) : ℝ) ^ 2 / 2 ^ (n + 4)) atTop (𝓝 0) :=
    h2.comp (tendsto_add_atTop_nat 4)
  have hmul := hshift.const_mul 32
  rw [mul_zero] at hmul
  refine hmul.congr fun n => ?_
  simp only [polynomialTailOrbit]
  push_cast
  field_simp
  ring

theorem polynomialGapDyadicTerm_nonneg (n : ℕ) : 0 ≤ polynomialGapDyadicTerm n := by
  unfold polynomialGapDyadicTerm
  have hpos := polynomialGapWord_pos (n + 1)
  have hR : (0 : ℝ) ≤ (polynomialGapWord (n + 1) : ℝ) := by exact_mod_cast hpos.le
  positivity

/-- **The countermodel series sums to `32`.** -/
theorem hasSum_polynomialGapDyadicTerm : HasSum polynomialGapDyadicTerm 32 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg polynomialGapDyadicTerm_nonneg]
  have hlim :=
    (tendsto_const_nhds (x := (32 : ℝ))).sub tendsto_polynomialTailOrbit_div_two_pow
  rw [sub_zero] at hlim
  refine hlim.congr fun N => ?_
  rw [polynomialGapDyadicTerm_partialSum_eq]

theorem summable_polynomialGapDyadicTerm : Summable polynomialGapDyadicTerm :=
  hasSum_polynomialGapDyadicTerm.summable

/-- **`Σ_{j ≥ 1} g_j / 2^j = 32` as a `tsum`.**  This replaces the Python
receipt for the countermodel series value. -/
theorem tsum_polynomialGapDyadicTerm_eq : ∑' n : ℕ, polynomialGapDyadicTerm n = 32 :=
  hasSum_polynomialGapDyadicTerm.tsum_eq

/-- The same identity with the term written out. -/
theorem tsum_polynomialGapWord_div_two_pow :
    ∑' n : ℕ, (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1) = 32 :=
  tsum_polynomialGapDyadicTerm_eq

/-- The series value is the initial tail state of the countermodel orbit. -/
theorem tsum_polynomialGapDyadicTerm_eq_orbit_zero :
    ∑' n : ℕ, polynomialGapDyadicTerm n = ((polynomialTailOrbit 0 : ℚ) : ℝ) := by
  rw [tsum_polynomialGapDyadicTerm_eq, polynomialTailOrbit_zero]
  norm_num

/-- The positive, even, strictly increasing, unbounded, nonperiodic gap word
therefore produces a rational dyadic series.  This is the infinite
countermodel in its final analytic form. -/
theorem not_irrational_tsum_polynomialGapDyadicTerm :
    ¬ Irrational (∑' n : ℕ, polynomialGapDyadicTerm n) := by
  rw [tsum_polynomialGapDyadicTerm_eq]
  exact_mod_cast (32 : ℚ).not_irrational

#print axioms tsum_polynomialGapDyadicTerm_eq
#print axioms not_irrational_tsum_polynomialGapDyadicTerm

end ErdosProblems.Erdos251
