import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernel for the torus/psh FP-to-(S) bridge

The analytic companion `FreePointTorusPshReduction.md` proves that `FP_m`
implies the separatrix aggregate inequality in degree `m+1`.  Once the
plurisubharmonic boundary reduction and the torus product identity have
changed the critical-value terms to nonnegative numbers `yᵢ` with
`∑ i, yᵢ ≤ m`, the remaining load-bearing step is the tangent inequality

`y^(m/(m+1)) ≤ (m/(m+1)) y + 1/(m+1)`.

This module checks that scalar step and its finite-sum fan-in for an
arbitrary exponent in `[0,1]`.
-/

namespace ErdosProblems.Erdos1041.FreePointTorusPshReduction

/-- The tangent at one dominates `y ↦ y^q` for `y ≥ 0` and `0 ≤ q ≤ 1`. -/
theorem rpow_le_tangent_at_one {y q : ℝ} (hy : 0 ≤ y)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    y ^ q ≤ q * y + (1 - q) := by
  have hs : -1 ≤ y - 1 := by linarith
  have h : (1 + (y - 1)) ^ q ≤ 1 + q * (y - 1) :=
    rpow_one_add_le_one_add_mul_self hs hq0 hq1
  have hbase : 1 + (y - 1) = y := by ring
  rw [hbase] at h
  calc
    y ^ q ≤ 1 + q * (y - 1) := h
    _ = q * y + (1 - q) := by ring

/-- Finite-sum form of the tangent estimate: if nonnegative entries have
sum at most the cardinality, then so do their `q`-powers. -/
theorem sum_rpow_le_card_of_sum_le_card {ι : Type*} [Fintype ι]
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (y : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i)
    (hsum : ∑ i, y i ≤ (Fintype.card ι : ℝ)) :
    ∑ i, y i ^ q ≤ (Fintype.card ι : ℝ) := by
  calc
    ∑ i, y i ^ q ≤ ∑ i, (q * y i + (1 - q)) := by
      exact Finset.sum_le_sum fun i _ => rpow_le_tangent_at_one (hy i) hq0 hq1
    _ = q * (∑ i, y i) + (Fintype.card ι : ℝ) * (1 - q) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    _ ≤ q * (Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) * (1 - q) := by
      gcongr
    _ = (Fintype.card ι : ℝ) := by ring

/-- The exact exponent used by the bridge lies in the concavity range. -/
theorem fp_exponent_mem_unit_interval (m : ℕ) :
    0 ≤ (m : ℝ) / (m + 1) ∧ (m : ℝ) / (m + 1) ≤ 1 := by
  constructor
  · positivity
  · have hden : (0 : ℝ) < m + 1 := by positivity
    apply (div_le_one hden).2
    linarith

/-- Direct specialization to the `m` critical points of a degree `m+1`
polynomial. -/
theorem fp_exponent_bridge (m : ℕ) (y : Fin m → ℝ)
    (hy : ∀ i, 0 ≤ y i)
    (hsum : ∑ i, y i ≤ (m : ℝ)) :
    ∑ i, y i ^ ((m : ℝ) / (m + 1)) ≤ (m : ℝ) := by
  have hq := fp_exponent_mem_unit_interval m
  simpa using
    (sum_rpow_le_card_of_sum_le_card hq.1 hq.2 y hy (by simpa using hsum))

end ErdosProblems.Erdos1041.FreePointTorusPshReduction
