import ErdosProblems.Erdos269.DyadicBlockThresholdPartition
import ErdosProblems.Erdos269.DyadicRadixTailEscape

/-!
# Erdős #269: the ordered source digit is the actual tail digit

The half-open dyadic shell has already been partitioned at the unique new
`3`- and `5`-power thresholds. This module performs the remaining source-to-
carry normalization. Clearing the literal reciprocal height mass of the shell
by half of the next endpoint height gives exactly the ordered block digit.
Consequently every tail satisfying the literal shell decomposition obeys the
affine recurrence consumed by the bounded-radix escape theorem.

No rationality or irrationality hypothesis is used here. The remaining
producer is arithmetic escape (or an exact integral tail) for this now
source-identified orbit.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- Literal reciprocal running-height mass of one half-open dyadic shell. -/
def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)

/-- Half of the next endpoint height clears the literal shell mass to the
all-scale ordered digit. -/
theorem half_threePrimeHeight_mul_dyadicShellMassQ235 (a : ℕ) :
    ((threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) / 2) *
        dyadicShellMassQ235 a =
      dyadicOrderedBlockDigit235 a := by
  unfold dyadicShellMassQ235
  rw [Finset.mul_sum]
  calc
    ∑ e ∈ dyadicSmoothShell235 a,
        ((threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) / 2) *
          ((threePrimeHeight 2 3 5
            (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹) =
      ∑ e ∈ dyadicSmoothShell235 a, (oddHeightSuffix235 a e : ℚ) := by
        apply Finset.sum_congr rfl
        intro e he
        have hfactor := threePrimeHeight_dyadicShell_factor_two he
        have hfactorQ :
            (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) =
              2 * oddHeightSuffix235 a e *
                threePrimeHeight 2 3 5
                  (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) := by
          exact_mod_cast hfactor
        rw [hfactorQ]
        have hheight :
            (threePrimeHeight 2 3 5
              (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ) ≠ 0 := by
          norm_num [threePrimeHeight]
        field_simp
    _ = (dyadicHalfClearedMass235 a : ℚ) := by
      norm_cast
    _ = dyadicOrderedBlockDigit235 a := by
      exact_mod_cast dyadicHalfClearedMass235_eq_orderedBlockDigit235 a

/-- Normalize a source tail by half of the current dyadic endpoint height. -/
def dyadicNormalizedTailStateQ235 (tail : ℕ → ℚ) (a : ℕ) : ℚ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℚ) / 2) * tail a

/-- Any literal tail decomposition by the dyadic source shell is carried to
the exact radix/digit orbit `X_(a+1)=b_a X_a-d_a`. -/
theorem dyadicNormalizedTailStateQ235_succ
    (tail : ℕ → ℚ)
    (htail : ∀ a, tail a = dyadicShellMassQ235 a + tail (a + 1))
    (a : ℕ) :
    dyadicNormalizedTailStateQ235 tail (a + 1) =
      dyadicBlockBase235 a * dyadicNormalizedTailStateQ235 tail a -
        dyadicOrderedBlockDigit235 a := by
  have hheight := threePrimeHeight_dyadicBlock_succ a
  have hheightQ :
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) =
        dyadicBlockBase235 a * threePrimeHeight 2 3 5 (2 ^ a) := by
    exact_mod_cast hheight
  have hmass := half_threePrimeHeight_mul_dyadicShellMassQ235 a
  unfold dyadicNormalizedTailStateQ235
  rw [hheightQ]
  rw [hheightQ] at hmass
  rw [htail a]
  linarith

/-- Real-valued shell mass used by the actual infinite analytic tail. -/
def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a

/-- The exact cleared-shell identity survives the canonical embedding into
the real numbers. -/
theorem half_threePrimeHeight_mul_dyadicShellMassR235 (a : ℕ) :
    ((threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2) *
        dyadicShellMassR235 a =
      dyadicOrderedBlockDigit235 a := by
  have h := congrArg (fun x : ℚ => (x : ℝ))
    (half_threePrimeHeight_mul_dyadicShellMassQ235 a)
  norm_num [dyadicShellMassR235] at h ⊢
  exact h

/-- Normalize a real source tail by half of the current endpoint height. -/
noncomputable def dyadicNormalizedTailStateR235 (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a

/-- Real-valued source-to-carry bridge.  This is the type needed by an actual
infinite `tsum`; proving that `tsum` has the displayed shell decomposition is
kept as a separate analytic obligation. -/
theorem dyadicNormalizedTailStateR235_succ
    (tail : ℕ → ℝ)
    (htail : ∀ a, tail a = dyadicShellMassR235 a + tail (a + 1))
    (a : ℕ) :
    dyadicNormalizedTailStateR235 tail (a + 1) =
      dyadicBlockBase235 a * dyadicNormalizedTailStateR235 tail a -
        dyadicOrderedBlockDigit235 a := by
  have hheight := threePrimeHeight_dyadicBlock_succ a
  have hheightR :
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) =
        dyadicBlockBase235 a * threePrimeHeight 2 3 5 (2 ^ a) := by
    exact_mod_cast hheight
  have hmass := half_threePrimeHeight_mul_dyadicShellMassR235 a
  unfold dyadicNormalizedTailStateR235
  rw [hheightR]
  rw [hheightR] at hmass
  rw [htail a]
  linarith

end ErdosProblems.Erdos269
