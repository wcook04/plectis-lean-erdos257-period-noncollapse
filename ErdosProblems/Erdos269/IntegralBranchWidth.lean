import ErdosProblems.Erdos269.IntegralBranchExtinction

/-!
# Erdős #269: the depth-`K` pinning telescope

This module proves the exact depth-`K` pinning telescope identity for the
normalized tail state, by induction on `K`:

`X_m = (sum_{i<K} d_(m+i) / prod_{j<=i} b_(m+j)) + (H_m / 2) * T_(m+K)`,

because `prod_{j<K} b_(m+j) = H_(m+K) / H_m` and
`X_(m+K) = (H_(m+K) / 2) * T_(m+K)`.

The single theorem here is `trueNormalizedState_eq_telescope`. It contains
no width bound on `X_m`.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- The exact depth-`K` pinning telescope: digit sum plus a remainder
equal to `(H_m / 2) * T_(m+K)`. -/
theorem trueNormalizedState_eq_telescope (m K : ℕ) :
    trueNormalizedState m =
      (∑ i ∈ Finset.range K,
          (dyadicOrderedBlockDigit235 (m + i) : ℝ) /
            ∏ j ∈ Finset.range (i + 1), (dyadicBlockBase235 (m + j) : ℝ)) +
        (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 *
          dyadicShellTsumTailR235 (m + K) := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    unfold trueNormalizedState dyadicNormalizedTailStateR235
    simp
  | succ K ih =>
    -- the radix word telescopes the three-smooth height: one factor per shell
    have hHprod : ∀ n : ℕ, (threePrimeHeight 2 3 5 (2 ^ (m + n)) : ℝ)
        = (threePrimeHeight 2 3 5 (2 ^ m) : ℝ)
          * ∏ j ∈ Finset.range n, (dyadicBlockBase235 (m + j) : ℝ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        have hstep : (threePrimeHeight 2 3 5 (2 ^ (m + (n + 1))) : ℝ)
            = (dyadicBlockBase235 (m + n) : ℝ)
              * (threePrimeHeight 2 3 5 (2 ^ (m + n)) : ℝ) :=
          mod_cast threePrimeHeight_dyadicBlock_succ (m + n)
        rw [Finset.prod_range_succ, hstep, ihn]
        ring
    have hbpos : (0 : ℝ) < ∏ j ∈ Finset.range (K + 1),
        (dyadicBlockBase235 (m + j) : ℝ) :=
      Finset.prod_pos fun j _ => by exact_mod_cast dyadicBlockBase235_pos (m + j)
    have hbne : (∏ j ∈ Finset.range (K + 1),
        (dyadicBlockBase235 (m + j) : ℝ)) ≠ 0 := ne_of_gt hbpos
    have hdigit : (threePrimeHeight 2 3 5 (2 ^ (m + K + 1)) : ℝ) / 2
        * dyadicShellMassR235 (m + K)
        = (dyadicOrderedBlockDigit235 (m + K) : ℝ) :=
      half_threePrimeHeight_mul_dyadicShellMassR235 (m + K)
    have hH : (threePrimeHeight 2 3 5 (2 ^ (m + K + 1)) : ℝ)
        = (threePrimeHeight 2 3 5 (2 ^ m) : ℝ)
          * ∏ j ∈ Finset.range (K + 1), (dyadicBlockBase235 (m + j) : ℝ) :=
      hHprod (K + 1)
    -- the new shell's mass is exactly the next digit over the radix product
    have hkey : (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2
          * dyadicShellMassR235 (m + K)
        = (dyadicOrderedBlockDigit235 (m + K) : ℝ)
          / ∏ j ∈ Finset.range (K + 1), (dyadicBlockBase235 (m + j) : ℝ) := by
      rw [eq_div_iff hbne, ← hdigit, hH]
      ring
    have hT : dyadicShellTsumTailR235 (m + K)
        = dyadicShellMassR235 (m + K)
          + dyadicShellTsumTailR235 (m + (K + 1)) :=
      dyadicShellTsumTailR235_eq_shell_add (m + K)
    rw [Finset.sum_range_succ, ih]
    linear_combination
      (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * hT + hkey

end ErdosProblems.Erdos269
