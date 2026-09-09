import ErdosProblems.Erdos269.BoundedRadixTailEscape
import ErdosProblems.Erdos269.ThreePrimeRunningLcm

/-!
# Erdős #269: actual dyadic-radix tail escape

This module specializes the generic bounded-radix escape mechanism to the
actual dyadic height ratios arising from the primes `2`, `3`, and `5`.

The specialization deliberately remains separate from the generic theorem.
It does not identify the integer block digit of the Erdős #269 tail or prove
the corresponding affine recurrence; those are the remaining arithmetic
inputs.
-/

namespace ErdosProblems.Erdos269

/-- The actual dyadic height ratios for the primes `2,3,5` satisfy the radix
hypotheses of `boundedRadix_zero_or_cofinal_far`. Thus any integer-digit
affine orbit using those ratios either reaches an integer state or is
cofinally separated from every integer by `1/31`.

The theorem does not identify the block digit of the Erdős #269 tail; that
integer-digit recurrence remains a separate input. -/
theorem dyadicBlockBase235_integer_or_cofinal_far
    (c : ℕ → ℤ) (x : ℕ → ℝ)
    (hrec :
      ∀ a, x (a + 1) =
        (dyadicBlockBase235 a : ℝ) * x a - (c a : ℝ)) :
    (∃ a : ℕ, ∃ z : ℤ, x a = (z : ℝ)) ∨
      ∀ a₀, ∃ a, a₀ ≤ a ∧
        FarFromIntegers (x a) ((1 : ℝ) / 31) := by
  apply boundedRadix_zero_or_cofinal_far dyadicBlockBase235 c x
  · intro a
    exact (dyadicBlockBase235_mem_interval a).1
  · intro a
    exact (dyadicBlockBase235_mem_interval a).2
  · exact hrec

end ErdosProblems.Erdos269
