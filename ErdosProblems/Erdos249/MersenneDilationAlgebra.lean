import Mathlib

/-!
# Coefficient-level Mersenne dilation identities

Lean-checked coefficient identities (r5; `cf_8309991b61ac4c53b3e3` exit 0).
These are exact algebraic identities, NOT a Lean proof of Pólya--Carlson,
a natural-boundary theorem, or irrationality of a value.
The actual series in the ordinary proof start at n=1, with b>=2,
so x=b^n satisfies the nonvanishing hypothesis. At n=0 the denominator
vanishes when r>0.
-/

namespace ErdosProblems.Erdos249.MersenneDilationAlgebra

variable {K : Type*} [Field K]

/-- One denominator-lowering operation. -/
theorem lower_power (a x : K) (r : ℕ) (hx : x ≠ 1) :
    x * (a / (x - 1) ^ (r + 1)) - a / (x - 1) ^ (r + 1) =
      a / (x - 1) ^ r := by
  have h : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  simp only [pow_succ]
  field_simp [h] <;> ring

/-- The r-fold operator `(sigma_b - 1)^r` multiplies coefficient n
by `(b^n - 1)^r`, cancelling the chosen denominator. -/
theorem iterated_multiplier (a x : K) (r : ℕ) (hx : x ≠ 1) :
    (x - 1) ^ r * (a / (x - 1) ^ r) = a := by
  have h : (x - 1) ^ r ≠ 0 := pow_ne_zero r (sub_ne_zero.mpr hx)
  field_simp [h] <;> ring

/-- Explicit square-ladder identity for the actual target family. -/
theorem square_ladder (a x : K) (hx : x ≠ 1) :
    x ^ 2 * (a / (x - 1) ^ 2) -
      2 * x * (a / (x - 1) ^ 2) + a / (x - 1) ^ 2 = a := by
  have h : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  field_simp [h] <;> ring

end ErdosProblems.Erdos249.MersenneDilationAlgebra
