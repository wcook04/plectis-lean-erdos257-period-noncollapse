import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #68: factorial digits and strict successors

Problem-owned landing surface for exact reductions around
`∑ n ≥ 2, 1 / (n! - 1)`.  No declaration in this module asserts the still-open
irrationality theorem.
-/

namespace ErdosProblems.Erdos68

/-- The least integer strictly greater than a rational number.  Unlike the
ordinary ceiling, this advances by one even at an integral input. -/
def strictSuccessor (x : ℚ) : ℤ :=
  ⌊x⌋ + 1

/-- Integer translation does not change the fractional geometry of the
strict-successor construction.  This is the exact cancellation that removes
the divisor-factorial prefix from the prime-block packets. -/
theorem strictSuccessor_sub_int (x : ℚ) (z : ℤ) :
    strictSuccessor (x - z) = strictSuccessor x - z := by
  simp [strictSuccessor]
  ring

/-- Canonical factorial digit at radix step `n + 1`, using the terminating
floor convention. -/
def canonicalFactorialDigit (x : ℚ) (n : ℕ) : ℤ :=
  ⌊((n + 1).factorial : ℚ) * x⌋ -
    (n + 1 : ℤ) * ⌊(n.factorial : ℚ) * x⌋

/-- Once an explicit rational denominator divides `n!`, the scaled rational
is literally an integer. -/
theorem factorial_scaled_rational_eq_intCast
    (a : ℤ) {q n : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    ((n.factorial : ℚ) * ((a : ℚ) / (q : ℚ))) =
      (((n.factorial / q : ℕ) : ℤ) * a : ℤ) := by
  have hqfac : q ∣ n.factorial := Nat.dvd_factorial hq hqn
  have hq0 : (q : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hcastDiv : (((n.factorial / q : ℕ) : ℚ)) =
      (n.factorial : ℚ) / (q : ℚ) :=
    Nat.cast_div hqfac hq0
  calc
    ((n.factorial : ℚ) * ((a : ℚ) / (q : ℚ))) =
        (a : ℚ) * ((n.factorial : ℚ) / (q : ℚ)) := by
      field_simp [hq0]
    _ = (a : ℚ) * ((n.factorial / q : ℕ) : ℚ) := by
      rw [hcastDiv]
    _ = ((((n.factorial / q : ℕ) : ℤ) * a : ℤ) : ℚ) := by
      have h := congrArg (fun z : ℤ => (z : ℚ))
        (mul_comm a ((n.factorial / q : ℕ) : ℤ))
      simpa only [Int.cast_mul, Int.cast_natCast] using h

/-- Every rational number has eventually zero canonical factorial digits.
The explicit threshold is its displayed denominator. -/
theorem canonicalFactorialDigit_eq_zero_of_rational
    (a : ℤ) {q n : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    canonicalFactorialDigit ((a : ℚ) / (q : ℚ)) n = 0 := by
  have hn := factorial_scaled_rational_eq_intCast a hq hqn
  have hsucc :
      (((n + 1).factorial : ℚ) * ((a : ℚ) / (q : ℚ))) =
        ((n + 1 : ℤ) * (((n.factorial / q : ℕ) : ℤ) * a) : ℤ) := by
    calc
      (((n + 1).factorial : ℕ) : ℚ) * ((a : ℚ) / (q : ℚ)) =
          (n + 1 : ℚ) *
            ((n.factorial : ℚ) * ((a : ℚ) / (q : ℚ))) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      _ = (n + 1 : ℚ) *
            ((((n.factorial / q : ℕ) : ℤ) * a : ℤ) : ℚ) := by rw [hn]
      _ = (((n + 1 : ℤ) *
            (((n.factorial / q : ℕ) : ℤ) * a) : ℤ) : ℚ) := by
        push_cast
        ring
  have hnFloor := congrArg (fun x : ℚ => ⌊x⌋) hn
  have hsuccFloor := congrArg (fun x : ℚ => ⌊x⌋) hsucc
  simp only [Int.floor_intCast] at hnFloor hsuccFloor
  unfold canonicalFactorialDigit
  rw [hnFloor, hsuccFloor]
  ring

/-- A prime contributes at least `k` copies to `(k p)!`.  This is the exact
valuation input behind the fixed-dilation prime-power criterion. -/
theorem prime_pow_dvd_factorial_dilation
    {p k : ℕ} (hp : p.Prime) :
    p ^ k ∣ (k * p).factorial := by
  rw [Nat.mul_comm]
  apply pow_dvd_iff_le_emultiplicity.mpr
  rw [hp.emultiplicity_factorial_mul]
  simp

/-- If a denominator is coprime to `p`, clearing it from `(k p)!` preserves
all `k` forced copies of `p`. -/
theorem prime_pow_dvd_factorial_dilation_div
    {p k q : ℕ} (hp : p.Prime) (hqfac : q ∣ (k * p).factorial)
    (hpq : ¬p ∣ q) :
    p ^ k ∣ (k * p).factorial / q := by
  have hcop : (p ^ k).Coprime q :=
    (hp.coprime_iff_not_dvd.mpr hpq).pow_left k
  have hmul : q * ((k * p).factorial / q) = (k * p).factorial :=
    Nat.mul_div_cancel' hqfac
  apply hcop.dvd_of_dvd_mul_left
  rw [hmul]
  exact prime_pow_dvd_factorial_dilation hp

/-- Multiplying by a numerator preserves the fixed-dilation prime power. -/
theorem prime_pow_dvd_cleared_rational_numerator
    {p k q a : ℕ} (hp : p.Prime) (hqfac : q ∣ (k * p).factorial)
    (hpq : ¬p ∣ q) :
    p ^ k ∣ ((k * p).factorial / q) * a :=
  dvd_mul_of_dvd_left
    (prime_pow_dvd_factorial_dilation_div hp hqfac hpq) a

end ErdosProblems.Erdos68
