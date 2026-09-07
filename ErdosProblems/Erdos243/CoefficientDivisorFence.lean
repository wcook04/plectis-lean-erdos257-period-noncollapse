import Mathlib.Tactic

/-!
# Coefficient-independent divisor fences (r5)

Finite transition algebra only.  This module does not claim the global CRT
supply theorem, the analytic positive-numerator transfer, or the Erdős #243
endpoint.  The covering hypothesis is explicit: producing such a cover is a
separate CRT argument, and producing the required old divisors is a separate
record argument.

Not imported into `ErdosProblems/Root.lean`.  Erdős #243 remains open.
-/

namespace ErdosProblems.Erdos243.CoefficientDivisorFence

/-- A persistent divisor of the state and clearing denominator divides the
jump, independently of the integral forcing coefficient. -/
theorem divides_jump (a b L u v m : ℤ)
    (hstep : v = a * u - b * L)
    (hu : m ∣ u) (hL : m ∣ L) : m ∣ v - u := by
  have hrewrite : v - u = (a - 1) * u - b * L := by
    rw [hstep]
    ring
  rw [hrewrite]
  exact dvd_sub (dvd_mul_of_dvd_right hu (a - 1)) (dvd_mul_of_dvd_right hL b)

/-- An exact transition cannot cross a covered interval whose persistent
moduli all exceed the positive jump budget.  All variables are integers;
`rho ≥ 1` is enough for this finite implication. -/
theorem no_jump_through_fence (a b L u v rho B z : ℤ)
    (hv : 0 < v) (hrho : 1 ≤ rho) (_hB : 0 ≤ B)
    (hcap : rho * v ≤ u + B)
    (hstep : rho * v = a * u - b * L)
    (hz : B < z) (hbefore : u < z + B)
    (hcover : ∀ x : ℤ, z ≤ x → x < z + B →
      ∃ m : ℤ, B < m ∧ m ∣ x ∧ m ∣ L) :
    v < z + B := by
  by_contra hnot
  have hafter : z + B ≤ v := by omega
  have hrhoone : rho = 1 := by
    by_contra hne
    have htwo : (2 : ℤ) ≤ rho := by omega
    have htwov : 2 * v ≤ rho * v := by nlinarith
    have hdrop : 2 * v ≤ u + B := by linarith
    have hzule : z ≤ u := by
      have : v ≤ rho * v := by nlinarith
      omega
    nlinarith
  have hstep' : v = a * u - b * L := by simpa [hrhoone] using hstep
  have hcap' : v ≤ u + B := by simpa [hrhoone] using hcap
  have hzu : z ≤ u := by omega
  obtain ⟨m, hm, hmu, hmL⟩ := hcover u hzu hbefore
  have hd : 0 < v - u := by omega
  have hdiv : m ∣ v - u := divides_jump a b L u v m hstep' hmu hmL
  have hle : m ≤ v - u := Int.le_of_dvd hd hdiv
  omega

/-- Iterate the finite fence.  This theorem does not construct its cover. -/
theorem stays_below_fence
    (a b L U rho : ℕ → ℤ) (B z : ℤ)
    (hU : ∀ n, 0 < U n)
    (hrho : ∀ n, 1 ≤ rho n)
    (hB : 0 ≤ B) (hz : B < z)
    (hcap : ∀ n, rho n * U (n + 1) ≤ U n + B)
    (hstep : ∀ n, rho n * U (n + 1) = a n * U n - b n * L n)
    (hstart : U 0 < z + B)
    (hcover : ∀ n, ∀ x : ℤ, z ≤ x → x < z + B →
      ∃ m : ℤ, B < m ∧ m ∣ x ∧ m ∣ L n) :
    ∀ n, U n < z + B := by
  intro n
  induction n with
  | zero => exact hstart
  | succ n ih =>
      exact no_jump_through_fence (a n) (b n) (L n) (U n) (U (n + 1))
        (rho n) B z (hU (n + 1)) (hrho n) hB (hcap n) (hstep n)
        hz ih (hcover n)

/-- The weighted centred error is the raw numerator decrement. -/
theorem centred_error_eq_decrement (a b C D Cnext : ℤ)
    (hC : Cnext = a * C - b * D) :
    b * D - (a - 1) * C = C - Cnext := by
  rw [hC]
  ring

/-- Two zero-error states give the weighted Sylvester equality, without
assuming that the numerator coefficient is invertible. -/
theorem weighted_recurrence_of_two_zero
    (a anext b bnext C D Dnext : ℤ)
    (hC : C ≠ 0)
    (hD : Dnext = a * D)
    (hzero : b * D = (a - 1) * C)
    (hzeronext : bnext * Dnext = (anext - 1) * C) :
    b * (anext - 1) = bnext * a * (a - 1) := by
  have hmul : (b * (anext - 1) - bnext * a * (a - 1)) * C = 0 := by
    calc
      (b * (anext - 1) - bnext * a * (a - 1)) * C =
          b * ((anext - 1) * C) - bnext * a * ((a - 1) * C) := by ring
      _ = b * (bnext * Dnext) - bnext * a * (b * D) := by
            rw [← hzeronext, ← hzero]
      _ = 0 := by
            rw [hD]
            ring
  rcases mul_eq_zero.mp hmul with hleft | hright
  · exact sub_eq_zero.mp hleft
  · exact (hC hright).elim

/-- The two-step coefficient-(1,3) example, parameterised polynomially. -/
theorem two_cycle_first_step (k : ℤ) :
    (2 * k + 3) * 1 - (2 * k + 1) = 2 := by ring

theorem two_cycle_second_step (k : ℤ) :
    2 * (6 * k ^ 2 + 12 * k + 5) - 3 * ((2 * k + 1) * (2 * k + 3)) = 1 := by
  ring

end ErdosProblems.Erdos243.CoefficientDivisorFence
