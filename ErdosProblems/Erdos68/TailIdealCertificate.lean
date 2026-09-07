import Mathlib

/-!
# Finite certificates for an infinite tail ideal

GENERIC TRANSPORT, kernel-checked. Focused `lean_fast_build` for
`ErdosProblems.Erdos68.TailIdealCertificate` exited 0
(`cf_3c203a9ba0ad46a1af65`, child `cmdrun_20260907T142428Z_64619`, 70s).
That checks the generic lemmas below. It does not formalise the factorial
envelope, moment ideal, \(D^4\) horizon, or p-adic dichotomy. No `sorry`.

These are generic transport and certificate lemmas. In particular,
`tail_divisor_certificate` ASSUMES the envelope. It does not assert that
`lcm (1,...,n)` divides the factorial-channel coefficient. That arithmetic
specialisation is proved ordinarily in Sections 3--4 of the accompanying
report and remains to be formalised. Nor does this file prove the basis or
minimum-moment formula. Those boundaries must remain explicit on import.
-/

open scoped BigOperators

namespace ErdosProblems.Erdos68.TailIdealCertificate

/-- Divisibility is preserved under a triangular integral recurrence when
    every edge transports the proposed envelope. -/
theorem envelope_of_triangular_recurrence
    (u A source : ℕ → ℤ) (w : ℕ → ℕ → ℤ)
    (hrec : ∀ n, u n = source n + ∑ d ∈ Finset.range n, w n d * u d)
    (hsource : ∀ n, A n ∣ source n)
    (htransport : ∀ n d, d < n → A n ∣ w n d * A d) :
    ∀ n, A n ∣ u n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [hrec n]
    apply dvd_add (hsource n)
    apply Finset.dvd_sum
    intro d hd
    have hdn : d < n := Finset.mem_range.mp hd
    obtain ⟨q, hq⟩ := ih d hdn
    have ht : A n ∣ (w n d * A d) * q :=
      dvd_mul_of_dvd_left (htransport n d hdn) q
    simpa only [hq, mul_assoc] using ht

/-- The finite prefix and one envelope divisibility certify all later terms. -/
theorem tail_divisor_certificate
    (u A : ℕ → ℤ) (g : ℤ) (D N : ℕ)
    (hchain : ∀ i j, i ≤ j → A i ∣ A j)
    (henvelope : ∀ n, D < n → A n ∣ u n)
    (hfinite : ∀ n, D < n → n ≤ N → g ∣ u n)
    (hstop : g ∣ A (N + 1)) :
    ∀ n, D < n → g ∣ u n := by
  intro n hn
  by_cases h : n ≤ N
  · exact hfinite n hn h
  · have hN : N + 1 ≤ n := by omega
    exact dvd_trans (dvd_trans hstop (hchain (N + 1) n hN)) (henvelope n hn)

/-- A finite gcd's universal property extends to the entire infinite tail
    when the stopping certificate applies. No positivity convention is
    needed for this common-divisor equivalence. -/
theorem tail_common_divisors_iff
    (u A : ℕ → ℤ) (g : ℤ) (D N : ℕ)
    (hchain : ∀ i j, i ≤ j → A i ∣ A j)
    (henvelope : ∀ n, D < n → A n ∣ u n)
    (hfinite : ∀ n, D < n → n ≤ N → g ∣ u n)
    (hstop : g ∣ A (N + 1))
    (hgreatest : ∀ b : ℤ,
      (∀ n, D < n → n ≤ N → b ∣ u n) → b ∣ g) :
    ∀ b : ℤ, (∀ n, D < n → b ∣ u n) ↔ b ∣ g := by
  intro b
  constructor
  · intro hb
    apply hgreatest b
    intro n hn _
    exact hb n hn
  · intro hb n hn
    exact dvd_trans hb
      (tail_divisor_certificate u A g D N hchain henvelope hfinite hstop n hn)

/-- Numerical Bézout payload used by the D=4 certificate. This arithmetic
    example does not identify the constants with the recursively defined u. -/
example : (23 : ℤ) * (-180) - (-4200) = 60 := by norm_num

end ErdosProblems.Erdos68.TailIdealCertificate
