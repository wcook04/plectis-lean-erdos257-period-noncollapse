import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Prime powers surviving rational denominator reduction

For a positive common denominator `L`, reduction replaces it by `L / gcd B L`.
A prime divisor of `L` retains its full exponent exactly when it does not divide
the numerator `B`. This is the rational-denominator step in maximal-hit
cancellation for a factorial-gap prefix.
-/

namespace ErdosProblems.Erdos68

/-- Reduction preserves the full exponent of a prime divisor of the common
denominator precisely when the numerator is nonzero modulo that prime. -/
theorem reducedDenominator_factorization_eq_iff
    {p B L : ℕ} (hp : p.Prime) (hL : 0 < L) (hpL : p ∣ L) :
    (L / B.gcd L).factorization p = L.factorization p ↔ ¬p ∣ B := by
  have hg : 0 < B.gcd L := Nat.gcd_pos_of_pos_right B hL
  have he : 1 ≤ L.factorization p :=
    (hp.dvd_iff_one_le_factorization hL.ne').mp hpL
  have hdiv := congrArg (fun f : ℕ →₀ ℕ => f p)
    (Nat.factorization_div (Nat.gcd_dvd_right B L))
  change (L / B.gcd L).factorization p =
    L.factorization p - (B.gcd L).factorization p at hdiv
  rw [hdiv]
  have hsub : L.factorization p - (B.gcd L).factorization p =
      L.factorization p ↔ (B.gcd L).factorization p = 0 := by omega
  rw [hsub]
  simp [Nat.factorization_eq_zero_iff, hg.ne', hp, Nat.dvd_gcd_iff, hpL]

/-- The denominator of the actual rational quotient is the common denominator
divided by the numerator's gcd with it. -/
theorem natRatio_den_eq (B : ℕ) {L : ℕ} (hL : 0 < L) :
    ((B : ℚ) / L).den = L / B.gcd L := by
  rw [Rat.natCast_div_eq_divInt, Rat.den_divInt]
  simp [hL.ne', Int.gcd, Nat.gcd_comm]

/-- Actual rational denominator form of the prime-power survival criterion. -/
theorem natRatio_den_factorization_eq_iff
    {p B L : ℕ} (hp : p.Prime) (hL : 0 < L) (hpL : p ∣ L) :
    ((B : ℚ) / L).den.factorization p = L.factorization p ↔ ¬p ∣ B := by
  rw [natRatio_den_eq B hL]
  exact reducedDenominator_factorization_eq_iff hp hL hpL

end ErdosProblems.Erdos68
