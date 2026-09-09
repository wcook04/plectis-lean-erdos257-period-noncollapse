import ErdosProblems.Erdos1041.TetranomialL2Selector
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The mean square of an actual cyclic fibre

For a primitive `q`th root of unity with `q > 1`, the mixed moment of the
complete orbit vanishes. Thus the mean squared distance of `h + y * ζ^k`
from zero is `‖h‖² + ‖y‖²`. If all these points lie in the open unit disk,
the fibre radius is strictly below one, as is the quotient root `y^q`.

These are the averaging and disk-transport steps used by the translated
quotient families. They do not construct a connecting path or select a safe
quotient spoke. The root-transfer lemma works for an arbitrary function `P`;
in the polynomial application it supplies the required complete orbit of zeros.
-/

namespace ErdosProblems.Erdos1041

/-- The complete regular orbit has exactly the stated total squared norm. -/
theorem cyclicFiber_sum_normSq {q : ℕ} (hq : 1 < q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q) (h y : ℂ) :
    ∑ k ∈ Finset.range q, Complex.normSq (h + y * ζ ^ k) =
      (q : ℝ) * (Complex.normSq h + Complex.normSq y) := by
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (by omega)
  have horbit : ∀ k : ℕ, Complex.normSq (ζ ^ k) = 1 := by
    intro k
    rw [Complex.normSq_eq_norm_sq, norm_pow, hnorm]
    simp
  rw [sum_normSq_const_add_mul_of_sum_eq_zero (Finset.range q)
    (fun k => ζ ^ k) y h (hζ.geom_sum_eq_zero hq)]
  simp only [horbit, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-- Open-disk membership of the full fibre bounds both its centre and radius
by the same strict mean-square budget. -/
theorem cyclicFiber_normSq_add_lt_one {q : ℕ} (hq : 1 < q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q) (h y : ℂ)
    (hdisk : ∀ k < q, ‖h + y * ζ ^ k‖ < 1) :
    Complex.normSq h + Complex.normSq y < 1 := by
  have hpoint : ∀ k ∈ Finset.range q, Complex.normSq (h + y * ζ ^ k) < 1 := by
    intro k hk
    rw [Complex.normSq_eq_norm_sq]
    have hb := hdisk k (Finset.mem_range.mp hk)
    have hn := norm_nonneg (h + y * ζ ^ k)
    nlinarith
  have hsum : ∑ k ∈ Finset.range q, Complex.normSq (h + y * ζ ^ k) <
      ∑ _k ∈ Finset.range q, (1 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact (hpoint k hk).le
    · exact ⟨0, Finset.mem_range.mpr (by omega), hpoint 0 (Finset.mem_range.mpr (by omega))⟩
  rw [cyclicFiber_sum_normSq hq hζ h y] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  nlinarith

/-- The quotient root is strictly inside the unit disk, with no assumption
that the translation centre is zero. -/
theorem cyclicFiber_quotient_norm_lt_one {q : ℕ} (hq : 1 < q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q) (h y : ℂ)
    (hdisk : ∀ k < q, ‖h + y * ζ ^ k‖ < 1) :
    ‖y ^ q‖ < 1 := by
  have hb := cyclicFiber_normSq_add_lt_one hq hζ h y hdisk
  have hh := Complex.normSq_nonneg h
  simp only [Complex.normSq_eq_norm_sq] at hb hh
  have hy : ‖y‖ < 1 := by nlinarith [norm_nonneg y]
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg y) hy (by omega)

/-- Each orbit point really is a zero of the translated composition when
the quotient value is a zero. No root enumeration is assumed here. -/
theorem cyclicFiber_composition_zero {q : ℕ} {ζ : ℂ}
    (hζ : ζ ^ q = 1) (P : ℂ → ℂ) (h y : ℂ) (hroot : P (y ^ q) = 0)
    (k : ℕ) : P ((h + y * ζ ^ k - h) ^ q) = 0 := by
  have hz : (ζ ^ k) ^ q = 1 := by
    rw [← pow_mul, Nat.mul_comm k q, pow_mul, hζ, one_pow]
  simpa only [add_sub_cancel_left, mul_pow, hz, mul_one] using hroot

end ErdosProblems.Erdos1041
