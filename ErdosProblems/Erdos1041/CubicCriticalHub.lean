import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Erdős #1041 for cubics: the smaller critical value selects a short hub

The accompanying proof note proves the degree-three case of Erdős #1041.  Its
one genuinely analytic input is a Rouché/homotopy lemma for

`P_b(w) = w^3 - (3/2) b w^2 + 1`:

if `‖1 - b^3 / 2‖ ≥ 1`, then `P_b` has at least two zeros in the closed unit
disc.  This module kernel-checks the algebraic and metric consumer of those
two zeros.  In particular, a small normalized zero produces an entire safe
straight spoke, not merely a short endpoint distance.

The root-count lemma itself is currently proved in ordinary complex analysis
in `CubicCriticalHub.md`; it is not asserted as an axiom here.
-/

namespace ErdosProblems.Erdos1041

/-- The normalized cubic obtained by expanding a monic cubic at one critical
point and scaling its critical value to one. -/
noncomputable def normalizedCubic (b z : ℂ) : ℂ :=
  z ^ 3 - ((3 : ℂ) / 2) * b * z ^ 2 + 1

/-- On a spoke from the critical point to a normalized root, the cubic value
has a two-term form whose coefficients have total mass `1 - t^3`. -/
theorem normalizedCubic_spoke_identity {b w : ℂ}
    (hw : normalizedCubic b w = 0) (t : ℝ) :
    normalizedCubic b ((t : ℂ) * w) =
      (1 - (t : ℂ) ^ 2) - (t : ℂ) ^ 2 * (1 - (t : ℂ)) * w ^ 3 := by
  unfold normalizedCubic at hw ⊢
  linear_combination ((t : ℂ) ^ 2) * hw

/-- The elementary real envelope used by the spoke estimate. -/
theorem cubicSpoke_envelope_le_one {t x : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - t ^ 2) + t ^ 2 * (1 - t) * x ^ 3 ≤ 1 := by
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have h1t : 0 ≤ 1 - t := by linarith
  have hx3 : x ^ 3 ≤ 1 := by nlinarith [sq_nonneg x, mul_self_le_mul_self hx0 hx1]
  nlinarith [mul_nonneg ht2 h1t,
    mul_le_mul_of_nonneg_left hx3 (mul_nonneg ht2 h1t)]

/-- A normalized root in the closed unit disc has a straight spoke on which
the normalized cubic never exceeds one in modulus. -/
theorem normalizedCubic_spoke_norm_le_one {b w : ℂ}
    (hw : normalizedCubic b w = 0) (hw_norm : ‖w‖ ≤ 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖normalizedCubic b ((t : ℂ) * w)‖ ≤ 1 := by
  rw [normalizedCubic_spoke_identity hw]
  calc
    ‖(1 - (t : ℂ) ^ 2) - (t : ℂ) ^ 2 * (1 - (t : ℂ)) * w ^ 3‖
        ≤ ‖1 - (t : ℂ) ^ 2‖ +
            ‖(t : ℂ) ^ 2 * (1 - (t : ℂ)) * w ^ 3‖ := norm_sub_le _ _
    _ = (1 - t ^ 2) + t ^ 2 * (1 - t) * ‖w‖ ^ 3 := by
      have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith
      have h1t : 0 ≤ 1 - t := by linarith
      have hfirst : 1 - (t : ℂ) ^ 2 = ((1 - t ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      have hsecond : 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by
        push_cast
        rfl
      have hnormfirst : ‖1 - (t : ℂ) ^ 2‖ = 1 - t ^ 2 := by
        rw [hfirst, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht2]
      have hnormsecond : ‖1 - (t : ℂ)‖ = 1 - t := by
        rw [hsecond, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1t]
      have hnormt : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      rw [norm_mul, norm_mul, norm_pow, norm_pow, hnormfirst, hnormsecond, hnormt]
    _ ≤ 1 := cubicSpoke_envelope_le_one ht0 ht1 (norm_nonneg w) hw_norm

/-- Two normalized roots in the closed unit disc become a hub of total length
strictly below two after rescaling by a factor of norm below one. -/
theorem two_small_normalized_roots_give_short_hub {scale w₁ w₂ : ℂ}
    (hscale : ‖scale‖ < 1) (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1) :
    ‖scale * w₁‖ + ‖scale * w₂‖ < 2 := by
  rw [norm_mul, norm_mul]
  have hs0 : 0 ≤ ‖scale‖ := norm_nonneg _
  have h1 : ‖scale‖ * ‖w₁‖ ≤ ‖scale‖ := by
    nlinarith
  have h2 : ‖scale‖ * ‖w₂‖ ≤ ‖scale‖ := by
    nlinarith
  nlinarith

/-- Kernel-checked fan-in for the cubic proof: the Rouché lemma supplies two
small normalized roots; this theorem supplies both spoke containment and the
strict metric budget after scaling back to the original cubic. -/
theorem normalizedCubic_two_small_roots_fan_in {b scale w₁ w₂ : ℂ}
    (hroot₁ : normalizedCubic b w₁ = 0)
    (hroot₂ : normalizedCubic b w₂ = 0)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hscale : ‖scale‖ < 1) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖normalizedCubic b ((t : ℂ) * w₁)‖ ≤ 1) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖normalizedCubic b ((t : ℂ) * w₂)‖ ≤ 1) ∧
    ‖scale * w₁‖ + ‖scale * w₂‖ < 2 := by
  exact ⟨fun t ht0 ht1 => normalizedCubic_spoke_norm_le_one hroot₁ hw₁ ht0 ht1,
    fun t ht0 ht1 => normalizedCubic_spoke_norm_le_one hroot₂ hw₂ ht0 ht1,
    two_small_normalized_roots_give_short_hub hscale hw₁ hw₂⟩

end ErdosProblems.Erdos1041
