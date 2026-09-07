import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Polar-derivative comparison on the unit circle

Finite-root form of the registered circle estimate in
`CentredCircleQuadrinomialConnector.md` Theorem 3.  For a unit `ζ` and a
point `a` strictly inside the disc, `Re(ζ/(ζ-a)) > 1/2`.  Summing over a
finite nonempty family of open-disc roots therefore puts the logarithmic
derivative strictly above half the cardinality, which is the polar
comparison `|n - H| < |H|` on the circle.

This module does not invoke the maximum principle, does not prove
`|σ_f| < 1` on the disc, and does not select a root-to-root path.
Erdős #1041 remains open.
-/

namespace ErdosProblems.Erdos1041

open Complex
open scoped ComplexConjugate

private theorem re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp [Finset.sum_insert hi, ih, Complex.add_re]

/-- The algebraic identity behind the unit-circle real-part estimate. -/
theorem unitCircle_root_realPart_identity {ζ a : ℂ}
    (hζ : Complex.normSq ζ = 1) :
    2 * (1 - (conj ζ * a).re) - Complex.normSq (ζ - a) =
      1 - Complex.normSq a := by
  have hζsq : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
    simpa [Complex.normSq_apply] using hζ
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [hζsq]

/-- For `|ζ| = 1` and `|a| < 1`, the logarithmic kernel has real part
strictly above one half. -/
theorem unitCircle_logDeriv_re_gt_half {ζ a : ℂ}
    (hζ : Complex.normSq ζ = 1) (ha : Complex.normSq a < 1) :
    (1 / 2 : ℝ) < (ζ / (ζ - a)).re := by
  have hne : ζ ≠ a := by
    intro h
    have : (1 : ℝ) < 1 := by
      calc
        (1 : ℝ) = Complex.normSq ζ := hζ.symm
        _ = Complex.normSq a := by rw [h]
        _ < 1 := ha
    exact (lt_irrefl (1 : ℝ)) this
  have hdenpos : 0 < Complex.normSq (ζ - a) := by
    simpa [Complex.normSq_pos, sub_ne_zero] using hne
  have hdiv : (ζ / (ζ - a)).re =
      (1 - (conj ζ * a).re) / Complex.normSq (ζ - a) := by
    have hnum : (ζ * conj (ζ - a)).re = 1 - (conj ζ * a).re := by
      have hmul :
          ζ * conj (ζ - a) = (Complex.normSq ζ : ℂ) - ζ * conj a := by
        simp [map_sub, mul_sub, mul_conj]
      have hconjRe : (ζ * conj a).re = (conj ζ * a).re := by
        have hc : conj (ζ * conj a) = conj ζ * a := by simp
        simpa using (congrArg Complex.re hc.symm).trans (by simp [Complex.conj_re])
      rw [hmul, hζ, Complex.ofReal_one, Complex.sub_re, Complex.one_re, hconjRe]
    have hdiv' : (ζ / (ζ - a)).re =
        (ζ * conj (ζ - a)).re / Complex.normSq (ζ - a) := by
      have : (ζ * conj (ζ - a)).re =
          ζ.re * (ζ - a).re + ζ.im * (ζ - a).im := by
        simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring
      rw [Complex.div_re, this]
      field_simp
    rw [hdiv', hnum]
  have hid := unitCircle_root_realPart_identity (ζ := ζ) (a := a) hζ
  have hpos : 0 < 1 - Complex.normSq a := sub_pos.mpr ha
  have hnumpos :
      0 < 2 * (1 - (conj ζ * a).re) - Complex.normSq (ζ - a) := by
    rwa [hid]
  have hre : (ζ / (ζ - a)).re - 1 / 2 =
      (2 * (1 - (conj ζ * a).re) - Complex.normSq (ζ - a)) /
        (2 * Complex.normSq (ζ - a)) := by
    rw [hdiv]
    field_simp
  have hden2 : 0 < 2 * Complex.normSq (ζ - a) := by positivity
  have : 0 < (ζ / (ζ - a)).re - 1 / 2 := by
    rw [hre]
    exact div_pos hnumpos hden2
  linarith

/-- Summing the kernel over a nonempty finite family of open-disc points. -/
theorem unitCircle_sum_logDeriv_re_gt_half_card
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) {ζ : ℂ}
    (hζ : Complex.normSq ζ = 1)
    (ha : ∀ i ∈ s, Complex.normSq (a i) < 1)
    (hne : s.Nonempty) :
    (s.card : ℝ) / 2 < (∑ i ∈ s, ζ / (ζ - a i)).re := by
  rw [re_sum]
  have hhalf : (s.card : ℝ) / 2 = ∑ _i ∈ s, (1 / 2 : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hhalf]
  refine Finset.sum_lt_sum (fun i hi =>
    (unitCircle_logDeriv_re_gt_half hζ (ha i hi)).le) ?_
  obtain ⟨i, hi⟩ := hne
  exact ⟨i, hi, unitCircle_logDeriv_re_gt_half hζ (ha i hi)⟩

/-- If `Re H > n/2` with `n > 0`, then `|n - H| < |H|`. -/
theorem polar_circle_normSq_lt {H : ℂ} {n : ℕ} (hn : 0 < n)
    (hRe : (n : ℝ) / 2 < H.re) :
    Complex.normSq ((n : ℂ) - H) < Complex.normSq H := by
  have hexp :
      Complex.normSq ((n : ℂ) - H) =
        (n : ℝ) ^ 2 + Complex.normSq H - 2 * n * H.re := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [hexp]
  nlinarith

/-- Polar-derivative comparison on the circle for a finite list of
open-disc roots: writing `H = ∑ ζ/(ζ-a_i)`, one has `|n - H| < |H|`. -/
theorem polar_derivative_circle_comparison
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) {ζ : ℂ}
    (hζ : Complex.normSq ζ = 1)
    (ha : ∀ i ∈ s, Complex.normSq (a i) < 1)
    (hne : s.Nonempty) :
    Complex.normSq ((s.card : ℂ) - ∑ i ∈ s, ζ / (ζ - a i)) <
      Complex.normSq (∑ i ∈ s, ζ / (ζ - a i)) := by
  have hn : 0 < s.card := Finset.card_pos.mpr hne
  exact polar_circle_normSq_lt hn
    (unitCircle_sum_logDeriv_re_gt_half_card s a hζ ha hne)

end ErdosProblems.Erdos1041
