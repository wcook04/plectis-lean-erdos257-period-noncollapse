import ErdosProblems.Erdos1041.PrimitiveQuinticInteriorTail
import ErdosProblems.Erdos1041.PaperPrimitivePath

/-!
# Primitive quintic: polynomial-to-moment-to-path completion

This module removes `hselected` from the paper endpoint.  The five occurrences
are obtained from the fundamental theorem of algebra.  Missing coefficients
supply the three Newton moments by exact five-point interpolation.  A unit
rotation feeds the existing harmonic separator, then the existing Abel and
variation lemmas assemble the path.  All elaboration and axiom checks: UNRUN.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10

open Polynomial Set PaperCurve PaperPrimitivePath
open scoped BigOperators

/-- Occurrences, not necessarily different locations. -/
def rootProduct (w : Fin 5 → ℂ) (z : ℂ) : ℂ :=
  (z - w 0) * (z - w 1) * (z - w 2) * (z - w 3) * (z - w 4)

private lemma list_length_five {l : List ℂ} (hl : l.length = 5) :
    ∃ a b c d e : ℂ, l = [a, b, c, d, e] := by
  cases l with
  | nil => simp at hl
  | cons a l =>
    cases l with
    | nil => simp at hl
    | cons b l =>
      cases l with
      | nil => simp at hl
      | cons c l =>
        cases l with
        | nil => simp at hl
        | cons d l =>
          cases l with
          | nil => simp at hl
          | cons e l =>
            have hn : l.length = 0 := by simp only [List.length_cons] at hl; omega
            have he : l = [] := List.length_eq_zero_iff.mp hn
            subst l
            exact ⟨a, b, c, d, e, rfl⟩

/-- No factorisation is imposed on the final polynomial theorem. -/
theorem monic_quintic_enumeration (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = 5) :
    ∃ w : Fin 5 → ℂ, ∀ z : ℂ, p.eval z = rootProduct w z := by
  have hc : p.roots.card = 5 := IsAlgClosed.card_roots_eq_natDegree.trans hd
  have hl : p.roots.toList.length = 5 := by simpa using hc
  obtain ⟨a, b, c, d, e, he⟩ := list_length_five hl
  have hr : p.roots = a ::ₘ b ::ₘ c ::ₘ d ::ₘ e ::ₘ 0 := by
    simpa [he] using (Multiset.coe_toList p.roots).symm
  refine ⟨![a, b, c, d, e], ?_⟩
  intro z
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp, hr]
  simp [rootProduct, mul_assoc]

/-- The first three power sums follow from the missing cubic and quadratic
coefficients.  The interpolation weights are recorded in certificates/. -/
theorem newton_moments {a b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z) :
    (∑ i, w i) = -a ∧ (∑ i, w i ^ 2) = a ^ 2 ∧
      (∑ i, w i ^ 3) = -a ^ 3 := by
  let e1 := w 0 + w 1 + w 2 + w 3 + w 4
  let e2 := w 0*w 1 + w 0*w 2 + w 0*w 3 + w 0*w 4 +
    w 1*w 2 + w 1*w 3 + w 1*w 4 + w 2*w 3 + w 2*w 4 + w 3*w 4
  let e3 := w 0*w 1*w 2 + w 0*w 1*w 3 + w 0*w 1*w 4 +
    w 0*w 2*w 3 + w 0*w 2*w 4 + w 0*w 3*w 4 +
    w 1*w 2*w 3 + w 1*w 2*w 4 + w 1*w 3*w 4 + w 2*w 3*w 4
  have h0 := hf 0
  have h1 := hf 1
  have hm1 := hf (-1)
  have h2 := hf 2
  have hm2 := hf (-2)
  dsimp [value, rootProduct] at h0 h1 hm1 h2 hm2
  have he1 : e1 = -a := by
    dsimp [e1]
    linear_combination (1/4)*h0 - (1/6)*h1 - (1/6)*hm1 + (1/24)*h2 + (1/24)*hm2
  have he2 : e2 = 0 := by
    dsimp [e2]
    linear_combination (1/6)*h1 - (1/6)*hm1 - (1/12)*h2 + (1/12)*hm2
  have he3 : e3 = 0 := by
    dsimp [e3]
    linear_combination -(5/4)*h0 + (2/3)*h1 + (2/3)*hm1 - (1/24)*h2 - (1/24)*hm2
  have hp1 : (∑ i, w i) = e1 := by simp [Fin.sum_univ_succ, e1]; ring
  have hp2 : (∑ i, w i ^ 2) = e1 ^ 2 - 2 * e2 := by
    simp [Fin.sum_univ_succ, e1, e2]; ring
  have hp3 : (∑ i, w i ^ 3) = e1 ^ 3 - 3 * e1 * e2 + 3 * e3 := by
    simp [Fin.sum_univ_succ, e1, e2, e3]; ring
  refine ⟨hp1.trans he1, ?_, ?_⟩
  · rw [hp2, he1, he2]; ring
  · rw [hp3, he1, he2, he3]; ring

private lemma norm_sq_coords (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

private lemma real_square (z : ℂ) :
    (z ^ 2).re = 2 * z.re ^ 2 - ‖z‖ ^ 2 := by
  rw [norm_sq_coords]
  simp [pow_two, Complex.mul_re]
  ring

private lemma real_cube (z : ℂ) :
    (z ^ 3).re = 4 * z.re ^ 3 - 3 * ‖z‖ ^ 2 * z.re := by
  rw [norm_sq_coords]
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

private lemma norm_add_real_sq (z : ℂ) (r : ℝ) :
    ‖z + (r : ℂ)‖ ^ 2 = ‖z‖ ^ 2 + r ^ 2 + 2 * r * z.re := by
  rw [norm_sq_coords, norm_sq_coords]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Complete two-tail selector under the actual polynomial factorisation.
The normalised moments, the coefficient bound and the rotation are all derived. -/
theorem two_tails_of_rootProduct {a b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z)
    (hw : ∀ i, ‖w i‖ < 1) :
    ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 := by
  have hroot (i : Fin 5) : value a b c (w i) = 0 := by
    rw [hf]; fin_cases i <;> simp [rootProduct]
  have htail (i : Fin 5) : b * w i + c = -(w i ^ 4 * (w i + a)) := by
    have H := hroot i
    dsimp [value] at H
    linear_combination H
  by_cases ha : a = 0
  · have hall (i : Fin 5) : ‖b * w i + c‖ < 1 := by
      rw [htail, ha, add_zero, ← pow_succ, norm_neg, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (hw i) (by norm_num)
    exact ⟨0, 1, by decide, hall 0, hall 1⟩
  let r : ℝ := ‖a‖
  have hr : 0 < r := norm_pos_iff.mpr ha
  let u : ℂ := (r : ℂ) / a
  have hua : u * a = (r : ℂ) := div_mul_cancel₀ _ ha
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_self (ne_of_gt hr)
  let z : Fin 5 → ℂ := fun i => u * w i
  have hzn (i : Fin 5) : ‖z i‖ = ‖w i‖ := by simp [z, norm_mul, hu]
  have hz (i : Fin 5) : ‖z i‖ < 1 := by rw [hzn]; exact hw i
  obtain ⟨hm1, hm2, hm3⟩ := newton_moments w hf
  have sum_rotation (k : ℕ) : (∑ i, z i ^ k) = u ^ k * ∑ i, w i ^ k := by
    simp only [z, mul_pow, Finset.mul_sum]
  have hz1 : (∑ i, z i) = -(r : ℂ) := by
    have H := sum_rotation 1
    simp only [pow_one] at H
    rw [H, hm1, mul_neg, hua]
  have hz2 : (∑ i, z i ^ 2) = (r : ℂ) ^ 2 := by
    rw [sum_rotation, hm2, ← mul_pow, hua]
  have hz3 : (∑ i, z i ^ 3) = -(r : ℂ) ^ 3 := by
    rw [sum_rotation, hm3, mul_neg, ← mul_pow, hua]
  have hsum3 : ‖∑ i, z i ^ 3‖ ≤ (5 : ℝ) := calc
    ‖∑ i, z i ^ 3‖ ≤ ∑ i, ‖z i ^ 3‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 5, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hz i).le
    _ = 5 := by simp
  have hr3 : r ^ 3 ≤ 5 := by
    simpa [hz3, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] using hsum3
  have hr2 : r < 2 := by
    by_contra H
    have H' : (2 : ℝ) ≤ r := le_of_not_gt H
    have hplus : 0 ≤ r + 2 := by linarith
    have hsqprod : 0 ≤ (r - 2) * (r + 2) :=
      mul_nonneg (sub_nonneg.mpr H') hplus
    have hsq : (4 : ℝ) ≤ r ^ 2 := by nlinarith
    have hcubicprod : 0 ≤ (r ^ 2 - 4) * r :=
      mul_nonneg (sub_nonneg.mpr hsq) hr.le
    have hcubic : (8 : ℝ) ≤ r ^ 3 := by nlinarith
    linarith
  have hs0 (i : Fin 5) : 0 ≤ ‖z i‖ ^ 2 := sq_nonneg _
  have hs1 (i : Fin 5) : ‖z i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hz i).le
  have hxs (i : Fin 5) : (z i).re ^ 2 ≤ ‖z i‖ ^ 2 := by
    rw [norm_sq_coords]; nlinarith [sq_nonneg (z i).im]
  have hx1 : (z 0).re + (z 1).re + (z 2).re + (z 3).re + (z 4).re = -r := by
    have H := congrArg Complex.re hz1
    simpa [Fin.sum_univ_succ, add_assoc] using H
  have hx2 :
      (2*(z 0).re^2 - ‖z 0‖^2) + (2*(z 1).re^2 - ‖z 1‖^2) +
      (2*(z 2).re^2 - ‖z 2‖^2) + (2*(z 3).re^2 - ‖z 3‖^2) +
      (2*(z 4).re^2 - ‖z 4‖^2) = r^2 := by
    have H := congrArg Complex.re hz2
    calc
      _ = 2 * r ^ 2 - r ^ 2 := by
        simpa [Fin.sum_univ_succ, real_square, add_assoc] using H
      _ = r ^ 2 := by ring
  have hx3 :
      (4*(z 0).re^3 - 3*‖z 0‖^2*(z 0).re) +
      (4*(z 1).re^3 - 3*‖z 1‖^2*(z 1).re) +
      (4*(z 2).re^3 - 3*‖z 2‖^2*(z 2).re) +
      (4*(z 3).re^3 - 3*‖z 3‖^2*(z 3).re) +
      (4*(z 4).re^3 - 3*‖z 4‖^2*(z 4).re) = -r^3 := by
    have H := congrArg Complex.re hz3
    calc
      _ = 3 * r ^ 2 * r - 4 * r ^ 3 := by
        simpa [Fin.sum_univ_succ, real_cube, add_assoc] using H
      _ = -r ^ 3 := by ring
  have henergy (i : Fin 5) :
      ‖b*w i+c‖ ^ 2 = (‖z i‖^2)^4 * (‖z i‖^2 + r^2 + 2*r*(z i).re) := by
    have he : z i + (r : ℂ) = u * (w i + a) := by dsimp [z]; rw [mul_add, hua]
    have heN : ‖z i + (r : ℂ)‖ = ‖w i + a‖ := by rw [he, norm_mul, hu, one_mul]
    rw [htail, norm_neg, norm_mul, norm_pow, ← hzn, ← heN, mul_pow,
      norm_add_real_sq]
    ring
  have safe (i : Fin 5)
      (H : (‖z i‖^2)^4 * (‖z i‖^2+r^2+2*r*(z i).re) < 1) :
      ‖b*w i+c‖ < 1 := by
    rw [← henergy] at H
    nlinarith [norm_nonneg (b*w i+c), sq_nonneg (‖b*w i+c‖ - 1)]
  have H := primitiveInterior_exists_two_tailEnergy_lt_one hr hr2
    (hs0 0) (hs1 0) (hxs 0) (hs0 1) (hs1 1) (hxs 1)
    (hs0 2) (hs1 2) (hxs 2) (hs0 3) (hs1 3) (hxs 3)
    (hs0 4) (hs1 4) (hxs 4) hx1 hx2 hx3
  rcases H with H | H | H | H | H | H | H | H | H | H
  · exact ⟨0, 1, by decide, safe 0 H.1, safe 1 H.2⟩
  · exact ⟨0, 2, by decide, safe 0 H.1, safe 2 H.2⟩
  · exact ⟨0, 3, by decide, safe 0 H.1, safe 3 H.2⟩
  · exact ⟨0, 4, by decide, safe 0 H.1, safe 4 H.2⟩
  · exact ⟨1, 2, by decide, safe 1 H.1, safe 2 H.2⟩
  · exact ⟨1, 3, by decide, safe 1 H.1, safe 3 H.2⟩
  · exact ⟨1, 4, by decide, safe 1 H.1, safe 4 H.2⟩
  · exact ⟨2, 3, by decide, safe 2 H.1, safe 3 H.2⟩
  · exact ⟨2, 4, by decide, safe 2 H.1, safe 4 H.2⟩
  · exact ⟨3, 4, by decide, safe 3 H.1, safe 4 H.2⟩

/-- End-to-end paper theorem, retaining actual root occurrences and the
constant-path alternative.  There is no additional selection hypothesis. -/
theorem complete_primitive_quintic (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = 5) (a b c : ℂ)
    (hvalue : ∀ z, p.eval z = value a b c z)
    (hdisk : ∀ z, p.eval z = 0 → ‖z‖ < 1) :
    ∃ w : Fin 5 → ℂ, (∀ z, p.eval z = rootProduct w z) ∧
      ∃ i j : Fin 5, i ≠ j ∧ ‖b*w i+c‖ < 1 ∧ ‖b*w j+c‖ < 1 ∧
        ConnectedBelow p.eval 1 2 (w i) (w j) ∧
        (w i ≠ w j → HubBelow p.eval 1 2 (w i) 0 (w j)) ∧
        (w i = w j →
          (∀ t : ℝ, ‖p.eval ((fun _ : ℝ => w i) t)‖ < 1) ∧
          eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0) := by
  obtain ⟨w, hw⟩ := monic_quintic_enumeration p hp hd
  have hroots (i : Fin 5) : p.eval (w i) = 0 := by
    rw [hw]; fin_cases i <;> simp [rootProduct]
  have hf : ∀ z, value a b c z = rootProduct w z := by
    intro z; rw [← hvalue, hw]
  have hs := two_tails_of_rootProduct w hf (fun i => hdisk _ (hroots i))
  exact ⟨w, hw, path_of_selected_tails p hp hd a b c hvalue hdisk w hroots hs⟩

end ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10
