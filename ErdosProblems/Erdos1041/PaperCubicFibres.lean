import ErdosProblems.Erdos1041.PaperCurveAssembly
import ErdosProblems.Erdos1041.CubicQuotientFiberCase
import ErdosProblems.Erdos1041.CyclicFiberMeanSquare
import Mathlib

/-!
# Complete translated cubic quotient fibres

The candidates below include: root extraction for a monic cubic; existence
of complex q-th roots; derivation of quotient-root bounds from the whole
translated fibre; selection of a NONZERO safe quotient root; two distinct
fibre endpoints; strict containment of both full segments; actual variation.

The nonzero selection matters. Selecting the zero quotient root by itself
would produce only the translation centre, not two distinct points.

New proof source, not elaborated in this environment.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCubicFibres

open Set Polynomial PaperCurve
open scoped ComplexConjugate

/-- Product form, with multiplicities retained. -/
def cubic (r s v z : ℂ) : ℂ := (z - r) * (z - s) * (z - v)

/-- The existing cubic estimate retains a strict root-radius factor. -/
theorem strict_spoke_of_charge {r s v : ℂ}
    (hr : ‖r‖ < 1) (hs : ‖s‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hc : -1 ≤ cubicRootCharge r s v)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖cubic r s v ((t : ℂ) * r)‖ < 1 := by
  have hdist := cubic_distanceProduct_le_cyclotomic ht0
    (norm_nonneg r) hr.le (norm_nonneg s) hs (norm_nonneg v) hv hc
    (cubic_distance_sq_sum_identity r s v t)
  have hfirst : (t : ℂ) * r - r = (((t - 1 : ℝ) : ℂ) * r) := by
    push_cast
    ring
  have hnfirst : ‖(t : ℂ) * r - r‖ = (1 - t) * ‖r‖ := by
    rw [hfirst, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (show t - 1 ≤ 0 by linarith)]
    ring
  calc
    ‖cubic r s v ((t : ℂ) * r)‖ = ‖r‖ * (1 - t) *
        (‖(t : ℂ) * r - s‖ * ‖(t : ℂ) * r - v‖) := by
      simp only [cubic, norm_mul, hnfirst]
      ring
    _ ≤ ‖r‖ * (1 - t) * (1 + t + t ^ 2) :=
      mul_le_mul_of_nonneg_left hdist
        (mul_nonneg (norm_nonneg r) (sub_nonneg.mpr ht1))
    _ = ‖r‖ * (1 - t ^ 3) := by ring
    _ ≤ ‖r‖ := by
      nlinarith [mul_nonneg (norm_nonneg r) (pow_nonneg ht0 3)]
    _ < 1 := hr

/-- If one root is zero, each other root has a safe spoke. -/
theorem spoke_with_zero_root {r v : ℂ} (hr : ‖r‖ < 1) (hv : ‖v‖ < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖cubic 0 r v ((t : ℂ) * r)‖ < 1 := by
  have hn : ‖r * conj v‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg r, norm_nonneg v,
      mul_nonneg (sub_nonneg.mpr hr.le) (sub_nonneg.mpr hv.le)]
  have hre : -‖r * conj v‖ ≤ (r * conj v).re :=
    (abs_le.mp (Complex.abs_re_le_norm (r * conj v))).1
  have hc : -1 ≤ cubicRootCharge r 0 v := by
    simp only [cubicRootCharge, zero_add]
    linarith
  have h := strict_spoke_of_charge hr (by simp) hv.le hc ht0 ht1
  simpa [cubic, mul_comm, mul_left_comm, mul_assoc] using h

/-- A nonzero safe root is selected, unless all three roots are zero. -/
theorem nonzero_safe_root {r s v : ℂ}
    (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) (hv : ‖v‖ < 1)
    (hnz : r ≠ 0 ∨ s ≠ 0 ∨ v ≠ 0) :
    ∃ w : ℂ, w ≠ 0 ∧ cubic r s v w = 0 ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖cubic r s v ((t : ℂ) * w)‖ < 1) := by
  by_cases hr0 : r = 0
  · subst r
    by_cases hs0 : s = 0
    · subst s
      have hv0 : v ≠ 0 := by simpa using hnz
      refine ⟨v, hv0, by simp [cubic], ?_⟩
      intro t ht0 ht1
      have h := spoke_with_zero_root hv (show ‖(0 : ℂ)‖ < 1 by norm_num) ht0 ht1
      simpa [cubic, mul_comm, mul_left_comm, mul_assoc] using h
    · refine ⟨s, hs0, by simp [cubic], ?_⟩
      exact fun t ht0 ht1 => spoke_with_zero_root hs hv ht0 ht1
  by_cases hs0 : s = 0
  · subst s
    refine ⟨r, hr0, by simp [cubic], ?_⟩
    intro t ht0 ht1
    have h := spoke_with_zero_root hr hv ht0 ht1
    simpa [cubic, mul_comm, mul_left_comm, mul_assoc] using h
  by_cases hv0 : v = 0
  · subst v
    refine ⟨r, hr0, by simp [cubic], ?_⟩
    intro t ht0 ht1
    have h := spoke_with_zero_root hr hs ht0 ht1
    simpa [cubic, mul_comm, mul_left_comm, mul_assoc] using h
  rcases one_cubicRootCharge_gt_neg_one hr hs hv with hc | hc | hc
  · exact ⟨r, hr0, by simp [cubic],
      fun t ht0 ht1 => strict_spoke_of_charge hr hs.le hv.le hc.le ht0 ht1⟩
  · refine ⟨s, hs0, by simp [cubic], ?_⟩
    intro t ht0 ht1
    have h := strict_spoke_of_charge hs hr.le hv.le hc.le ht0 ht1
    simpa [cubic, mul_comm, mul_left_comm, mul_assoc] using h
  · refine ⟨v, hv0, by simp [cubic], ?_⟩
    intro t ht0 ht1
    have h := strict_spoke_of_charge hv hr.le hs.le hc.le ht0 ht1
    simpa [cubic, mul_comm, mul_left_comm, mul_assoc] using h

/-- Complex q-th roots are supplied, not assumed. -/
theorem exists_nth_root {q : ℕ} (hq : q ≠ 0) (w : ℂ) :
    ∃ y : ℂ, y ^ q = w := by
  by_cases hw : w = 0
  · exact ⟨0, by simp [hw, hq]⟩
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  refine ⟨Complex.exp (Complex.log w / (q : ℂ)), ?_⟩
  rw [← Complex.exp_nat_mul]
  have he : (q : ℂ) * (Complex.log w / (q : ℂ)) = Complex.log w := by
    field_simp [hqC]
  rw [he, Complex.exp_log hw]

/-- Every zero of the quotient is forced into the open disc by the complete
translated fibre, even when the centre is nonzero. -/
theorem quotient_roots_open {q : ℕ} (hq : 2 ≤ q) (h : ℂ) (P : ℂ → ℂ)
    (hdisk : ∀ z : ℂ, P ((z - h) ^ q) = 0 → ‖z‖ < 1)
    {w : ℂ} (hw : P w = 0) : ‖w‖ < 1 := by
  obtain ⟨y, hy⟩ := exists_nth_root (show q ≠ 0 by omega) w
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ))
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q (by omega)
  have hfibre : ∀ k < q, ‖h + y * ζ ^ k‖ < 1 := by
    intro k hk
    apply hdisk
    exact cyclicFiber_composition_zero hζ.pow_eq_one P h y (by simpa [hy] using hw) k
  simpa [hy] using cyclicFiber_quotient_norm_lt_one (by omega) hζ h y hfibre

/-- The geometric pullback from ONE nonzero safe quotient root. -/
theorem connection_of_nonzero_safe_quotient_root
    {q : ℕ} (hq : 2 ≤ q) (h : ℂ) (P : ℂ → ℂ)
    (hdisk : ∀ z : ℂ, P ((z - h) ^ q) = 0 → ‖z‖ < 1)
    {w : ℂ} (hw0 : w ≠ 0) (hw : P w = 0)
    (hsafe : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖P ((t : ℂ) * w)‖ < 1) :
    ∃ a b : ℂ, a ≠ b ∧ P ((a - h) ^ q) = 0 ∧ P ((b - h) ^ q) = 0 ∧
      HubBelow (fun z => P ((z - h) ^ q)) 1 2 a h b := by
  obtain ⟨y, hy⟩ := exists_nth_root (show q ≠ 0 by omega) w
  have hy0 : y ≠ 0 := by
    intro hz
    apply hw0
    rw [← hy, hz, zero_pow (by omega)]
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ))
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q (by omega)
  have hζnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (by omega)
  have hζne : ζ ≠ 1 := by
    intro hz
    have hg := hζ.geom_sum_eq_zero (show 1 < q by omega)
    have hqC : (q : ℂ) = 0 := by simpa [hz] using hg
    have : q = 0 := by exact_mod_cast hqC
    omega
  have hfibre : ∀ k < q, ‖h + y * ζ ^ k‖ < 1 := by
    intro k hk
    exact hdisk _ (cyclicFiber_composition_zero hζ.pow_eq_one P h y
      (by simpa [hy] using hw) k)
  have hb := cyclicFiber_normSq_add_lt_one (by omega) hζ h y hfibre
  have hynorm : ‖y‖ < 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hb
    nlinarith [sq_nonneg ‖h‖, norm_nonneg y]
  have hroot₁ : P ((h + y - h) ^ q) = 0 := by simpa [hy] using hw
  have hroot₂ : P ((h + y * ζ - h) ^ q) = 0 := by
    simpa using cyclicFiber_composition_zero hζ.pow_eq_one P h y
      (by simpa [hy] using hw) 1
  have hdistinct : h + y ≠ h + y * ζ := by
    intro heq
    have hm : y * 1 = y * ζ := by simpa using add_left_cancel heq
    have : 1 = ζ := mul_left_cancel₀ hy0 hm
    exact hζne this.symm
  refine ⟨h + y, h + y * ζ, hdistinct, hroot₁, hroot₂, ?_⟩
  apply hubBelow_of_spokes (h := h)
  · intro u hu0 hu1
    have huq0 : 0 ≤ u ^ q := pow_nonneg hu0 q
    have huq1 : u ^ q ≤ 1 := pow_le_one₀ hu0 hu1
    have he : (h + (u : ℂ) * (h + y - h) - h) ^ q =
        ((u ^ q : ℝ) : ℂ) * w := by
      simp only [add_sub_cancel_left, mul_pow, hy, Complex.ofReal_pow]
    rw [he]
    exact hsafe (u ^ q) huq0 huq1
  · intro u hu0 hu1
    have huq0 : 0 ≤ u ^ q := pow_nonneg hu0 q
    have huq1 : u ^ q ≤ 1 := pow_le_one₀ hu0 hu1
    have he : (h + (u : ℂ) * (h + y * ζ - h) - h) ^ q =
        ((u ^ q : ℝ) : ℂ) * w := by
      simp only [add_sub_cancel_left, mul_pow, hy, hζ.pow_eq_one,
        mul_one, Complex.ofReal_pow]
    rw [he]
    exact hsafe (u ^ q) huq0 huq1
  · have he₁ : h - (h + y) = -y := by ring
    have he₂ : h + y * ζ - h = y * ζ := by ring
    rw [he₁, he₂, norm_neg, norm_mul, hζnorm, mul_one]
    linarith

private theorem list_length_three {l : List ℂ} (hl : l.length = 3) :
    ∃ r s v : ℂ, l = [r, s, v] := by
  cases l with
  | nil => simp at hl
  | cons r l =>
    cases l with
    | nil => simp at hl
    | cons s l =>
      cases l with
      | nil => simp at hl
      | cons v l =>
        have hzero : l.length = 0 := by simp only [List.length_cons] at hl; omega
        have hnil : l = [] := List.length_eq_zero_iff.mp hzero
        subst l
        exact ⟨r, s, v, rfl⟩

/-- Factorisation is extracted from the monic cubic hypothesis, so it is not
an extra input in the main theorem. -/
theorem monic_cubic_factorisation (P : ℂ[X]) (hP : P.Monic) (hdeg : P.natDegree = 3) :
    ∃ r s v : ℂ, ∀ z : ℂ, P.eval z = cubic r s v z := by
  have hs : P.Splits := IsAlgClosed.splits P
  have hcard : P.roots.card = 3 := by
    rw [Polynomial.splits_iff_card_roots.mp hs, hdeg]
  have hl : P.roots.toList.length = 3 := by simpa using hcard
  obtain ⟨r, s, v, hlist⟩ := list_length_three hl
  have hroots : P.roots = r ::ₘ s ::ₘ v ::ₘ 0 := by
    simpa [hlist] using (Multiset.coe_toList P.roots).symm
  have hp := hs.eq_prod_roots
  refine ⟨r, s, v, ?_⟩
  intro z
  rw [hp, hP.leadingCoeff, hroots]
  simp [cubic, mul_assoc]

/-- End-to-end paper theorem: no supplied safe root, no supplied quotient
root bounds, no supplied fibre enumeration, and no supplied metric budget. -/
theorem complete_translated_cubic_quotient_fibres
    {q : ℕ} (hq : 2 ≤ q) (h : ℂ) (P : ℂ[X])
    (hP : P.Monic) (hdeg : P.natDegree = 3)
    (hdisk : ∀ z : ℂ, P.eval ((z - h) ^ q) = 0 → ‖z‖ < 1)
    (htwo : ∃ a b : ℂ, a ≠ b ∧
      P.eval ((a - h) ^ q) = 0 ∧ P.eval ((b - h) ^ q) = 0) :
    ∃ a b : ℂ, a ≠ b ∧ P.eval ((a - h) ^ q) = 0 ∧
      P.eval ((b - h) ^ q) = 0 ∧
      HubBelow (fun z => P.eval ((z - h) ^ q)) 1 2 a h b := by
  obtain ⟨r, s, v, hfac⟩ := monic_cubic_factorisation P hP hdeg
  have hrzero : P.eval r = 0 := by simp [hfac, cubic]
  have hszero : P.eval s = 0 := by simp [hfac, cubic]
  have hvzero : P.eval v = 0 := by simp [hfac, cubic]
  have hr := quotient_roots_open hq h P.eval hdisk hrzero
  have hs := quotient_roots_open hq h P.eval hdisk hszero
  have hv := quotient_roots_open hq h P.eval hdisk hvzero
  have hnz : r ≠ 0 ∨ s ≠ 0 ∨ v ≠ 0 := by
    by_contra hall
    push_neg at hall
    rcases htwo with ⟨a, b, hab, ha, hb⟩
    have hzero : ∀ z : ℂ, P.eval z = z ^ 3 := by
      intro z
      rw [hfac, hall.1, hall.2.1, hall.2.2]
      simp [cubic] <;> ring
    rw [hzero] at ha hb
    have hq0 : q ≠ 0 := by omega
    have haq : (a - h) ^ q = 0 :=
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp ha
    have hbq : (b - h) ^ q = 0 :=
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hb
    have haeq : a = h := sub_eq_zero.mp ((pow_eq_zero_iff hq0).mp haq)
    have hbeq : b = h := sub_eq_zero.mp ((pow_eq_zero_iff hq0).mp hbq)
    exact hab (haeq.trans hbeq.symm)
  obtain ⟨w, hw0, hw, hsafe⟩ := nonzero_safe_root hr hs hv hnz
  apply connection_of_nonzero_safe_quotient_root hq h P.eval hdisk hw0
  · simpa [hfac] using hw
  · intro t ht0 ht1
    simpa [hfac] using hsafe t ht0 ht1

/-- Explicit coefficient presentation in the long record. -/
def coefficientFamily (q : ℕ) (h a b c z : ℂ) : ℂ :=
  (z - h) ^ (3 * q) + a * (z - h) ^ (2 * q) + b * (z - h) ^ q + c

theorem complete_cubic_coefficient_family
    {q : ℕ} (hq : 2 ≤ q) (h a b c : ℂ)
    (hdisk : ∀ z : ℂ, coefficientFamily q h a b c z = 0 → ‖z‖ < 1)
    (htwo : ∃ x y : ℂ, x ≠ y ∧
      coefficientFamily q h a b c x = 0 ∧ coefficientFamily q h a b c y = 0) :
    ∃ x y : ℂ, x ≠ y ∧ coefficientFamily q h a b c x = 0 ∧
      coefficientFamily q h a b c y = 0 ∧
      HubBelow (coefficientFamily q h a b c) 1 2 x h y := by
  let P : ℂ[X] := X ^ 3 + (C a * X ^ 2 + (C b * X ^ 1 + C c))
  have hsmall : (C b * X ^ 1 + C c : ℂ[X]).degree ≤ (1 : WithBot ℕ) :=
    le_trans (degree_add_le _ _) (max_le (degree_C_mul_X_pow_le 1 b)
      (le_trans degree_C_le (by norm_num)))
  have htail : (C a * X ^ 2 + (C b * X ^ 1 + C c) : ℂ[X]).degree ≤
      (2 : WithBot ℕ) :=
    le_trans (degree_add_le _ _) (max_le (degree_C_mul_X_pow_le 2 a)
      (le_trans hsmall (by norm_num)))
  have hlt : (C a * X ^ 2 + (C b * X ^ 1 + C c) : ℂ[X]).degree <
      (X ^ 3 : ℂ[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt htail (by norm_num)
  have hmonic : P.Monic := (monic_X_pow 3).add_of_left hlt
  have hdegree : P.natDegree = 3 := by
    apply natDegree_eq_of_degree_eq_some
    change (X ^ 3 + (C a * X ^ 2 + (C b * X ^ 1 + C c)) : ℂ[X]).degree = _
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  have heval (z : ℂ) : P.eval ((z - h) ^ q) = coefficientFamily q h a b c z := by
    simp [P, coefficientFamily, ← pow_mul, Nat.mul_comm] <;> ring
  have hdisk' : ∀ z : ℂ, P.eval ((z - h) ^ q) = 0 → ‖z‖ < 1 := by
    intro z hz
    exact hdisk z (by simpa only [heval] using hz)
  have htwo' : ∃ x y : ℂ, x ≠ y ∧ P.eval ((x - h) ^ q) = 0 ∧
      P.eval ((y - h) ^ q) = 0 := by
    simpa only [heval] using htwo
  obtain ⟨x, y, hxy, hx, hy, H⟩ :=
    complete_translated_cubic_quotient_fibres hq h P hmonic hdegree hdisk' htwo'
  exact ⟨x, y, hxy, by simpa only [heval] using hx,
    by simpa only [heval] using hy, by simpa only [heval] using H⟩

#print axioms complete_translated_cubic_quotient_fibres
#print axioms complete_cubic_coefficient_family

end ErdosProblems.Erdos1041.PaperCubicFibres
