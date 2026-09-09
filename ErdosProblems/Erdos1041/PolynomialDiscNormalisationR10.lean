import ErdosProblems.Erdos1041.PaperReflectedCompletion

/-! Actual affine normalisation of a monic polynomial and its entire critical
multiset. No continuity or labelling of moving critical roots is required.
All Lean builds and axiom audits are UNRUN. -/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
noncomputable section
namespace ErdosProblems.Erdos1041
open Polynomial PaperAnalyticTargets

/-- Extract a finite root enumeration without requiring simple roots. -/
theorem exists_monic_root_enumeration {n : ℕ} (p : ℂ[X]) (hp : p.Monic)
    (hdeg : p.natDegree = n) : ∃ a : Fin n → ℂ, RootEnumeration p a := by
  classical
  let l : List ℂ := p.roots.toList
  let a : Fin l.length → ℂ := fun i => l[i.val]
  have hl : l.length = n := by
    have hcard := Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p)
    simpa [l, hdeg] using hcard
  have hfactor : p = ∏ i : Fin l.length, (X - C (a i)) := by
    rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp]
    have ht := Fin.prod_univ_fun_getElem l (fun x : ℂ => (X - C x : ℂ[X]))
    simpa only [a, l, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList] using ht.symm
  rw [← hl]
  exact ⟨a, hfactor⟩

def normaliseDiscPolynomial (p : ℂ[X]) (h : ℂ) (R : ℝ) (n : ℕ) : ℂ[X] :=
  C (((R : ℂ) ^ n)⁻¹) * p.comp (C h + C (R : ℂ) * X)

theorem normaliseDiscPolynomial_eval (p : ℂ[X]) (h : ℂ) (R : ℝ) (n : ℕ) (z : ℂ) :
    (normaliseDiscPolynomial p h R n).eval z =
      ((R : ℂ) ^ n)⁻¹ * p.eval (h + (R : ℂ) * z) := by
  simp only [normaliseDiscPolynomial, eval_mul, eval_C, eval_comp, eval_add, eval_X]

theorem affine_root_product {m : ℕ} (a : Fin m → ℂ) (h r z : ℂ) (hr : r ≠ 0) :
    (∏ i, (h + r * z - a i)) = r ^ m * ∏ i, (z - (a i - h) / r) := by
  have he (i : Fin m) : h + r * z - a i = r * (z - (a i - h) / r) := by
    field_simp [hr]
    <;> ring
  simp only [he, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem normaliseDiscPolynomial_factor {n : ℕ} (p : ℂ[X]) (a : Fin n → ℂ)
    (ha : RootEnumeration p a) (h : ℂ) (R : ℝ) (hR : R ≠ 0) :
    normaliseDiscPolynomial p h R n = ∏ i, (X - C ((a i - h) / (R : ℂ))) := by
  have hr : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  apply Polynomial.funext
  intro z
  rw [normaliseDiscPolynomial_eval, ha]
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  rw [affine_root_product a h (R : ℂ) z hr, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero n hr), one_mul]

theorem normaliseDiscPolynomial_monic_degree {n : ℕ} (p : ℂ[X]) (hp : p.Monic)
    (hdeg : p.natDegree = n) (h : ℂ) (R : ℝ) (hR : R ≠ 0) :
    (normaliseDiscPolynomial p h R n).Monic ∧
      (normaliseDiscPolynomial p h R n).natDegree = n := by
  classical
  obtain ⟨a, ha⟩ := exists_monic_root_enumeration p hp hdeg
  rw [normaliseDiscPolynomial_factor p a ha h R hR]
  constructor
  · exact monic_prod_X_sub_C _ _
  · rw [natDegree_prod_of_monic Finset.univ _ (fun i _ => monic_X_sub_C _)]
    simp

theorem normaliseDiscPolynomial_roots {n : ℕ} (p : ℂ[X]) (h : ℂ) (R : ℝ)
    (hR : 0 < R) (hroots : RootsInClosedDisc p h R) :
    RootsInClosedDisc (normaliseDiscPolynomial p h R n) 0 1 := by
  have hr : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  intro z hz
  rw [normaliseDiscPolynomial_eval] at hz
  have hpz : p.eval (h + (R : ℂ) * z) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (pow_ne_zero n hr))
  have hb := hroots _ hpz
  have he : h + (R : ℂ) * z - h = (R : ℂ) * z := by ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hb
  have hb' : R * ‖z‖ ≤ R * 1 := by simpa only [mul_one] using hb
  have hz1 : ‖z‖ ≤ 1 := le_of_mul_le_mul_left hb' hR
  simpa only [sub_zero] using hz1

theorem normaliseDiscPolynomial_derivative_eval (p : ℂ[X]) (h : ℂ)
    (R : ℝ) (n : ℕ) (z : ℂ) :
    (normaliseDiscPolynomial p h R n).derivative.eval z =
      ((R : ℂ) ^ n)⁻¹ * (R : ℂ) * p.derivative.eval (h + (R : ℂ) * z) := by
  simp only [normaliseDiscPolynomial, derivative_C_mul, derivative_comp,
    derivative_add, derivative_C, derivative_C_mul_X, derivative_X, zero_add,
    eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one, mul_one]
  ring

/-- Exact derivative factorisation after translation and scaling: multiplicities
are transported by a bijective affine map, not chosen by an external supplier. -/
theorem normaliseDiscPolynomial_critical {n : ℕ} (hn : 1 ≤ n) (p : ℂ[X])
    (c : Fin (n - 1) → ℂ) (hc : CriticalEnumeration p c)
    (h : ℂ) (R : ℝ) (hR : R ≠ 0) :
    CriticalEnumeration (normaliseDiscPolynomial p h R n)
      (fun j => (c j - h) / (R : ℂ)) := by
  have hr : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hpow : (R : ℂ) * (R : ℂ) ^ (n - 1) = (R : ℂ) ^ n := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  apply Polynomial.funext
  intro z
  rw [normaliseDiscPolynomial_derivative_eval, hc]
  simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  rw [affine_root_product c h (R : ℂ) z hr]
  calc
    _ = (((R : ℂ) ^ n)⁻¹ * ((R : ℂ) * (R : ℂ) ^ (n - 1))) *
        ((n : ℂ) * ∏ j, (z - (c j - h) / (R : ℂ))) := by ring
    _ = _ := by rw [hpow, inv_mul_cancel₀ (pow_ne_zero n hr), one_mul]

theorem normaliseDiscPolynomial_value_transport (p : ℂ[X]) (h : ℂ) (R : ℝ)
    (n : ℕ) (hR : 0 < R) (z : ℂ) :
    ‖p.eval z‖ = R ^ n * ‖(normaliseDiscPolynomial p h R n).eval ((z - h) / (R : ℂ))‖ := by
  have hr : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have ha : h + (R : ℂ) * ((z - h) / (R : ℂ)) = z := by
    field_simp [hr]
    <;> ring
  have hv : p.eval z = (R : ℂ) ^ n *
      (normaliseDiscPolynomial p h R n).eval ((z - h) / (R : ℂ)) := by
    rw [normaliseDiscPolynomial_eval, ha, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n hr), one_mul]
  rw [hv, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]

/-- The radius-zero endpoint is proved from actual root and derivative
factorisations, without dividing by the enclosing radius. -/
theorem critical_values_zero_of_zero_radius {n : ℕ} (hn : 2 ≤ n) (p : ℂ[X])
    (hp : p.Monic) (hdeg : p.natDegree = n) (h : ℂ)
    (hroots : RootsInClosedDisc p h 0) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration p c) : ∀ j, p.eval (c j) = 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_monic_root_enumeration p hp hdeg
  have hai (i : Fin n) : a i = h := by
    have hz : p.eval (a i) = 0 := by
      rw [ha, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have he : a i - h = 0 := norm_eq_zero.mp (le_antisymm (hroots _ hz) (norm_nonneg _))
    exact sub_eq_zero.mp he
  have hform : p = (X - C h) ^ n := by
    rw [ha]
    simp only [hai, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  intro j
  have hder := PaperReflectedCompletion.listed_critical_is_root hc j
  rw [hform, derivative_X_sub_C_pow] at hder
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X] at hder
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpow := (mul_eq_zero.mp hder).resolve_left hn0
  have hsub : c j - h = 0 := by
    by_contra hh
    exact pow_ne_zero (n - 1) hh hpow
  rw [hform]
  simp only [eval_pow, eval_sub, eval_X, eval_C, hsub,
    zero_pow (by omega : n ≠ 0)]

end ErdosProblems.Erdos1041
end
