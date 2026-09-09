import Mathlib
import ErdosProblems.Erdos1041.PaperAnalyticTargets

/-!
# B4: the polar boundary inequality and the reflected-value consumer

Uncompiled at Lean 4.29.1 / Mathlib
5e932f97dd25535344f80f9dd8da3aab83df0fe6.

The finite product logarithmic derivative and the boundary norm comparison
have explicit proof scripts rather than hypothesis-only wrappers. The
maximum-principle passage through possible boundary zeros and critical-point
localisation are retained as interfaces here; PaperReflectedCompletion now
supplies both source candidates and the full endpoint. None is compiled.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.PaperReflectedBoundary
open Polynomial Set PaperAnalyticTargets
open scoped BigOperators ComplexConjugate

-- Pinned Mathlib/Data/Complex/Basic.lean: div_re, normSq_apply,
-- normSq_pos, sub_re, sub_im.
/-- The boundary half-plane estimate before any summation. -/
theorem radial_fraction_identity (z a : ℂ) (hza : z-a ≠ 0) :
    (2*(z/(z-a)).re-1)*Complex.normSq (z-a) =
      Complex.normSq z-Complex.normSq a := by
  have hq : Complex.normSq (z-a) ≠ 0 := (Complex.normSq_pos.mpr hza).ne'
  rw [Complex.div_re, ← add_div]
  calc
    (2*((z.re*(z-a).re+z.im*(z-a).im)/Complex.normSq (z-a))-1)*
        Complex.normSq (z-a) =
      2*(z.re*(z-a).re+z.im*(z-a).im)-Complex.normSq (z-a) := by
        field_simp [hq]
        <;> ring
    _ = Complex.normSq z-Complex.normSq a := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring

-- Pinned Mathlib/Analysis/Complex/Norm.lean: normSq_eq_norm_sq.
theorem radial_fraction_half_plane (z a : ℂ) (hz : ‖z‖ = 1)
    (ha : ‖a‖ ≤ 1) (hza : z-a ≠ 0) : 1 ≤ 2*(z/(z-a)).re := by
  have hi := radial_fraction_identity z a hza
  have hq : 0 < Complex.normSq (z-a) := Complex.normSq_pos.mpr hza
  have hzaSq : Complex.normSq a ≤ Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hz]
    simpa only [one_pow] using (pow_le_one₀ (norm_nonneg a) ha : ‖a‖ ^ 2 ≤ 1)
  have hprod : 0 ≤ (2*(z/(z-a)).re-1)*Complex.normSq (z-a) := by
    rw [hi]
    exact sub_nonneg.mpr hzaSq
  have hnonneg : 0 ≤ 2*(z/(z-a)).re-1 := by
    by_contra hneg
    have hn : 2*(z/(z-a)).re-1 < 0 := lt_of_not_ge hneg
    have hc := mul_neg_of_neg_of_pos hn hq
    exact (not_lt_of_ge hprod) hc
  linarith

-- Pinned Mathlib/Algebra/Polynomial/Derivative.lean: derivative_mul,
-- derivative_sub, derivative_X, derivative_C.
-- Mathlib/Algebra/Polynomial/Eval/Defs.lean: eval_prod and ring operations.
-- Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean: prod_ne_zero_iff.
/-- Exact finite logarithmic derivative; repeated roots are allowed. -/
theorem product_log_derivative {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (z : ℂ)
    (hnz : ∀ i ∈ s, z-a i ≠ 0) :
    (∏ i ∈ s, (X-C (a i))).derivative.eval z /
      (∏ i ∈ s, (X-C (a i))).eval z = ∑ i ∈ s, (z-a i)⁻¹ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hi : z-a i ≠ 0 := hnz i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, z-a j ≠ 0 := fun j hj => hnz j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ s, (X-C (a j))).eval z ≠ 0 := by
      rw [eval_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      simpa only [eval_sub, eval_X, eval_C] using hs j hj
    simp only [Finset.prod_insert his, derivative_mul, derivative_sub,
      derivative_X, derivative_C, eval_add, eval_mul, eval_sub, eval_one,
      eval_zero, eval_X, eval_C, sub_zero, one_mul, Finset.sum_insert his]
    rw [← ih hs]
    field_simp [hi, hprod]
    <;> ring

/-- A half-plane condition is equivalent to the needed scalar norm comparison. -/
theorem polar_scalar_norm (n : ℝ) (L : ℂ) (hn : 0 ≤ n)
    (hL : n ≤ 2*L.re) : ‖(n : ℂ)-L‖ ≤ ‖L‖ := by
  have he : Complex.normSq ((n : ℂ)-L) =
      Complex.normSq L+n^2-2*n*L.re := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hprod : 0 ≤ n*(2*L.re-n) := mul_nonneg hn (sub_nonneg.mpr hL)
  have hsq : ‖(n : ℂ)-L‖^2 ≤ ‖L‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, he]
    nlinarith only [hprod]
  nlinarith only [hsq, norm_nonneg ((n : ℂ)-L), norm_nonneg L]

-- Pinned Mathlib/Data/Complex/BigOperators.lean: Complex.re_sum.
/-- The actual boundary inequality for a factored polynomial, including
boundary roots (the f(z)=0 case is treated without division). -/
theorem polar_boundary_of_roots (n : ℕ) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (z : ℂ) (hz : ‖z‖ = 1) :
    let p : ℂ[X] := ∏ i : Fin n, (X-C (a i))
    ‖(n : ℂ)*p.eval z-z*p.derivative.eval z‖ ≤ ‖p.derivative.eval z‖ := by
  classical
  dsimp only
  let p : ℂ[X] := ∏ i : Fin n, (X-C (a i))
  change ‖(n : ℂ)*p.eval z-z*p.derivative.eval z‖ ≤ ‖p.derivative.eval z‖
  by_cases hpz : p.eval z = 0
  · simp only [hpz, mul_zero, zero_sub, norm_neg, Complex.norm_mul, hz, one_mul, le_refl]
  have hnz : ∀ i : Fin n, z-a i ≠ 0 := by
    have hprod : (∏ i : Fin n, (z-a i)) ≠ 0 := by
      simpa only [p, eval_prod, eval_sub, eval_X, eval_C] using hpz
    exact fun i => Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  let L : ℂ := z*p.derivative.eval z / p.eval z
  have hlog : L = ∑ i : Fin n, z/(z-a i) := by
    have h := product_log_derivative Finset.univ a z (fun i _ => hnz i)
    calc
      L = z*(p.derivative.eval z/p.eval z) := by dsimp [L]; ring
      _ = z*∑ i : Fin n, (z-a i)⁻¹ := by rw [h]
      _ = ∑ i : Fin n, z/(z-a i) := by rw [Finset.mul_sum]; rfl
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => radial_fraction_half_plane z (a i) hz (ha i) (hnz i))
  have hL : (n : ℝ) ≤ 2*L.re := by
    rw [hlog, Complex.re_sum]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Finset.mul_sum] using hsum
  have hnorm := polar_scalar_norm (n : ℝ) L (Nat.cast_nonneg n) hL
  have hfactor : (n : ℂ)*p.eval z-z*p.derivative.eval z =
      ((n : ℂ)-L)*p.eval z := by
    dsimp [L]
    field_simp [hpz]
    <;> ring
  have hcancel : L*p.eval z = z*p.derivative.eval z := by
    dsimp [L]
    exact div_mul_cancel₀ _ hpz
  calc
    ‖(n : ℂ)*p.eval z-z*p.derivative.eval z‖ =
        ‖(n : ℂ)-L‖*‖p.eval z‖ := by rw [hfactor, Complex.norm_mul]
    _ ≤ ‖L‖*‖p.eval z‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖p.derivative.eval z‖ := by
      rw [← Complex.norm_mul, hcancel, Complex.norm_mul, hz, one_mul]

/-- Localisation of the listed critical points, with the paper's exact
root-location hypothesis. A proof candidate is in PaperReflectedCompletion. -/
def CriticalDiscLocation_target : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n-1) → ℂ),
    2 ≤ n → p.Monic → p.natDegree = n → RootsInClosedDisc p 0 1 →
    CriticalEnumeration p c → ∀ j, ‖c j‖ ≤ 1

/-- The maximum-principle/reflection supplier is separate from the proved
boundary inequality. Boundary zeros and root factorisation must be handled
when this target is discharged; they are not silently excluded. -/
def ReflectedPolarInterior_target : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n-1) → ℂ),
    2 ≤ n → p.Monic → p.natDegree = n → RootsInClosedDisc p 0 1 →
    CriticalEnumeration p c → ∀ z : ℂ, ‖z‖ ≤ 1 →
    ‖(n : ℂ)*p.eval z-z*p.derivative.eval z‖ ≤
      (n : ℝ)*∏ k, ‖1-conj (c k)*z‖

/-- The critical-value consumer with explicit analytic inputs. Its full
application, without those premises, is in PaperReflectedCompletion. -/
theorem reflectedCriticalValue_of_polar
    (hloc : CriticalDiscLocation_target) (hpolar : ReflectedPolarInterior_target) :
    ReflectedCriticalValue := by
  intro n p c hn hp hdeg hroots hc j
  have hcrit : p.derivative.eval (c j) = 0 := by
    change p.derivative = C (n : ℂ)*∏ k : Fin (n-1), (X-C (c k)) at hc
    rw [hc, eval_mul, eval_C, eval_prod]
    have hzero : (∏ k : Fin (n-1), (X-C (c k)).eval (c j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
    rw [hzero, mul_zero]
  have h := hpolar n p c hn hp hdeg hroots hc (c j)
    (hloc n p c hn hp hdeg hroots hc j)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hnC : ‖(n : ℂ)‖ = (n : ℝ) := by
    change ‖((n : ℝ) : ℂ)‖ = (n : ℝ)
    exact Complex.norm_of_nonneg (Nat.cast_nonneg n)
  rw [hcrit, mul_zero, sub_zero, Complex.norm_mul, hnC] at h
  nlinarith only [h, hnR]

#print axioms radial_fraction_identity
#print axioms product_log_derivative
#print axioms polar_boundary_of_roots
#print axioms reflectedCriticalValue_of_polar
end ErdosProblems.Erdos1041.PaperReflectedBoundary
