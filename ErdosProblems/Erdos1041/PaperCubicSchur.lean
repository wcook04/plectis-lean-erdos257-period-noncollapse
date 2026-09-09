import Mathlib
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperCubicFibres

/-!
# An algebraic supplier for the normalised cubic root count

Uncompiled candidates at the round-eight pin. No Rouché, homotopy, or
root-count conclusion is taken as a premise. The elementary degree-two Schur
inequality is applied to the reciprocals of two hypothetical exterior roots.
The resulting real polynomial certificate is displayed explicitly.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.PaperCubicSchur
open Polynomial Set PaperAnalyticTargets
open scoped ComplexConjugate

/-- The strict degree-two Schur inequality, proved directly from two roots. -/
theorem schur_pair (x y : ℂ) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    ‖x+y-conj (x+y)*(x*y)‖ < 1-(‖x‖*‖y‖)^2 := by
  have hx2 : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hy2 : 0 ≤ 1-‖y‖^2 := by nlinarith [norm_nonneg y]
  have hxy : ‖x‖*‖y‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg x) hx hy.le
  have hsum : ‖x‖+‖y‖ < 1+‖x‖*‖y‖ := by
    nlinarith only [mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)]
  have he : x+y-conj (x+y)*(x*y) =
      ((1-‖y‖^2 : ℝ) : ℂ)*x+((1-‖x‖^2 : ℝ) : ℂ)*y := by
    rw [Complex.sq_norm, Complex.sq_norm]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [map_add]
    ring
  calc
    ‖x+y-conj (x+y)*(x*y)‖ ≤
        (1-‖y‖^2)*‖x‖+(1-‖x‖^2)*‖y‖ := by
      rw [he]
      exact (norm_add_le _ _).trans_eq (by
        rw [norm_mul, norm_mul, Complex.norm_of_nonneg hy2,
          Complex.norm_of_nonneg hx2])
    _ = (‖x‖+‖y‖)*(1-‖x‖*‖y‖) := by ring
    _ < (1+‖x‖*‖y‖)*(1-‖x‖*‖y‖) :=
      mul_lt_mul_of_pos_right hsum (sub_pos.mpr hxy)
    _ = 1-(‖x‖*‖y‖)^2 := by ring

/-- A real certificate for the discriminant region. It is proved by a
factorisation with positive factors, rather than a numerical plot. -/
theorem discriminant_region (t X : ℝ) (ht : 1 < t) (ht3 : t < 3)
    (hX : t^3+2*t-1 < 2*t*X) :
    0 < 27*(t^3*(2*X^2-t^3-3*X+3)-X)-2*(t^3-2*X+1)^3 := by
  have ht0 : 0 < t := by linarith only [ht]
  have htm1 : 0 < t-1 := sub_pos.mpr ht
  let X0 := (t^3+2*t-1)/(2*t)
  have hXX0 : X0 < X := (div_lt_iff₀ (by positivity : 0 < 2*t)).mpr (by nlinarith only [hX])
  have hX0 : 1 < X0 := by
    have hid : X0-1 = (t-1)*(t^2+t+1)/(2*t) := by
      dsimp [X0]
      field_simp [ht0.ne']
      <;> ring
    have hpos : 0 < (t-1)*(t^2+t+1)/(2*t) := by positivity
    linarith only [hid, hpos]
  have hquad : 2*t^2-7*t+2 < 0 := by
    nlinarith only [mul_pos (sub_pos.mpr ht) (sub_pos.mpr ht3), ht3]
  let Q := fun Y : ℝ => -2*t^6+14*t^3*Y-37*t^3+16*Y^2+8*Y+1
  have hQ0 : 0 < Q X0 := by
    have hid : Q X0 =
        -(t-1)^3*(t+2)*(t^2+t+1)*(2*t^2-7*t+2)/t^2 := by
      dsimp [Q, X0]
      field_simp [ht0.ne']
      <;> ring
    rw [hid]
    have hpos : 0 < (t-1)^3*(t+2)*(t^2+t+1)*(-(2*t^2-7*t+2))/t^2 :=
      div_pos (mul_pos (by positivity) (neg_pos.mpr hquad)) (sq_pos_of_pos ht0)
    convert hpos using 1 <;> ring
  have hQdiff : Q X-Q X0 = 2*(X-X0)*(7*t^3+8*X+8*X0+4) := by
    dsimp [Q]
    ring
  have hQinc : 0 < Q X-Q X0 := by
    rw [hQdiff]
    have hXpos : 0 < X := by linarith only [hXX0, hX0]
    have hX0pos : 0 < X0 := by linarith only [hX0]
    exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hXX0)) (by positivity)
  have hQ : 0 < Q X := by linarith only [hQ0, hQinc]
  have ht3pos : 1 < t^3 := one_lt_pow₀ ht (by norm_num)
  have hfirst : 0 < t^3+X-2 := by linarith only [ht3pos, hX0, hXX0]
  convert mul_pos hfirst hQ using 1 <;> dsimp [Q] <;> ring

/-- The strict Schur constraint expressed through v=x+y. -/
theorem reciprocal_schur_region (x y : ℂ) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hprod : x*y*(x+y)=1) :
    1 < ‖x+y‖^2 ∧ ‖x+y‖^2 < 3 ∧
      (‖x+y‖^2)^3+2*‖x+y‖^2-1 < 2*‖x+y‖^2*((x+y)^3).re := by
  let v := x+y
  let R := ‖v‖
  let r := ‖x‖*‖y‖
  have hnorm : r*R=1 := by
    have h := congrArg norm hprod
    simpa only [norm_mul, norm_one, r, R, v] using h
  have hr0 : 0 ≤ r := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  have hR0 : 0 ≤ R := norm_nonneg v
  have hr1 : r < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg x) hx hy.le
  have hRp : 0 < R := by
    have hne : R ≠ 0 := by
      intro he
      rw [he,mul_zero] at hnorm
      norm_num at hnorm
    exact lt_of_le_of_ne hR0 (Ne.symm hne)
  have hR1 : 1 < R := by
    nlinarith only [hnorm, hr1, hR0,
      mul_pos (sub_pos.mpr hr1) hRp]
  have hsum : ‖x‖+‖y‖ < 1+r := by
    dsimp [r]
    nlinarith only [mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)]
  have htri : R ≤ ‖x‖+‖y‖ := norm_add_le x y
  have hR2 : R < 2 := by linarith only [htri, hx, hy]
  have hRbound : R^2 < R+1 := by
    have h := mul_lt_mul_of_pos_right (htri.trans_lt hsum) hRp
    nlinarith only [h, hnorm]
  have ht1 : 1 < R^2 := by nlinarith only [hR1]
  have ht3 : R^2 < 3 := by linarith only [hRbound, hR2]
  let e := ‖v-conj v*(x*y)‖
  have he : e < 1-r^2 := schur_pair x y hx hy
  have he0 : 0 ≤ e := norm_nonneg _
  have hid : v*(v-conj v*(x*y)) = v^2-conj v := by
    dsimp [v]
    calc
      (x+y)*(x+y-conj (x+y)*(x*y)) =
          (x+y)^2-conj (x+y)*(x*y*(x+y)) := by ring
      _ = (x+y)^2-conj (x+y) := by rw [hprod, mul_one]
  have hnid : R*e = ‖v^2-conj v‖ := by
    simpa only [norm_mul, R, e] using congrArg norm hid
  have hscaled : R^2*e < R^2-1 := by
    have h := mul_lt_mul_of_pos_left he (sq_pos_of_pos hRp)
    have h1 : R^2*r^2=1 := by nlinarith only [congrArg (fun a : ℝ => a^2) hnorm]
    nlinarith only [h, h1]
  have hscaled0 : 0 ≤ R^2*e := mul_nonneg (sq_nonneg _) he0
  have hsquare : (R^2*e)^2 < (R^2-1)^2 :=
    pow_lt_pow_left₀ hscaled hscaled0 (by norm_num)
  have hnsq : ‖v^2-conj v‖^2 = R^4+R^2-2*(v^3).re := by
    have hv : Complex.normSq v = R^2 := Complex.normSq_eq_norm_sq v
    rw [← Complex.normSq_eq_norm_sq]
    have hR4 : R^4=(Complex.normSq v)^2 := by rw [hv]; ring
    rw [hR4,← hv]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im, pow_succ, pow_zero, one_mul,
      Complex.mul_re, Complex.mul_im]
    ring
  have hnid2 : R^2*e^2 = ‖v^2-conj v‖^2 := by
    nlinarith only [congrArg (fun a : ℝ => a^2) hnid]
  have hleft : (R^2*e)^2 = R^2*(R^4+R^2-2*(v^3).re) := by
    calc
      (R^2*e)^2 = R^2*(R^2*e^2) := by ring
      _ = R^2*(R^4+R^2-2*(v^3).re) := by rw [hnid2, hnsq]
  rw [hleft] at hsquare
  refine ⟨ht1, ht3, ?_⟩
  change (R^2)^3+2*R^2-1 < 2*R^2*(v^3).re
  nlinarith only [hsquare]

/-- The scalar certificate controls the complex discriminant exactly. -/
theorem discriminant_lt_one (v a : ℂ) (hv : 1 < ‖v‖^2)
    (hv3 : ‖v‖^2 < 3)
    (hreg : (‖v‖^2)^3+2*‖v‖^2-1 < 2*‖v‖^2*(v^3).re)
    (ha : a*v=v^3-1) :
    ‖1-(4/27 : ℂ)*a^3‖ < 1 := by
  have hv0 : v ≠ 0 := by intro h; norm_num [h] at hv
  let w := v^3
  let T := ‖v‖^2
  have hwp : 0 < Complex.normSq w :=
    Complex.normSq_pos.mpr (pow_ne_zero _ hv0)
  have hnorm : Complex.normSq w = T^3 := by
    simp only [w, Complex.normSq_eq_norm_sq, norm_pow, T]
    ring
  have ha3 : a^3=(w-1)^3/w := by
    apply (eq_div_iff (pow_ne_zero 3 hv0)).mpr
    change a^3*v^3 = (v^3-1)^3
    rw [← mul_pow, ha]
  have hreal : (a^3).re = 2*w.re^2-Complex.normSq w-3*w.re+3-w.re/Complex.normSq w := by
    rw [ha3, Complex.div_re]
    field_simp [hwp.ne']
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, pow_succ, pow_zero, one_mul,
      Complex.mul_re, Complex.mul_im]
    ring
  have hsize : Complex.normSq (a^3) =
      (Complex.normSq w-2*w.re+1)^3/Complex.normSq w := by
    rw [ha3, Complex.normSq_div, map_pow]
    congr 1
    congr 1
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  have hD := discriminant_region T w.re hv hv3 hreg
  have hweighted :
      0 < 27*T^3*(a^3).re-2*T^3*Complex.normSq (a^3) := by
    rw [hreal, hsize, hnorm]
    have hT : T ≠ 0 := by
      intro hz
      rw [hz, zero_pow (by norm_num)] at hnorm
      exact hwp.ne' hnorm
    convert hD using 1 <;> field_simp [hT] <;> ring
  have hcore : 0 < 27*(a^3).re-2*Complex.normSq (a^3) := by
    have hid : 27*T^3*(a^3).re-2*T^3*Complex.normSq (a^3) =
        T^3*(27*(a^3).re-2*Complex.normSq (a^3)) := by ring
    rw [hid] at hweighted
    have hpT : 0 < T^3 := hnorm ▸ hwp
    by_contra hbad
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hpT.le (le_of_not_gt hbad)
    exact (not_lt_of_ge hnonpos) hweighted
  have hid : Complex.normSq (1-(4/27 : ℂ)*a^3) =
      1-(8/27 : ℝ)*(a^3).re+(16/729 : ℝ)*Complex.normSq (a^3) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im]
    norm_num
    ring
  have hs : ‖1-(4/27 : ℂ)*a^3‖^2 < 1 := by
    rw [← Complex.normSq_eq_norm_sq, hid]
    linarith only [hcore]
  nlinarith only [hs, norm_nonneg (1-(4/27 : ℂ)*a^3)]

/-- Two exterior roots of a cubic with zero linear coefficient force the
other critical value strictly inside the unit disc. -/
theorem two_exterior_force_discriminant (r s u a : ℂ)
    (hr : 1 < ‖r‖) (hs : 1 < ‖s‖)
    (hsum : r+s+u=a) (hpair : r*s+r*u+s*u=0) (hprod : r*s*u = -1) :
    ‖1-(4/27 : ℂ)*a^3‖ < 1 := by
  have hr0 : r ≠ 0 := by intro h; norm_num [h] at hr
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hp0 : r*s ≠ 0 := mul_ne_zero hr0 hs0
  have hsum2 : r+s=(r*s)^2 := by
    linear_combination -(r*s)*hpair+(r+s)*hprod
  let x := r⁻¹
  let y := s⁻¹
  have hx : ‖x‖ < 1 := by
    change ‖r⁻¹‖<1
    rw [norm_inv,← one_div]
    exact (div_lt_one (norm_pos_iff.mpr hr0)).mpr hr
  have hy : ‖y‖ < 1 := by
    change ‖s⁻¹‖<1
    rw [norm_inv,← one_div]
    exact (div_lt_one (norm_pos_iff.mpr hs0)).mpr hs
  have hv : x+y=r*s := by
    dsimp [x,y]
    field_simp [hr0,hs0]
    linear_combination hsum2
  have hxy : x*y*(x+y)=1 := by
    rw [hv]
    dsimp [x,y]
    field_simp [hr0,hs0]
  have ha : a*(x+y)=(x+y)^3-1 := by
    rw [hv,← hsum]
    linear_combination (r*s)*hsum2+hprod
  obtain ⟨h1,h3,hreg⟩ := reciprocal_schur_region x y hx hy hxy
  exact discriminant_lt_one (x+y) a h1 h3 hreg ha

/-- The repeated-root case lies on the excluded discriminant value. -/
theorem repeated_forces_discriminant (r u a : ℂ)
    (hsum : r+r+u=a) (hpair : r*r+r*u+r*u=0) (hprod : r*r*u = -1) :
    1-(4/27 : ℂ)*a^3=0 := by
  have hr : r ≠ 0 := by intro h; simp [h] at hprod
  have hlu : r+2*u=0 := by
    apply (mul_eq_zero.mp (show r*(r+2*u)=0 by linear_combination hpair)).resolve_left hr
  have hu : u = -r/2 := by linear_combination hlu/2
  have ha : a = 3*r/2 := by rw [hu] at hsum; linear_combination -hsum
  rw [ha]
  rw [hu] at hprod
  linear_combination hprod

/-- Three scalar values of a factorisation determine the cubic Vieta data. -/
theorem cubic_vieta (a r s u : ℂ)
    (hf : ∀ z : ℂ, z^3-a*z^2+1=(z-r)*(z-s)*(z-u)) :
    r+s+u=a ∧ r*s+r*u+s*u=0 ∧ r*s*u = -1 := by
  have h0 := hf 0
  have h1 := hf 1
  have hm := hf (-1)
  constructor
  · linear_combination (h1+hm)/2-h0
  constructor
  · linear_combination (hm-h1)/2
  · linear_combination h0

/-- B5's exact previously analytic root-count target, supplied algebraically. -/
theorem cubic_root_count : CubicRootCount := by
  intro b hb
  let a : ℂ := (3/2 : ℂ)*b
  let P : ℂ[X] := X^3+(C (-a)*X^2+C 1)
  have hsmall : (C (-a)*X^2+C 1 : ℂ[X]).degree < (X^3 : ℂ[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt (degree_add_le _ _ |>.trans (max_le
      (degree_C_mul_X_pow_le 2 (-a)) (degree_C_le.trans (by norm_num)))) (by norm_num)
  have hmonic : P.Monic := (monic_X_pow 3).add_of_left hsmall
  have hdeg : P.natDegree=3 := by
    apply natDegree_eq_of_degree_eq_some
    change (X^3+(C (-a)*X^2+C 1) : ℂ[X]).degree = _
    rw [degree_add_eq_left_of_degree_lt hsmall,degree_X_pow] <;> simp
  obtain ⟨r,s,u,hf⟩ := PaperCubicFibres.monic_cubic_factorisation P hmonic hdeg
  have hfac : ∀ z : ℂ, z^3-a*z^2+1=(z-r)*(z-s)*(z-u) := by
    intro z
    simpa only [P,eval_add,eval_mul,eval_C,eval_pow,eval_X,
      neg_mul,sub_eq_add_neg,add_assoc,PaperCubicFibres.cubic] using hf z
  obtain ⟨hsum,hpair,hprod⟩ := cubic_vieta a r s u hfac
  have hdisc : 1 ≤ ‖1-(4/27 : ℂ)*a^3‖ := by
    have he : 1-(4/27 : ℂ)*a^3=1-b^3/2 := by dsimp [a]; ring
    rwa [he]
  have hrs : r ≠ s := by
    intro h; subst s
    have hzero := repeated_forces_discriminant r u a hsum hpair hprod
    rw [hzero,norm_zero] at hdisc
    linarith only [hdisc]
  have hru : r ≠ u := by
    intro h; subst u
    have hzero := repeated_forces_discriminant r s a
      (by linear_combination hsum) (by linear_combination hpair) (by linear_combination hprod)
    rw [hzero,norm_zero] at hdisc
    linarith only [hdisc]
  have hsu : s ≠ u := by
    intro h; subst u
    have hzero := repeated_forces_discriminant s r a
      (by linear_combination hsum) (by linear_combination hpair) (by linear_combination hprod)
    rw [hzero,norm_zero] at hdisc
    linarith only [hdisc]
  have hrroot : r^3-(3/2 : ℂ)*b*r^2+1=0 := by simpa only [a,sub_self,zero_mul] using hfac r
  have hsroot : s^3-(3/2 : ℂ)*b*s^2+1=0 := by simpa only [a,sub_self,mul_zero,zero_mul] using hfac s
  have huroot : u^3-(3/2 : ℂ)*b*u^2+1=0 := by simpa only [a,sub_self,mul_zero] using hfac u
  have hnotrs : ¬ (1 < ‖r‖ ∧ 1 < ‖s‖) := fun h =>
    (two_exterior_force_discriminant r s u a h.1 h.2 hsum hpair hprod).not_ge hdisc
  have hnotru : ¬ (1 < ‖r‖ ∧ 1 < ‖u‖) := fun h =>
    (two_exterior_force_discriminant r u s a h.1 h.2
      (by linear_combination hsum) (by linear_combination hpair) (by linear_combination hprod)).not_ge hdisc
  have hnotsu : ¬ (1 < ‖s‖ ∧ 1 < ‖u‖) := fun h =>
    (two_exterior_force_discriminant s u r a h.1 h.2
      (by linear_combination hsum) (by linear_combination hpair) (by linear_combination hprod)).not_ge hdisc
  by_cases hr : ‖r‖ ≤ 1
  · by_cases hs : ‖s‖ ≤ 1
    · exact ⟨r,s,hrs,hr,hs,hrroot,hsroot⟩
    · have hu : ‖u‖ ≤ 1 := le_of_not_gt (fun hu => hnotsu ⟨lt_of_not_ge hs,hu⟩)
      exact ⟨r,u,hru,hr,hu,hrroot,huroot⟩
  · have hs : ‖s‖ ≤ 1 := le_of_not_gt (fun hs => hnotrs ⟨lt_of_not_ge hr,hs⟩)
    have hu : ‖u‖ ≤ 1 := le_of_not_gt (fun hu => hnotru ⟨lt_of_not_ge hr,hu⟩)
    exact ⟨s,u,hsu,hs,hu,hsroot,huroot⟩

end ErdosProblems.Erdos1041.PaperCubicSchur
