import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Complex.AbsMax
import ErdosProblems.Erdos1041.PaperReflectedBoundary

/-!
# The complete reflected-derivative inequality

Source candidate, not elaborated in the preparation environment.
Lean 4.29.1; Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6.

The two targets left open in PaperReflectedBoundary are proved here.
The denominator is regularised as prod(t-conj(c_k)*z), t>1, before maximum
modulus is applied. It is zero-free on the CLOSED unit disc, including when
some critical points lie on the unit circle. Passing t down to one avoids
assuming away boundary zeros or assuming a removable-singularity theorem.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.PaperReflectedCompletion
open Polynomial Set Filter Metric Bornology PaperAnalyticTargets
open PaperReflectedBoundary
open scoped BigOperators ComplexConjugate Topology

-- Mathlib/Algebra/Polynomial/Eval/Defs.lean: eval_prod, eval_mul, eval_C.
-- Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean: prod_eq_zero.
theorem listed_critical_is_root {n : ℕ} {p : ℂ[X]}
    {c : Fin (n-1) → ℂ} (hc : CriticalEnumeration p c) (j : Fin (n-1)) :
    p.derivative.eval (c j) = 0 := by
  change p.derivative = C (n : ℂ) * ∏ k, (X-C (c k)) at hc
  rw [hc, eval_mul, eval_C, eval_prod]
  have hzero : (∏ k : Fin (n-1), (X-C (c k)).eval (c j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  rw [hzero, mul_zero]

-- Mathlib/Analysis/Complex/Polynomial/GaussLucas.lean:
-- Polynomial.rootSet_derivative_subset_convexHull_rootSet.
-- Mathlib/Algebra/Polynomial/Roots.lean: mem_rootSet, coe_aeval_eq_eval.
-- Mathlib/Algebra/Polynomial/Derivative.lean:
-- natDegree_eq_zero_of_derivative_eq_zero.
-- Mathlib/Analysis/Convex/Hull.lean: convexHull_min.
-- Mathlib/Analysis/Normed/Module/Convex.lean: convex_closedBall.
/-- The exact critical-disc target, including boundary and multiple roots. -/
theorem critical_disc_location : CriticalDiscLocation_target := by
  intro n p c hn hp hdeg hroots hc j
  have hpos : 0 < p.natDegree := by omega
  have hdegree : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hpos
  have hpd : p.derivative ≠ 0 := by
    intro he
    have hz : p.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero he
    omega
  have hjroot : c j ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hpd, listed_critical_is_root hc j⟩
  have hsub : p.rootSet ℂ ⊆ closedBall (0 : ℂ) 1 := by
    intro z hz
    have hz' : p ≠ 0 ∧ p.eval z = 0 := by
      simpa only [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] using hz
    have hb : ‖z-0‖ ≤ 1 := hroots z hz'.2
    simpa only [mem_closedBall, dist_eq_norm] using hb
  have hconv : convexHull ℝ (p.rootSet ℂ) ⊆ closedBall (0 : ℂ) 1 :=
    convexHull_min hsub (convex_closedBall (0 : ℂ) (1 : ℝ))
  have hj : c j ∈ closedBall (0 : ℂ) 1 :=
    hconv (Polynomial.rootSet_derivative_subset_convexHull_rootSet hdegree hjroot)
  simpa only [mem_closedBall, dist_zero_right] using hj

-- Mathlib/Algebra/Polynomial/Splits.lean:
-- Splits.eq_prod_roots_of_monic, Polynomial.splits_iff_card_roots.
-- Mathlib/Algebra/BigOperators/Fin.lean: Fin.prod_univ_fun_getElem.
-- Mathlib/Data/Multiset/Basic.lean: coe_toList.
/-- Remove the auxiliary root enumeration from the boundary estimate. -/
theorem polar_boundary (n : ℕ) (p : ℂ[X]) (hp : p.Monic)
    (hdeg : p.natDegree = n) (hroots : RootsInClosedDisc p 0 1)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(n : ℂ)*p.eval z-z*p.derivative.eval z‖ ≤ ‖p.derivative.eval z‖ := by
  classical
  let l : List ℂ := p.roots.toList
  let a : Fin l.length → ℂ := fun i => l[i.val]
  have hl : l.length = n := by
    have hcard : p.roots.card = p.natDegree :=
      Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p)
    simpa [l, hdeg] using hcard
  have hfactor : p = ∏ i : Fin l.length, (X-C (a i)) := by
    rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp]
    have ht := Fin.prod_univ_fun_getElem l (fun x : ℂ => (X-C x : ℂ[X]))
    simpa only [a, l, ← Multiset.prod_coe, ← Multiset.map_coe,
      Multiset.coe_toList] using ht.symm
  have ha : ∀ i, ‖a i‖ ≤ 1 := by
    intro i
    have hz0 : p.eval (a i) = 0 := by
      rw [hfactor, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    simpa only [sub_zero] using hroots (a i) hz0
  have h := polar_boundary_of_roots l.length a ha z hz
  rw [← hfactor, hl] at h
  exact h

-- Mathlib/Analysis/Complex/Norm.lean: normSq_eq_norm_sq.
-- Mathlib/Data/Complex/Basic.lean: normSq_apply and conjugation formulae.
/-- Reflection on the unit circle, expressed without division. -/
theorem reflected_factor_norm (c z : ℂ) (hz : ‖z‖ = 1) :
    ‖z-c‖ = ‖1-conj c*z‖ := by
  have hzsq : z.re^2+z.im^2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simpa only [Complex.normSq_apply, one_pow, pow_two, one_mul] using h
  have hs : ‖z-c‖^2 = ‖1-conj c*z‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    nlinarith only [hzsq,
      congrArg (fun x : ℝ => (c.re^2+c.im^2)*x) hzsq]
  nlinarith only [hs, norm_nonneg (z-c), norm_nonneg (1-conj c*z)]

-- Mathlib/Analysis/Complex/Norm.lean: re_le_norm, normSq_eq_norm_sq.
/-- Moving the positive real endpoint outward increases distance from
any point of the unit disc. -/
theorem regularised_factor_norm (x : ℂ) (hx : ‖x‖ ≤ 1)
    (t : ℝ) (ht : 1 ≤ t) : ‖1-x‖ ≤ ‖(t : ℂ)-x‖ := by
  have hre : x.re ≤ 1 := (Complex.re_le_norm x).trans hx
  have hprod : 0 ≤ (t-1)*(t+1-2*x.re) :=
    mul_nonneg (sub_nonneg.mpr ht) (by linarith only [ht, hre])
  have he : Complex.normSq ((t : ℂ)-x)-Complex.normSq (1-x) =
      (t-1)*(t+1-2*x.re) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  rw [← he, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hprod
  nlinarith only [hprod, norm_nonneg ((t : ℂ)-x), norm_nonneg (1-x)]

/-- The regularised reflected denominator. -/
def regularised {m : ℕ} (c : Fin m → ℂ) (t : ℝ) : ℂ[X] :=
  ∏ k, (C (t : ℂ)-C (conj (c k))*X)

theorem regularised_eval {m : ℕ} (c : Fin m → ℂ) (t : ℝ) (z : ℂ) :
    (regularised c t).eval z = ∏ k, ((t : ℂ)-conj (c k)*z) := by
  simp only [regularised, eval_prod, eval_sub, eval_C, eval_mul, eval_X]

/-- Zero-freeness on the closed disc, not just its interior. -/
theorem regularised_ne_zero {m : ℕ} (c : Fin m → ℂ)
    (hc : ∀ k, ‖c k‖ ≤ 1) (t : ℝ) (ht : 1 < t)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : (regularised c t).eval z ≠ 0 := by
  rw [regularised_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hmul : ‖conj (c k)*z‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (hc k) (norm_nonneg z) hz
  intro hzero
  have he : (t : ℂ) = conj (c k)*z := sub_eq_zero.mp hzero
  have hnorm : t = ‖conj (c k)*z‖ := by
    have h := congrArg norm he
    simpa only [Complex.norm_of_nonneg (by linarith only [ht] : 0 ≤ t)] using h
  linarith only [hnorm, hmul, ht]

-- Mathlib/Analysis/Complex/AbsMax.lean:
-- Complex.norm_le_of_forall_mem_frontier_norm_le.
-- Mathlib/Analysis/Calculus/DiffContOnCl.lean: DiffContOnCl.
-- Mathlib/Analysis/Calculus/Deriv/Polynomial.lean: differentiableAt.
-- Mathlib/Analysis/Normed/Module/RCLike/Real.lean: closure_ball, frontier_ball.
-- Mathlib/Topology/Order/Closed.lean: le_of_tendsto.
/-- A closed-disc maximum-modulus comparison allowing boundary zeros in
all reflected factors. No root, simplicity or strict-radius assumption. -/
theorem reflected_product_domination {m : ℕ} (U : ℂ[X]) (c : Fin m → ℂ)
    (hc : ∀ k, ‖c k‖ ≤ 1) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ z : ℂ, ‖z‖ = 1 →
      ‖U.eval z‖ ≤ K*∏ k, ‖1-conj (c k)*z‖)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖U.eval z‖ ≤ K*∏ k, ‖1-conj (c k)*z‖ := by
  have hreg (t : ℝ) (ht : 1 < t) :
      ‖U.eval z‖ ≤ K*∏ k, ‖(t : ℂ)-conj (c k)*z‖ := by
    let Q : ℂ[X] := regularised c t
    let F : ℂ → ℂ := fun w => U.eval w / Q.eval w
    have hnz (w : ℂ) (hw : ‖w‖ ≤ 1) : Q.eval w ≠ 0 :=
      regularised_ne_zero c hc t ht w hw
    have hdc : DiffContOnCl ℂ F (ball (0 : ℂ) 1) := by
      constructor
      · intro w hw
        have hw' : ‖w‖ ≤ 1 := (by simpa only [mem_ball, dist_zero_right] using hw : ‖w‖ < 1).le
        exact (U.differentiableAt.div Q.differentiableAt (hnz w hw')).differentiableWithinAt
      · intro w hw
        have hw' : ‖w‖ ≤ 1 := by
          simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
            mem_closedBall, dist_zero_right] using hw
        exact (U.differentiableAt.div Q.differentiableAt (hnz w hw')).continuousAt.continuousWithinAt
    have hbound : ∀ w ∈ frontier (ball (0 : ℂ) 1), ‖F w‖ ≤ K := by
      intro w hw
      have hw' : ‖w‖ = 1 := by
        simpa only [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
          mem_sphere, dist_zero_right] using hw
      have hprod : (∏ k, ‖1-conj (c k)*w‖) ≤ ∏ k, ‖(t : ℂ)-conj (c k)*w‖ := by
        apply Finset.prod_le_prod
        · intro k hk; exact norm_nonneg _
        · intro k hk
          apply regularised_factor_norm _ _ t ht.le
          rw [norm_mul, Complex.norm_conj, hw', mul_one]
          exact hc k
      have hu : ‖U.eval w‖ ≤ K*‖Q.eval w‖ := by
        calc
          ‖U.eval w‖ ≤ K*∏ k, ‖1-conj (c k)*w‖ := hb w hw'
          _ ≤ K*∏ k, ‖(t : ℂ)-conj (c k)*w‖ := mul_le_mul_of_nonneg_left hprod hK
          _ = K*‖Q.eval w‖ := by simp only [Q, regularised_eval, norm_prod]
      have hnorm : 0 < ‖Q.eval w‖ := norm_pos_iff.mpr (hnz w hw'.le)
      change ‖U.eval w / Q.eval w‖ ≤ K
      rw [norm_div]
      exact (div_le_iff₀ hnorm).mpr hu
    have hzcl : z ∈ closure (ball (0 : ℂ) 1) := by
      simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
        mem_closedBall, dist_zero_right] using hz
    have hf : ‖F z‖ ≤ K := Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_ball : IsBounded (ball (0 : ℂ) (1 : ℝ))) hdc hbound hzcl
    change ‖U.eval z/Q.eval z‖ ≤ K at hf
    rw [norm_div] at hf
    have hu := (div_le_iff₀ (norm_pos_iff.mpr (hnz z hz))).mp hf
    simpa only [Q, regularised_eval, norm_prod] using hu
  have hcont : Continuous (fun t : ℝ => K*∏ k, ‖(t : ℂ)-conj (c k)*z‖) := by
    fun_prop
  have hlim : Tendsto (fun t : ℝ => K*∏ k, ‖(t : ℂ)-conj (c k)*z‖)
      (𝓝[>] (1 : ℝ)) (𝓝 (K*∏ k, ‖1-conj (c k)*z‖)) := by
    simpa only [Complex.ofReal_one] using
      (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun t : ℝ => K*∏ k, ‖(t : ℂ)-conj (c k)*z‖)
          (𝓝[>] (1 : ℝ)) (𝓝 (K*∏ k, ‖((1 : ℝ) : ℂ)-conj (c k)*z‖)))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hreg t ht

/-- The complete polar-interior supplier; all its former premises are
proved above from the original polynomial hypotheses. -/
theorem reflected_polar_interior : ReflectedPolarInterior_target := by
  intro n p c hn hp hdeg hroots hc z hz
  let U : ℂ[X] := C (n : ℂ)*p-X*p.derivative
  have hU (w : ℂ) : U.eval w = (n : ℂ)*p.eval w-w*p.derivative.eval w := by
    simp only [U, eval_sub, eval_mul, eval_C, eval_X]
  have hloc := critical_disc_location n p c hn hp hdeg hroots hc
  have hb : ∀ w : ℂ, ‖w‖ = 1 → ‖U.eval w‖ ≤ (n : ℝ)*∏ k, ‖1-conj (c k)*w‖ := by
    intro w hw
    rw [hU]
    calc
      ‖(n : ℂ)*p.eval w-w*p.derivative.eval w‖ ≤ ‖p.derivative.eval w‖ :=
        polar_boundary n p hp hdeg hroots w hw
      _ = (n : ℝ)*∏ k, ‖1-conj (c k)*w‖ := by
        change p.derivative = C (n : ℂ)*∏ k, (X-C (c k)) at hc
        rw [hc, eval_mul, eval_C, eval_prod, norm_mul, norm_prod]
        simp only [eval_sub, eval_X, eval_C, Complex.norm_natCast]
        congr 1
        apply Finset.prod_congr rfl
        intro k hk
        exact reflected_factor_norm (c k) w hw
  simpa only [hU] using reflected_product_domination U c hloc (n : ℝ)
    (Nat.cast_nonneg n) hb z hz

/-- B4, against the exact desk target. No new analytic premise. -/
theorem reflected_critical_value : ReflectedCriticalValue :=
  reflectedCriticalValue_of_polar critical_disc_location reflected_polar_interior

end ErdosProblems.Erdos1041.PaperReflectedCompletion
