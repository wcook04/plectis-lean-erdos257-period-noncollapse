import Mathlib
import ErdosProblems.Erdos1041.PaperCubicSchur
import ErdosProblems.Erdos1041.PaperReflectedCompletion
import ErdosProblems.Erdos1041.CubicCriticalHub

/-!
# The complete cubic polygonal connector

Uncompiled proof candidates. The root-count supplier is proved algebraically
in PaperCubicSchur. The existence of a small critical value is derived from
the completed reflected inequality, not from an assumed component lemma.
Repeated critical points and repeated roots are retained separately.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.PaperCubicCompletion
open Polynomial Set Function PaperAnalyticTargets PaperCurve
open PaperReflectedCompletion
open scoped ComplexConjugate BigOperators

/-- Original root occurrences give the coefficient presentation exactly. -/
theorem cubic_coefficients (p : ℂ[X]) (z : Fin 3 → ℂ) (hp : RootEnumeration p z) :
    ∃ A B C : ℂ, p=X^3+Polynomial.C A*X^2+Polynomial.C B*X+Polynomial.C C := by
  refine ⟨-(z 0+z 1+z 2), z 0*z 1+z 0*z 2+z 1*z 2, -(z 0*z 1*z 2), ?_⟩
  change p=∏i, (X-Polynomial.C (z i)) at hp
  rw [hp,Fin.prod_univ_three]
  simp only [map_neg,map_add,map_mul]
  ring

/-- Evaluation and derivative formulae, without analytic premises. -/
theorem cubic_formulas (p : ℂ[X]) (A B C : ℂ)
    (hp : p=X^3+Polynomial.C A*X^2+Polynomial.C B*X+Polynomial.C C) (x : ℂ) :
    p.eval x=x^3+A*x^2+B*x+C ∧ p.derivative.eval x=3*x^2+2*A*x+B := by
  rw [hp]
  constructor <;> simp <;> ring

/-- A cubic's two critical occurrences are explicitly constructed by a
complex square root. Their enumeration is an exact polynomial identity. -/
theorem critical_pair (p : ℂ[X]) (A B C : ℂ)
    (hp : p=X^3+Polynomial.C A*X^2+Polynomial.C B*X+Polynomial.C C) :
    ∃ c : Fin 2 → ℂ, CriticalEnumeration (n := 3) p c ∧
      c 0+c 1=-(2/3 : ℂ)*A := by
  obtain ⟨d,hd⟩ := PaperCubicFibres.exists_nth_root (q := 2) (by norm_num)
    (A^2/9-B/3)
  let h : ℂ := -A/3
  let c : Fin 2 → ℂ := ![h+d,h-d]
  refine ⟨c, ?_, ?_⟩
  · change p.derivative=Polynomial.C (3 : ℂ)*∏j : Fin 2, (X-Polynomial.C (c j))
    apply Polynomial.funext
    intro x
    rw [(cubic_formulas p A B C hp x).2]
    simp only [eval_mul,eval_C,eval_prod,Fin.prod_univ_two,
      eval_sub,eval_X]
    change 3*x^2+2*A*x+B=3*((x-(h+d))*(x-(h-d)))
    dsimp [h]
    linear_combination (3 : ℂ)*hd
  · dsimp [c,h]
    ring

/-- The supplied root enumeration entails monicity, degree and all roots. -/
theorem enumeration_facts (p : ℂ[X]) (z : Fin 3 → ℂ) (hp : RootEnumeration p z) :
    p.Monic ∧ p.natDegree=3 ∧ (∀ x : ℂ, p.eval x=0 ↔ ∃ i, z i=x) := by
  change p=∏i, (X-C (z i)) at hp
  constructor
  · rw [hp]
    exact Polynomial.monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (z i))
  constructor
  · rw [hp,natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (z i))]
    simp
  · intro x
    rw [hp,eval_prod]
    simp only [eval_sub,eval_X,eval_C]
    rw [Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ,true_and,sub_eq_zero,eq_comm]

/-- No common root with the derivative under injectivity of the three
listed occurrences. This is proved by the product formula in degree three. -/
theorem derivative_at_root_ne_zero (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : RootEnumeration p z) (hz : Injective z) (i : Fin 3) :
    p.derivative.eval (z i) ≠ 0 := by
  have h01 : z 0 ≠ z 1 := hz.ne (by decide)
  have h02 : z 0 ≠ z 2 := hz.ne (by decide)
  have h12 : z 1 ≠ z 2 := hz.ne (by decide)
  change p=∏j, (X-C (z j)) at hp
  fin_cases i <;>
    simp [hp,Fin.prod_univ_three,sub_eq_zero,h01,h02,h12,
      Ne.symm h01,Ne.symm h02,Ne.symm h12]

/-- The open root hypothesis gives |p(0)|<1, including zero roots. -/
theorem cubic_constant_lt (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : RootEnumeration p z) (hz : ∀i, ‖z i‖<1) : ‖p.eval 0‖<1 := by
  change p=∏j, (X-C (z j)) at hp
  rw [hp,eval_prod,Fin.prod_univ_three]
  simp only [eval_sub,eval_X,eval_C,zero_sub,norm_mul,norm_neg]
  apply mul_lt_one_of_nonneg_of_lt_one_left
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hz 0) (hz 1).le
  · exact (hz 2).le

/-- Maximal critical-point modulus yields strictness in degree three. -/
theorem max_critical_value_lt (c d v : ℂ) (hc : ‖c‖≤1) (hd : ‖d‖≤‖c‖)
    (hc0 : c ≠ 0)
    (hb : ‖v‖≤‖1-conj c*c‖*‖1-conj d*c‖) : ‖v‖<1 := by
  have hnonneg : 0≤1-‖c‖^2 := by nlinarith [norm_nonneg c]
  have hself : ‖1-conj c*c‖=1-‖c‖^2 := by
    have he : 1-conj c*c=((1-‖c‖^2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    rw [he,Complex.norm_of_nonneg hnonneg]
  have hother : ‖1-conj d*c‖≤1+‖c‖^2 := by
    calc
      ‖1-conj d*c‖≤1+‖d‖*‖c‖ := by
        simpa only [norm_one,norm_mul,Complex.norm_conj] using norm_sub_le (1 : ℂ) (conj d*c)
      _ ≤ 1+‖c‖^2 := by nlinarith only [mul_le_mul_of_nonneg_right hd (norm_nonneg c)]
  have hbound : ‖v‖≤1-‖c‖^4 := by
    calc
      ‖v‖≤‖1-conj c*c‖*‖1-conj d*c‖ := hb
      _ ≤ (1-‖c‖^2)*(1+‖c‖^2) := by
        rw [hself]
        exact mul_le_mul_of_nonneg_left hother hnonneg
      _ = 1-‖c‖^4 := by ring
  have hp : 0<‖c‖^4 := pow_pos (norm_pos_iff.mpr hc0) _
  linarith only [hbound,hp]

/-- Actual small-critical-value existence for a cubic; no component lemma. -/
theorem cubic_small_critical (p : ℂ[X]) (z : Fin 3 → ℂ) (c : Fin 2 → ℂ)
    (hp : RootEnumeration p z) (hz : ∀i, ‖z i‖<1)
    (hc : CriticalEnumeration (n := 3) p c) :
    ∃ j : Fin 2, ‖p.eval (c j)‖<1 := by
  obtain ⟨hmonic,hdeg,hroots⟩ := enumeration_facts p z hp
  have hclosed : RootsInClosedDisc p 0 1 := by
    intro x hx
    obtain ⟨i,rfl⟩ := (hroots x).mp hx
    simpa only [sub_zero] using (hz i).le
  have hloc := critical_disc_location 3 p c (by norm_num) hmonic hdeg hclosed hc
  have href := reflected_critical_value 3 p c (by norm_num) hmonic hdeg hclosed hc
  by_cases h00 : c 0=0 ∧ c 1=0
  · refine ⟨0, ?_⟩
    rw [h00.1]
    exact cubic_constant_lt p z hp hz
  by_cases hle : ‖c 1‖≤‖c 0‖
  · have hc0 : c 0 ≠ 0 := by
      intro he
      have hn : ‖c 1‖≤0 := by simpa only [he,norm_zero] using hle
      have hc1 : c 1=0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
      exact h00 ⟨he,hc1⟩
    refine ⟨0,max_critical_value_lt (c 0) (c 1) (p.eval (c 0)) (hloc 0) hle hc0 ?_⟩
    have hb := href 0
    change ‖p.eval (c 0)‖ ≤ ∏ k : Fin 2, ‖1-conj (c k)*c 0‖ at hb
    simpa only [Fin.prod_univ_two] using hb
  · have hc1 : c 1 ≠ 0 := by
      intro he
      have hh : ‖c 1‖≤‖c 0‖ := by rw [he,norm_zero]; exact norm_nonneg _
      exact hle hh
    refine ⟨1,max_critical_value_lt (c 1) (c 0) (p.eval (c 1)) (hloc 1)
      (le_of_not_ge hle) hc1 ?_⟩
    have hb := href 1
    change ‖p.eval (c 1)‖ ≤ ∏ k : Fin 2, ‖1-conj (c k)*c 1‖ at hb
    simpa only [Fin.prod_univ_two,mul_comm] using hb

/-- A critical point and the other critical occurrence determine the
entire translated cubic, including the repeated-critical case. -/
theorem expansion_at_critical (p : ℂ[X]) (A B C c d : ℂ)
    (hp : p=X^3+Polynomial.C A*X^2+Polynomial.C B*X+Polynomial.C C)
    (hc : p.derivative.eval c=0) (hsum : c+d=-(2/3 : ℂ)*A) (x : ℂ) :
    p.eval (c+x)=x^3-(3/2 : ℂ)*(d-c)*x^2+p.eval c := by
  rw [(cubic_formulas p A B C hp c).2] at hc
  rw [(cubic_formulas p A B C hp (c+x)).1,(cubic_formulas p A B C hp c).1]
  linear_combination x*hc+(3/2 : ℂ)*x^2*hsum

/-- The algebraic root-count supplier now produces a genuine polygonal
hub. There is no supplied root pair, curve, or metric budget in this lemma. -/
theorem hub_from_critical_expansion (p : ℂ[X]) (c δ v : ℂ)
    (hv0 : v ≠ 0) (hv : ‖v‖<1)
    (hform : ∀x : ℂ, p.eval (c+x)=x^3-(3/2 : ℂ)*δ*x^2+v)
    (hmin : ‖v‖≤‖p.eval (c+δ)‖) :
    ∃ a b : ℂ, a ≠ b ∧ p.eval a=0 ∧ p.eval b=0 ∧ HubBelow p.eval 1 2 a c b := by
  obtain ⟨α,hα⟩ := PaperCubicFibres.exists_nth_root (q := 3) (by norm_num) v
  have hα0 : α ≠ 0 := by intro he; rw [he,zero_pow (by norm_num)] at hα; exact hv0 hα.symm
  have hαn : ‖α‖<1 := by
    have hh : ‖α‖^3=‖v‖ := by simpa only [norm_pow] using congrArg norm hα
    by_contra hn
    have : 1≤‖α‖^3 := one_le_pow₀ (le_of_not_gt hn)
    linarith only [hh,this,hv]
  let B : ℂ := δ/α
  have hpull (w : ℂ) : p.eval (c+α*w)=v*normalizedCubic B w := by
    rw [hform,← hα]
    dsimp [normalizedCubic,B]
    field_simp [hα0]
    <;> ring
  have hother : p.eval (c+δ)=v*(1-B^3/2) := by
    rw [hform,← hα]
    dsimp [B]
    field_simp [hα0]
    <;> ring
  have hB : 1≤‖1-B^3/2‖ := by
    rw [hother,norm_mul] at hmin
    have hvp : 0<‖v‖ := norm_pos_iff.mpr hv0
    by_contra hlt
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hlt) hvp
    simp only [mul_one] at hh
    exact hh.not_ge hmin
  obtain ⟨u,w,huw,hu,hw,huroot,hwroot⟩ := PaperCubicSchur.cubic_root_count B hB
  have hur : normalizedCubic B u=0 := huroot
  have hwr : normalizedCubic B w=0 := hwroot
  have ha : p.eval (c+α*u)=0 := by rw [hpull,hur,mul_zero]
  have hb : p.eval (c+α*w)=0 := by rw [hpull,hwr,mul_zero]
  have hab : c+α*u ≠ c+α*w := by
    intro he
    exact huw ((mul_left_cancel₀ hα0) (add_left_cancel he))
  have hspoke (q : ℂ) (hq : normalizedCubic B q=0) (hqn : ‖q‖≤1)
      (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
      ‖p.eval (c+(t : ℂ)*((c+α*q)-c))‖<1 := by
    have he : c+(t : ℂ)*((c+α*q)-c)=c+α*((t : ℂ)*q) := by ring
    rw [he,hpull,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg v)
      (normalizedCubic_spoke_norm_le_one hq hqn ht0 ht1)).trans_lt hv
  have hlength : ‖c-(c+α*u)‖+‖(c+α*w)-c‖<2 := by
    have he1 : c-(c+α*u)=-(α*u) := by ring
    have he2 : (c+α*w)-c=α*w := by ring
    rw [he1,he2,norm_neg]
    exact two_small_normalized_roots_give_short_hub hαn hu hw
  exact ⟨c+α*u,c+α*w,hab,ha,hb,
    hubBelow_of_spokes (hspoke u hur hu) (hspoke w hwr hw) hlength⟩

/-- The main distinct-root construction, with every supplier discharged. -/
theorem cubic_distinct_hub (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : RootEnumeration p z) (hz : ∀i, ‖z i‖<1) (hinj : Injective z) :
    ∃ i j : Fin 3, ∃ c : ℂ, i ≠ j ∧ z i ≠ z j ∧ HubBelow p.eval 1 2 (z i) c (z j) := by
  obtain ⟨A,B,C,hpoly⟩ := cubic_coefficients p z hp
  obtain ⟨c,hcrit,hsum⟩ := critical_pair p A B C hpoly
  obtain ⟨k,hsmall⟩ := cubic_small_critical p z c hp hz hcrit
  have hrootcrit (i : Fin 2) : p.derivative.eval (c i)=0 := listed_critical_is_root hcrit i
  have hnz (i : Fin 2) : p.eval (c i) ≠ 0 := by
    intro he
    obtain ⟨j,hj⟩ := ((enumeration_facts p z hp).2.2 (c i)).mp he
    have hne := derivative_at_root_ne_zero p z hp hinj j
    apply hne
    simpa only [hj] using hrootcrit i
  have hpair : ∃ i j : Fin 2,
      c i+c j=-(2/3 : ℂ)*A ∧ ‖p.eval (c i)‖<1 ∧ ‖p.eval (c i)‖≤‖p.eval (c j)‖ := by
    by_cases hle : ‖p.eval (c 0)‖≤‖p.eval (c 1)‖
    · refine ⟨0,1,hsum,?_,hle⟩
      fin_cases k
      · exact hsmall
      · exact hle.trans_lt hsmall
    · refine ⟨1,0,?_,?_,le_of_not_ge hle⟩
      · simpa only [add_comm] using hsum
      · fin_cases k
        · exact (le_of_not_ge hle).trans_lt hsmall
        · exact hsmall
  obtain ⟨i,j,hsum',hsmall',hmin⟩ := hpair
  have hform := expansion_at_critical p A B C (c i) (c j) hpoly (hrootcrit i) hsum'
  obtain ⟨a,b,hab,ha,hb,H⟩ := hub_from_critical_expansion p (c i) (c j-c i)
    (p.eval (c i)) (hnz i) hsmall' hform (by
      have he : c i+(c j-c i)=c j := by ring
      simpa only [he] using hmin)
  obtain ⟨ia,hia⟩ := ((enumeration_facts p z hp).2.2 a).mp ha
  obtain ⟨ib,hib⟩ := ((enumeration_facts p z hp).2.2 b).mp hb
  refine ⟨ia,ib,c i,?_,?_,?_⟩
  · intro he; subst ib; exact hab (hia.symm.trans hib)
  · simpa only [hia,hib] using hab
  · simpa only [hia,hib] using H

-- Mathlib/Algebra/Squarefree/Basic.lean: Squarefree is the no-nonunit-square predicate.
-- Mathlib/Algebra/Polynomial/RingDivision.lean: prime_X_sub_C.
/-- Squarefreeness supplies the advertised endpoint distinctness. -/
theorem squarefree_enumeration_injective (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : RootEnumeration p z) (hs : Squarefree p) : Injective z := by
  change p=∏i, (X-C (z i)) at hp
  have h01 : z 0 ≠ z 1 := by
    intro he
    have hd : (X-C (z 0))*(X-C (z 0)) ∣ p := by
      refine ⟨X-C (z 2), ?_⟩
      rw [hp,Fin.prod_univ_three,← he]
    exact (prime_X_sub_C (z 0)).not_unit (hs _ hd)
  have h02 : z 0 ≠ z 2 := by
    intro he
    have hd : (X-C (z 0))*(X-C (z 0)) ∣ p := by
      refine ⟨X-C (z 1), ?_⟩
      rw [hp,Fin.prod_univ_three,← he]
      ring
    exact (prime_X_sub_C (z 0)).not_unit (hs _ hd)
  have h12 : z 1 ≠ z 2 := by
    intro he
    have hd : (X-C (z 1))*(X-C (z 1)) ∣ p := by
      refine ⟨X-C (z 0), ?_⟩
      rw [hp,Fin.prod_univ_three,← he]
      ring
    exact (prime_X_sub_C (z 1)).not_unit (hs _ hd)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [h01,h02,h12,Ne.symm h01,Ne.symm h02,Ne.symm h12]

/-- The entire long-record degree-three theorem, including multiplicity,
a specified polygonal hub, continuity, rectifiability and strict length. -/
theorem cubic_paper_complete (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : RootEnumeration p z) (hz : ∀i, ‖z i‖<1) :
    ∃ i j : Fin 3, ∃ c : ℂ, i ≠ j ∧
      Continuous (hub (z i) c (z j)) ∧
      BoundedVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) ∧
      HubBelow p.eval 1 2 (z i) c (z j) ∧
      ConnectedBelow p.eval 1 2 (z i) (z j) ∧
      (Squarefree p → z i ≠ z j) := by
  by_cases hinj : Injective z
  · obtain ⟨i,j,c,hij,hval,H⟩ := cubic_distinct_hub p z hp hz hinj
    exact ⟨i,j,c,hij,hub_continuous _ _ _,hub_rectifiable _ _ _,H,H.connectedBelow,fun _ => hval⟩
  · have hdup : ∃ i j : Fin 3, i ≠ j ∧ z i=z j := by
      by_contra h
      apply hinj
      intro i j hij
      by_contra hne
      exact h ⟨i,j,hne,hij⟩
    obtain ⟨i,j,hij,heq⟩ := hdup
    have hr : p.eval (z i)=0 := ((enumeration_facts p z hp).2.2 (z i)).mpr ⟨i,rfl⟩
    have H : HubBelow p.eval 1 2 (z i) (z i) (z j) := by
      rw [← heq]
      apply hubBelow_of_spokes
      · intro t ht0 ht1; simp [hr]
      · intro t ht0 ht1; simp [hr]
      · simp
    refine ⟨i,j,z i,hij,hub_continuous _ _ _,hub_rectifiable _ _ _,H,H.connectedBelow,?_⟩
    intro hs he
    exact hinj (squarefree_enumeration_injective p z hp hs)

end ErdosProblems.Erdos1041.PaperCubicCompletion
