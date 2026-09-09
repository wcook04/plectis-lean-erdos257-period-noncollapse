import ErdosProblems.Erdos1041.PaperCurveAssembly
import ErdosProblems.Erdos1041.CyclicTetranomialCoefficientCase
import Mathlib

/-!
# Primitive quintic: from the two selected tails to actual paths

The missing selector-to-polynomial moment bridge is NOT smuggled in as a
proved fact. It is the explicit `hselected` premise below. The constant-term
bound is derived by Vieta and the remaining curve is assembled with actual
variation. New source, not elaborated in this environment.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperPrimitivePath

open Polynomial Set PaperCurve

private theorem product_norm_lt_one {s : Multiset ℂ}
    (hs : ∀ z ∈ s, ‖z‖ < 1) (hne : s ≠ 0) : ‖s.prod‖ < 1 := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl hne
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ z ∈ s, ‖z‖ < 1 := fun z hz => hs z (Multiset.mem_cons.mpr (Or.inr hz))
    rw [Multiset.prod_cons, norm_mul]
    by_cases hz : s = 0
    · subst s
      simpa using ha
    · have hprod := ih hs' hz
      nlinarith [norm_nonneg a, norm_nonneg s.prod]

/-- The constant term of any positive-degree monic open-disc-root polynomial. -/
theorem constant_norm_lt_one (p : ℂ[X]) (hp : p.Monic) (hdeg : 0 < p.natDegree)
    (hdisk : ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1) : ‖p.eval 0‖ < 1 := by
  have hs : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := Polynomial.splits_iff_card_roots.mp hs
  have hprod : p.eval 0 = (p.roots.map (fun z : ℂ => -z)).prod := by
    have h := congrArg (fun q : ℂ[X] => q.eval 0) hs.eq_prod_roots
    simpa [hp.leadingCoeff, eval_multiset_prod, Multiset.map_map] using h
  rw [hprod]
  apply product_norm_lt_one
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    rw [norm_neg]
    exact hdisk w ((Polynomial.mem_roots hp.ne_zero).mp hw)
  · intro hz
    have hc := congrArg Multiset.card hz
    simp only [Multiset.card_map, Multiset.card_zero, hcard] at hc
    omega

/-- The precise primitive quintic function. -/
def value (a b c z : ℂ) : ℂ := z ^ 5 + a * z ^ 4 + b * z + c

/-- A selected tail supplies a whole spoke; no low-coefficient bound is added. -/
theorem spoke_of_tail {a b c w : ℂ}
    (hroot : value a b c w = 0) (hw : ‖w‖ < 1)
    (hc : ‖c‖ < 1) (htail : ‖b * w + c‖ < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖value a b c ((t : ℂ) * w)‖ < 1 := by
  have hroot' : w ^ 5 + a * w ^ 4 + b * w ^ 1 + c = 0 := by
    simpa [value] using hroot
  have htail' : ‖a * w ^ 4 + w ^ 5‖ < 1 := by
    have he : a * w ^ 4 + w ^ 5 = -(b * w + c) := by
      unfold value at hroot
      linear_combination hroot
    rw [he, norm_neg]
    exact htail
  have h := tetranomialRoot_spoke_norm_lt_one_of_tail
    (m := 5) (r := 4) (s := 1) (by norm_num) (by norm_num) (by norm_num)
    hroot' hw hc htail' ht0 ht1
  simpa [value, mul_pow, mul_assoc, mul_left_comm, mul_comm] using h

/-- Once the polynomial moment selector supplies two tails, both distinct
location and repeated-occurrence cases have actual rectifiable connections. -/
theorem path_of_selected_tails (p : ℂ[X]) (hp : p.Monic)
    (hdeg : p.natDegree = 5) (a b c : ℂ)
    (hvalue : ∀ z : ℂ, p.eval z = value a b c z)
    (hdisk : ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1)
    (w : Fin 5 → ℂ) (hroots : ∀ i, p.eval (w i) = 0)
    (hselected : ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1) :
    ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 ∧
      ConnectedBelow p.eval 1 2 (w i) (w j) ∧
      (w i ≠ w j → HubBelow p.eval 1 2 (w i) 0 (w j)) ∧
      (w i = w j →
        (∀ t : ℝ, ‖p.eval ((fun _ : ℝ => w i) t)‖ < 1) ∧
        eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0) := by
  have hc : ‖c‖ < 1 := by
    have h := constant_norm_lt_one p hp (by omega) hdisk
    simpa [hvalue, value] using h
  obtain ⟨i, j, hij, hi, hj⟩ := hselected
  have hwi := hdisk (w i) (hroots i)
  have hwj := hdisk (w j) (hroots j)
  have hhub : HubBelow p.eval 1 2 (w i) 0 (w j) := by
    apply hubBelow_of_spokes
    · intro t ht0 ht1
      simpa [hvalue] using spoke_of_tail (by simpa [hvalue] using hroots i) hwi hc hi ht0 ht1
    · intro t ht0 ht1
      simpa [hvalue] using spoke_of_tail (by simpa [hvalue] using hroots j) hwj hc hj ht0 ht1
    · simp only [zero_sub, norm_neg, sub_zero]
      linarith
  refine ⟨i, j, hij, hi, hj, ?_, fun _ => hhub, ?_⟩
  · by_cases heq : w i = w j
    · rw [heq]
      exact connectedBelow_refl (by rw [hroots j]; norm_num) (by norm_num)
    · exact hhub.connectedBelow
  · intro heq
    constructor
    · intro t
      simp [hroots i]
    · apply eVariationOn.constant_on
      intro x hx y hy
      rcases hx with ⟨s, hs, rfl⟩
      rcases hy with ⟨t, ht, rfl⟩
      rfl

#print axioms path_of_selected_tails

end ErdosProblems.Erdos1041.PaperPrimitivePath
