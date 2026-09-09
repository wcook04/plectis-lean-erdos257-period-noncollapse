import Mathlib

/-!
# Rectifiable two-segment connectors for the #1041 paper campaign

This file supplies actual continuous curves, not a proxy called `length`.
The extended length is Mathlib's `eVariationOn`; rectifiability is
`BoundedVariationOn`. Parameter time is `[0,2]`, with the hub at time one.

Validation: proof source written in this return; not elaborated in this
execution environment. No new axiom or admitted lemma is used.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCurve

open Set
open scoped NNReal ENNReal

/-- An affine parametrisation, defined on the whole real line. -/
def affine (a v : ℂ) (t : ℝ) : ℂ := a + (t : ℂ) * v

theorem affine_dist (a v : ℂ) (s t : ℝ) :
    dist (affine a v s) (affine a v t) = dist s t * ‖v‖ := by
  rw [dist_eq_norm]
  have he : affine a v s - affine a v t = ((s - t : ℝ) : ℂ) * v := by
    simp only [affine]
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]

theorem affine_lipschitz (a v : ℂ) : LipschitzWith ‖v‖₊ (affine a v) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [affine_dist]
  change dist s t * ‖v‖ ≤ ‖v‖ * dist s t
  exact le_of_eq (mul_comm _ _)

/-- The variation of an affine curve on a unit interval is its speed. -/
theorem affine_unit_variation (a v : ℂ) (s : ℝ) :
    eVariationOn (affine a v) (Icc s (s + 1)) = (‖v‖₊ : ℝ≥0∞) := by
  apply le_antisymm
  · have hl : LipschitzOnWith ‖v‖₊ (affine a v) univ :=
      (affine_lipschitz a v).lipschitzOnWith
    have hm : MapsTo (id : ℝ → ℝ) (Icc s (s + 1)) univ := by
      intro x hx
      trivial
    have hv := hl.comp_eVariationOn_le hm
    have hid : eVariationOn (id : ℝ → ℝ) (Icc s (s + 1)) ≤ 1 := by
      have h := (monotone_id.monotoneOn (univ : Set ℝ)).eVariationOn_le
        (mem_univ s) (mem_univ (s + 1))
      simpa only [univ_inter, id_eq, add_sub_cancel_left,
        ENNReal.ofReal_one] using h
    calc
      eVariationOn (affine a v) (Icc s (s + 1))
          ≤ (‖v‖₊ : ℝ≥0∞) * eVariationOn (id : ℝ → ℝ) (Icc s (s + 1)) := by
            simpa only [Function.comp_id] using hv
      _ ≤ (‖v‖₊ : ℝ≥0∞) * 1 := by
            exact mul_le_mul_left' hid _
      _ = (‖v‖₊ : ℝ≥0∞) := mul_one _
  · have hs : s ≤ s + 1 := by linarith
    have hv := eVariationOn.edist_le (affine a v)
      (left_mem_Icc.mpr hs) (right_mem_Icc.mpr hs)
    have he : edist (affine a v s) (affine a v (s + 1)) =
        (‖v‖₊ : ℝ≥0∞) := by
      rw [edist_dist, affine_dist, Real.dist_eq]
      rw [show s - (s + 1) = (-1 : ℝ) by ring]
      norm_num only [abs_neg, abs_one, one_mul]
      simp [enorm_eq_nnnorm]
    rw [he] at hv
    exact hv

/-- A continuous broken line `a → h → b`, with no division by a segment length. -/
def hub (a h b : ℂ) (t : ℝ) : ℂ :=
  h + ((max (1 - t) 0 : ℝ) : ℂ) * (a - h) + ((max (t - 1) 0 : ℝ) : ℂ) * (b - h)

theorem hub_continuous (a h b : ℂ) : Continuous (hub a h b) := by
  unfold hub
  fun_prop

@[simp] theorem hub_zero (a h b : ℂ) : hub a h b 0 = a := by
  norm_num [hub] <;> ring

@[simp] theorem hub_one (a h b : ℂ) : hub a h b 1 = h := by
  norm_num [hub] <;> ring

@[simp] theorem hub_two (a h b : ℂ) : hub a h b 2 = b := by
  norm_num [hub] <;> ring

theorem hub_eq_first {a h b : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    hub a h b t = affine a (h - a) t := by
  have h0 : 0 ≤ 1 - t := by linarith
  have h1 : t - 1 ≤ 0 := by linarith
  simp only [hub, affine, max_eq_left h0, max_eq_right h1,
    Complex.ofReal_zero, zero_mul, add_zero]
  push_cast
  ring

theorem hub_eq_second {a h b : ℂ} {t : ℝ} (ht1 : 1 ≤ t) :
    hub a h b t = affine (2 * h - b) (b - h) t := by
  have h0 : 1 - t ≤ 0 := by linarith
  have h1 : 0 ≤ t - 1 := by linarith
  simp only [hub, affine, max_eq_right h0, max_eq_left h1,
    Complex.ofReal_zero, zero_mul, add_zero]
  push_cast
  ring

/-- Both segments have their actual variation, and variations add at the hub. -/
theorem hub_variation (a h b : ℂ) :
    eVariationOn (hub a h b) (Icc (0 : ℝ) 2) =
      (‖h - a‖₊ : ℝ≥0∞) + (‖b - h‖₊ : ℝ≥0∞) := by
  have hfirst : eVariationOn (hub a h b) (Icc (0 : ℝ) 1) =
      (‖h - a‖₊ : ℝ≥0∞) := by
    have heq : EqOn (hub a h b) (affine a (h - a)) (Icc (0 : ℝ) 1) :=
      fun t ht => hub_eq_first ht.1 ht.2
    rw [eVariationOn.congr heq]
    simpa only [zero_add] using affine_unit_variation a (h - a) 0
  have hsecond : eVariationOn (hub a h b) (Icc (1 : ℝ) 2) =
      (‖b - h‖₊ : ℝ≥0∞) := by
    have heq : EqOn (hub a h b) (affine (2 * h - b) (b - h)) (Icc (1 : ℝ) 2) :=
      fun t ht => hub_eq_second ht.1
    rw [eVariationOn.congr heq]
    convert affine_unit_variation (2 * h - b) (b - h) 1 using 1 <;> norm_num
  have hs := eVariationOn.Icc_add_Icc (hub a h b) (s := univ)
    (a := (0 : ℝ)) (b := 1) (c := 2) (by norm_num) (by norm_num) (by trivial)
  simp only [univ_inter] at hs
  rw [← hs, hfirst, hsecond]

theorem hub_variation_ofReal (a h b : ℂ) :
    eVariationOn (hub a h b) (Icc (0 : ℝ) 2) =
      ENNReal.ofReal (‖h - a‖ + ‖b - h‖) := by
  rw [hub_variation, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  rw [show ENNReal.ofReal ‖h - a‖ = (‖h - a‖₊ : ℝ≥0∞) by
    simp [enorm_eq_nnnorm]]
  rw [show ENNReal.ofReal ‖b - h‖ = (‖b - h‖₊ : ℝ≥0∞) by
    simp [enorm_eq_nnnorm]]

theorem hub_rectifiable (a h b : ℂ) :
    BoundedVariationOn (hub a h b) (Icc (0 : ℝ) 2) := by
  change eVariationOn (hub a h b) (Icc (0 : ℝ) 2) ≠ ⊤
  rw [hub_variation_ofReal]
  exact ENNReal.ofReal_ne_top

theorem hub_length (a h b : ℂ) :
    (eVariationOn (hub a h b) (Icc (0 : ℝ) 2)).toReal =
      ‖h - a‖ + ‖b - h‖ := by
  rw [hub_variation_ofReal, ENNReal.toReal_ofReal
    (add_nonneg (norm_nonneg _) (norm_nonneg _))]

/-- Containment is transported from the two actual spokes, not from an
endpoint-only condition. -/
theorem hub_mem {a h b : ℂ} {S : Set ℂ}
    (ha : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → h + (u : ℂ) * (a - h) ∈ S)
    (hb : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → h + (u : ℂ) * (b - h) ∈ S)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : hub a h b t ∈ S := by
  by_cases hle : t ≤ 1
  · have he : hub a h b t = h + (((1 - t : ℝ)) : ℂ) * (a - h) := by
      rw [hub_eq_first ht.1 hle]
      unfold affine
      push_cast
      ring
    rw [he]
    exact ha (1 - t) (by linarith) (by linarith [ht.1])
  · have he : hub a h b t = h + (((t - 1 : ℝ)) : ℂ) * (b - h) := by
      rw [hub_eq_second (le_of_not_ge hle)]
      unfold affine
      push_cast
      ring
    rw [he]
    exact hb (t - 1) (by linarith) (by linarith [ht.2])

/-- The geometric conclusion used by the paper: a continuous rectifiable
curve with specified endpoints, containment at every parameter, and a strict
variation bound. -/
def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L

theorem connectedBelow_of_spokes {f : ℂ → ℂ} {R L : ℝ} {a h b : ℂ}
    (ha : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (h + (u : ℂ) * (a - h))‖ < R)
    (hb : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (h + (u : ℂ) * (b - h))‖ < R)
    (hL : ‖h - a‖ + ‖b - h‖ < L) : ConnectedBelow f R L a b := by
  refine ⟨hub a h b, (hub_continuous a h b).continuousOn, hub_zero a h b,
    hub_two a h b, ?_, hub_rectifiable a h b, ?_⟩
  · intro t ht
    exact hub_mem (S := {z | ‖f z‖ < R}) ha hb ht
  · rw [hub_variation_ofReal]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (lt_of_le_of_lt (add_nonneg (norm_nonneg _) (norm_nonneg _)) hL)).2 hL

/-- A specified two-segment connector, rather than merely existence of
some rectifiable curve. The public `hub` fixes its image and parametrisation. -/
def HubBelow (f : ℂ → ℂ) (R L : ℝ) (a h b : ℂ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 2, ‖f (hub a h b t)‖ < R) ∧
    eVariationOn (hub a h b) (Icc (0 : ℝ) 2) < ENNReal.ofReal L

theorem hubBelow_of_spokes {f : ℂ → ℂ} {R L : ℝ} {a h b : ℂ}
    (ha : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (h + (u : ℂ) * (a - h))‖ < R)
    (hb : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (h + (u : ℂ) * (b - h))‖ < R)
    (hL : ‖h - a‖ + ‖b - h‖ < L) : HubBelow f R L a h b := by
  constructor
  · exact fun t ht => hub_mem (S := {z | ‖f z‖ < R}) ha hb ht
  · rw [hub_variation_ofReal]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hL

theorem HubBelow.connectedBelow {f : ℂ → ℂ} {R L : ℝ} {a h b : ℂ}
    (H : HubBelow f R L a h b) : ConnectedBelow f R L a b :=
  ⟨hub a h b, (hub_continuous a h b).continuousOn,
    hub_zero a h b, hub_two a h b, H.1, hub_rectifiable a h b, H.2⟩

/-- A repeated root occurrence is dealt with by an actual constant curve. -/
theorem connectedBelow_refl {f : ℂ → ℂ} {R L : ℝ} {a : ℂ}
    (ha : ‖f a‖ < R) (hL : 0 < L) : ConnectedBelow f R L a a := by
  apply connectedBelow_of_spokes (h := a)
  · intro u hu0 hu1
    simpa using ha
  · intro u hu0 hu1
    simpa using ha
  · simpa using hL

end ErdosProblems.Erdos1041.PaperCurve
