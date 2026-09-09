import ErdosProblems.Erdos1041.PaperCurveAssembly
import Mathlib

/-!
# Affine transport of actual rectifiable connectors

This discharges the metric transport step of the scale-free corollaries.
It DOES NOT assume or assert the low-critical existence theorem as an axiom.
The polynomial rescaling and critical-value-minimum identities remain listed
separately in coverage. New source, not elaborated here.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperMetricScaling

open Set PaperCurve
open scoped NNReal ENNReal

/-- The spatial affine map has exactly the expected Lipschitz constant. -/
theorem affine_lipschitz (h c : ℂ) :
    LipschitzWith ‖c‖₊ (fun z : ℂ => h + c * z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have he : h + c * z - (h + c * w) = c * (z - w) := by ring
  simp only [dist_eq_norm, he, norm_mul, coe_nnnorm]
  exact le_rfl

/-- Variation is controlled for every curve, with no differentiability
assumption and no replacement of length by an endpoint distance. -/
theorem transported_variation_le (γ : ℝ → ℂ) (s : Set ℝ) (h c : ℂ) :
    eVariationOn (fun t => h + c * γ t) s ≤
      (‖c‖₊ : ℝ≥0∞) * eVariationOn γ s := by
  have hl := (affine_lipschitz h c).lipschitzOnWith (s := (univ : Set ℂ))
  have hm : MapsTo γ s univ := fun _ _ => mem_univ _
  simpa only [Function.comp_def] using hl.comp_eVariationOn_le hm

/-- Transport both the level and the length. Both nonzero hypotheses are
necessary for the strict conclusion with the scaled thresholds. -/
theorem connectedBelow_affine
    {f g : ℂ → ℂ} {R L : ℝ} {a b h c d : ℂ}
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hid : ∀ z : ℂ, f (h + c * z) = d * g z)
    (H : ConnectedBelow g R L a b) :
    ConnectedBelow f (‖d‖ * R) (‖c‖ * L) (h + c * a) (h + c * b) := by
  obtain ⟨γ, hcont, h0, h2, hlevel, hrect, hlen⟩ := H
  have hcpos : (0 : ℝ≥0∞) < (‖c‖₊ : ℝ≥0∞) := by
    exact_mod_cast (show (0 : ℝ) < ‖c‖ from norm_pos_iff.mpr hc)
  have hcfin : (‖c‖₊ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hlen' : eVariationOn (fun t => h + c * γ t) (Icc (0 : ℝ) 2) <
      ENNReal.ofReal (‖c‖ * L) := by
    calc
      eVariationOn (fun t => h + c * γ t) (Icc (0 : ℝ) 2)
          ≤ (‖c‖₊ : ℝ≥0∞) * eVariationOn γ (Icc (0 : ℝ) 2) :=
        transported_variation_le γ _ h c
      _ < (‖c‖₊ : ℝ≥0∞) * ENNReal.ofReal L :=
        ENNReal.mul_lt_mul_right (ne_of_gt hcpos) hcfin hlen
      _ = ENNReal.ofReal (‖c‖ * L) := by
        rw [ENNReal.ofReal_mul (norm_nonneg c)]
        rw [show ENNReal.ofReal ‖c‖ = (‖c‖₊ : ℝ≥0∞) by
          simp [enorm_eq_nnnorm]]
  refine ⟨fun t => h + c * γ t, ?_, ?_, ?_, ?_, ?_, hlen'⟩
  · exact continuousOn_const.add (continuousOn_const.mul hcont)
  · simp [h0]
  · simp [h2]
  · intro t ht
    rw [hid, norm_mul]
    exact mul_lt_mul_of_pos_left (hlevel t ht) (norm_pos_iff.mpr hd)
  · change eVariationOn (fun t => h + c * γ t) (Icc (0 : ℝ) 2) ≠ ⊤
    exact ne_of_lt (lt_of_lt_of_le hlen' le_top)

/-- Strict containment cannot be obtained by multiplying a threshold by
zero. Repeated occurrences are handled by the separate constant-curve
constructor, not by a singular application of affine transport. -/
theorem no_strict_zero_level (f : ℂ → ℂ) (a b : ℂ) (L : ℝ) :
    ¬ ConnectedBelow f 0 L a b := by
  rintro ⟨γ, hcont, h0, h2, hlevel, hrect, hlen⟩
  have h := hlevel 0 (by constructor <;> norm_num)
  exact (not_lt_of_ge (norm_nonneg _)) h

#print axioms connectedBelow_affine

end ErdosProblems.Erdos1041.PaperMetricScaling
