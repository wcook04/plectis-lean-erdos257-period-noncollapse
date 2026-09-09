import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperMetricScaling

/-!
# Actual closed and open connectors: elementary infrastructure

AUTHORED / UNRUN. Every connector below uses `eVariationOn` and
`BoundedVariationOn`. No endpoint-distance surrogate is substituted for length.
These lemmas are not suppliers of first-merge geometry.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ReturnV5
open Set PaperCurve PaperAnalyticTargets
open scoped ENNReal

/-- Enlarge both bounds on an already constructed closed connector. -/
theorem connectedAtMost_mono {f : ℂ → ℂ} {R R' L L' : ℝ} {a b : ℂ}
    (hR : R ≤ R') (hL : L ≤ L') (H : ConnectedAtMost f R L a b) :
    ConnectedAtMost f R' L' a b := by
  obtain ⟨γ, hc, h0, h2, hs, hv, hl⟩ := H
  exact ⟨γ, hc, h0, h2, fun t ht => (hs t ht).trans hR, hv,
    hl.trans (ENNReal.ofReal_le_ofReal hL)⟩

/-- Closed containment plus genuine slack gives open containment and length. -/
theorem connectedBelow_of_closed_slack {f : ℂ → ℂ} {R R' L L' : ℝ} {a b : ℂ}
    (hR : R < R') (hL : L < L') (hL' : 0 < L')
    (H : ConnectedAtMost f R L a b) : ConnectedBelow f R' L' a b := by
  obtain ⟨γ, hc, h0, h2, hs, hv, hl⟩ := H
  refine ⟨γ, hc, h0, h2, fun t ht => lt_of_le_of_lt (hs t ht) hR, hv, ?_⟩
  exact lt_of_le_of_lt hl ((ENNReal.ofReal_lt_ofReal_iff hL').2 hL)

/-- Two safe spokes produce their actual polygonal connector, also at level zero. -/
theorem connectedAtMost_of_spokes {f : ℂ → ℂ} {R L : ℝ} {a h b : ℂ}
    (ha : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (h + (u : ℂ) * (a - h))‖ ≤ R)
    (hb : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (h + (u : ℂ) * (b - h))‖ ≤ R)
    (hL : ‖h - a‖ + ‖b - h‖ ≤ L) : ConnectedAtMost f R L a b := by
  refine ⟨hub a h b, (hub_continuous a h b).continuousOn,
    hub_zero a h b, hub_two a h b, ?_, hub_rectifiable a h b, ?_⟩
  · exact fun t ht => hub_mem (S := {z | ‖f z‖ ≤ R}) ha hb ht
  · rw [hub_variation_ofReal]
    exact ENNReal.ofReal_le_ofReal hL

/-- Coincident occurrences admit a constant curve with exactly zero variation. -/
theorem connectedAtMost_refl {f : ℂ → ℂ} {R : ℝ} {a : ℂ}
    (ha : ‖f a‖ ≤ R) : ConnectedAtMost f R 0 a a := by
  apply connectedAtMost_of_spokes (h := a)
  · intro u hu0 hu1
    simpa using ha
  · intro u hu0 hu1
    simpa using ha
  · simp

/-- Exact spatial scaling of a closed connector, including singular maps.
Unlike strict transport, this does not require nonzero scale factors. -/
theorem connectedAtMost_affine {f g : ℂ → ℂ} {R L : ℝ} {a b h c d : ℂ}
    (hid : ∀ z : ℂ, f (h + c * z) = d * g z)
    (H : ConnectedAtMost g R L a b) :
    ConnectedAtMost f (‖d‖ * R) (‖c‖ * L) (h + c * a) (h + c * b) := by
  obtain ⟨γ, hc, h0, h2, hs, hv, hl⟩ := H
  have hlen : eVariationOn (fun t => h + c * γ t) (Icc (0 : ℝ) 2) ≤
      ENNReal.ofReal (‖c‖ * L) := by
    calc
      _ ≤ (‖c‖₊ : ℝ≥0∞) * eVariationOn γ (Icc (0 : ℝ) 2) :=
        PaperMetricScaling.transported_variation_le γ _ h c
      _ ≤ (‖c‖₊ : ℝ≥0∞) * ENNReal.ofReal L := mul_le_mul_left' hl _
      _ = ENNReal.ofReal (‖c‖ * L) := by
        rw [ENNReal.ofReal_mul (norm_nonneg c)]
        simp [enorm_eq_nnnorm]
  refine ⟨fun t => h + c * γ t,
    continuousOn_const.add (continuousOn_const.mul hc), ?_, ?_, ?_, ?_, hlen⟩
  · simp [h0]
  · simp [h2]
  · intro t ht
    rw [hid, norm_mul]
    exact mul_le_mul_of_nonneg_left (hs t ht) (norm_nonneg d)
  · change eVariationOn (fun t => h + c * γ t) (Icc (0 : ℝ) 2) ≠ ⊤
    exact ne_of_lt (lt_of_le_of_lt hlen ENNReal.ofReal_lt_top)

/-- A closed zero-level connector cannot be relabelled as an open zero-level one. -/
theorem open_zero_impossible (f : ℂ → ℂ) (a b : ℂ) (L : ℝ) :
    ¬ ConnectedBelow f 0 L a b :=
  PaperMetricScaling.no_strict_zero_level f a b L

end ErdosProblems.Erdos1041.ReturnV5
