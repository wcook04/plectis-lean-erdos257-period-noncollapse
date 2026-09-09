import ErdosProblems.Erdos1041.PaperAnalyticTargets

/-!
# Actual rectifiable-curve algebra for the connector construction

AUTHORED / UNRUN against the supplied Lean 4.29.1 / mathlib pin.
Every length below is Mathlib's `eVariationOn`. No analytic existence
hypothesis is introduced in this file. The clamped-clock construction avoids
assuming that an arbitrary rectifiable curve is Lipschitz or differentiable.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ConnectorR18
open Set PaperCurve PaperAnalyticTargets
open scoped ENNReal

/-- A connector in an arbitrary set, including an open sublevel, with a
non-strict extended-variation bound. -/
def InSetAtMost (S : Set ℂ) (L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, γ t ∈ S) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L

theorem inSetAtMost_closed_iff (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) :
    InSetAtMost {z | ‖f z‖ ≤ R} L a b ↔ ConnectedAtMost f R L a b := Iff.rfl

theorem InSetAtMost.mono {S T : Set ℂ} {L M : ℝ} {a b : ℂ}
    (H : InSetAtMost S L a b) (hST : S ⊆ T) (hLM : L ≤ M) :
    InSetAtMost T M a b := by
  obtain ⟨γ, hc, h0, h2, hS, hr, hv⟩ := H
  exact ⟨γ, hc, h0, h2, fun t ht => hST (hS t ht), hr,
    hv.trans (ENNReal.ofReal_le_ofReal hLM)⟩

theorem connectedAtMost_mono {f : ℂ → ℂ} {R R' L L' : ℝ} {a b : ℂ}
    (H : ConnectedAtMost f R L a b) (hR : R ≤ R') (hL : L ≤ L') :
    ConnectedAtMost f R' L' a b := by
  apply (inSetAtMost_closed_iff f R' L' a b).1
  exact InSetAtMost.mono ((inSetAtMost_closed_iff f R L a b).2 H)
    (fun _ hz => hz.trans hR) hL

theorem closed_to_open {f : ℂ → ℂ} {R R' L : ℝ} {a b : ℂ}
    (H : ConnectedAtMost f R L a b) (hR : R < R') :
    InSetAtMost {z | ‖f z‖ < R'} L a b := by
  exact InSetAtMost.mono ((inSetAtMost_closed_iff f R L a b).2 H)
    (fun _ hz => lt_of_le_of_lt hz hR) le_rfl

/-- This implication needs a strict inequality between levels. In particular
`R ≤ 1` alone does not turn closed containment into open containment. -/
theorem closed_to_open_mono {f : ℂ → ℂ} {R L M : ℝ} {a b : ℂ}
    (H : ConnectedAtMost f R L a b) (hR : R < 1) (hLM : L ≤ M) :
    InSetAtMost {z | ‖f z‖ < 1} M a b := by
  exact (closed_to_open H hR).mono (fun _ hz => hz) hLM

theorem InSetAtMost.refl {S : Set ℂ} {a : ℂ} {L : ℝ}
    (ha : a ∈ S) : InSetAtMost S L a a := by
  refine ⟨hub a a a, (hub_continuous _ _ _).continuousOn,
    hub_zero _ _ _, hub_two _ _ _, ?_, hub_rectifiable _ _ _, ?_⟩
  · intro t ht
    simpa [hub] using ha
  · rw [hub_variation_ofReal]
    simp

/-- A closed-level version of the source corpus's two-spoke constructor. -/
theorem connectedAtMost_of_spokes {f : ℂ → ℂ} {R L : ℝ} {a h b : ℂ}
    (ha : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (h + (u : ℂ) * (a - h))‖ ≤ R)
    (hb : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (h + (u : ℂ) * (b - h))‖ ≤ R)
    (hL : ‖h - a‖ + ‖b - h‖ ≤ L) : ConnectedAtMost f R L a b := by
  refine ⟨hub a h b, (hub_continuous _ _ _).continuousOn,
    hub_zero _ _ _, hub_two _ _ _, ?_, hub_rectifiable _ _ _, ?_⟩
  · exact fun t ht => hub_mem (S := {z | ‖f z‖ ≤ R}) ha hb ht
  · rw [hub_variation_ofReal]
    exact ENNReal.ofReal_le_ofReal hL

/-- Two arbitrary continuous curves joined at time one. Each input clock
runs through `[0,2]`; outside its active half it is held at an endpoint. -/
def joinCurve (α β : ℝ → ℂ) (t : ℝ) : ℂ :=
  α (min (2 * t) 2) + β (max (2 * t - 2) 0) - α 2

theorem joinCurve_left {α β : ℝ → ℂ} (hjoin : α 2 = β 0)
    {t : ℝ} (ht : t ≤ 1) : joinCurve α β t = α (2 * t) := by
  have h₁ : 2 * t ≤ 2 := by linarith
  have h₂ : 2 * t - 2 ≤ 0 := by linarith
  simp only [joinCurve, min_eq_left h₁, max_eq_right h₂, ← hjoin]
  abel

theorem joinCurve_right {α β : ℝ → ℂ} {t : ℝ} (ht : 1 ≤ t) :
    joinCurve α β t = β (2 * t - 2) := by
  have h₁ : 2 ≤ 2 * t := by linarith
  have h₂ : 0 ≤ 2 * t - 2 := by linarith
  simp only [joinCurve, min_eq_right h₁, max_eq_left h₂]
  abel

theorem joinCurve_continuousOn {α β : ℝ → ℂ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 2))
    (hβ : ContinuousOn β (Icc (0 : ℝ) 2)) :
    ContinuousOn (joinCurve α β) (Icc (0 : ℝ) 2) := by
  have hA : MapsTo (fun t : ℝ => min (2 * t) 2)
      (Icc (0 : ℝ) 2) (Icc (0 : ℝ) 2) := by
    intro t ht
    exact ⟨le_min (by linarith [ht.1]) (by norm_num), min_le_right _ _⟩
  have hB : MapsTo (fun t : ℝ => max (2 * t - 2) 0)
      (Icc (0 : ℝ) 2) (Icc (0 : ℝ) 2) := by
    intro t ht
    exact ⟨le_max_right _ _, max_le (by linarith [ht.2]) (by norm_num)⟩
  have hcA : Continuous (fun t : ℝ => min (2 * t) 2) := by fun_prop
  have hcB : Continuous (fun t : ℝ => max (2 * t - 2) 0) := by fun_prop
  exact ((hα.comp hcA.continuousOn hA).add
    (hβ.comp hcB.continuousOn hB)).sub continuousOn_const

/-- Concatenation never increases length beyond the sum of the actual
variations. This applies to all rectifiable curves, not just affine spokes. -/
theorem joinCurve_variation_le {α β : ℝ → ℂ} (hjoin : α 2 = β 0) :
    eVariationOn (joinCurve α β) (Icc (0 : ℝ) 2) ≤
      eVariationOn α (Icc (0 : ℝ) 2) + eVariationOn β (Icc (0 : ℝ) 2) := by
  have hleft : eVariationOn (joinCurve α β) (Icc (0 : ℝ) 1) ≤
      eVariationOn α (Icc (0 : ℝ) 2) := by
    have he : EqOn (joinCurve α β) (α ∘ (fun t : ℝ => 2 * t))
        (Icc (0 : ℝ) 1) := fun t ht => joinCurve_left hjoin ht.2
    rw [eVariationOn.congr he]
    apply eVariationOn.comp_le_of_monotoneOn
    · intro x hx y hy hxy
      dsimp
      linarith
    · intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hright : eVariationOn (joinCurve α β) (Icc (1 : ℝ) 2) ≤
      eVariationOn β (Icc (0 : ℝ) 2) := by
    have he : EqOn (joinCurve α β) (β ∘ (fun t : ℝ => 2 * t - 2))
        (Icc (1 : ℝ) 2) := fun t ht => joinCurve_right ht.1
    rw [eVariationOn.congr he]
    apply eVariationOn.comp_le_of_monotoneOn
    · intro x hx y hy hxy
      dsimp
      linarith
    · intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hadd := eVariationOn.Icc_add_Icc (joinCurve α β) (s := univ)
    (a := (0 : ℝ)) (b := 1) (c := 2) (by norm_num) (by norm_num) (by trivial)
  simp only [univ_inter] at hadd
  rw [← hadd]
  exact add_le_add hleft hright

theorem InSetAtMost.trans {S : Set ℂ} {L M : ℝ} {a b c : ℂ}
    (H : InSetAtMost S L a b) (K : InSetAtMost S M b c)
    (hL : 0 ≤ L) (hM : 0 ≤ M) : InSetAtMost S (L + M) a c := by
  obtain ⟨α, hα, hα0, hα2, hαS, hαr, hαv⟩ := H
  obtain ⟨β, hβ, hβ0, hβ2, hβS, hβr, hβv⟩ := K
  have hj : α 2 = β 0 := hα2.trans hβ0.symm
  have hv : eVariationOn (joinCurve α β) (Icc (0 : ℝ) 2) ≤
      ENNReal.ofReal (L + M) := by
    rw [ENNReal.ofReal_add hL hM]
    exact (joinCurve_variation_le hj).trans (add_le_add hαv hβv)
  refine ⟨joinCurve α β, joinCurve_continuousOn hα hβ, ?_, ?_, ?_, ?_, hv⟩
  · rw [joinCurve_left hj (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using hα0
  · rw [joinCurve_right (by norm_num : (1 : ℝ) ≤ 2)]
    convert hβ2 using 1 <;> norm_num
  · intro t ht
    by_cases h : t ≤ 1
    · rw [joinCurve_left hj h]
      exact hαS _ ⟨by linarith [ht.1], by linarith⟩
    · rw [joinCurve_right (le_of_not_ge h)]
      exact hβS _ ⟨by linarith, by linarith [ht.2]⟩
  · change eVariationOn (joinCurve α β) (Icc (0 : ℝ) 2) ≠ ⊤
    exact ne_of_lt (lt_of_le_of_lt hv (by simp))

theorem InSetAtMost.symm {S : Set ℂ} {L : ℝ} {a b : ℂ}
    (H : InSetAtMost S L a b) : InSetAtMost S L b a := by
  obtain ⟨γ, hc, h0, h2, hS, hr, hv⟩ := H
  have hm : MapsTo (fun t : ℝ => 2 - t) (Icc (0 : ℝ) 2) (Icc (0 : ℝ) 2) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have ha : AntitoneOn (fun t : ℝ => 2 - t) (Icc (0 : ℝ) 2) := by
    intro x hx y hy hxy
    dsimp
    linarith
  have hb : eVariationOn (γ ∘ (fun t : ℝ => 2 - t)) (Icc (0 : ℝ) 2) ≤
      ENNReal.ofReal L :=
    (eVariationOn.comp_le_of_antitoneOn γ _ ha hm).trans hv
  refine ⟨γ ∘ (fun t : ℝ => 2 - t), hc.comp (by fun_prop) hm,
    ?_, ?_, ?_, ?_, hb⟩
  · simpa using h2
  · simpa using h0
  · exact fun t ht => hS _ (hm ht)
  · change eVariationOn (γ ∘ (fun t : ℝ => 2 - t)) (Icc (0 : ℝ) 2) ≠ ⊤
    exact ne_of_lt (lt_of_le_of_lt hb (by simp))

theorem connectedAtMost_trans {f : ℂ → ℂ} {R L M : ℝ} {a b c : ℂ}
    (H : ConnectedAtMost f R L a b) (K : ConnectedAtMost f R M b c)
    (hL : 0 ≤ L) (hM : 0 ≤ M) : ConnectedAtMost f R (L + M) a c := by
  apply (inSetAtMost_closed_iff f R (L + M) a c).1
  exact InSetAtMost.trans ((inSetAtMost_closed_iff f R L a b).2 H)
    ((inSetAtMost_closed_iff f R M b c).2 K) hL hM

theorem connectedAtMost_symm {f : ℂ → ℂ} {R L : ℝ} {a b : ℂ}
    (H : ConnectedAtMost f R L a b) : ConnectedAtMost f R L b a := by
  apply (inSetAtMost_closed_iff f R L b a).1
  exact InSetAtMost.symm ((inSetAtMost_closed_iff f R L a b).2 H)

end ErdosProblems.Erdos1041.ConnectorR18
