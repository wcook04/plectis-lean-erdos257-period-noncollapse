import ErdosProblems.Erdos1041.ReturnV5.RootOccurrences

/-!
# The full degree-two geometric branch

AUTHORED / UNRUN. Actual polynomial, critical minimum, contained curve and
variation are supplied. The degree-two source does not assume a path-length
certificate. No first-merge analytic assumption is used.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ReturnV5
open Polynomial Set PaperAnalyticTargets PaperCurve

 def quadratic (a b : ℂ) : ℂ[X] := (X - C a) * (X - C b)
 def midpoint (a b : ℂ) : ℂ := (a + b) / 2
 def halfDifference (a b : ℂ) : ℂ := (a - b) / 2

theorem quadratic_critical_iff (a b c : ℂ) :
    (quadratic a b).derivative.eval c = 0 ↔ c = midpoint a b := by
  have he : (quadratic a b).derivative.eval c = 2 * c - a - b := by
    simp [quadratic]
    ring
  rw [he]
  constructor
  · intro h
    dsimp [midpoint]
    linear_combination (1 / 2 : ℂ) * h
  · intro h
    rw [h]
    dsimp [midpoint]
    ring

theorem quadratic_center_value (a b : ℂ) :
    (quadratic a b).eval (midpoint a b) = -(halfDifference a b) ^ 2 := by
  simp [quadratic, midpoint, halfDifference]
  ring

theorem quadratic_critical_minimum (a b : ℂ) :
    CriticalMinimum (quadratic a b) (‖halfDifference a b‖ ^ 2) := by
  have hn : ‖(quadratic a b).eval (midpoint a b)‖ = ‖halfDifference a b‖ ^ 2 := by
    rw [quadratic_center_value, norm_neg, norm_pow]
  constructor
  · exact ⟨midpoint a b, (quadratic_critical_iff a b _).2 rfl, hn.symm⟩
  · rintro x ⟨c, hc, hx⟩
    rw [(quadratic_critical_iff a b c).1 hc, hn] at hx
    exact le_of_eq hx.symm

theorem quadratic_minimum_eq {a b : ℂ} {μ : ℝ}
    (hμ : CriticalMinimum (quadratic a b) μ) : μ = ‖halfDifference a b‖ ^ 2 := by
  have H := quadratic_critical_minimum a b
  exact le_antisymm (hμ.2 H.1) (H.2 hμ.1)

/-- The least-critical radius is exactly the half-distance of the roots. -/
theorem quadratic_radius_eq {a b : ℂ} {μ : ℝ}
    (hμ : CriticalMinimum (quadratic a b) μ) :
    μ ^ (1 / (2 : ℝ)) = ‖halfDifference a b‖ := by
  rw [quadratic_minimum_eq hμ, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_sq (norm_nonneg _)

/-- Exact norm along the central diameter, including its endpoints. -/
theorem quadratic_diameter_norm (a b : ℂ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    ‖(quadratic a b).eval (midpoint a b + (s : ℂ) * halfDifference a b)‖ =
      (1 - s ^ 2) * ‖halfDifference a b‖ ^ 2 := by
  have he : (quadratic a b).eval (midpoint a b + (s : ℂ) * halfDifference a b) =
      ((s ^ 2 - 1 : ℝ) : ℂ) * (halfDifference a b) ^ 2 := by
    simp only [quadratic, eval_mul, eval_sub, eval_X, eval_C,
      midpoint, halfDifference]
    push_cast
    ring
  have hsq : s ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2)
      (show 0 ≤ 1 + s by linarith [hs.1])]
  rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hsq)]
  ring

theorem quadratic_diameter_bound (a b : ℂ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    ‖(quadratic a b).eval (midpoint a b + (s : ℂ) * halfDifference a b)‖ ≤
      ‖halfDifference a b‖ ^ 2 := by
  rw [quadratic_diameter_norm a b hs]
  nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg ‖halfDifference a b‖)]

/-- The root segment is a continuous rectifiable curve in the exact critical
sublevel, with its exact length budget. The double-root case is included. -/
theorem quadratic_segment (a b : ℂ) :
    ConnectedAtMost (quadratic a b).eval (‖halfDifference a b‖ ^ 2)
      (2 * ‖halfDifference a b‖) a b := by
  apply connectedAtMost_of_spokes (h := midpoint a b)
  · intro u hu0 hu1
    have he : a - midpoint a b = halfDifference a b := by
      dsimp [midpoint, halfDifference]
      ring
    rw [he]
    exact quadratic_diameter_bound a b ⟨by linarith, hu1⟩
  · intro u hu0 hu1
    have he : midpoint a b + (u : ℂ) * (b - midpoint a b) =
        midpoint a b + ((-u : ℝ) : ℂ) * halfDifference a b := by
      dsimp [midpoint, halfDifference]
      push_cast
      ring
    rw [he]
    exact quadratic_diameter_bound a b ⟨by linarith, by linarith⟩
  · have he₁ : midpoint a b - a = -halfDifference a b := by
      dsimp [midpoint, halfDifference]
      ring
    have he₂ : b - midpoint a b = -halfDifference a b := by
      dsimp [midpoint, halfDifference]
      ring
    simp only [he₁, he₂, norm_neg]
    linarith

/-- Degree-two endpoint, with precisely the polynomial and critical-minimum
hypotheses used by `ConstantFactorPath`. -/
theorem constantFactor_quadratic_branch (p : ℂ[X]) (z : Fin 2 → ℂ) (μ : ℝ)
    (hp : RootEnumeration p z) (hμ : CriticalMinimum p μ) :
    (∃ i j : Fin 2, i ≠ j ∧
      ConnectedAtMost p.eval (2 * μ) ((71 / 10 : ℝ) * μ ^ (1 / (2 : ℝ)))
        (z i) (z j) ∧ (Squarefree p → z i ≠ z j)) ∧
    (μ ≤ 1 / 2 → ∃ i j : Fin 2, i ≠ j ∧ ∃ γ : ℝ → ℂ,
      ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
      BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal (57 / 10)) := by
  have hpq : p = quadratic (z 0) (z 1) := by
    simpa only [RootEnumeration, Fin.prod_univ_two, quadratic] using hp
  have hμq : CriticalMinimum (quadratic (z 0) (z 1)) μ := by simpa [hpq] using hμ
  have hμeq := quadratic_minimum_eq hμq
  have hr := quadratic_radius_eq hμq
  have H : ConnectedAtMost p.eval μ (2 * ‖halfDifference (z 0) (z 1)‖) (z 0) (z 1) := by
    rw [hpq, hμeq]
    exact quadratic_segment _ _
  constructor
  · refine ⟨0, 1, by decide, ?_, ?_⟩
    · apply connectedAtMost_mono (H := H)
      · linarith [criticalMinimum_nonneg hμ]
      · rw [hr]
        nlinarith [norm_nonneg (halfDifference (z 0) (z 1))]
    · intro hs he
      exact (show (0 : Fin 2) ≠ 1 by decide) (squarefree_rootEnumeration_injective hp hs he)
  · intro hsmall
    obtain ⟨γ, hc, h0, h2, hs, hv, hl⟩ := H
    refine ⟨0, 1, by decide, γ, hc, h0, h2, ?_, hv, ?_⟩
    · intro t ht
      exact lt_of_le_of_lt (hs t ht) (by linarith)
    · apply hl.trans
      apply ENNReal.ofReal_le_ofReal
      have hd : ‖halfDifference (z 0) (z 1)‖ ≤ 1 := by
        rw [hμeq] at hsmall
        nlinarith [sq_nonneg (‖halfDifference (z 0) (z 1)‖ - 1)]
      linarith

/-- The low-critical theorem really is complete in degree two, with no root
location assumption. The general-degree analytic supplier is separate. -/
theorem lowCritical_quadratic (p : ℂ[X]) (z : Fin 2 → ℂ) (μ : ℝ)
    (hp : RootEnumeration p z) (hs : Squarefree p)
    (hμ : CriticalMinimum p μ) (hsmall : μ ≤ 13 / 25) :
    HasDistinctConnection p 1 2 := by
  have hpq : p = quadratic (z 0) (z 1) := by
    simpa only [RootEnumeration, Fin.prod_univ_two, quadratic] using hp
  have hμq : CriticalMinimum (quadratic (z 0) (z 1)) μ := by simpa [hpq] using hμ
  have hμeq := quadratic_minimum_eq hμq
  have H : ConnectedAtMost p.eval μ (2 * ‖halfDifference (z 0) (z 1)‖) (z 0) (z 1) := by
    rw [hpq, hμeq]
    exact quadratic_segment _ _
  have hlen : 2 * ‖halfDifference (z 0) (z 1)‖ < 2 := by
    rw [hμeq] at hsmall
    nlinarith [sq_nonneg (‖halfDifference (z 0) (z 1)‖ - 1)]
  refine ⟨z 0, z 1, ?_, enumeration_root hp 0, enumeration_root hp 1, ?_⟩
  · exact fun he => (show (0 : Fin 2) ≠ 1 by decide)
      (squarefree_rootEnumeration_injective hp hs he)
  · exact connectedBelow_of_closed_slack (by linarith) hlen (by norm_num) H

/-- Extra result: the whole degree-two open connector construction only needs
μ < 1, not the paper's much smaller universal low-critical cutoff. -/
theorem quadratic_open_connector (p : ℂ[X]) (z : Fin 2 → ℂ) (μ : ℝ)
    (hp : RootEnumeration p z) (hμ : CriticalMinimum p μ) (hsmall : μ < 1) :
    ConnectedBelow p.eval 1 2 (z 0) (z 1) := by
  have hpq : p = quadratic (z 0) (z 1) := by
    simpa only [RootEnumeration, Fin.prod_univ_two, quadratic] using hp
  have hμq : CriticalMinimum (quadratic (z 0) (z 1)) μ := by simpa [hpq] using hμ
  have he := quadratic_minimum_eq hμq
  have H : ConnectedAtMost p.eval μ (2 * ‖halfDifference (z 0) (z 1)‖) (z 0) (z 1) := by
    rw [hpq, he]
    exact quadratic_segment _ _
  apply connectedBelow_of_closed_slack hsmall _ (by norm_num) H
  rw [he] at hsmall
  nlinarith [sq_nonneg (‖halfDifference (z 0) (z 1)‖ - 1)]

/-- Exact endpoint distance; the segment budget is not a loose surrogate. -/
theorem quadratic_distance (a b : ℂ) : dist a b = 2 * ‖halfDifference a b‖ := by
  rw [dist_eq_norm]
  have he : a - b = (2 : ℂ) * halfDifference a b := by
    dsimp [halfDifference]
    ring
  rw [he, norm_mul]
  norm_num

end ErdosProblems.Erdos1041.ReturnV5
