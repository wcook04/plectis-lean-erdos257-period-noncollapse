import ErdosProblems.Erdos1041.ReturnV5.CurveInfrastructure

/-!
# Root occurrences and the repeated-root branch in every degree

AUTHORED / UNRUN. The polynomial identity enumerates multiplicities. A repeated
occurrence is proved to be a critical point before the critical minimum is set
to zero. This is not an assumption of the desired connector.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ReturnV5
open Polynomial Set PaperAnalyticTargets PaperCurve
open scoped BigOperators

/-- A root enumeration is an exact polynomial factorisation. -/
theorem enumeration_eval {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (x : ℂ) :
    p.eval x = ∏ i, (x - z i) := by
  change p = ∏ i, (X - C (z i)) at hp
  rw [hp, eval_prod]
  simp only [eval_sub, eval_X, eval_C]

theorem enumeration_root {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (i : Fin n) : p.eval (z i) = 0 := by
  classical
  rw [enumeration_eval hp]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

theorem enumeration_root_iff {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (x : ℂ) :
    p.eval x = 0 ↔ ∃ i, x = z i := by
  classical
  rw [enumeration_eval hp, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, sub_eq_zero.mp hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, Finset.mem_univ i, sub_self _⟩

/-- Actual polynomial differentiation, not a reciprocal-balance premise. -/
theorem enumeration_derivative_eval {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (x : ℂ) :
    p.derivative.eval x = ∑ i, ∏ j ∈ Finset.univ.erase i, (x - z j) := by
  classical
  change p = ∏ i, (X - C (z i)) at hp
  rw [hp]
  simp only [Polynomial.derivative_prod_finset, Polynomial.eval_finset_sum, eval_mul, eval_prod,
    derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_sub, eval_X, eval_C,
    Finset.sum_filter, Finset.filter_true_of_mem]

theorem enumeration_derivative_at_root {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (i : Fin n) :
    p.derivative.eval (z i) = ∏ j ∈ Finset.univ.erase i, (z i - z j) := by
  classical
  rw [enumeration_derivative_eval hp]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩) (sub_self _)
  · simp

theorem repeated_occurrence_critical {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) {i j : Fin n} (hij : i ≠ j) (he : z i = z j) :
    p.derivative.eval (z i) = 0 := by
  classical
  rw [enumeration_derivative_at_root hp]
  exact Finset.prod_eq_zero
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩) (sub_eq_zero.mpr he)

/-- No nonunit repeated linear factor is compatible with squarefreeness. -/
theorem squarefree_rootEnumeration_injective {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (hs : Squarefree p) : Function.Injective z := by
  classical
  intro i j he
  by_contra hij
  let F : Fin n → ℂ[X] := fun k => X - C (z k)
  have hp' : p = ∏ k, F k := hp
  have hj : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hfac : p = F i * F j * ∏ k ∈ (Finset.univ.erase i).erase j, F k := by
    calc
      p = F i * ∏ k ∈ Finset.univ.erase i, F k := by
        rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i), hp']
      _ = F i * (F j * ∏ k ∈ (Finset.univ.erase i).erase j, F k) := by
        rw [Finset.mul_prod_erase _ _ hj]
      _ = _ := by ring
  have hfij : F i = F j := by simp [F, he]
  have hdiv : (X - C (z i)) * (X - C (z i)) ∣ p := by
    refine ⟨∏ k ∈ (Finset.univ.erase i).erase j, F k, ?_⟩
    simpa only [← hfij] using hfac
  exact (prime_X_sub_C (z i)).not_unit (hs _ hdiv)

theorem criticalMinimum_nonneg {p : ℂ[X]} {μ : ℝ}
    (hμ : CriticalMinimum p μ) : 0 ≤ μ := by
  obtain ⟨c, hc, he⟩ := hμ.1
  rw [he]
  exact norm_nonneg _

theorem criticalMinimum_zero_of_repeated {n : ℕ} {p : ℂ[X]}
    {z : Fin n → ℂ} {μ : ℝ} (hp : RootEnumeration p z)
    (hμ : CriticalMinimum p μ) {i j : Fin n} (hij : i ≠ j) (he : z i = z j) :
    μ = 0 := by
  apply le_antisymm
  · apply hμ.2
    exact ⟨z i, repeated_occurrence_critical hp hij he, by simp [enumeration_root hp i]⟩
  · exact criticalMinimum_nonneg hμ

/-- Injective enumeration makes every critical value nonzero; no topological
statement about polynomial sublevel components is required here. -/
theorem criticalMinimum_pos_of_injective {n : ℕ} {p : ℂ[X]}
    {z : Fin n → ℂ} {μ : ℝ} (hp : RootEnumeration p z)
    (hμ : CriticalMinimum p μ) (hz : Function.Injective z) : 0 < μ := by
  classical
  obtain ⟨c, hc, he⟩ := hμ.1
  rw [he]
  apply norm_pos_iff.mpr
  intro hzero
  obtain ⟨i, rfl⟩ := (enumeration_root_iff hp c).mp hzero
  have hne : (∏ j ∈ Finset.univ.erase i, (z i - z j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hz h).symm)
  exact hne ((enumeration_derivative_at_root hp i).symm.trans hc)

/-- Both conclusions of the constant-factor paper theorem in its repeated-root
branch. The open-unit conclusion does not need the root-location hypothesis. -/
theorem constantFactor_repeated_branch {n : ℕ} (p : ℂ[X]) (z : Fin n → ℂ)
    (μ : ℝ) (hp : RootEnumeration p z) (hμ : CriticalMinimum p μ)
    (hrepeat : ∃ i j, i ≠ j ∧ z i = z j) :
    (∃ i j : Fin n, i ≠ j ∧
      ConnectedAtMost p.eval (2 * μ) ((71 / 10 : ℝ) * μ ^ (1 / (n : ℝ)))
        (z i) (z j) ∧ (Squarefree p → z i ≠ z j)) ∧
    (∃ i j : Fin n, i ≠ j ∧ ∃ γ : ℝ → ℂ,
      ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
      BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal (57 / 10)) := by
  obtain ⟨i, j, hij, he⟩ := hrepeat
  have hμ0 := criticalMinimum_zero_of_repeated hp hμ hij he
  have H : ConnectedAtMost p.eval 0 0 (z i) (z j) := by
    rw [← he]
    exact connectedAtMost_refl (by simp [enumeration_root hp i])
  constructor
  · refine ⟨i, j, hij, ?_, ?_⟩
    · apply connectedAtMost_mono (H := H)
      · rw [hμ0]
        norm_num
      · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (criticalMinimum_nonneg hμ) _)
    · intro hs hsame
      exact hij (squarefree_rootEnumeration_injective hp hs hsame)
  · obtain ⟨γ, hc, h0, h2, hs, hv, hl⟩ := H
    refine ⟨i, j, hij, γ, hc, h0, h2, ?_, hv, ?_⟩
    · intro t ht
      exact lt_of_le_of_lt (hs t ht) (by norm_num)
    · exact hl.trans (ENNReal.ofReal_le_ofReal (by norm_num))

end ErdosProblems.Erdos1041.ReturnV5
