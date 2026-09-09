import ErdosProblems.Erdos1041.ConnectorR18.CurveAlgebra

/-!
# Repeated occurrences and the complete quadratic connector branch

AUTHORED / UNRUN. The minimum critical value is the exact `IsLeast` predicate
from the paper. Derivative equations are derived from the polynomial product,
not inserted as assumptions. The open-unit branch retains actual variation.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.ConnectorR18
open Polynomial Set PaperAnalyticTargets PaperCurve
open scoped BigOperators ENNReal

/-- The two conclusions at fixed parameters, definitionally matching the
body of `PaperAnalyticTargets.ConstantFactorPath`. -/
def Conclusion (n : ℕ) (p : ℂ[X]) (z : Fin n → ℂ) (μ : ℝ) : Prop :=
  (∃ i j : Fin n, i ≠ j ∧
    ConnectedAtMost p.eval (2 * μ) ((71 / 10 : ℝ) * μ ^ (1 / (n : ℝ))) (z i) (z j) ∧
    (Squarefree p → z i ≠ z j)) ∧
  (RootsInOpenUnitDisc p → μ ≤ 1 / 2 →
    ∃ i j : Fin n, i ≠ j ∧ InSetAtMost {w | ‖p.eval w‖ < 1} (57 / 10) (z i) (z j))

theorem enumeration_eval {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (w : ℂ) : p.eval w = ∏ i, (w - z i) := by
  change p = ∏ i, (X - C (z i)) at hp
  rw [hp, eval_prod]
  simp only [eval_sub, eval_X, eval_C]

theorem listed_root {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (i : Fin n) : p.eval (z i) = 0 := by
  classical
  rw [enumeration_eval hp]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

theorem enumeration_derivative {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (w : ℂ) :
    p.derivative.eval w = ∑ i : Fin n, ∏ j ∈ (Finset.univ.erase i), (w - z j) := by
  classical
  change p = ∏ i, (X - C (z i)) at hp
  rw [hp]
  simp only [Polynomial.derivative_prod_finset, Polynomial.eval_finset_sum, eval_mul, eval_prod,
    derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_sub, eval_X, eval_C,
    Finset.sum_filter, Finset.filter_true_of_mem]

theorem listed_root_derivative {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (i : Fin n) :
    p.derivative.eval (z i) = ∏ j ∈ (Finset.univ.erase i), (z i - z j) := by
  classical
  rw [enumeration_derivative hp]
  apply Finset.sum_eq_single i
  · intro j hj hji
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩)
    simp
  · simp

theorem duplicate_is_critical {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) {i j : Fin n} (hij : i ≠ j) (heq : z i = z j) :
    p.derivative.eval (z i) = 0 := by
  classical
  rw [listed_root_derivative hp]
  exact Finset.prod_eq_zero
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩) (sub_eq_zero.mpr heq)

theorem criticalMinimum_nonneg {p : ℂ[X]} {μ : ℝ} (hm : CriticalMinimum p μ) :
    0 ≤ μ := by
  obtain ⟨c, hc, hval⟩ := hm.1
  rw [hval]
  exact norm_nonneg _

theorem criticalMinimum_eq_zero_of_duplicate {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    {μ : ℝ} (hp : RootEnumeration p z) (hm : CriticalMinimum p μ)
    {i j : Fin n} (hij : i ≠ j) (heq : z i = z j) : μ = 0 := by
  apply le_antisymm _ (criticalMinimum_nonneg hm)
  apply hm.2
  exact ⟨z i, duplicate_is_critical hp hij heq, by simp [listed_root hp i]⟩

theorem factor_two_occurrences {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) {i j : Fin n} (hij : i ≠ j) :
    p = (X - C (z i)) * (X - C (z j)) *
      ∏ k ∈ ((Finset.univ.erase i).erase j), (X - C (z k)) := by
  classical
  have hi := Finset.mul_prod_erase Finset.univ
    (fun k : Fin n => (X - C (z k) : ℂ[X])) (Finset.mem_univ i)
  have hj := Finset.mul_prod_erase (Finset.univ.erase i)
    (fun k : Fin n => (X - C (z k) : ℂ[X]))
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  rw [hp, ← hi, ← hj]
  ring

/-- Generalizes the degree-three squarefree-enumeration lemma in the packet. -/
theorem squarefree_enumeration_injective {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    (hp : RootEnumeration p z) (hs : Squarefree p) : Function.Injective z := by
  classical
  intro i j heq
  by_contra hij
  have hd : (X - C (z i)) * (X - C (z i)) ∣ p := by
    refine ⟨∏ k ∈ ((Finset.univ.erase i).erase j), (X - C (z k)), ?_⟩
    rw [factor_two_occurrences hp hij, ← heq]
  exact (prime_X_sub_C (z i)).not_unit (hs _ hd)

theorem criticalMinimum_pos_of_injective {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    {μ : ℝ} (hp : RootEnumeration p z) (hm : CriticalMinimum p μ)
    (hz : Function.Injective z) : 0 < μ := by
  classical
  obtain ⟨c, hc, hval⟩ := hm.1
  rw [hval]
  apply norm_pos_iff.mpr
  intro hroot
  rw [enumeration_eval hp] at hroot
  obtain ⟨i, hi, he⟩ := Finset.prod_eq_zero_iff.mp hroot
  have hec : c = z i := sub_eq_zero.mp he
  rw [hec, listed_root_derivative hp] at hc
  have hne : (∏ j ∈ (Finset.univ.erase i), (z i - z j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro hh
    exact (Finset.mem_erase.mp hj).1 (hz hh).symm
  exact hne hc

/-- Both exact paper conclusions for any repeated occurrence. -/
theorem repeated_occurrences_complete {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ}
    {μ : ℝ} (hp : RootEnumeration p z) (hm : CriticalMinimum p μ)
    {i j : Fin n} (hij : i ≠ j) (heq : z i = z j) : Conclusion n p z μ := by
  have hμ : μ = 0 := criticalMinimum_eq_zero_of_duplicate hp hm hij heq
  have hr := listed_root hp i
  subst μ
  constructor
  · refine ⟨i, j, hij, ?_, ?_⟩
    · rw [← heq]
      apply (inSetAtMost_closed_iff p.eval (2 * 0)
        ((71 / 10 : ℝ) * 0 ^ (1 / (n : ℝ))) (z i) (z i)).mp
      exact InSetAtMost.refl (by change ‖p.eval (z i)‖ ≤ 2 * 0; rw [hr]; norm_num)
    · exact fun hs hh => hij (squarefree_enumeration_injective hp hs hh)
  · intro hdisc hhalf
    refine ⟨i, j, hij, ?_⟩
    rw [← heq]
    exact InSetAtMost.refl (by change ‖p.eval (z i)‖ < 1; rw [hr]; norm_num)

/-- The exact critical value in degree two, without choosing a square root
in the complex plane. -/
theorem quadratic_critical_value {p : ℂ[X]} {z : Fin 2 → ℂ} {μ : ℝ}
    (hp : RootEnumeration p z) (hm : CriticalMinimum p μ) :
    μ = (1 / 4 : ℝ) * ‖z 1 - z 0‖ ^ 2 := by
  have hf : p = (X - C (z 0)) * (X - C (z 1)) := by
    simpa only [RootEnumeration, Fin.prod_univ_two] using hp
  have hd (w : ℂ) : p.derivative.eval w = 2 * w - (z 0 + z 1) := by
    rw [hf]
    simp [Polynomial.derivative_mul]
    <;> ring
  obtain ⟨c, hc, hval⟩ := hm.1
  have hcentre : c = (z 0 + z 1) / 2 := by
    rw [hd] at hc
    linear_combination (1 / 2 : ℂ) * hc
  have he : p.eval c = (-1 / 4 : ℂ) * (z 1 - z 0) ^ 2 := by
    rw [hf, hcentre]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    ring
  rw [hval, he, norm_mul, norm_pow]
  norm_num [norm_div]

theorem quadratic_segment_containment {p : ℂ[X]} {z : Fin 2 → ℂ} {μ : ℝ}
    (hp : RootEnumeration p z) (hm : CriticalMinimum p μ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖p.eval (z 0 + (u : ℂ) * (z 1 - z 0))‖ ≤ μ := by
  have he : p.eval (z 0 + (u : ℂ) * (z 1 - z 0)) =
      ((u * (u - 1) : ℝ) : ℂ) * (z 1 - z 0) ^ 2 := by
    rw [hp, Fin.prod_univ_two]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    push_cast
    ring
  have hfactor : |u * (u - 1)| ≤ (1 / 4 : ℝ) := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (u - 1 / 2)]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hu0 (sub_nonpos.mpr hu1)]
  rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    quadratic_critical_value hp hm]
  exact mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)

theorem quadratic_segment_certificate {p : ℂ[X]} {z : Fin 2 → ℂ} {μ : ℝ}
    (hp : RootEnumeration p z) (hm : CriticalMinimum p μ) :
    ConnectedAtMost p.eval μ ‖z 1 - z 0‖ (z 0) (z 1) := by
  apply connectedAtMost_of_spokes (h := z 0)
  · intro u hu0 hu1
    simpa [listed_root hp 0] using criticalMinimum_nonneg hm
  · intro u hu0 hu1
    exact quadratic_segment_containment hp hm hu0 hu1
  · simp

theorem quadratic_length_identity {p : ℂ[X]} {z : Fin 2 → ℂ} {μ : ℝ}
    (hp : RootEnumeration p z) (hm : CriticalMinimum p μ) :
    ‖z 1 - z 0‖ = 2 * μ ^ ((1 : ℝ) / 2) := by
  rw [← Real.sqrt_eq_rpow]
  have hs := Real.sq_sqrt (criticalMinimum_nonneg hm)
  have hv := quadratic_critical_value hp hm
  nlinarith [Real.sqrt_nonneg μ, norm_nonneg (z 1 - z 0)]

/-- The degree-two branch of BOTH parts of ConstantFactorPath. The roots-in-
unit-disc hypothesis is not needed for the open part when μ ≤ 1/2. -/
theorem quadratic_complete {p : ℂ[X]} {z : Fin 2 → ℂ} {μ : ℝ}
    (hp : RootEnumeration p z) (hm : CriticalMinimum p μ) : Conclusion 2 p z μ := by
  have hμ := criticalMinimum_nonneg hm
  have H := quadratic_segment_certificate hp hm
  constructor
  · refine ⟨0, 1, by decide, ?_, ?_⟩
    · apply connectedAtMost_mono H (by linarith)
      rw [quadratic_length_identity hp hm]
      norm_num only [Nat.cast_ofNat]
      have hr : 0 ≤ μ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hμ _
      nlinarith
    · intro hs he
      have hh : (0 : Fin 2) = 1 := squarefree_enumeration_injective hp hs he
      exact (by decide : (0 : Fin 2) ≠ 1) hh
  · intro hdisc hhalf
    refine ⟨0, 1, by decide, ?_⟩
    apply closed_to_open_mono H (by linarith)
    have hv := quadratic_critical_value hp hm
    nlinarith [norm_nonneg (z 1 - z 0)]

end ErdosProblems.Erdos1041.ConnectorR18
