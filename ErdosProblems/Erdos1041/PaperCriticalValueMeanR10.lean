import ErdosProblems.Erdos1041.PaperWeightedRefinementsR10
import ErdosProblems.Erdos1041.PolynomialDiscNormalisationR10

/-! The actual polynomial critical-value mean, not a hypothesis-only consumer.
Both paper exponents, all degrees, arbitrary disc centres, R=0, and critical
multiplicities are included. All Lean builds and axiom audits are UNRUN. -/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
noncomputable section
namespace ErdosProblems.Erdos1041
open Polynomial Real PaperAnalyticTargets

/-- Reflected critical values composed with the actual all-degree quadratic
free-point theorem. -/
theorem critical_unit_quadratic {n : ℕ} (hn : 2 ≤ n) (p : ℂ[X])
    (hp : p.Monic) (hdeg : p.natDegree = n) (hroots : RootsInClosedDisc p 0 1)
    (c : Fin (n - 1) → ℂ) (hc : CriticalEnumeration p c) :
    (∑ j, ‖p.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤ (n : ℝ) - 1 := by
  have hm : 0 < n - 1 := by omega
  have hmpos : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast hm
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hcdisc := PaperReflectedCompletion.critical_disc_location n p c hn hp hdeg hroots hc
  have href := PaperReflectedCompletion.reflected_critical_value n p c hn hp hdeg hroots hc
  have ht (j : Fin (n - 1)) :
      ‖p.eval (c j)‖ ^ (2 / ((n - 1 : ℕ) : ℝ)) ≤ equalFreePointRow c j ^ 2 := by
    have hprod0 : 0 ≤ ∏ k, ‖1 - conj (c k) * c j‖ :=
      Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    have hpow := Real.rpow_le_rpow (norm_nonneg (p.eval (c j))) (href j)
      (show 0 ≤ 2 / ((n - 1 : ℕ) : ℝ) by positivity)
    have he : equalFreePointRow c j ^ 2 =
        (∏ k, ‖1 - conj (c k) * c j‖) ^ (2 / ((n - 1 : ℕ) : ℝ)) := by
      unfold equalFreePointRow
      rw [← Real.rpow_two, ← Real.rpow_mul hprod0]
      congr 1
      ring
    rw [he]
    exact hpow
  have h := (Finset.sum_le_sum (fun j _ => ht j)).trans
    (equal_free_point_quadratic hm c hcdisc)
  simpa only [hcast] using h

/-- Every lower nonnegative exponent, in cardinality-normalised form. -/
theorem critical_unit_moment {n : ℕ} (hn : 2 ≤ n) (p : ℂ[X])
    (hp : p.Monic) (hdeg : p.natDegree = n) (hroots : RootsInClosedDisc p 0 1)
    (c : Fin (n - 1) → ℂ) (hc : CriticalEnumeration p c)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 2 / ((n : ℝ) - 1)) :
    (∑ j, ‖p.eval (c j)‖ ^ t) ≤ (n : ℝ) - 1 := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcast : (Fintype.card (Fin (n - 1)) : ℝ) = (n : ℝ) - 1 := by
    simp only [Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have h := PaperMomentConsumers.lower_moment (fun j => ‖p.eval (c j)‖)
    (fun j => norm_nonneg _) (div_pos (by norm_num : (0 : ℝ) < 2) hn1) ht0 ht
    (by simpa only [hcast] using critical_unit_quadratic hn p hp hdeg hroots c hc)
  simpa only [hcast] using h

/-- Scaling an actual monic polynomial supplies its own unit-disc hypotheses. -/
theorem critical_disc_moment_positive_radius {n : ℕ} (hn : 2 ≤ n) (p : ℂ[X])
    (hp : p.Monic) (hdeg : p.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 < R)
    (hroots : RootsInClosedDisc p h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration p c) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : t ≤ 2 / ((n : ℝ) - 1)) :
    (∑ j, ‖p.eval (c j)‖ ^ t) ≤ ((n : ℝ) - 1) * R ^ ((n : ℝ) * t) := by
  let q := normaliseDiscPolynomial p h R n
  let d : Fin (n - 1) → ℂ := fun j => (c j - h) / (R : ℂ)
  have hqd := normaliseDiscPolynomial_monic_degree p hp hdeg h R hR.ne'
  have hqr := normaliseDiscPolynomial_roots (n := n) p h R hR hroots
  have hqc := normaliseDiscPolynomial_critical (by omega : 1 ≤ n) p c hc h R hR.ne'
  have H := critical_unit_moment hn q hqd.1 hqd.2 hqr d hqc t ht0 ht
  have he (j : Fin (n - 1)) : ‖p.eval (c j)‖ ^ t =
      R ^ ((n : ℝ) * t) * ‖q.eval (d j)‖ ^ t := by
    rw [normaliseDiscPolynomial_value_transport p h R n hR (c j),
      Real.mul_rpow (pow_nonneg hR.le n) (norm_nonneg _)]
    change (R ^ n) ^ t * ‖q.eval (d j)‖ ^ t = _
    rw [← Real.rpow_natCast R n, ← Real.rpow_mul hR.le]
  rw [show (∑ j, ‖p.eval (c j)‖ ^ t) =
    R ^ ((n : ℝ) * t) * (∑ j, ‖q.eval (d j)‖ ^ t) by
      simp only [he, Finset.mul_sum]]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left H (Real.rpow_nonneg hR.le _)

/-- Positive-exponent form including the degenerate enclosing disc. -/
theorem critical_disc_moment {n : ℕ} (hn : 2 ≤ n) (p : ℂ[X])
    (hp : p.Monic) (hdeg : p.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc p h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration p c) (t : ℝ) (ht0 : 0 < t)
    (ht : t ≤ 2 / ((n : ℝ) - 1)) :
    (∑ j, ‖p.eval (c j)‖ ^ t) ≤ ((n : ℝ) - 1) * R ^ ((n : ℝ) * t) := by
  rcases eq_or_lt_of_le hR with hzero | hpos
  · have hzR : R = 0 := hzero.symm
    subst R
    have hz := critical_values_zero_of_zero_radius hn p hp hdeg h hroots c hc
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simp only [hz, norm_zero, Real.zero_rpow ht0.ne', Finset.sum_const_zero,
      Real.zero_rpow (mul_pos hnpos ht0).ne', mul_zero, le_refl]
  · exact critical_disc_moment_positive_radius hn p hp hdeg h R hpos hroots c hc t ht0.le ht

/-- Exact conjunction requested by res:fp-to-s. -/
theorem paper_critical_value_mean : PaperAnalyticTargets.CriticalValueMean := by
  intro n p c h R hn hp hdeg hR hroots hc
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  constructor
  · have H := critical_disc_moment hn p hp hdeg h R hR hroots c hc
      (2 / ((n : ℝ) - 1)) (div_pos (by norm_num) hmpos) le_rfl
    have he : (n : ℝ) * (2 / ((n : ℝ) - 1)) = 2 * (n : ℝ) / ((n : ℝ) - 1) := by ring
    simpa only [he] using H
  · have ht : 1 / (n : ℝ) ≤ 2 / ((n : ℝ) - 1) := by
      apply (div_le_div_iff₀ hnpos hmpos).mpr
      linarith
    have H := critical_disc_moment hn p hp hdeg h R hR hroots c hc
      (1 / (n : ℝ)) (div_pos (by norm_num) hnpos) ht
    have he : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
    simpa only [he, Real.rpow_one] using H

/-- The older long-paper 1/(n-1) budget, now in every degree, hence also in
its original domain 2 ≤ n ≤ 5. -/
theorem paper_critical_value_power_budget {n : ℕ} (hn : 2 ≤ n) (p : ℂ[X])
    (hp : p.Monic) (hdeg : p.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc p h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration p c) :
    (∑ j, ‖p.eval (c j)‖ ^ (1 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) := by
  have hmpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have H := critical_disc_moment hn p hp hdeg h R hR hroots c hc
    (1 / ((n : ℝ) - 1)) (div_pos (by norm_num) hmpos)
    ((div_le_div_iff_of_pos_right hmpos).mpr (by norm_num))
  simpa only [mul_one_div] using H

/-- The older theorem as literally quantified in the long paper. -/
theorem paper_critical_value_budget_degrees_two_through_five {n : ℕ}
    (hn : 2 ≤ n) (_hn5 : n ≤ 5) (p : ℂ[X]) (hp : p.Monic) (hdeg : p.natDegree = n)
    (h : ℂ) (R : ℝ) (hR : 0 ≤ R) (hroots : RootsInClosedDisc p h R)
    (c : Fin (n - 1) → ℂ) (hc : CriticalEnumeration p c) :
    (∑ j, ‖p.eval (c j)‖ ^ (1 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ j, ‖p.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R :=
  ⟨paper_critical_value_power_budget hn p hp hdeg h R hR hroots c hc,
    (paper_critical_value_mean n p c h R hn hp hdeg hR hroots hc).2⟩

end ErdosProblems.Erdos1041
end
