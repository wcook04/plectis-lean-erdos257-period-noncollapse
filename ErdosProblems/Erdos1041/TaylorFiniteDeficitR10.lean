import ErdosProblems.Erdos1041.TaylorCoefficientDeficit
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Retain any finite set of positive-degree Taylor deficits.
This is a candidate: all compilation and axiom audits are UNRUN.
The degree-zero term is explicitly zero, so no exceptional index is hidden. -/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate NNReal ENNReal
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Real Metric

/-- The positive-degree contribution, with the constant coefficient excluded. -/
def taylorDeficitTerm (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ((2 : ℝ) * n - 1) * ‖a n‖ ^ 2

theorem taylorDeficitTerm_nonneg (a : ℕ → ℂ) (n : ℕ) :
    0 ≤ taylorDeficitTerm a n := by
  by_cases hn : n = 0
  · simp [taylorDeficitTerm, hn]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    simp only [taylorDeficitTerm, if_neg hn]
    exact mul_nonneg (by linarith) (sq_nonneg _)

/-- Every finite coefficient set can be retained in the circle energy bound.
In particular this is not a statement obtained by adding individual bounds. -/
theorem circle_taylor_energy_add_finite_deficit_le {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) (s : Finset ℕ) :
    circleAverage (fun z => ‖g z‖ ^ 2 -
      2 * (z * deriv g z * conj (g z)).re) 0 1 +
      ∑ n ∈ s, taylorDeficitTerm
        (fun k => cauchyPowerSeries g 0 R k (fun _ => (1 : ℂ))) n ≤ ‖g 0‖ ^ 2 := by
  classical
  let a : ℕ → ℂ := fun n => cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))
  have hseries := hg.hasFPowerSeriesOnBall (lt_trans (by norm_num) hR)
  have hsub : sphere (0 : ℂ) 1 ⊆ eball (0 : ℂ) (R : ℝ≥0∞) := by
    intro z hz
    rw [Metric.eball_coe]
    have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
    simpa [mem_ball, dist_eq_norm, hz1] using
      (show (1 : ℝ) < R by exact_mod_cast hR)
  have hc := hseries.continuousOn.mono hsub
  have hd : ContinuousOn (deriv g) (sphere (0 : ℂ) 1) := by
    have h := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_continuousOn
      (hseries.fderiv.continuousOn.mono hsub)
    simpa only [ContinuousLinearMap.apply_apply, fderiv_apply_one_eq_deriv] using h
  have hn : CircleIntegrable (fun z => ‖g z‖ ^ 2) 0 1 :=
    ContinuousOn.circleIntegrable (by norm_num) (hc.norm.pow 2)
  have hx : CircleIntegrable (fun z => (z * deriv g z * conj (g z)).re) 0 1 :=
    ContinuousOn.circleIntegrable (by norm_num)
      (Complex.continuous_re.comp_continuousOn
        ((continuousOn_id.mul hd).mul (Complex.continuous_conj.comp_continuousOn hc)))
  have hx2 : CircleIntegrable (fun z => 2 * (z * deriv g z * conj (g z)).re) 0 1 := by
    simpa only [smul_eq_mul] using hx.const_smul (a := (2 : ℝ))
  rw [circleAverage_fun_sub hn hx2]
  have hscale : circleAverage (fun z => 2 * (z * deriv g z * conj (g z)).re) 0 1 =
      2 * circleAverage (fun z => (z * deriv g z * conj (g z)).re) 0 1 := by
    simpa only [smul_eq_mul] using
      (circleAverage_fun_smul (a := (2 : ℝ))
        (f := fun z => (z * deriv g z * conj (g z)).re) (c := 0) (R := 1))
  rw [hscale]
  have hs := (hasSum_cauchy_circle_norm_sq hg hR).sub
    ((hasSum_cauchy_derivative_circle_energy hg hR).mul_left 2)
  have hfinite : HasSum
      (fun n : ℕ => ∑ k ∈ s, if n = k then taylorDeficitTerm a k else 0)
      (∑ k ∈ s, taylorDeficitTerm a k) :=
    hasSum_sum (s := s) (fun k _ => hasSum_ite_eq k (taylorDeficitTerm a k))
  have htarget := (hasSum_ite_eq 0 (‖a 0‖ ^ 2)).sub hfinite
  have hle : ∀ n : ℕ, ‖a n‖ ^ 2 - 2 * ((n : ℝ) * ‖a n‖ ^ 2) ≤
      (if n = 0 then ‖a 0‖ ^ 2 else 0) -
        ∑ k ∈ s, if n = k then taylorDeficitTerm a k else 0 := by
    intro n
    have he : (∑ k ∈ s, if n = k then taylorDeficitTerm a k else 0) =
        if n ∈ s then taylorDeficitTerm a n else 0 := by simp
    rw [he]
    by_cases hn : n = 0
    · subst n
      simp [taylorDeficitTerm]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      by_cases hns : n ∈ s
      · simp only [if_neg hn, if_pos hns, taylorDeficitTerm, if_neg hn]
        exact le_of_eq (by ring)
      · simp only [if_neg hn, if_neg hns, sub_zero]
        nlinarith [sq_nonneg ‖a n‖]
  have hupper := hasSum_le hle hs htarget
  have ha0 : a 0 = g 0 := hseries.coeff_zero (fun _ => (1 : ℂ))
  rw [ha0] at hupper
  exact (le_sub_iff_add_le).mp hupper


/-- Exact summable diagonal deficit for a function analytic beyond the circle. -/
theorem circle_taylor_deficit_hasSum {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) :
    HasSum (taylorDeficitTerm
      (fun n => cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))))
      (‖g 0‖ ^ 2 - (circleAverage (fun z => ‖g z‖ ^ 2) 0 1 -
        2 * circleAverage (fun z => (z * deriv g z * conj (g z)).re) 0 1)) := by
  let a : ℕ → ℂ := fun n => cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))
  have hs := (hasSum_cauchy_circle_norm_sq hg hR).sub
    ((hasSum_cauchy_derivative_circle_energy hg hR).mul_left 2)
  have ha0 : a 0 = g 0 :=
    (hg.hasFPowerSeriesOnBall (lt_trans (by norm_num) hR)).coeff_zero (fun _ => (1 : ℂ))
  have H := (hasSum_ite_eq 0 (‖a 0‖ ^ 2)).sub hs
  have he : (fun n : ℕ => (if n = 0 then ‖a 0‖ ^ 2 else 0) -
      (‖a n‖ ^ 2 - 2 * ((n : ℝ) * ‖a n‖ ^ 2))) = taylorDeficitTerm a := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [taylorDeficitTerm]
    · simp only [if_neg hn, taylorDeficitTerm, if_neg hn]
      ring
  change HasSum (fun n : ℕ => (if n = 0 then ‖a 0‖ ^ 2 else 0) -
    (‖a n‖ ^ 2 - 2 * ((n : ℝ) * ‖a n‖ ^ 2))) _ at H
  rw [he, ha0] at H
  exact H

/-- The diagonal identity after integration, with every infinite series justified
by the two supplied HasSum theorems. -/
theorem circle_taylor_energy_identity {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) :
    circleAverage (fun z => ‖g z‖ ^ 2 -
      2 * (z * deriv g z * conj (g z)).re) 0 1 =
    ‖g 0‖ ^ 2 - ∑' n, taylorDeficitTerm
      (fun k => cauchyPowerSeries g 0 R k (fun _ => (1 : ℂ))) n := by
  have hseries := hg.hasFPowerSeriesOnBall (lt_trans (by norm_num) hR)
  have hsub : sphere (0 : ℂ) 1 ⊆ eball (0 : ℂ) (R : ℝ≥0∞) := by
    intro z hz
    rw [Metric.eball_coe]
    have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
    simpa [mem_ball, dist_eq_norm, hz1] using
      (show (1 : ℝ) < R by exact_mod_cast hR)
  have hc := hseries.continuousOn.mono hsub
  have hd : ContinuousOn (deriv g) (sphere (0 : ℂ) 1) := by
    have H := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_continuousOn
      (hseries.fderiv.continuousOn.mono hsub)
    simpa only [ContinuousLinearMap.apply_apply, fderiv_apply_one_eq_deriv] using H
  have hnorm : CircleIntegrable (fun z => ‖g z‖ ^ 2) 0 1 :=
    ContinuousOn.circleIntegrable (by norm_num) (hc.norm.pow 2)
  have hcross : CircleIntegrable (fun z => (z * deriv g z * conj (g z)).re) 0 1 :=
    ContinuousOn.circleIntegrable (by norm_num)
      (Complex.continuous_re.comp_continuousOn
        ((continuousOn_id.mul hd).mul (Complex.continuous_conj.comp_continuousOn hc)))
  have hcross2 : CircleIntegrable (fun z => 2 * (z * deriv g z * conj (g z)).re) 0 1 := by
    simpa only [smul_eq_mul] using hcross.const_smul (a := (2 : ℝ))
  rw [circleAverage_fun_sub hnorm hcross2]
  have hscale : circleAverage (fun z => 2 * (z * deriv g z * conj (g z)).re) 0 1 =
      2 * circleAverage (fun z => (z * deriv g z * conj (g z)).re) 0 1 := by
    simpa only [smul_eq_mul] using
      (circleAverage_fun_smul (a := (2 : ℝ))
        (f := fun z => (z * deriv g z * conj (g z)).re) (c := 0) (R := 1))
  rw [hscale, (circle_taylor_deficit_hasSum hg hR).tsum_eq]
  ring

end ErdosProblems.Erdos1041
end
