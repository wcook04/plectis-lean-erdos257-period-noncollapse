import ErdosProblems.Erdos1041.TaylorCrossEnergy

/-! Classical analytic energy bound used in the weighted free-point proof.
The signed coefficient series and all integral interchanges are derived from
actual Cauchy coefficients. Candidate pending compilation. -/
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Real Metric

/-- Analyticity beyond the circle makes every positive-degree coefficient's
contribution to this energy nonpositive. No energy bound is assumed. -/
theorem circle_taylor_energy_le_value_zero {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) :
    circleAverage (fun z => ‖g z‖ ^ 2 -
      2 * (z * deriv g z * conj (g z)).re) 0 1 ≤ ‖g 0‖ ^ 2 := by
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
  have hle : ∀ n : ℕ, ‖a n‖ ^ 2 - 2 * ((n : ℝ) * ‖a n‖ ^ 2) ≤
      if n = 0 then ‖a 0‖ ^ 2 else 0 := by
    intro n
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      simp only [if_neg hn0]
      nlinarith [sq_nonneg ‖a n‖]
  have hupper := hasSum_le hle hs (hasSum_ite_eq 0 (‖a 0‖ ^ 2))
  have ha0 : a 0 = g 0 := hseries.coeff_zero (fun _ => (1 : ℂ))
  simpa only [ha0] using hupper

end ErdosProblems.Erdos1041
end
