import ErdosProblems.Erdos1041.TaylorCircleEnergy

/-! Classical degree-weighted cross energy, from actual analytic Taylor
coefficients. Candidate source: neither this module nor its pending Taylor
prerequisites are promoted by its presence on disk. -/
open scoped NNReal ENNReal

noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Real Metric
open scoped ComplexConjugate

/-- Diagonal extraction with the first coefficient sequence weighted by its
actual degree identifies the radial derivative cross integral. -/
theorem hasSum_cauchy_derivative_circle_product {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) :
    HasSum (fun n : ℕ => (n : ℂ) * cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ)) *
      conj (cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))))
      (circleAverage (fun z => z * deriv g z * conj (g z)) 0 1) := by
  let a : ℕ → ℂ := fun n : ℕ => cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))
  have hcoeff := summable_cauchy_coefficient_and_degree hg hR
  have hs := hasSum_taylor_diagonal_circle (fun n : ℕ => (n : ℂ) * a n) a
    hcoeff.2 hcoeff.1
  have heq : circleAverage (fun z => ∑' q : ℕ × ℕ,
      ((q.1 : ℂ) * a q.1) * conj (a q.2) * z ^ q.1 * conj (z ^ q.2)) 0 1 =
      circleAverage (fun z => z * deriv g z * conj (g z)) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    have hz' : z ∈ sphere (0 : ℂ) 1 := by simpa using hz
    have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz'
    have hgz := hasSum_cauchy_on_unit_circle hg hR hz'
    have hdz := hasSum_degree_cauchy_on_unit_circle hg hR hz'
    have hcgz : HasSum (fun n : ℕ => conj (a n * z ^ n)) (conj (g z)) := by
      simpa only [Complex.conjCLE_apply] using
        Complex.conjCLE.toContinuousLinearMap.hasSum hgz
    have hn : Summable (fun n : ℕ => ‖(n : ℂ) * a n * z ^ n‖) := by
      simpa only [norm_mul, norm_pow, hz1, one_pow, mul_one] using hcoeff.2
    have hcn : Summable (fun n : ℕ => ‖conj (a n * z ^ n)‖) := by
      simpa only [Complex.norm_conj, norm_mul, norm_pow, hz1, one_pow, mul_one]
        using hcoeff.1
    have hp : HasSum
        (fun q : ℕ × ℕ => ((q.1 : ℂ) * a q.1 * z ^ q.1) *
          conj (a q.2 * z ^ q.2)) (z * deriv g z * conj (g z)) :=
      hasSum_complex_product_of_norms (fun n : ℕ => (n : ℂ) * a n * z ^ n)
        (fun n : ℕ => conj (a n * z ^ n)) hdz hcgz hn hcn
    calc
      _ = ∑' q : ℕ × ℕ, ((q.1 : ℂ) * a q.1 * z ^ q.1) *
          conj (a q.2 * z ^ q.2) := by
        apply tsum_congr
        intro q
        simp only [map_mul]
        ring
      _ = z * deriv g z * conj (g z) := hp.tsum_eq
  rw [heq] at hs
  exact hs

/-- The real radial-derivative energy is the degree-weighted norm-square
coefficient series. The function and coefficient suppliers are actual analytic
objects, not an assumed energy identity. -/
theorem hasSum_cauchy_derivative_circle_energy {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) :
    HasSum (fun n : ℕ => (n : ℝ) *
      ‖cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))‖ ^ 2)
      (circleAverage (fun z => (z * deriv g z * conj (g z)).re) 0 1) := by
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
  have hi : CircleIntegrable (fun z => z * deriv g z * conj (g z)) 0 1 :=
    ContinuousOn.circleIntegrable (by norm_num)
      ((continuousOn_id.mul hd).mul (Complex.continuous_conj.comp_continuousOn hc))
  have h := Complex.reCLM.hasSum (hasSum_cauchy_derivative_circle_product hg hR)
  rw [← Complex.reCLM.circleAverage_comp_comm hi] at h
  simpa only [Function.comp_def, Complex.reCLM_apply, mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using h

end ErdosProblems.Erdos1041
end
