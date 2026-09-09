import Mathlib.Analysis.Complex.Poisson
import Mathlib.Tactic

/-!
Analytic Poisson majorization for the squared norm. The hypotheses are only
holomorphy on the open unit disc, continuity on its closure, and an interior
sampling point. No norm-square mean inequality is an assumed supplier.
Candidate source: not yet compiled.
-/
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Metric Real
open scoped ComplexConjugate

private theorem poisson_continuousOn_unit_circle {c : ℂ} (hc : ‖c‖ < 1) :
    ContinuousOn (poissonKernel 0 c) (sphere 0 1) := by
  have hne : ∀ z ∈ sphere (0 : ℂ) 1, z - c ≠ 0 := by
    intro z hz hzero
    have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
    have hzc : z = c := sub_eq_zero.mp hzero
    rw [hzc] at hz1
    linarith
  unfold poissonKernel
  simp only [sub_zero]
  fun_prop (disch := aesop)

private theorem poisson_unit_circle_nonneg {c z : ℂ} (hc : ‖c‖ < 1)
    (hz : z ∈ sphere (0 : ℂ) 1) : 0 ≤ poissonKernel 0 c z := by
  have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
  simp only [poissonKernel, sub_zero, hz1, one_pow]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg c]

private theorem poisson_real_part_mean {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (ball 0 1)) {c : ℂ} (hc : ‖c‖ < 1) :
    circleAverage (fun z => poissonKernel 0 c z * (g z).re) 0 1 = (g c).re := by
  have hgc : ContinuousOn g (sphere 0 1) :=
    hg.2.mono (sphere_subset_closedBall.trans_eq (closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)).symm)
  have hi : CircleIntegrable (fun z => poissonKernel 0 c z • g z) 0 1 := by
    have ht := ((Complex.continuous_ofReal.comp_continuousOn
      (poisson_continuousOn_unit_circle hc)).mul hgc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [Complex.real_smul] using ht
  have hm := hg.circleAverage_poissonKernel_smul (by simpa [mem_ball, dist_eq_norm] using hc)
  have hm' : circleAverage (fun z => poissonKernel 0 c z • g z) 0 1 = g c := by
    simpa only [Pi.smul_apply] using hm
  have hr := Complex.reCLM.circleAverage_comp_comm hi
  rw [hm'] at hr
  simpa only [Function.comp_def, map_smul, Complex.reCLM_apply, smul_eq_mul] using hr

/-- Squared modulus is majorized by its actual Poisson boundary average.
The proof averages the quadratic tangent inequality, equivalently the
nonnegative kernel times `normSq (g z - g c)`. -/
theorem normSq_le_poisson_circleAverage {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (ball 0 1)) {c : ℂ} (hc : ‖c‖ < 1) :
    Complex.normSq (g c) ≤
      circleAverage (fun z => poissonKernel 0 c z * Complex.normSq (g z)) 0 1 := by
  let P := poissonKernel 0 c
  let h : ℂ → ℂ := fun z => g z * conj (g c)
  have hh : DiffContOnCl ℂ h (ball 0 1) := by
    simpa only [h, smul_eq_mul] using hg.smul_const (conj (g c))
  have hpmean : circleAverage P 0 1 = 1 := by
    have ht := poisson_real_part_mean
      (diffContOnCl_const : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball 0 1)) hc
    simpa only [Complex.one_re, mul_one, P] using ht
  have hhmean : circleAverage (fun z => P z * (h z).re) 0 1 = Complex.normSq (g c) := by
    have ht := poisson_real_part_mean hh hc
    simpa only [h, P, Complex.mul_conj, Complex.ofReal_re] using ht
  have hpc := poisson_continuousOn_unit_circle hc
  have hgc : ContinuousOn g (sphere 0 1) :=
    hg.2.mono (sphere_subset_closedBall.trans_eq (closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)).symm)
  have hhc : ContinuousOn h (sphere 0 1) := hgc.mul continuousOn_const
  have hlinear : CircleIntegrable (fun z => P z * (h z).re) 0 1 :=
    (hpc.mul (Complex.continuous_re.comp_continuousOn hhc)).circleIntegrable (by norm_num)
  have hpint : CircleIntegrable P 0 1 := hpc.circleIntegrable (by norm_num)
  have hquad : CircleIntegrable (fun z => P z * Complex.normSq (g z)) 0 1 :=
    (hpc.mul (Complex.continuous_normSq.comp_continuousOn hgc)).circleIntegrable (by norm_num)
  have htwo : CircleIntegrable (fun z => 2 * (P z * (h z).re)) 0 1 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hlinear.const_smul (a := (2 : ℝ))
  have hconst : CircleIntegrable (fun z => Complex.normSq (g c) * P z) 0 1 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hpint.const_smul (a := Complex.normSq (g c))
  have hleft : CircleIntegrable
      (fun z => 2 * (P z * (h z).re) - Complex.normSq (g c) * P z) 0 1 :=
    htwo.sub hconst
  have hbound := circleAverage_mono hleft hquad (by
    intro z hz
    have hz' : z ∈ sphere (0 : ℂ) 1 := by simpa using hz
    have hp : 0 ≤ P z := poisson_unit_circle_nonneg hc hz'
    have ht : 2 * (h z).re - Complex.normSq (g c) ≤ Complex.normSq (g z) := by
      have hn := Complex.normSq_nonneg (g z - g c)
      simp only [h, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.conj_re, Complex.conj_im] at hn ⊢
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht hp])
  have heq : circleAverage
      (fun z => 2 * (P z * (h z).re) - Complex.normSq (g c) * P z) 0 1 =
      Complex.normSq (g c) := by
    rw [circleAverage_fun_sub htwo hconst]
    have htwoavg : circleAverage (fun z => 2 * (P z * (h z).re)) 0 1 =
        2 * circleAverage (fun z => P z * (h z).re) 0 1 := by
      simpa only [smul_eq_mul] using
        (circleAverage_fun_smul (a := (2 : ℝ)) (f := fun z => P z * (h z).re)
          (c := (0 : ℂ)) (R := (1 : ℝ)))
    have hconstavg : circleAverage (fun z => Complex.normSq (g c) * P z) 0 1 =
        Complex.normSq (g c) * circleAverage P 0 1 := by
      simpa only [smul_eq_mul] using
        (circleAverage_fun_smul (a := Complex.normSq (g c)) (f := P)
          (c := (0 : ℂ)) (R := (1 : ℝ)))
    rw [htwoavg, hconstavg, hhmean, hpmean]
    ring
  rw [heq] at hbound
  exact hbound

/-- The same majorization in the norm-square notation used by the paper. -/
theorem norm_sq_le_poisson_circleAverage {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (ball 0 1)) {c : ℂ} (hc : ‖c‖ < 1) :
    ‖g c‖ ^ 2 ≤
      circleAverage (fun z => poissonKernel 0 c z * ‖g z‖ ^ 2) 0 1 := by
  simpa only [Complex.normSq_eq_norm_sq] using normSq_le_poisson_circleAverage hg hc

end ErdosProblems.Erdos1041
end
