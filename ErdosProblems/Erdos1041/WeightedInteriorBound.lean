import ErdosProblems.Erdos1041.WeightedPoissonIdentity
import ErdosProblems.Erdos1041.PoissonNormSquare
import ErdosProblems.Erdos1041.WeightedAnalyticModulus

/-! Finite interior weighted point bound. Candidate pending compilation. -/
open scoped BigOperators ComplexConjugate NNReal ENNReal
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Real Metric

/-- The actual finite weighted point-value inequality, with an explicit
analytic radius. No Poisson or energy inequality is assumed as input. -/
theorem weighted_interior_point_le_energy {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (R : ℝ≥0) (hR : 1 < R)
    (hc : ∀ j, ‖c j‖ * (R : ℝ) < 1) :
    (∑ j, w j * ‖weightedAnalyticLog w c (c j)‖ ^ 2) ≤
      circleAverage (fun z => ‖weightedAnalyticLog w c z‖ ^ 2 *
        (∑ j, w j * poissonKernel 0 (c j) z)) 0 1 := by
  classical
  let g := weightedAnalyticLog w c
  have hc1 : ∀ j, ‖c j‖ < 1 := by
    intro j
    have h := (mul_le_mul_of_nonneg_left
      (le_of_lt (show (1 : ℝ) < R by exact_mod_cast hR)) (norm_nonneg (c j))).trans_lt (hc j)
    simpa only [mul_one] using h
  have hg : DiffContOnCl ℂ g (ball 0 1) := by
    exact (diffContOnCl_weightedAnalyticLog w c R hc).mono
      (ball_subset_ball (le_of_lt (show (1 : ℝ) < R by exact_mod_cast hR)))
  have hgc : ContinuousOn g (sphere 0 1) :=
    hg.2.mono (sphere_subset_closedBall.trans_eq
      (closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)).symm)
  have hp : ∀ j, ContinuousOn (poissonKernel 0 (c j)) (sphere 0 1) := by
    intro j
    have hne : ∀ z ∈ sphere (0 : ℂ) 1, z - c j ≠ 0 := by
      intro z hz he
      have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
      have he' : z = c j := sub_eq_zero.mp he
      rw [he'] at hz1
      linarith [hc1 j]
    unfold poissonKernel
    simp only [sub_zero]
    fun_prop (disch := aesop)
  have hi : ∀ j, CircleIntegrable
      (fun z => w j * (poissonKernel 0 (c j) z * ‖g z‖ ^ 2)) 0 1 := by
    intro j
    exact ContinuousOn.circleIntegrable (by norm_num)
      (continuousOn_const.mul ((hp j).mul (hgc.norm.pow 2)))
  have hsum : (∑ j, w j * ‖g (c j)‖ ^ 2) ≤
      ∑ j, w j * circleAverage (fun z => poissonKernel 0 (c j) z * ‖g z‖ ^ 2) 0 1 := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (norm_sq_le_poisson_circleAverage hg (hc1 j)) (hw0 j)
  have heq : (∑ j, w j * circleAverage
      (fun z => poissonKernel 0 (c j) z * ‖g z‖ ^ 2) 0 1) =
      circleAverage (fun z => ‖g z‖ ^ 2 *
        (∑ j, w j * poissonKernel 0 (c j) z)) 0 1 := by
    calc
      _ = ∑ j, circleAverage
          (fun z => w j * (poissonKernel 0 (c j) z * ‖g z‖ ^ 2)) 0 1 := by
        apply Finset.sum_congr rfl
        intro j _
        symm
        simpa only [smul_eq_mul] using
          (circleAverage_fun_smul (a := w j)
            (f := fun z => poissonKernel 0 (c j) z * ‖g z‖ ^ 2) (c := 0) (R := 1))
      _ = circleAverage (fun z => ∑ j,
          w j * (poissonKernel 0 (c j) z * ‖g z‖ ^ 2)) 0 1 :=
        (circleAverage_fun_sum (fun j _ => hi j)).symm
      _ = _ := by
        congr 1
        funext z
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [heq] at hsum
  exact hsum

/-- The non-strict bound consumes the actual Poisson majorisation and energy. -/
theorem weighted_interior_point_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (R : ℝ≥0) (hR : 1 < R)
    (hc : ∀ j, ‖c j‖ * (R : ℝ) < 1) :
    (∑ j, w j * ‖weightedAnalyticLog w c (c j)‖ ^ 2) ≤ 1 :=
  (weighted_interior_point_le_energy w c hw0 hw R hR hc).trans
    (circle_weighted_poisson_energy_le_one w c hw R hR hc)

/-- Literal weighted geometric products inherit the interior point bound. -/
theorem weighted_interior_product_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (R : ℝ≥0) (hR : 1 < R)
    (hc : ∀ j, ‖c j‖ * (R : ℝ) < 1) :
    (∑ j, w j * (∏ k, ‖1 - conj (c k) * c j‖ ^ w k) ^ 2) ≤ 1 := by
  have hc1 : ∀ j, ‖c j‖ < 1 := by
    intro j
    have h := (mul_le_mul_of_nonneg_left
      (le_of_lt (show (1 : ℝ) < R by exact_mod_cast hR)) (norm_nonneg (c j))).trans_lt (hc j)
    simpa only [mul_one] using h
  have hm : ∀ j, ‖weightedAnalyticLog w c (c j)‖ =
      ∏ k, ‖1 - conj (c k) * c j‖ ^ w k := by
    intro j
    apply norm_weightedAnalyticLog_of_norm_bound
    intro k
    calc
      ‖c k‖ * ‖c j‖ ≤ ‖c k‖ * 1 :=
        mul_le_mul_of_nonneg_left (hc1 j).le (norm_nonneg _)
      _ < 1 := by simpa only [mul_one] using hc1 k
  simpa only [hm] using weighted_interior_point_bound w c hw0 hw R hR hc

end ErdosProblems.Erdos1041
end
