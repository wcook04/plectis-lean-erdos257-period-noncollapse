import ErdosProblems.Erdos1041.WeightedClosedDisc
import ErdosProblems.Erdos1041.TaylorFiniteDeficitR10
import ErdosProblems.Erdos1041.WeightedCauchyTransportR10

/-! Actual finite and infinite coefficient deficits on the CLOSED unit disc.
The endpoint is obtained from finite sums before taking the coefficient-series
supremum. All compilation and axiom audits are UNRUN. -/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate NNReal ENNReal Topology
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Real Metric Filter

def weightedGeometric {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (z : ℂ) : ℝ :=
  ∏ k, ‖1 - conj (c k) * z‖ ^ w k

def weightedQuadratic {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) : ℝ :=
  ∑ j, w j * weightedGeometric w c (c j) ^ 2

theorem weightedQuadratic_nonneg {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j) :
    0 ≤ weightedQuadratic w c :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hw0 j) (sq_nonneg _))

/-- The finite coefficient estimate is supplied by the actual analytic function,
not an additional energy or point-value assumption. -/
theorem weighted_interior_add_finite_deficit_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (R : ℝ≥0) (hR : 1 < R)
    (hc : ∀ j, ‖c j‖ * (R : ℝ) < 1) (s : Finset ℕ) :
    weightedQuadratic w c + ∑ n ∈ s, taylorDeficitTerm
      (fun k => cauchyPowerSeries (weightedAnalyticLog w c) 0 R k
        (fun _ => (1 : ℂ))) n ≤ 1 := by
  have hc1 : ∀ j, ‖c j‖ < 1 := by
    intro j
    have h := (mul_le_mul_of_nonneg_left
      (le_of_lt (show (1 : ℝ) < R by exact_mod_cast hR)) (norm_nonneg (c j))).trans_lt (hc j)
    simpa only [mul_one] using h
  have hm : ∀ j, ‖weightedAnalyticLog w c (c j)‖ = weightedGeometric w c (c j) := by
    intro j
    apply norm_weightedAnalyticLog_of_norm_bound
    intro k
    exact (mul_le_mul_of_nonneg_left (hc1 j).le (norm_nonneg _)).trans_lt
      (by simpa only [mul_one] using hc1 k)
  have hp := weighted_interior_point_le_energy w c hw0 hw R hR hc
  simp only [hm] at hp
  change weightedQuadratic w c ≤ _ at hp
  have heq : circleAverage (fun z => ‖weightedAnalyticLog w c z‖ ^ 2 *
      (∑ j, w j * poissonKernel 0 (c j) z)) 0 1 =
      circleAverage (fun z => ‖weightedAnalyticLog w c z‖ ^ 2 -
        2 * (z * deriv (weightedAnalyticLog w c) z *
          conj (weightedAnalyticLog w c z)).re) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
    change ‖weightedAnalyticLog w c z‖ ^ 2 *
        (∑ j, w j * poissonKernel 0 (c j) z) =
      ‖weightedAnalyticLog w c z‖ ^ 2 -
        2 * (z * deriv (weightedAnalyticLog w c) z *
          conj (weightedAnalyticLog w c z)).re
    rw [weighted_poisson_log_identity w c hw hc1 hz1]
    exact weightedAnalyticLog_energy_identity w c z (by
      intro j
      simpa only [hz1, mul_one] using hc1 j)
  rw [heq] at hp
  have he := circle_taylor_energy_add_finite_deficit_le
    (diffContOnCl_weightedAnalyticLog w c R hc) hR s
  simp only [weightedAnalyticLog_zero, norm_one, one_pow] at he
  linarith

def weightedRadialSeq (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ n

theorem weightedRadialSeq_nonneg (n : ℕ) : 0 ≤ weightedRadialSeq n := by
  have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := n)
  dsimp [weightedRadialSeq]
  linarith

theorem weightedRadialSeq_lt_one (n : ℕ) : weightedRadialSeq n < 1 := by
  have h := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n
  dsimp [weightedRadialSeq]
  linarith

theorem weightedRadialSeq_tendsto : Tendsto weightedRadialSeq atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ n) atTop
      (𝓝 ((1 : ℝ) - 0)) := tendsto_const_nhds.sub
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  simpa only [weightedRadialSeq, sub_zero] using h

theorem continuous_weightedQuadratic_radial {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j) :
    Continuous (fun r : ℝ => weightedQuadratic w (fun j => (r : ℂ) * c j)) := by
  unfold weightedQuadratic weightedGeometric
  apply continuous_finset_sum
  intro j _
  apply continuous_const.mul
  apply Continuous.pow
  apply continuous_finset_prod
  intro k _
  apply (Real.continuous_rpow_const (hw0 k)).comp
  fun_prop

/-- Finite retained deficits survive the boundary limit, coefficient by
coefficient using the EXACT r^n transport law. -/
theorem weighted_closed_disc_add_finite_deficit_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) (s : Finset ℕ) :
    weightedQuadratic w c + ∑ n ∈ s,
      taylorDeficitTerm (weightedTaylorCoeff w c) n ≤ 1 := by
  classical
  let F : ℝ → ℝ := fun r => weightedQuadratic w (fun j => (r : ℂ) * c j) +
    ∑ n ∈ s, taylorDeficitTerm (fun k => (r : ℂ) ^ k * weightedTaylorCoeff w c k) n
  have hF : Continuous F := by
    apply (continuous_weightedQuadratic_radial w c hw0).add
    apply continuous_finset_sum
    intro n _
    by_cases hn : n = 0
    · simp only [taylorDeficitTerm, if_pos hn]
      exact continuous_const
    · simp only [taylorDeficitTerm, if_neg hn]
      fun_prop
  have hbound : ∀ N : ℕ, F (weightedRadialSeq N) ≤ 1 := by
    intro N
    let r := weightedRadialSeq N
    have hr0 : 0 ≤ r := weightedRadialSeq_nonneg N
    have hr1 : r < 1 := weightedRadialSeq_lt_one N
    have hrc : ∀ j, ‖(r : ℂ) * c j‖ < 1 := by
      intro j
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      exact (mul_le_mul_of_nonneg_left (hc j) hr0).trans_lt
        (by simpa only [mul_one] using hr1)
    obtain ⟨R, hR, hRc⟩ := exists_weighted_interior_radius (fun j => (r : ℂ) * c j) hrc
    have h := weighted_interior_add_finite_deficit_le w (fun j => (r : ℂ) * c j)
      hw0 hw R hR hRc s
    have he : (fun k => cauchyPowerSeries
        (weightedAnalyticLog w (fun j => (r : ℂ) * c j)) 0 R k (fun _ => (1 : ℂ))) =
        (fun k => (r : ℂ) ^ k * weightedTaylorCoeff w c k) := by
      funext k
      exact weighted_cauchy_coefficient_radial w c hc r R
        (lt_trans (by norm_num) hR) hRc k
    rw [he] at h
    exact h
  have hlim := le_of_tendsto (hF.continuousAt.tendsto.comp weightedRadialSeq_tendsto)
    (Eventually.of_forall hbound)
  simpa only [F, Complex.ofReal_one, one_mul, one_pow] using hlim

/-- The nonnegative deficit series is genuinely summable at the boundary.
The infinite-sum inequality follows from the finite estimates, not from an
unjustified interchange at |z|=1. -/
theorem weighted_closed_disc_full_deficit {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) :
    Summable (taylorDeficitTerm (weightedTaylorCoeff w c)) ∧
    weightedQuadratic w c + ∑' n, taylorDeficitTerm (weightedTaylorCoeff w c) n ≤ 1 := by
  have hnonneg : 0 ≤ taylorDeficitTerm (weightedTaylorCoeff w c) :=
    fun n => taylorDeficitTerm_nonneg _ n
  have hfinite (s : Finset ℕ) :
      ∑ n ∈ s, taylorDeficitTerm (weightedTaylorCoeff w c) n ≤ 1 - weightedQuadratic w c := by
    have h := weighted_closed_disc_add_finite_deficit_le w c hw0 hw hc s
    linarith
  refine ⟨summable_of_sum_le hnonneg hfinite, ?_⟩
  have h := Real.tsum_le_of_sum_le hnonneg hfinite
  linarith

theorem weighted_closed_disc_single_deficit {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    weightedQuadratic w c + ((2 : ℝ) * k - 1) * ‖weightedTaylorCoeff w c k‖ ^ 2 ≤ 1 := by
  have h := weighted_closed_disc_add_finite_deficit_le w c hw0 hw hc {k}
  simpa only [Finset.sum_singleton, taylorDeficitTerm,
    if_neg (by omega : k ≠ 0)] using h

theorem weightedTaylorCoeff_eq_zero_of_equality {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1)
    (heq : weightedQuadratic w c = 1) (k : ℕ) (hk : 1 ≤ k) :
    weightedTaylorCoeff w c k = 0 := by
  have h := weighted_closed_disc_single_deficit w c hw0 hw hc k hk
  rw [heq] at h
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 0 < (2 : ℝ) * k - 1 := by linarith
  have hprod : ((2 : ℝ) * k - 1) * ‖weightedTaylorCoeff w c k‖ ^ 2 ≤
      ((2 : ℝ) * k - 1) * 0 := by linarith
  have hs := (mul_le_mul_iff_of_pos_left ht).mp hprod
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (weightedTaylorCoeff w c k)])

end ErdosProblems.Erdos1041
end
