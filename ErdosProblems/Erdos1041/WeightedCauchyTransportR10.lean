import ErdosProblems.Erdos1041.WeightedRadialIdentity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness

/-! Cauchy coefficients of the actual weighted function, at a fixed safe radius.
Radial transport follows from one-dimensional power-series uniqueness.
All compilation and axiom audits are UNRUN. -/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate NNReal ENNReal Topology
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Metric Filter FormalMultilinearSeries

/-- A fixed radius is essential: coefficients must not depend on a selected
radius tending to the boundary. -/
def weightedTaylorSeries {ι : Type*} [Fintype ι] (w : ι → ℝ) (c : ι → ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries (weightedAnalyticLog w c) 0 (1 / 2)

def weightedTaylorCoeff {ι : Type*} [Fintype ι] (w : ι → ℝ) (c : ι → ℂ)
    (n : ℕ) : ℂ := weightedTaylorSeries w c n (fun _ => 1)

theorem weightedTaylorSeries_hasSum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) :
    HasFPowerSeriesOnBall (weightedAnalyticLog w c) (weightedTaylorSeries w c)
      0 ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  let R : ℝ≥0 := 1 / 2
  have hR : (0 : ℝ≥0) < R := by
    norm_num [R]
  have hcR : ∀ j, ‖c j‖ * (R : ℝ) < 1 := by
    intro j
    calc
      ‖c j‖ * (R : ℝ) ≤ 1 * (R : ℝ) :=
        mul_le_mul_of_nonneg_right (hc j) R.coe_nonneg
      _ < 1 := by norm_num [R]
  have hg : DiffContOnCl ℂ (weightedAnalyticLog w c)
      (ball (0 : ℂ) (R : ℝ)) :=
    diffContOnCl_weightedAnalyticLog w c (R : ℝ) hcR
  have hs : HasFPowerSeriesOnBall (weightedAnalyticLog w c)
      (cauchyPowerSeries (weightedAnalyticLog w c) (0 : ℂ) R)
      (0 : ℂ) (R : ℝ≥0∞) :=
    DiffContOnCl.hasFPowerSeriesOnBall hg hR
  simpa only [weightedTaylorSeries, R] using hs

/-- Scalar precomposition, proved directly from the local HasSum criterion. -/
theorem hasFPowerSeriesAt_scalar_precomp {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) (t : ℂ) :
    HasFPowerSeriesAt (fun z => f (t * z)) (fun n => t ^ n • p n) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  have hloc := hasFPowerSeriesAt_iff.mp hp
  have ht : Tendsto (fun z : ℂ => t * z) (𝓝 0) (𝓝 0) := by
    simpa using
      ((continuous_const.mul continuous_id).tendsto (0 : ℂ) :
        Tendsto (fun z : ℂ => t * z) (𝓝 0) (𝓝 (t * 0)))
  filter_upwards [ht.eventually hloc] with z hz
  change HasSum (fun n => z ^ n * (t ^ n * p n (fun _ => 1))) (f (t * (0 + z)))
  change HasSum (fun n => (t * z) ^ n * p n (fun _ => 1)) (f (0 + t * z)) at hz
  convert hz using 1
  · funext n
    rw [mul_pow]
    ring
  · simp

/-- Exact transport of the Cauchy coefficient at any admissible radius.
No sign assumption on the weights or on the real contraction is needed. -/
theorem weighted_cauchy_coefficient_radial {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1)
    (r : ℝ) (R : ℝ≥0) (hR : 0 < R)
    (hRc : ∀ j, ‖(r : ℂ) * c j‖ * (R : ℝ) < 1) (n : ℕ) :
    cauchyPowerSeries (weightedAnalyticLog w (fun j => (r : ℂ) * c j))
        0 R n (fun _ => (1 : ℂ)) = (r : ℂ) ^ n * weightedTaylorCoeff w c n := by
  have hbase := (weightedTaylorSeries_hasSum w c hc).hasFPowerSeriesAt
  have hr := hasFPowerSeriesAt_scalar_precomp hbase (r : ℂ)
  have heq : (fun z => weightedAnalyticLog w c ((r : ℂ) * z)) =
      weightedAnalyticLog w (fun j => (r : ℂ) * c j) := by
    funext z
    exact (weightedAnalyticLog_radial w c r z).symm
  rw [heq] at hr
  have hnew := (diffContOnCl_weightedAnalyticLog w (fun j => (r : ℂ) * c j)
    R hRc).hasFPowerSeriesOnBall hR
  have huniq := hnew.hasFPowerSeriesAt.eq_formalMultilinearSeries hr
  exact congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1)) huniq

theorem weightedTaylorCoeff_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) :
    weightedTaylorCoeff w c 0 = 1 := by
  have h := (weightedTaylorSeries_hasSum w c hc).coeff_zero (fun _ => (1 : ℂ))
  simpa only [weightedTaylorCoeff, weightedAnalyticLog_zero] using h

/-- The first coefficient is the negative conjugate centroid. -/
theorem weightedTaylorCoeff_one {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) :
    weightedTaylorCoeff w c 1 = -conj (∑ j, (w j : ℂ) * c j) := by
  have hd := (weightedTaylorSeries_hasSum w c hc).hasFPowerSeriesAt.deriv
  change deriv (weightedAnalyticLog w c) 0 = weightedTaylorCoeff w c 1 at hd
  rw [← hd, deriv_weightedAnalyticLog_zero]
  simp only [map_sum, map_mul, Complex.conj_ofReal]

/-- If all positive-degree coefficients vanish, the actual function equals one
on the fixed half-disc. This suffices for the rational-pole argument. -/
theorem weightedAnalyticLog_eq_one_on_halfDisc {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1)
    (ha : ∀ n : ℕ, 1 ≤ n → weightedTaylorCoeff w c n = 0)
    {z : ℂ} (hz : ‖z‖ < 1 / 2) : weightedAnalyticLog w c z = 1 := by
  have hs := (weightedTaylorSeries_hasSum w c hc).hasSum (y := z) (by
    rw [Metric.eball_coe]
    simpa only [mem_ball, dist_zero_right] using hz)
  have he : (fun n : ℕ => weightedTaylorSeries w c n (fun _ => z)) =
      (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) := by
    funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    change z ^ n * weightedTaylorCoeff w c n = _
    by_cases hn : n = 0
    · subst n
      simp [weightedTaylorCoeff_zero w c hc]
    · rw [ha n (Nat.one_le_iff_ne_zero.mpr hn)]
      simp [hn]
  rw [he, zero_add] at hs
  exact hs.unique (hasSum_ite_eq 0 (1 : ℂ))

end ErdosProblems.Erdos1041
end
