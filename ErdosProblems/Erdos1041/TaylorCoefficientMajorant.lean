import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! Geometric coefficient majorants from an analytic disc strictly larger than
one. These supply both absolute series needed by CircleSeriesTransport.
Candidate pending focused compilation; no energy inequality is assumed. -/
open scoped NNReal ENNReal

noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Metric Set

/-- Evaluating multilinear coefficients on the constant unit vector inherits
an exponential bound whenever the convergence radius exceeds one. -/
theorem scalar_coefficient_geometric_majorant
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (hp : 1 < p.radius) :
    ∃ q ∈ Ioo (0 : ℝ) 1, ∃ C > 0,
      ∀ n, ‖p n (fun _ => (1 : ℂ))‖ ≤ C * q ^ n := by
  obtain ⟨q, hq, C, hC, hbound⟩ :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (r := 1) hp
  refine ⟨q, hq, C, hC, fun n : ℕ => ?_⟩
  have hn : ‖p n (fun _ => (1 : ℂ))‖ ≤ ‖p n‖ := by
    simpa using (p n).le_opNorm (fun _ => (1 : ℂ))
  exact hn.trans (by simpa using hbound n)

/-- A geometric bound supplies absolute summability both for coefficients
and for the coefficients of `z * g'(z)`, indexed by the original degree. -/
theorem summable_scalar_coefficient_and_degree
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (hp : 1 < p.radius) :
    Summable (fun n : ℕ => ‖p n (fun _ => (1 : ℂ))‖) ∧
    Summable (fun n : ℕ => ‖(n : ℂ) * p n (fun _ => (1 : ℂ))‖) := by
  obtain ⟨q, hq, C, hC, hbound⟩ := scalar_coefficient_geometric_majorant p hp
  have hgeom : Summable (fun n : ℕ => C * q ^ n) :=
    (summable_geometric_of_lt_one hq.1.le hq.2).mul_left C
  have hdegree : Summable (fun n : ℕ => C * ((n : ℝ) * q ^ n)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := q)
      (by simpa [Real.norm_eq_abs, abs_of_pos hq.1] using hq.2)
    simpa only [pow_one] using h.mul_left C
  constructor
  · exact hgeom.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  · apply hdegree.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    have h := mul_le_mul_of_nonneg_left (hbound n) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simpa only [norm_mul, Complex.norm_natCast, mul_left_comm] using h

/-- Cauchy's actual Taylor coefficients for a function analytic on a disc of
radius `R > 1` satisfy the geometric majorant; no coefficient decay hypothesis
is added. -/
theorem cauchy_coefficient_geometric_majorant {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) :
    ∃ q ∈ Ioo (0 : ℝ) 1, ∃ C > 0,
      ∀ n, ‖cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))‖ ≤ C * q ^ n := by
  have hseries := hg.hasFPowerSeriesOnBall (lt_trans (by norm_num) hR)
  apply scalar_coefficient_geometric_majorant
  exact lt_of_lt_of_le (by exact_mod_cast hR) hseries.r_le

/-- Absolute coefficient and degree-weighted coefficient suppliers for
termwise circle integration on the unit circle. -/
theorem summable_cauchy_coefficient_and_degree {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) :
    Summable (fun n : ℕ => ‖cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))‖) ∧
    Summable (fun n : ℕ => ‖(n : ℂ) * cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))‖) := by
  have hseries := hg.hasFPowerSeriesOnBall (lt_trans (by norm_num) hR)
  apply summable_scalar_coefficient_and_degree
  exact lt_of_lt_of_le (by exact_mod_cast hR) hseries.r_le

end ErdosProblems.Erdos1041
end
