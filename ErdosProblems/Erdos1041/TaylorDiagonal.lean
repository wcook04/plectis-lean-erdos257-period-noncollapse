import ErdosProblems.Erdos1041.CircleSeriesTransport
import Mathlib.Analysis.Complex.MeanValue

/-! Unit-circle monomial orthogonality, the diagonal extraction step after
absolute double-series transport. Candidate pending focused compilation. -/
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Real Metric
open scoped ComplexConjugate

private theorem circleAverage_monomial (n : ℕ) :
    circleAverage (fun z : ℂ => z ^ n) 0 1 = if n = 0 then 1 else 0 := by
  have h : DiffContOnCl ℂ (fun z : ℂ => z ^ n) (ball 0 |(1 : ℝ)|) :=
    (differentiable_id.pow n).diffContOnCl
  by_cases hn : n = 0
  · simpa [hn] using h.circleAverage
  · simpa [hn, zero_pow hn] using h.circleAverage

/-- Mixed monomials are orthogonal for normalized unit-circle integration.
This is an exact integral identity, with no analytic-energy bound assumed. -/
theorem circleAverage_monomial_conj (n m : ℕ) :
    circleAverage (fun z : ℂ => z ^ n * conj (z ^ m)) 0 1 =
      if n = m then 1 else 0 := by
  induction n generalizing m with
  | zero =>
    have hi : CircleIntegrable (fun z : ℂ => z ^ m) 0 1 :=
      ContinuousOn.circleIntegrable (by norm_num) (by fun_prop)
    have h := Complex.conjCLE.toContinuousLinearMap.circleAverage_comp_comm hi
    by_cases hm : m = 0
    · simp [hm, circleAverage_const]
    · simpa [hm, Function.comp_def, Complex.conjCLE_apply, circleAverage_monomial, eq_comm] using h
  | succ n ih =>
    cases m with
    | zero => simpa using circleAverage_monomial (n + 1)
    | succ m =>
      have heq : circleAverage (fun z : ℂ => z ^ (n + 1) * conj (z ^ (m + 1))) 0 1 =
          circleAverage (fun z : ℂ => z ^ n * conj (z ^ m)) 0 1 := by
        apply circleAverage_congr_sphere
        intro z hz
        have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
        have hzz : z * conj z = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz1]
          norm_num
        calc
          z ^ (n + 1) * conj (z ^ (m + 1)) =
              (z ^ n * conj (z ^ m)) * (z * conj z) := by
                simp only [pow_succ, map_mul]
                ring
          _ = z ^ n * conj (z ^ m) := by rw [hzz, mul_one]
      rw [heq, ih]
      simp

end ErdosProblems.Erdos1041
end
