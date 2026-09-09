import ErdosProblems.Erdos1041.CircleSeriesTransport
import ErdosProblems.Erdos1041.TaylorDiagonal
import ErdosProblems.Erdos1041.TaylorCoefficientMajorant
import ErdosProblems.Erdos1041.TaylorCircleIdentification

/-! Exact diagonal circle energy from actual Cauchy coefficients. Candidate
pending focused compilation. This is Parseval's classical identity, not the
full-disc weighted geometric-mean theorem. -/
open scoped NNReal ENNReal

noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Real Metric
open scoped ComplexConjugate

/-- Absolute double-series transport and monomial orthogonality extract the
diagonal. No diagonal or energy identity is assumed. -/
theorem hasSum_taylor_diagonal_circle (a b : ℕ → ℂ)
    (ha : Summable (fun n : ℕ => ‖a n‖)) (hb : Summable (fun n : ℕ => ‖b n‖)) :
    HasSum (fun n : ℕ => a n * conj (b n))
      (circleAverage (fun z => ∑' q : ℕ × ℕ,
        a q.1 * conj (b q.2) * z ^ q.1 * conj (z ^ q.2)) 0 1) := by
  classical
  have hs := hasSum_circleAverage_taylor_double a b ha hb
  have hterm : ∀ n m, circleAverage
      (fun z : ℂ => a n * conj (b m) * z ^ n * conj (z ^ m)) 0 1 =
        if n = m then a n * conj (b m) else 0 := by
    intro n m
    calc
      _ = (a n * conj (b m)) *
          circleAverage (fun z : ℂ => z ^ n * conj (z ^ m)) 0 1 := by
        simpa only [smul_eq_mul, mul_assoc] using
          (circleAverage_fun_smul (a := a n * conj (b m))
            (f := fun z : ℂ => z ^ n * conj (z ^ m)) (c := 0) (R := 1))
      _ = _ := by rw [circleAverage_monomial_conj]; split_ifs <;> simp
  simp_rw [hterm] at hs
  apply hs.prod_fiberwise
  intro n
  simpa using (hasSum_single n (fun m hm => by simp [Ne.symm hm]) :
    HasSum (fun m => if n = m then a n * conj (b m) else 0)
      (if n = n then a n * conj (b n) else 0))

/-- Keep the product-series inference abstract before substituting Cauchy coefficients. -/
theorem hasSum_complex_product_of_norms (f g : ℕ → ℂ) {u v : ℂ}
    (hf : HasSum f u) (hg : HasSum g v)
    (hnf : Summable (fun n : ℕ => ‖f n‖))
    (hng : Summable (fun n : ℕ => ‖g n‖)) :
    HasSum (fun q : ℕ × ℕ => f q.1 * g q.2) (u * v) :=
  HasSum.mul (f := f) (g := g) hf hg
    (summable_mul_of_summable_norm (f := f) (g := g) hnf hng)

/-- Cauchy's actual coefficients give the norm-square energy of the analytic
function on the unit circle. This complex-valued form precedes real projection. -/
theorem hasSum_cauchy_circle_product {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) :
    HasSum (fun n : ℕ => cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ)) *
      conj (cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))))
      (circleAverage (fun z => g z * conj (g z)) 0 1) := by
  let a : ℕ → ℂ := fun n : ℕ => cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))
  have ha : Summable (fun n : ℕ => ‖a n‖) :=
    (summable_cauchy_coefficient_and_degree hg hR).1
  have hs := hasSum_taylor_diagonal_circle a a ha ha
  have heq : circleAverage (fun z => ∑' q : ℕ × ℕ,
      a q.1 * conj (a q.2) * z ^ q.1 * conj (z ^ q.2)) 0 1 =
      circleAverage (fun z => g z * conj (g z)) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    have hz' : z ∈ sphere (0 : ℂ) 1 := by simpa using hz
    have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz'
    have hgz : HasSum (fun n : ℕ => a n * z ^ n) (g z) :=
      hasSum_cauchy_on_unit_circle hg hR hz'
    have hcgz : HasSum (fun n : ℕ => conj (a n * z ^ n)) (conj (g z)) := by
      simpa only [Complex.conjCLE_apply] using
        Complex.conjCLE.toContinuousLinearMap.hasSum hgz
    have hn : Summable (fun n : ℕ => ‖a n * z ^ n‖) := by
      simpa only [norm_mul, norm_pow, hz1, one_pow, mul_one] using ha
    have hcn : Summable (fun n : ℕ => ‖conj (a n * z ^ n)‖) := by
      simpa only [Complex.norm_conj] using hn
    have hp : HasSum
        (fun q : ℕ × ℕ => (a q.1 * z ^ q.1) * conj (a q.2 * z ^ q.2))
        (g z * conj (g z)) :=
      hasSum_complex_product_of_norms (fun n : ℕ => a n * z ^ n)
        (fun n : ℕ => conj (a n * z ^ n)) hgz hcgz hn hcn
    calc
      _ = ∑' q : ℕ × ℕ, (a q.1 * z ^ q.1) * conj (a q.2 * z ^ q.2) := by
        apply tsum_congr
        intro q
        simp only [map_mul]
        ring
      _ = g z * conj (g z) := hp.tsum_eq
  rw [heq] at hs
  exact hs

/-- Classical Parseval identity, stated as a real HasSum for the actual
Cauchy coefficient norms. Analyticity beyond the unit circle supplies every
summability and interchange premise. -/
theorem hasSum_cauchy_circle_norm_sq {g : ℂ → ℂ} {R : ℝ≥0}
    (hg : DiffContOnCl ℂ g (ball 0 R)) (hR : 1 < R) :
    HasSum (fun n : ℕ => ‖cauchyPowerSeries g 0 R n (fun _ => (1 : ℂ))‖ ^ 2)
      (circleAverage (fun z => ‖g z‖ ^ 2) 0 1) := by
  have hc : ContinuousOn g (sphere (0 : ℂ) 1) := by
    apply hg.continuousOn.mono
    intro z hz
    apply subset_closure
    have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
    simpa [mem_ball, dist_eq_norm, hz1] using
      (show (1 : ℝ) < R by exact_mod_cast hR)
  have hi : CircleIntegrable (fun z => g z * conj (g z)) 0 1 :=
    ContinuousOn.circleIntegrable (by norm_num) (hc.mul (Complex.continuous_conj.comp_continuousOn hc))
  have h := Complex.reCLM.hasSum (hasSum_cauchy_circle_product hg hR)
  rw [← Complex.reCLM.circleAverage_comp_comm hi] at h
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq] using h

end ErdosProblems.Erdos1041
end
