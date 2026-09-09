import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Absolute series transport through normalized circle integration. This is the
infinite interchange step needed for Taylor energy: it applies to the double
index `(n,k)` once a geometric coefficient majorant has been established.
No energy inequality or final integral identity is an assumed hypothesis.
Candidate source, not yet compiled.
-/
noncomputable section
namespace ErdosProblems.Erdos1041
open MeasureTheory Set Real
open scoped ComplexConjugate

/-- A summable uniform norm majorant permits termwise circle averaging.
The countable index permits direct application to Taylor double products. -/
theorem hasSum_circleAverage_of_uniform_majorant {ι : Type*} [Countable ι]
    (F : ι → ℂ → ℂ) (b : ι → ℝ)
    (hF : ∀ i, CircleIntegrable (F i) 0 1) (hb : Summable b)
    (hbound : ∀ i z, z ∈ Metric.sphere (0 : ℂ) 1 → ‖F i z‖ ≤ b i) :
    HasSum (fun i => circleAverage (F i) 0 1)
      (circleAverage (fun z => ∑' i, F i z) 0 1) := by
  let T : ℝ := 2 * Real.pi
  have hT : 0 ≤ T := Real.two_pi_pos.le
  let f : ι → ℝ → ℂ := fun i θ => F i (circleMap 0 1 θ)
  have hi : ∀ i, IntervalIntegrable (f i) volume 0 T := fun i => hF i
  have hint : ∀ i, Integrable (f i) (volume.restrict (Ioc 0 T)) := fun i => (hi i).1
  have hnorm : ∀ i, (∫ θ in 0..T, ‖f i θ‖) ≤ T * b i := by
    intro i
    have hm := intervalIntegral.integral_mono_on hT (hi i).norm
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => b i) volume 0 T)
      (fun θ _ => hbound i _ (by simpa using circleMap_mem_sphere' (0 : ℂ) (1 : ℝ) θ))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hm
  have hs : Summable (fun i => ∫ θ, ‖f i θ‖ ∂volume.restrict (Ioc 0 T)) := by
    apply (hb.mul_left T).of_nonneg_of_le
    · intro i
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro i
      simpa only [intervalIntegral.integral_of_le hT] using hnorm i
  have hsum := hasSum_integral_of_summable_integral_norm hint hs
  have hscaled := hsum.const_smul ((2 * Real.pi)⁻¹ : ℝ)
  simpa only [circleAverage, intervalIntegral.integral_of_le hT, f, T] using hscaled

/-- Equality form of the absolute circle-series transport. -/
theorem circleAverage_tsum_of_uniform_majorant {ι : Type*} [Countable ι]
    (F : ι → ℂ → ℂ) (b : ι → ℝ)
    (hF : ∀ i, CircleIntegrable (F i) 0 1) (hb : Summable b)
    (hbound : ∀ i z, z ∈ Metric.sphere (0 : ℂ) 1 → ‖F i z‖ ≤ b i) :
    circleAverage (fun z => ∑' i, F i z) 0 1 = ∑' i, circleAverage (F i) 0 1 :=
  (hasSum_circleAverage_of_uniform_majorant F b hF hb hbound).tsum_eq.symm

/-- Actual Taylor double products admit termwise circle integration when
both scalar coefficient sequences are absolutely summable. For the derivative
energy use `a n = n * coefficient n`; analyticity beyond the circle supplies
both absolute-summability hypotheses by geometric coefficient bounds. -/
theorem hasSum_circleAverage_taylor_double (a b : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖)) :
    HasSum (fun q : ℕ × ℕ => circleAverage
      (fun z => a q.1 * conj (b q.2) * z ^ q.1 * conj (z ^ q.2)) 0 1)
      (circleAverage (fun z => ∑' q : ℕ × ℕ,
        a q.1 * conj (b q.2) * z ^ q.1 * conj (z ^ q.2)) 0 1) := by
  apply hasSum_circleAverage_of_uniform_majorant _
    (fun q : ℕ × ℕ => ‖a q.1‖ * ‖b q.2‖)
  · intro q
    apply ContinuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
    fun_prop
  · exact ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  · intro q z hz
    have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    simp only [norm_mul, Complex.norm_conj, norm_pow, hz1, one_pow, mul_one, le_refl]

end ErdosProblems.Erdos1041
end
