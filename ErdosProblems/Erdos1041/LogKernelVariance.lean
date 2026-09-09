import ErdosProblems.Erdos1041.LogKernelEnergy
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The logarithmic row-variance bound

Cauchy--Schwarz on finite partial sums, followed by their established
limits, bounds an actual logarithmic interaction row by the total energy
times its diagonal kernel value.
-/

open scoped BigOperators ComplexConjugate
open Filter

namespace ErdosProblems.Erdos1041

private theorem sq_sum_le_of_hasSum
    (a f g : ℕ → ℝ) {A F G : ℝ}
    (ha : HasSum a A) (hf : HasSum f F) (hg : HasSum g G)
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hpoint : ∀ n, (a n) ^ 2 ≤ f n * g n) : A ^ 2 ≤ F * G := by
  have hF : 0 ≤ F := by rw [← hf.tsum_eq]; exact tsum_nonneg hf0
  have hfinite (s : Finset ℕ) : (∑ n ∈ s, a n) ^ 2 ≤ F * G := by
    have habs : |∑ n ∈ s, a n| ≤ ∑ n ∈ s, Real.sqrt (f n * g n) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro n _
      apply Real.le_sqrt_of_sq_le
      simpa only [sq_abs] using hpoint n
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
      (r := fun n => Real.sqrt (f n * g n))
      (fun n _ => hf0 n) (fun n _ => hg0 n)
      (fun n _ => Real.sq_sqrt (mul_nonneg (hf0 n) (hg0 n)))
    calc
      (∑ n ∈ s, a n) ^ 2 = |∑ n ∈ s, a n| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ n ∈ s, Real.sqrt (f n * g n)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ ≤ (∑ n ∈ s, f n) * ∑ n ∈ s, g n := hcs
      _ ≤ F * G := mul_le_mul
        (by simpa only [hf.tsum_eq] using hf.summable.sum_le_tsum s (fun n _ => hf0 n))
        (by simpa only [hg.tsum_eq] using hg.summable.sum_le_tsum s (fun n _ => hg0 n))
        (Finset.sum_nonneg fun n _ => hg0 n) hF
  exact le_of_tendsto (ha.tendsto_sum_nat.pow 2)
    (Filter.Eventually.of_forall fun N => hfinite (Finset.range N))

/-- The unnormalized row variance is bounded by the diagonal kernel times
the total logarithmic energy. All quantities come from the given points. -/
theorem log_kernel_row_sq_le_energy {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (hc : ∀ i ∈ s, ‖c i‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    (∑ j ∈ s, Real.log ‖1 - conj z * c j‖) ^ 2 ≤
      (-Real.log ‖1 - conj z * z‖) *
        (-∑ i ∈ s, ∑ j ∈ s, Real.log ‖1 - conj (c i) * c j‖) := by
  have hdiag : HasSum (fun n : ℕ => ‖z ^ n‖ ^ 2 / n)
      (-Real.log ‖1 - conj z * z‖) := by
    simpa only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq] using hasSum_log_kernel hz hz
  have hpoint (n : ℕ) :
      ((conj (z ^ n) * (∑ j ∈ s, c j ^ n)).re / n) ^ 2 ≤
        (‖z ^ n‖ ^ 2 / n) * (‖∑ j ∈ s, c j ^ n‖ ^ 2 / n) := by
    have hre : (conj (z ^ n) * (∑ j ∈ s, c j ^ n)).re ^ 2 ≤
        ‖conj (z ^ n) * (∑ j ∈ s, c j ^ n)‖ ^ 2 := by
      nlinarith [Complex.sq_norm_sub_sq_re (conj (z ^ n) * (∑ j ∈ s, c j ^ n)),
        sq_nonneg (conj (z ^ n) * (∑ j ∈ s, c j ^ n)).im]
    calc
      ((conj (z ^ n) * (∑ j ∈ s, c j ^ n)).re / n) ^ 2 ≤
          ‖conj (z ^ n) * (∑ j ∈ s, c j ^ n)‖ ^ 2 / (n : ℝ) ^ 2 := by
        rw [div_pow]
        exact div_le_div_of_nonneg_right hre (sq_nonneg _)
      _ = (‖z ^ n‖ ^ 2 / n) * (‖∑ j ∈ s, c j ^ n‖ ^ 2 / n) := by
        rw [norm_mul, Complex.norm_conj]
        ring

  have h := sq_sum_le_of_hasSum
    (fun n => (conj (z ^ n) * (∑ j ∈ s, c j ^ n)).re / n)
    (fun n => ‖z ^ n‖ ^ 2 / n)
    (fun n => ‖∑ j ∈ s, c j ^ n‖ ^ 2 / n)
    (hasSum_log_kernel_row s c hc hz) hdiag (hasSum_log_kernel_energy s c hc)
    (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))
    (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)) hpoint
  simpa only [neg_sq] using h

end ErdosProblems.Erdos1041
