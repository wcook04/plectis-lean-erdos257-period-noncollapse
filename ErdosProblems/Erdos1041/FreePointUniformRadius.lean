import ErdosProblems.Erdos1041.LogKernelCentralCertificate

/-!
# A uniform central radius for every finite free-point mean

The row certificate is produced from a common bound `a < 1` on the squared
radii. With `L = -log (1-a)`, the scalar condition `exp L ≤ 1 + 2L`
implies the free-point mean inequality in every positive degree.
-/

open scoped BigOperators ComplexConjugate

namespace ErdosProblems.Erdos1041

private theorem norm_lt_one_of_sq_le {z : ℂ} {a : ℝ}
    (ha : a < 1) (hz : ‖z‖ ^ 2 ≤ a) : ‖z‖ < 1 := by
  nlinarith [norm_nonneg z]

private theorem log_kernel_le_radius {z w : ℂ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hz : ‖z‖ ^ 2 ≤ a) (hw : ‖w‖ ^ 2 ≤ a) :
    Real.log ‖1 - conj z * w‖ ≤ -Real.log (1 - a) := by
  have hden : 0 < 1 - a := by linarith
  have hprod : ‖z‖ * ‖w‖ ≤ a := by nlinarith [sq_nonneg (‖z‖ - ‖w‖)]
  have hi : 1 + a ≤ (1 - a)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg a]
  have hn : ‖1 - conj z * w‖ ≤ (1 - a)⁻¹ := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖conj z * w‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ * ‖w‖ := by rw [norm_one, norm_mul, Complex.norm_conj]
      _ ≤ 1 + a := by linarith
      _ ≤ _ := hi
  have h := Real.log_le_log
    (log_kernel_factor_pos (norm_lt_one_of_sq_le ha1 hz) (norm_lt_one_of_sq_le ha1 hw)) hn
  simpa only [Real.log_inv] using h

private theorem log_diagonal_le_radius {z : ℂ} {a : ℝ}
    (ha1 : a < 1) (hz : ‖z‖ ^ 2 ≤ a) :
    -Real.log ‖1 - conj z * z‖ ≤ -Real.log (1 - a) := by
  have hden : 0 < 1 - a := by linarith
  have hzden : 0 < 1 - ‖z‖ ^ 2 := by linarith
  have heq : ‖1 - conj z * z‖ = 1 - ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Complex.normSq_eq_norm_sq, abs_of_pos hzden]
  rw [heq, neg_le_neg_iff]
  exact Real.log_le_log hden (by linarith)

/-- A uniform squared-radius bound produces the actual adaptive certificate
for every positive number of disk points. -/
theorem freePointMean_le_of_uniform_radius
    {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hc : ∀ i, ‖c i‖ ^ 2 ≤ a)
    (hscalar : exponentialRemainder (-Real.log (1 - a)) * (-Real.log (1 - a)) ≤ 1) :
    (∑ i, (∏ j, ‖1 - conj (c i) * c j‖) ^ (1 / (m : ℝ))) ≤ m := by
  let L := -Real.log (1 - a)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : 0 ≤ L := by
    dsimp [L]
    exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have hPhi : 0 ≤ exponentialRemainder L := by
    have h := exponentialRemainder_monotone hL
    rw [exponentialRemainder_zero] at h
    linarith
  apply freePointMean_le_of_log_certificate hm c
    (fun i => norm_lt_one_of_sq_le ha1 (hc i)) (fun _ => L) (fun _ => hL)
  · intro i
    unfold logInteractionRow
    apply (div_le_iff₀ hmpos).2
    calc
      _ ≤ ∑ _j : Fin m, L := Finset.sum_le_sum
        (fun j _ => log_kernel_le_radius ha0 ha1 (hc i) (hc j))
      _ = L * m := by simp [mul_comm]
  · calc
      _ ≤ ∑ _i : Fin m, exponentialRemainder L * L := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_left (log_diagonal_le_radius ha1 (hc i)) hPhi)
      _ = (m : ℝ) * (exponentialRemainder L * L) := by simp
      _ ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left hscalar hmpos.le
      _ = m := mul_one _

/-- The scalar exponential inequality is the uniform-radius criterion in the
paper. It yields the geometric-mean inequality for the actual configuration. -/
theorem freePointMean_le_of_exp_radius
    {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hc : ∀ i, ‖c i‖ ^ 2 ≤ a)
    (hexp : Real.exp (-Real.log (1 - a)) ≤ 1 + 2 * (-Real.log (1 - a))) :
    (∑ i, (∏ j, ‖1 - conj (c i) * c j‖) ^ (1 / (m : ℝ))) ≤ m := by
  apply freePointMean_le_of_uniform_radius hm c ha0 ha1 hc
  let L := -Real.log (1 - a)
  have hL : 0 ≤ L := by
    exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  by_cases hzero : L = 0
  · change exponentialRemainder L * L ≤ 1
    simp only [hzero, mul_zero, zero_le_one]
  · have hpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hzero)
    apply (mul_le_mul_iff_left₀ hpos).mp
    have ht := exp_eq_one_add_add_sq_remainder L
    change Real.exp L ≤ 1 + 2 * L at hexp
    nlinarith

end ErdosProblems.Erdos1041
