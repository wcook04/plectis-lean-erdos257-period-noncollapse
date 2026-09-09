import Mathlib

/-!
# Exact polynomial barriers for the retained one-root counterexample

AUTHORED / UNRUN. These are actual inequalities for z^8 - (3/2)z,
not a claimed proof of Rouché, component topology, or perimeter monotonicity.
The component/perimeter assembly remains an explicit coverage obligation.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ReturnV5
open Polynomial

def lobePolynomial : ℂ[X] := X ^ 8 - C (3 / 2) * X

theorem lobe_eval (z : ℂ) : lobePolynomial.eval z = z ^ 8 - (3 / 2 : ℂ) * z := by
  simp [lobePolynomial]

theorem lobe_eval_factor (z : ℂ) :
    lobePolynomial.eval z = z * (z ^ 7 - (3 / 2 : ℂ)) := by
  rw [lobe_eval]
  ring

theorem lobe_root_iff (z : ℂ) :
    lobePolynomial.eval z = 0 ↔ z = 0 ∨ z ^ 7 = (3 / 2 : ℂ) := by
  rw [lobe_eval_factor, mul_eq_zero, sub_eq_zero]

/-- A whole closed disk, not a finite sample, is strictly inside |p|<1. -/
theorem lobe_inner_disk {z : ℂ} (hz : ‖z‖ ≤ 5 / 8) :
    ‖lobePolynomial.eval z‖ < 1 := by
  have hp : ‖z‖ ^ 8 ≤ (5 / 8 : ℝ) ^ 8 := by gcongr
  have htriangle : ‖lobePolynomial.eval z‖ ≤ ‖z‖ ^ 8 + (3 / 2 : ℝ) * ‖z‖ := by
    rw [lobe_eval]
    have H := norm_sub_le (z ^ 8) ((3 / 2 : ℂ) * z)
    simpa [norm_pow, norm_mul, norm_div] using H
  nlinarith

/-- Every point of the circle |z|=4/5 is outside the closed unit sublevel. -/
theorem lobe_outer_circle {z : ℂ} (hz : ‖z‖ = 4 / 5) :
    1 < ‖lobePolynomial.eval z‖ := by
  have hid : (3 / 2 : ℂ) * z = z ^ 8 - lobePolynomial.eval z := by
    rw [lobe_eval]
    ring
  have H : (3 / 2 : ℝ) * ‖z‖ ≤ ‖z‖ ^ 8 + ‖lobePolynomial.eval z‖ := by
    calc
      (3 / 2 : ℝ) * ‖z‖ = ‖(3 / 2 : ℂ) * z‖ := by
        simp [norm_mul, norm_div]
      _ = ‖z ^ 8 - lobePolynomial.eval z‖ := congrArg norm hid
      _ ≤ ‖z ^ 8‖ + ‖lobePolynomial.eval z‖ := norm_sub_le _ _
      _ = ‖z‖ ^ 8 + ‖lobePolynomial.eval z‖ := by rw [norm_pow]
  rw [hz] at H
  norm_num at H
  linarith

/-- The barrier disk contains exactly one zero location. -/
theorem lobe_unique_root_in_barrier {z : ℂ} (hz : ‖z‖ ≤ 4 / 5) :
    lobePolynomial.eval z = 0 ↔ z = 0 := by
  constructor
  · intro hroot
    rcases (lobe_root_iff z).1 hroot with he | he
    · exact he
    · have hnorm : ‖z‖ ^ 7 = (3 / 2 : ℝ) := by
        have H := congrArg norm he
        simpa [norm_pow, norm_div] using H
      have hpow : ‖z‖ ^ 7 ≤ (4 / 5 : ℝ) ^ 7 := by gcongr
      norm_num at hpow
      linarith
  · rintro rfl
    simp [lobePolynomial]

/-- No root can also be critical. This is derived from the actual derivative. -/
theorem lobe_no_common_root (z : ℂ) (hz : lobePolynomial.eval z = 0) :
    lobePolynomial.derivative.eval z ≠ 0 := by
  have hd : lobePolynomial.derivative.eval z = 8 * z ^ 7 - (3 / 2 : ℂ) := by
    simp [lobePolynomial] <;> norm_num
  rw [hd]
  rcases (lobe_root_iff z).1 hz with rfl | he
  · norm_num
  · rw [he]
    norm_num

/-- Exact numerical comparison in the perimeter contradiction, independent of
any unsupported evaluation of the gamma constant. -/
theorem lobe_perimeter_numeric_gap :
    (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4 := by
  have hs : Real.sqrt 2 < (3 / 2 : ℝ) := by
    have H := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  nlinarith [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr hs)]

end ErdosProblems.Erdos1041.ReturnV5
