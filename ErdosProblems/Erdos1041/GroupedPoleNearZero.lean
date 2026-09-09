import ErdosProblems.Erdos1041.GroupedPolePolynomial
import Mathlib

/-! Actual local nonvanishing of a finite rational pole sum.
Candidate pending compilation; distinct centers are already grouped. -/
open scoped BigOperators Topology
noncomputable section
namespace ErdosProblems.Erdos1041
open Polynomial Metric

/-- Literal denominator clearing away from the finite pole set. -/
theorem groupedPole_clear_denominators {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (z : ℂ) (hz : ∀ j, 1 - a j * z ≠ 0) :
    (∑ j, b j * a j / (1 - a j * z)) * (∏ k, (1 - a k * z)) =
      (groupedPoleNumerator a b).eval z := by
  classical
  simp only [groupedPoleNumerator, eval_finset_sum, eval_mul, eval_C,
    eval_prod, eval_sub, eval_one, eval_X]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_prod_erase Finset.univ (fun k => 1 - a k * z) (Finset.mem_univ j)]
  rw [← mul_assoc, div_mul_cancel₀ _ (hz j)]

/-- A genuine puncture-free ball cannot be a zero neighborhood of the
rational sum when one distinct pole has nonzero weight. -/
theorem groupedPole_not_zero_on_ball {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (ha : Function.Injective a) (i : ι)
    (hi : a i ≠ 0) (hb : b i ≠ 0) (ε : ℝ) (hε : 0 < ε)
    (hden : ∀ z ∈ ball (0 : ℂ) ε, ∀ j, 1 - a j * z ≠ 0) :
    ¬ ∀ z ∈ ball (0 : ℂ) ε, (∑ j, b j * a j / (1 - a j * z)) = 0 := by
  intro hzero
  have hroots : ball (0 : ℂ) ε ⊆
      {z | (groupedPoleNumerator a b).IsRoot z} := by
    intro z hz
    have he := groupedPole_clear_denominators a b z (hden z hz)
    rw [hzero z hz, zero_mul] at he
    exact he.symm
  have hfinite := (Polynomial.finite_setOf_isRoot
    (groupedPoleNumerator_ne_zero a b ha i hi hb)).subset hroots
  exact (infinite_of_mem_nhds (0 : ℂ) (Metric.ball_mem_nhds _ hε)) hfinite

/-- Existential form with strictly positive grouped real weight. -/
theorem groupedPole_positive_exists_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (w : ι → ℝ) (ha : Function.Injective a) (i : ι)
    (hi : a i ≠ 0) (hw : 0 < w i) (ε : ℝ) (hε : 0 < ε)
    (hden : ∀ z ∈ ball (0 : ℂ) ε, ∀ j, 1 - a j * z ≠ 0) :
    ∃ z ∈ ball (0 : ℂ) ε, (∑ j, (w j : ℂ) * a j / (1 - a j * z)) ≠ 0 := by
  have hn := groupedPole_not_zero_on_ball a (fun j => (w j : ℂ)) ha i hi
    (by
      change (w i : ℂ) ≠ 0
      exact_mod_cast (ne_of_gt hw)) ε hε hden
  push_neg at hn
  exact hn

end ErdosProblems.Erdos1041
end
