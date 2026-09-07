import Erdos257PeriodNoncollapse.AllBaseTotientKernel
import Mathlib

/-!
# Freezing periodic coefficients in affine totient relations

Lean-checked helper (r5). Type A retargeted the import from the packet's
`Erdos249257.AllBaseTotientKernel` to the live
`Erdos257PeriodNoncollapse.AllBaseTotientKernel`. Focused `lean_fast_build`
completed as `cf_8309991b61ac4c53b3e3` exit 0. Periodic transport only;
does not complete `dim = #signatures` and does not decide `S`.

This uses the already proved all-affine independence theorem after an affine
change of variable. It requires NO new prime-isolation hypothesis. The positive
intercept condition of that theorem is met by using n + Q + Q*m, even when an
original intercept is zero.
-/

namespace ErdosProblems.Erdos249.PeriodicTotientIndependence

open scoped BigOperators

/-- Iterating a period, stated without any division or residue conventions. -/
theorem periodic_add_mul {K : Type*} (w : ℕ → K) (Q : ℕ)
    (hw : ∀ n, w (n + Q) = w n) (n t : ℕ) :
    w (n + Q * t) = w n := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show n + Q * (t + 1) = (n + Q * t) + Q by ring, hw, ih]

/-- Periodic coefficients in a finite affine-totient relation all vanish.
The affine forms may have zero intercepts; slopes are positive. -/
theorem periodic_coefficients_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i)
    (Q : ℕ) (hQ : 0 < Q) (w : ι → ℕ → ℚ)
    (hw : ∀ i n, w i (n + Q) = w i n)
    (hrel : ∀ n, ∑ i, w i n * (Nat.totient (a i * n + b i) : ℚ) = 0) :
    ∀ i n, w i n = 0 := by
  classical
  intro i n
  let aa : ι → ℕ := fun j => a j * Q
  let bb : ι → ℕ := fun j => a j * (n + Q) + b j
  have haa : ∀ j, 0 < aa j := fun j => Nat.mul_pos (ha j) hQ
  have hbb : ∀ j, 0 < bb j := by
    intro j
    dsimp [bb]
    have hnQ : 0 < n + Q := by omega
    have hp := Nat.mul_pos (ha j) hnQ
    omega
  have hcc : ∀ j k, j ≠ k → aa j * bb k ≠ aa k * bb j := by
    intro j k hjk heq
    apply hcross j k hjk
    have hh : Q * (a j * b k) = Q * (a k * b j) := by
      dsimp [aa, bb] at heq
      nlinarith [heq]
    exact Nat.mul_left_cancel hQ hh
  have hli := Erdos257PeriodNoncollapse.linearIndependent_totientAffineForms aa bb haa hbb hcc
  have hz : (∑ j, w j n • (fun m : ℕ => (Nat.totient (aa j * m + bb j) : ℚ))) = 0 := by
    funext m
    have hh := hrel (n + Q * (m + 1))
    have hper : ∀ j, w j (n + Q * (m + 1)) = w j n :=
      fun j => periodic_add_mul (w j) Q (hw j) n (m + 1)
    have harg : ∀ j, a j * (n + Q * (m + 1)) + b j = aa j * m + bb j := by
      intro j
      dsimp [aa, bb]
      ring
    simpa only [hper, harg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using hh
  exact (Fintype.linearIndependent_iff.mp hli) (fun j => w j n) hz i

end ErdosProblems.Erdos249.PeriodicTotientIndependence
