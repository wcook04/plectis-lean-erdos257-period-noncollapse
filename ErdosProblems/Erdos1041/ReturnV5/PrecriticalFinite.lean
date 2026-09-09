import Mathlib

/-!
# Finite consequences of the precritical inverse-map area estimate

AUTHORED / UNRUN. The first lemma extends the input's aggregation candidate;
its ANALYTIC premises must still be supplied from actual inverse maps and area.
These finite lemmas are not first-merge geometry producers.
-/

namespace ErdosProblems.Erdos1041.ReturnV5
open scoped BigOperators

/-- Unconditional finite implication: no no-short-connector premise occurs. -/
theorem precritical_energy_of_area {n : ℕ} (cr area : Fin n → ℝ) (ρ : ℝ)
    (hlocal : ∀ i, Real.pi * cr i ^ 2 ≤ area i)
    (hglobal : (∑ i, area i) ≤ Real.pi * ρ ^ 2) :
    (∑ i, cr i ^ 2) ≤ ρ ^ 2 := by
  have hmul : Real.pi * (∑ i, cr i ^ 2) ≤ Real.pi * ρ ^ 2 := by
    calc
      Real.pi * (∑ i, cr i ^ 2) = ∑ i, Real.pi * cr i ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i, area i := Finset.sum_le_sum fun i _ => hlocal i
      _ ≤ Real.pi * ρ ^ 2 := hglobal
  nlinarith [Real.pi_pos]

/-- Cauchy--Schwarz for the actual finite list of radii. -/
theorem precritical_sum_sq_le {n : ℕ} (cr : Fin n → ℝ) {ρ : ℝ}
    (henergy : (∑ i, cr i ^ 2) ≤ ρ ^ 2) :
    (∑ i, cr i) ^ 2 ≤ (n : ℝ) * ρ ^ 2 := by
  have H := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset (Fin n))
    (r := cr) (f := fun i => cr i ^ 2) (g := fun _ => (1 : ℝ))
    (fun i _ => sq_nonneg _) (fun _ _ => zero_le_one) (fun _ _ => by ring)
  have H' : (∑ i, cr i) ^ 2 ≤ (n : ℝ) * (∑ i, cr i ^ 2) := by
    simpa [mul_comm] using H
  exact H'.trans (mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg n))

/-- The square-root lift budget, including an empty list and radius zero. -/
theorem precritical_sum_le {n : ℕ} (cr : Fin n → ℝ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (henergy : (∑ i, cr i ^ 2) ≤ ρ ^ 2) :
    (∑ i, cr i) ≤ Real.sqrt (n : ℝ) * ρ := by
  have H := precritical_sum_sq_le cr henergy
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hnon : 0 ≤ Real.sqrt (n : ℝ) * ρ := mul_nonneg (Real.sqrt_nonneg _) hρ
  have he : (Real.sqrt (n : ℝ) * ρ) ^ 2 = (n : ℝ) * ρ ^ 2 := by
    rw [mul_pow, hs]
  nlinarith [sq_nonneg ((∑ i, cr i) - Real.sqrt (n : ℝ) * ρ)]

/-- Convert individual Koebe-type low-piece bounds to the summed budget.
The theorem does not claim that a curve satisfies the individual premise. -/
theorem summed_low_piece_budget {n : ℕ} (cr low : Fin n → ℝ) {ρ K : ℝ}
    (hρ : 0 ≤ ρ) (hK : 0 ≤ K) (henergy : (∑ i, cr i ^ 2) ≤ ρ ^ 2)
    (hlow : ∀ i, low i ≤ K * cr i) :
    (∑ i, low i) ≤ K * (Real.sqrt (n : ℝ) * ρ) := by
  calc
    (∑ i, low i) ≤ ∑ i, K * cr i := Finset.sum_le_sum fun i _ => hlow i
    _ = K * (∑ i, cr i) := (Finset.mul_sum ..).symm
    _ ≤ K * (Real.sqrt (n : ℝ) * ρ) :=
      mul_le_mul_of_nonneg_left (precritical_sum_le cr hρ henergy) hK

end ErdosProblems.Erdos1041.ReturnV5
