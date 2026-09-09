import ErdosProblems.Erdos1041.ConnectorR18.CurveAlgebra
import ErdosProblems.Erdos1041.ConnectorR18.NumericalBounds

/-!
# Finite energy budgets and assembly of an actual adjacent connector

AUTHORED / UNRUN. Analytic energy inequalities and geometric boundary ordering
are explicit INPUTS, not claimed theorems here. Once those inputs are available,
this file constructs the curve itself, with the actual extended-variation
bound; it does not merely produce a scalar inequality or a pair of labels.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.ConnectorR18
open Set PaperAnalyticTargets
open scoped BigOperators

/-- The finite step of CF2. No no-short-path assumption is used. The local
area formula and global area estimate remain separate analytic obligations. -/
theorem sum_conformalRadius_sq_le {k : ℕ} (cr area : Fin k → ℝ) (ρ : ℝ)
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

/-- The low-radius Koebe estimate, once supplied pointwise, propagates CF2 to
its squared finite budget. Here 60/289 = (3/20)/(1-3/20)^2 exactly. -/
theorem low_energy_of_radius_energy {k : ℕ} (cr low : Fin k → ℝ) (ρ : ℝ)
    (hcr : ∀ i, 0 ≤ cr i) (hlow : ∀ i, 0 ≤ low i)
    (hbound : ∀ i, low i ≤ (60 / 289 : ℝ) * cr i)
    (henergy : (∑ i, cr i ^ 2) ≤ ρ ^ 2) :
    (∑ i, low i ^ 2) ≤ (60 / 289 : ℝ) ^ 2 * ρ ^ 2 := by
  calc
    (∑ i, low i ^ 2) ≤ ∑ i, ((60 / 289 : ℝ) * cr i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ (hlow i) (mul_nonneg (by norm_num) (hcr i))).2 (hbound i)
    _ = (60 / 289 : ℝ) ^ 2 * ∑ i, cr i ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ (60 / 289 : ℝ) ^ 2 * ρ ^ 2 :=
      mul_le_mul_of_nonneg_left henergy (sq_nonneg _)

theorem sum_sq_le_card_mul_sum_sq {k : ℕ} (a : Fin k → ℝ) :
    (∑ i, a i) ^ 2 ≤ (k : ℝ) * ∑ i, a i ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset (Fin k))
    (r := a) (f := fun i => a i ^ 2) (g := fun _ => (1 : ℝ))
    (fun i _ => sq_nonneg _) (fun _ _ => zero_le_one) (fun _ _ => by simp)
  simpa [mul_comm] using h

/-- The k≥2 averaging gain, without a square-root manipulation. -/
theorem linear_bound_of_quadratic {K x y : ℝ} (hK : 2 ≤ K)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hsq : x ^ 2 ≤ 2 * K * y ^ 2) : x ≤ K * y := by
  have hK0 : 0 ≤ K := by linarith
  have hprod : 0 ≤ (K - 2) * K * y ^ 2 :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hK) hK0) (sq_nonneg y)
  have hsq' : x ^ 2 ≤ (K * y) ^ 2 := by nlinarith
  exact (sq_le_sq₀ hx (mul_nonneg hK0 hy)).mp hsq'

/-- Converts the three energy estimates of CF into the exact rational budget.
The hypotheses contain NO connector-length conclusion in disguise: two are
squared sums, and the low term is a sum of individual squares. -/
theorem three_energy_budget {k : ℕ} (hk : 2 ≤ k) (low high arc : Fin k → ℝ)
    {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hlow0 : ∀ i, 0 ≤ low i) (hhigh0 : ∀ i, 0 ≤ high i)
    (harc0 : ∀ i, 0 ≤ arc i)
    (hlow : (∑ i, low i ^ 2) ≤ (60 / 289 : ℝ) ^ 2 * ρ ^ 2)
    (hhigh : (∑ i, high i) ^ 2 ≤ ((k : ℝ) / 2) * Real.log (40 / 3 : ℝ) * τ ^ 2)
    (harc : (∑ i, arc i) ^ 2 ≤ (2 * Real.pi ^ 2 * (k : ℝ) / Real.log 2) * τ ^ 2) :
    2 * (∑ i, (low i + high i)) + (∑ i, arc i) ≤
      (k : ℝ) * (lowConstant * ρ + highConstant * τ) := by
  have hK : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hK0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hL0 : 0 ≤ ∑ i, low i := Finset.sum_nonneg fun i _ => hlow0 i
  have hH0 : 0 ≤ ∑ i, high i := Finset.sum_nonneg fun i _ => hhigh0 i
  have hA0 : 0 ≤ ∑ i, arc i := Finset.sum_nonneg fun i _ => harc0 i
  have hLsq : (∑ i, low i) ^ 2 ≤ (k : ℝ) * ((60 / 289 : ℝ) ^ 2 * ρ ^ 2) :=
    (sum_sq_le_card_mul_sum_sq low).trans (mul_le_mul_of_nonneg_left hlow hK0)
  have hlowCoefficient : 2 * (60 / 289 : ℝ) ^ 2 ≤ lowConstant ^ 2 := by
    norm_num [lowConstant]
  have hLcompare := mul_le_mul_of_nonneg_left hlowCoefficient
    (show 0 ≤ 2 * (k : ℝ) * ρ ^ 2 by positivity)
  have hL : 2 * (∑ i, low i) ≤ (k : ℝ) * (lowConstant * ρ) := by
    apply linear_bound_of_quadratic hK (by positivity) (mul_nonneg lowConstant_nonneg hρ)
    nlinarith
  have hHcompare := mul_le_mul_of_nonneg_left log_forty_thirds_upper.le
    (show 0 ≤ 2 * (k : ℝ) * τ ^ 2 by positivity)
  have hH : 2 * (∑ i, high i) ≤ (k : ℝ) * ((161 / 100 : ℝ) * τ) := by
    apply linear_bound_of_quadratic hK (by positivity) (by positivity)
    nlinarith
  have hAcompare := mul_le_mul_of_nonneg_left boundary_squared_constant
    (show 0 ≤ 2 * (k : ℝ) * τ ^ 2 by positivity)
  have hArewrite : (2 * Real.pi ^ 2 * (k : ℝ) / Real.log 2) * τ ^ 2 =
      (2 * (k : ℝ) * τ ^ 2) * (Real.pi ^ 2 / Real.log 2) := by ring
  have hA : (∑ i, arc i) ≤ (k : ℝ) * ((1375 / 364 : ℝ) * τ) := by
    apply linear_bound_of_quadratic hK hA0 (by positivity)
    rw [hArewrite] at harc
    nlinarith
  rw [Finset.sum_add_distrib]
  dsimp [highConstant]
  linarith

theorem sum_permutation {k : ℕ} (σ : Equiv.Perm (Fin k)) (a : Fin k → ℝ) :
    (∑ i, a (σ i)) = ∑ i, a i := by
  classical
  refine Finset.sum_bij (fun i _ => σ i) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro i hi j hj hij
    exact σ.injective hij
  · intro j hj
    exact ⟨σ.symm j, Finset.mem_univ _, σ.apply_symm_apply j⟩
  · intro i hi
    rfl

theorem exists_le_of_sum_le_card_mul {k : ℕ} (hk : 0 < k)
    (a : Fin k → ℝ) (C : ℝ) (h : (∑ i, a i) ≤ (k : ℝ) * C) :
    ∃ i, a i ≤ C := by
  classical
  by_contra hcon
  push_neg at hcon
  have hs : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hlt : (∑ _i : Fin k, C) < ∑ i, a i :=
    Finset.sum_lt_sum_of_nonempty hs (fun i _ => hcon i)
  have hlt' : (k : ℝ) * C < ∑ i, a i := by simpa [Finset.sum_const, nsmul_eq_mul] using hlt
  linarith

/-- A genuine adjacent connector: two supplied lifts, one supplied boundary
arc, finite averaging, and arbitrary rectifiable-curve concatenation. A
fixed-point-free permutation is the only cyclic-order fact the consumer needs.
Geometric construction of this ordering is NOT proved by this theorem. -/
theorem adjacent_connector_of_budget {n k : ℕ} {f : ℂ → ℂ} {R C : ℝ}
    (hk : 2 ≤ k) (z : Fin n → ℂ) (label : Fin k → Fin n)
    (hinj : Function.Injective label) (boundary : Fin k → ℂ)
    (σ : Equiv.Perm (Fin k)) (hnofix : ∀ i, σ i ≠ i)
    (length arc : Fin k → ℝ) (hlen0 : ∀ i, 0 ≤ length i) (harc0 : ∀ i, 0 ≤ arc i)
    (hlift : ∀ i, ConnectedAtMost f R (length i) (z (label i)) (boundary i))
    (hboundary : ∀ i, ConnectedAtMost f R (arc i) (boundary i) (boundary (σ i)))
    (hbudget : 2 * (∑ i, length i) + (∑ i, arc i) ≤ (k : ℝ) * C) :
    ∃ i j : Fin n, i ≠ j ∧ ConnectedAtMost f R C (z i) (z j) := by
  have htotal : (∑ i, (length i + arc i + length (σ i))) ≤ (k : ℝ) * C := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_permutation σ length]
    linarith
  obtain ⟨i, hi⟩ := exists_le_of_sum_le_card_mul (by omega : 0 < k)
    (fun i => length i + arc i + length (σ i)) C htotal
  have H := connectedAtMost_trans (hlift i) (hboundary i) (hlen0 i) (harc0 i)
  have H' := connectedAtMost_trans H (connectedAtMost_symm (hlift (σ i)))
    (add_nonneg (hlen0 i) (harc0 i)) (hlen0 (σ i))
  refine ⟨label i, label (σ i), ?_, connectedAtMost_mono H' le_rfl hi⟩
  intro heq
  exact hnofix i (hinj heq).symm

end ErdosProblems.Erdos1041.ConnectorR18
