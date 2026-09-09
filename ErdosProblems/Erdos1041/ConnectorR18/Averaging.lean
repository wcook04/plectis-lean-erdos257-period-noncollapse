import Mathlib

/-!
# Measure-theoretic selection and the complete radial coefficient energy

AUTHORED / UNRUN. The integral selection lemma keeps a supplied almost-everywhere
good set, so it may be used after excluding the finite exceptional rays/levels.
No assertion that polynomial coarea or a conformal inverse has been constructed
is made. The coefficient theorem includes summability, not just a formal tsum.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.ConnectorR18
open MeasureTheory Filter
open scoped BigOperators

/-- Strict mean slack gives a good point strictly below the budget. This is
the applicable version for choosing a regular level below the TOP of a window;
there is no endpoint selection and no assumption that null exceptional points
may be used. The construction of the logarithmic probability measure and its
polynomial integral identity are separate analytic inputs. -/
theorem exists_good_lt_of_integral_lt {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → ℝ) (Good : α → Prop)
    {C : ℝ} (hf : Integrable f ν) (hmean : (∫ x, f x ∂ν) < C)
    (hgood : ∀ᵐ x ∂ν, Good x) : ∃ x, Good x ∧ f x < C := by
  by_contra h
  have hpoint : ∀ x, Good x → C ≤ f x := by
    intro x hx
    by_contra hlt
    exact h ⟨x, hx, lt_of_not_ge hlt⟩
  have hae : ∀ᵐ x ∂ν, (fun _ : α => C) x ≤ f x := by
    filter_upwards [hgood] with x hx
    exact hpoint x hx
  have hmono := integral_mono_ae (integrable_const C) hf hae
  have hle : C ≤ ∫ x, f x ∂ν := by simpa using hmono
  exact (not_lt_of_ge hle) hmean

/-- Complete-lift averaging has coefficient (m+1)^2/(2m+1), no Koebe cutoff. -/
def radialWeight (m : ℕ) : ℝ :=
  (((m + 1 : ℕ) : ℝ) ^ 2) / (2 * ((m + 1 : ℕ) : ℝ) - 1)

theorem radialWeight_nonneg (m : ℕ) : 0 ≤ radialWeight m := by
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  exact div_nonneg (sq_nonneg _) (by linarith)

theorem radialWeight_le (m : ℕ) : radialWeight m ≤ ((m + 1 : ℕ) : ℝ) := by
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hd : 0 < 2 * ((m + 1 : ℕ) : ℝ) - 1 := by linarith
  rw [radialWeight, div_le_iff₀ hd]
  nlinarith

/-- Bounded finite conformal coefficient energies entail actual summability
and the full radial energy bound. Parseval and the area formula identifying
the upper energy E with Area(U)/π are NOT proved by this algebraic theorem. -/
theorem radial_energy_of_coefficient_energy (a : ℕ → ℂ) (E : ℝ)
    (henergy : ∀ s : Finset ℕ,
      (∑ m ∈ s, ((m + 1 : ℕ) : ℝ) * ‖a m‖ ^ 2) ≤ E) :
    Summable (fun m => radialWeight m * ‖a m‖ ^ 2) ∧
      (∑' m, radialWeight m * ‖a m‖ ^ 2) ≤ E := by
  have hnonneg (m : ℕ) : 0 ≤ radialWeight m * ‖a m‖ ^ 2 :=
    mul_nonneg (radialWeight_nonneg m) (sq_nonneg _)
  have hbound (s : Finset ℕ) : (∑ m ∈ s, radialWeight m * ‖a m‖ ^ 2) ≤ E := by
    calc
      (∑ m ∈ s, radialWeight m * ‖a m‖ ^ 2) ≤
          ∑ m ∈ s, ((m + 1 : ℕ) : ℝ) * ‖a m‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (radialWeight_le m) (sq_nonneg _)
      _ ≤ E := henergy s
  exact ⟨summable_of_sum_le hnonneg hbound, Real.tsum_le_of_sum_le hnonneg hbound⟩

/-- The Cauchy identity for the disjoint low/high area budgets. No positivity
assumptions are needed for this algebraic inequality. -/
theorem two_component_cauchy (a b x y : ℝ) :
    (a * x + b * y) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (a * y - b * x)]

end ErdosProblems.Erdos1041.ConnectorR18
