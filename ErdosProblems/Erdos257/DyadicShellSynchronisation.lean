import Mathlib

/-!
# Finite interfaces for dyadic-shell synchronisation

Candidate module supplied with the round-5 ordinary proof. NOT COMPILED in
this return. There are no admitted propositions or added axioms in this file.

These lemmas isolate finite gluing and witness extraction. They do not
formalise the modular-atom estimate, the countable sums, the weighted
schedule, or the mixed-support irrationality theorem. Those obligations are
listed in the accompanying formalisation plan. All analytic hypotheses below
are explicit premises.
-/

namespace ErdosProblems.Erdos257.DyadicShellSynchronisation

/-- Two nonnegative error budgets whose combined probability mean is below
one admit a common sample where both errors are below one. -/
theorem exists_common_sample_of_weighted_sum_lt_one
    {ι : Type*} (s : Finset ι) (μ f g : ι → ℝ)
    (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i)
    (hprob : ∑ i ∈ s, μ i = 1)
    (hmean : ∑ i ∈ s, μ i * (f i + g i) < 1) :
    ∃ i ∈ s, f i < 1 ∧ g i < 1 := by
  classical
  by_contra hnone
  have hall : ∀ i ∈ s, 1 ≤ f i + g i := by
    intro i hi
    by_contra hnot
    have hlt : f i + g i < 1 := lt_of_not_ge hnot
    apply hnone
    refine ⟨i, hi, ?_, ?_⟩
    · linarith [hg i hi]
    · linarith [hf i hi]
  have hlow : 1 ≤ ∑ i ∈ s, μ i * (f i + g i) := by
    calc
      1 = ∑ i ∈ s, μ i := hprob.symm
      _ ≤ ∑ i ∈ s, μ i * (f i + g i) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          μ i = μ i * 1 := by ring
          _ ≤ μ i * (f i + g i) :=
            mul_le_mul_of_nonneg_left (hall i hi) (hμ i hi)
  linarith

/-- The arithmetic end of the three-regime argument. Once the near and
transition errors each have total mass at most `2 * L * a`, averaging over
`m` lengths gives `(1 + 4 * L / m) * a`. -/
theorem finite_average_le_of_two_error_budgets
    {ι : Type*} (s : Finset ι) (m : ℕ) (hm : 0 < m)
    (hcard : s.card = m) (L a : ℝ) (u near transition : ι → ℝ)
    (hpoint : ∀ i ∈ s, u i ≤ a + near i + transition i)
    (hnear : ∑ i ∈ s, near i ≤ 2 * L * a)
    (htransition : ∑ i ∈ s, transition i ≤ 2 * L * a) :
    (∑ i ∈ s, u i) / (m : ℝ) ≤ (1 + 4 * L / m) * a := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsum : (∑ i ∈ s, u i) ≤ (m : ℝ) * a + 4 * L * a := by
    calc
      (∑ i ∈ s, u i) ≤ ∑ i ∈ s, (a + near i + transition i) :=
        Finset.sum_le_sum hpoint
      _ = (m : ℝ) * a + (∑ i ∈ s, near i) +
          (∑ i ∈ s, transition i) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul, hcard]
      _ ≤ (m : ℝ) * a + 4 * L * a := by linarith
  apply (div_le_iff₀ hmR).2
  calc
    (∑ i ∈ s, u i) ≤ (m : ℝ) * a + 4 * L * a := hsum
    _ = ((1 + 4 * L / (m : ℝ)) * a) * m := by
      field_simp [ne_of_gt hmR]
      <;> ring

/-- A sequence which at least doubles between distinct indices has at most
one transition length `L*T < d ≤ 2*L*T`. Dyadic lengths are the intended
instance; their growth hypothesis is not hidden in the statement. -/
theorem transition_index_unique
    (T : ℕ → ℝ) (L d : ℝ) (hL : 0 ≤ L)
    (hdouble : ∀ i j : ℕ, i < j → 2 * T i ≤ T j)
    {i j : ℕ}
    (hi₁ : L * T i < d) (hi₂ : d ≤ 2 * L * T i)
    (hj₁ : L * T j < d) (hj₂ : d ≤ 2 * L * T j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have h := mul_le_mul_of_nonneg_left (hdouble i j hij) hL
    nlinarith
  · have h := mul_le_mul_of_nonneg_left (hdouble j i hji) hL
    nlinarith

#print axioms exists_common_sample_of_weighted_sum_lt_one
#print axioms finite_average_le_of_two_error_budgets
#print axioms transition_index_unique

end ErdosProblems.Erdos257.DyadicShellSynchronisation
