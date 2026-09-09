import ErdosProblems.Erdos243.PaperCompleteR11.CRTObstructionDensity

/-!
# Removing the prime-size loss

Authored candidate, UNRUN. These proofs use only a finite product inequality:
`(1 + sum x) * product (1 - x) ≤ 1` for `0 ≤ x ≤ 1`.
Consequently divergence of the reciprocal-prime sum supplies finite CRT unions
of density as close to one as desired. This is a genuine analytic hypothesis
on the available primes, not a formal good-prime existence theorem.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators

/-- A finite, division-free bound for a product of survival proportions. -/
theorem sum_mul_product_one_sub_le_one {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    (1 + ∑ i ∈ s, x i) * (∏ i ∈ s, (1 - x i)) ≤ 1 := by
  classical
  revert h0 h1
  induction s using Finset.induction_on with
  | empty =>
      intro h0 h1
      simp
  | @insert a s ha ih =>
      intro h0 h1
      have h0s : ∀ i ∈ s, 0 ≤ x i := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
      have h1s : ∀ i ∈ s, x i ≤ 1 := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
      have hxa := h0 a (Finset.mem_insert_self a s)
      have hS := Finset.sum_nonneg h0s
      have hP : 0 ≤ ∏ i ∈ s, (1 - x i) :=
        Finset.prod_nonneg (fun i hi ↦ sub_nonneg.mpr (h1s i hi))
      have hstep :
          (1 + (x a + ∑ i ∈ s, x i)) *
            ((1 - x a) * ∏ i ∈ s, (1 - x i)) ≤
          (1 + ∑ i ∈ s, x i) * (∏ i ∈ s, (1 - x i)) := by
        have h := mul_nonneg
          (add_nonneg (mul_nonneg hxa hS) (sq_nonneg (x a))) hP
        nlinarith
      simpa only [Finset.sum_insert ha, Finset.prod_insert ha] using
        hstep.trans (ih h0s h1s)

/-- The complementary union is at least `sum x / (1 + sum x)`. -/
theorem sum_div_one_add_sum_le_union {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    (∑ i ∈ s, x i) / (1 + ∑ i ∈ s, x i) ≤
      1 - ∏ i ∈ s, (1 - x i) := by
  have hS := Finset.sum_nonneg h0
  have hden : 0 < 1 + ∑ i ∈ s, x i := by linarith
  apply (div_le_iff₀ hden).mpr
  have h := sum_mul_product_one_sub_le_one s x h0 h1
  nlinarith

/-- Divergence of a nonnegative ordinary series yields explicit finite masses.
Here `Summable` is used only for the nonnegative reciprocal-prime series; this
lemma is not a replacement for the signed endpoint's ordered hypothesis. -/
theorem unbounded_partial_sums_of_nonnegative_not_summable
    (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) (hns : ¬ Summable x) :
    ∀ B : ℝ, ∃ N : ℕ, B < ∑ i ∈ Finset.range N, x i := by
  intro B
  by_contra h
  apply hns
  apply summable_of_sum_range_le (c := B) hx
  intro N
  exact le_of_not_gt (fun hN ↦ h ⟨N, hN⟩)

/-- A divergent supply of pairwise coprime residue obstructions forces the
full `1/L` lower density. No bounded-size-prime premise is required. -/
theorem divergent_reciprocal_window_density
    (p : ℕ → ℕ) (hp : ∀ i, 0 < p i)
    (hc : Pairwise (fun i j ↦ Nat.Coprime (p i) (p j)))
    (r : ∀ i, ZMod (p i)) (E : Set ℕ) (L T : ℕ) (hL : 0 < L)
    (hdiv : ¬ Summable (fun i ↦ (1 : ℝ) / (p i : ℝ)))
    (hhit : ∀ i (n : ℕ), T ≤ n → (n : ZMod (p i)) = r i →
      ∃ j : ℕ, j < L ∧ n + j ∈ E) :
    LowerDensityAtLeast E (1 / (L : ℝ)) := by
  classical
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hmass := unbounded_partial_sums_of_nonnegative_not_summable
    (fun i ↦ (1 : ℝ) / (p i : ℝ)) (fun i ↦ by positivity) hdiv
  apply lowerDensityAtLeast_of_approximations E (1 / (L : ℝ))
  intro ε hε
  have hLε : 0 < (L : ℝ) * ε := mul_pos hLr hε
  obtain ⟨N, hN⟩ := hmass (1 / ((L : ℝ) * ε))
  let x : Fin N → ℝ := fun i ↦ 1 / (p i.val : ℝ)
  let S : ℝ := ∑ i : Fin N, x i
  let P : ℝ := ∏ i : Fin N, (1 - x i)
  have hSlarge : 1 / ((L : ℝ) * ε) < S := by
    change 1 / ((L : ℝ) * ε) < ∑ i : Fin N, 1 / (p i.val : ℝ)
    calc
      _ < ∑ i ∈ Finset.range N, (1 : ℝ) / (p i : ℝ) := hN
      _ = ∑ i : Fin N, 1 / (p i.val : ℝ) := by
        exact (Fin.sum_univ_eq_sum_range
          (fun i : ℕ ↦ (1 : ℝ) / (p i : ℝ)) N).symm
  have h0 : ∀ i ∈ (Finset.univ : Finset (Fin N)), 0 ≤ x i := by
    intro i _
    dsimp [x]
    positivity
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin N)), x i ≤ 1 := by
    intro i _
    have hi : (0 : ℝ) < (p i.val : ℝ) := by exact_mod_cast hp i.val
    apply (div_le_iff₀ hi).mpr
    have hpi : (1 : ℝ) ≤ (p i.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (hp i.val)
    simpa using hpi
  have hP : (1 + S) * P ≤ 1 := sum_mul_product_one_sub_le_one Finset.univ x h0 h1
  have hS0 : 0 ≤ S := Finset.sum_nonneg h0
  have hden : 0 < 1 + S := by linarith
  have hPbound : P ≤ 1 / (1 + S) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hsmall : 1 / (1 + S) < (L : ℝ) * ε := by
    apply (div_lt_iff₀ hden).mpr
    have h := (div_lt_iff₀ hLε).mp hSlarge
    nlinarith
  have hPlt : P < (L : ℝ) * ε := hPbound.trans_lt hsmall
  have hcN : Pairwise (fun i j : Fin N ↦ Nat.Coprime (p i.val) (p j.val)) := by
    intro i j hij
    apply hc
    intro he
    exact hij (Fin.ext he)
  have hd := crt_window_lower_density (fun i : Fin N ↦ p i.val)
    (fun i ↦ hp i.val) hcN (fun i ↦ r i.val) E L T hL
    (fun i n hn hnr ↦ hhit i.val n hn hnr)
  refine ⟨(1 - P) / (L : ℝ), ?_, ?_⟩
  · apply (lt_div_iff₀ hLr).mpr
    have hid : (1 / (L : ℝ) - ε) * (L : ℝ) = 1 - ε * (L : ℝ) := by
      field_simp [ne_of_gt hLr]
    rw [hid]
    nlinarith
  · simpa only [P, x] using hd

end ErdosProblems.Erdos243.PaperCompleteR11
