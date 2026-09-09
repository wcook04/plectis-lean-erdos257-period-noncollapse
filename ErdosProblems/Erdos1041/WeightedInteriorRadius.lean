import ErdosProblems.Erdos1041.WeightedInteriorBound

/-! Finite interior radius selection; candidate pending compilation. -/
open scoped BigOperators NNReal ComplexConjugate
noncomputable section
namespace ErdosProblems.Erdos1041

private theorem finite_radius {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (hc : ∀ j ∈ s, ‖c j‖ < 1) :
    ∃ R : ℝ, 1 < R ∧ ∀ j ∈ s, ‖c j‖ * R < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨2, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨R, hR, hRs⟩ := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have hca := hc a (Finset.mem_insert_self a s)
    have hd : 0 < 1 + ‖c a‖ := by positivity
    have hA : 1 < 2 / (1 + ‖c a‖) := by
      apply (lt_div_iff₀ hd).2
      linarith
    have hcaA : ‖c a‖ * (2 / (1 + ‖c a‖)) < 1 := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hd).2
      linarith
    refine ⟨min R (2 / (1 + ‖c a‖)), lt_min hR hA, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)).trans_lt hcaA
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _)).trans_lt (hRs j hj)

/-- Every finite family strictly inside the unit disc admits the common
analytic radius required by the energy construction. -/
theorem exists_weighted_interior_radius {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (hc : ∀ j, ‖c j‖ < 1) :
    ∃ R : ℝ≥0, 1 < R ∧ ∀ j, ‖c j‖ * (R : ℝ) < 1 := by
  obtain ⟨R, hR, hRc⟩ := finite_radius Finset.univ c (fun j _ => hc j)
  refine ⟨⟨R, (by linarith)⟩, ?_, ?_⟩
  · exact_mod_cast hR
  · intro j
    exact hRc j (Finset.mem_univ j)

/-- Full interior weighted geometric-product inequality, with no auxiliary
radius premise and allowing zero weights. Boundary points are not included. -/
theorem weighted_open_disc_product_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ < 1) :
    (∑ j, w j * (∏ k, ‖1 - conj (c k) * c j‖ ^ w k) ^ 2) ≤ 1 := by
  obtain ⟨R, hR, hRc⟩ := exists_weighted_interior_radius c hc
  exact weighted_interior_product_bound w c hw0 hw R hR hRc

end ErdosProblems.Erdos1041
end
