import ErdosProblems.Erdos1049.AdelicHeightBridge

/-!
# Quantitative selector escape: finite certificate layer

R5 candidate source. NOT compiled in the review environment.
This module uses the live packet's bounded-fibre theorem. It constructs
neither source rows nor bins for their real remainders. The ordinary dossier
constructs interval bins and states the source-dependent obligations.
-/

namespace ErdosProblems.Erdos1049

noncomputable section

local instance : DecidableEq ℝ := Classical.decEq ℝ

/-- Add a finite bin label to the modular signature before applying bounded-fibre
escape. The cardinal cost is the product of signature count, bin count, and
maximum multiplicity of an exact observable value. -/
theorem exists_same_signature_same_bin_different_value
    {α β γ ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq ι]
    (f : α → β) (g : α → γ) (bin : α → ι) (k : ℕ)
    (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k)
    (hcard : (Fintype.card β * Fintype.card ι) * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧ bin x = bin y ∧ g x ≠ g y := by
  have hc : Fintype.card (β × ι) * k < Fintype.card α := by
    simpa only [Fintype.card_prod] using hcard
  obtain ⟨x, y, hxy, hpair, hval⟩ :=
    exists_ne_map_eq_map_ne_of_card_mul_lt
      (fun a => (f a, bin a)) g k hg hc
  exact ⟨x, y, hxy, congrArg Prod.fst hpair,
    congrArg Prod.snd hpair, hval⟩

/-- A finite binning certificate whose cells have real diameter less than δ
turns the previous result into a small, nonzero real difference. -/
theorem exists_same_signature_small_nonzero_real_difference
    {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (f : α → β) (g : α → ℝ) (bin : α → ι) (k : ℕ) (δ : ℝ)
    (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k)
    (hdiam : ∀ x y : α, bin x = bin y → |g x - g y| < δ)
    (hcard : (Fintype.card β * Fintype.card ι) * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧
      0 < |g x - g y| ∧ |g x - g y| < δ := by
  classical
  obtain ⟨x, y, hxy, hf, hb, hgxy⟩ :=
    exists_same_signature_same_bin_different_value f g bin k hg hcard
  exact ⟨x, y, hxy, hf,
    abs_pos.mpr (sub_ne_zero.mpr hgxy), hdiam x y hb⟩


/-- Only multiplicity inside one modular fibre needs to be controlled. Values
that agree in different modular fibres cannot be the bad collision here. -/
theorem exists_same_signature_same_bin_different_value_conditional
    {α β γ ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq ι]
    (f : α → β) (g : α → γ) (bin : α → ι) (k : ℕ)
    (hg : ∀ x : α,
      (Finset.univ.filter fun y => f y = f x ∧ g y = g x).card ≤ k)
    (hcard : (Fintype.card β * Fintype.card ι) * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧ bin x = bin y ∧ g x ≠ g y := by
  have hpair : ∀ x : α,
      (Finset.univ.filter fun y => (f y, g y) = (f x, g x)).card ≤ k := by
    intro x
    simpa only [Prod.mk.injEq] using hg x
  obtain ⟨x, y, hxy, hf, hb, hfg⟩ :=
    exists_same_signature_same_bin_different_value
      f (fun a => (f a, g a)) bin k hpair hcard
  refine ⟨x, y, hxy, hf, hb, ?_⟩
  intro h
  exact hfg (Prod.ext hf h)

/-- Quantitative real escape with the sharper, conditional multiplicity. -/
theorem exists_small_real_escape_of_conditional_multiplicity
    {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (f : α → β) (g : α → ℝ) (bin : α → ι) (k : ℕ) (δ : ℝ)
    (hg : ∀ x : α,
      (Finset.univ.filter fun y => f y = f x ∧ g y = g x).card ≤ k)
    (hdiam : ∀ x y : α, bin x = bin y → |g x - g y| < δ)
    (hcard : (Fintype.card β * Fintype.card ι) * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧
      0 < |g x - g y| ∧ |g x - g y| < δ := by
  classical
  obtain ⟨x, y, hxy, hf, hb, hgxy⟩ :=
    exists_same_signature_same_bin_different_value_conditional f g bin k hg hcard
  exact ⟨x, y, hxy, hf,
    abs_pos.mpr (sub_ne_zero.mpr hgxy), hdiam x y hb⟩

end

end ErdosProblems.Erdos1049
