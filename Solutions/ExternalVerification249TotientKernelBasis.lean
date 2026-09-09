/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.AllBaseTotientKernel
import ErdosProblems.Erdos249.PaperCompleteR8.KernelRelationBasis

/-!
# Source transport for the all-base totient kernel basis, rank and relation module

The challenge vocabulary is redefined here verbatim and identified with the
source definitions in `Erdos249257/AllBaseTotientKernel.lean`.  The
identifications are definitional; the mathematics is entirely in the source
declarations

* `Erdos249257.linearIndependent_totientAffineForms`
* `Erdos249257.linearIndependent_allBaseCanonicalFamily`
* `Erdos249257.span_allBaseThroughLevelFamily_eq`
* `Erdos249257.allBaseTotientKernelBasis`
* `Erdos249257.finrank_allBaseThroughLevelFamily_eq`
* `Erdos249257.finrank_allBaseRelationModule_eq`
-/

namespace Erdos249257.ExternalVerification249TotientKernelBasis

open Module

theorem allSlopeAffineTotientFormsLinearIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) :
    LinearIndependent ℚ (fun (i : ι) (n : ℕ) => (Nat.totient (a i * n + b i) : ℚ)) :=
  Erdos249257.linearIndependent_totientAffineForms a b ha hb hcross

def kernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  (Nat.totient (k ^ j * n + r) : ℚ)

abbrev CanonicalIndex (k e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)

def canonicalResidue (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ :=
  k * x.2.1.val + (x.2.2.val + 1)

def canonicalFamily (k e : ℕ) : CanonicalIndex k e → ℕ → ℚ
  | Sum.inl i => kernelSeq k i.val 0
  | Sum.inr x => kernelSeq k (x.1.val + 1) (canonicalResidue k x)

abbrev ThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)

def throughLevelFamily (k e : ℕ) : ThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => kernelSeq k j.val r.val

noncomputable def relationMap (k e : ℕ) :
    (ThroughLevelIndex k e → ℚ) →ₗ[ℚ] (ℕ → ℚ) :=
  Fintype.linearCombination ℚ (throughLevelFamily k e)

/-! ## Definitional identification with the source vocabulary -/

theorem kernelSeq_eq (k j r : ℕ) :
    kernelSeq k j r = Erdos249257.allBaseTotientKernelSeq k j r := rfl

theorem canonicalResidue_eq (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) :
    canonicalResidue k x = Erdos249257.allBaseCanonicalResidue k x := rfl

theorem canonicalFamily_eq (k e : ℕ) :
    canonicalFamily k e = Erdos249257.allBaseCanonicalFamily k e := by
  funext i
  cases i with
  | inl i => rfl
  | inr x => rfl

theorem throughLevelFamily_eq (k e : ℕ) :
    throughLevelFamily k e = Erdos249257.allBaseThroughLevelFamily k e := by
  funext x
  rcases x with ⟨j, r⟩
  rfl

theorem relationMap_eq (k e : ℕ) :
    relationMap k e = Erdos249257.allBaseRelationMap k e := by
  simp only [relationMap, Erdos249257.allBaseRelationMap,
    throughLevelFamily_eq]

/-! ## The compared theorem -/

theorem allBaseTotientKernelBasisRankAndRelationDimension
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalFamily k e) ∧
      Submodule.span ℚ (Set.range (throughLevelFamily k e)) =
        Submodule.span ℚ (Set.range (canonicalFamily k e)) ∧
      Nonempty (Basis (CanonicalIndex k e) ℚ
        (Submodule.span ℚ (Set.range (throughLevelFamily k e)))) ∧
      finrank ℚ (Submodule.span ℚ (Set.range (throughLevelFamily k e))) =
        k ^ e + 1 ∧
      finrank ℚ (LinearMap.ker (relationMap k e)) =
        ∑ j ∈ Finset.Ico 1 e, k ^ j := by
  rw [canonicalFamily_eq, throughLevelFamily_eq, relationMap_eq]
  exact ⟨Erdos249257.linearIndependent_allBaseCanonicalFamily k e hk,
    Erdos249257.span_allBaseThroughLevelFamily_eq k e hk he,
    ⟨Erdos249257.allBaseTotientKernelBasis k e hk he⟩,
    Erdos249257.finrank_allBaseThroughLevelFamily_eq k e hk he,
    Erdos249257.finrank_allBaseRelationModule_eq k e hk he⟩

abbrev IntegralSpan (k e : ℕ) :=
  Submodule.span ℤ (Set.range (throughLevelFamily k e))

def retainedChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    CanonicalIndex k e → ThroughLevelIndex k e
  | Sum.inl i =>
      ⟨⟨i.val, by have hi := i.isLt; omega⟩,
        ⟨0, pow_pos (by omega : 0 < k) _⟩⟩
  | Sum.inr x =>
      ⟨⟨x.1.val + 1, by have hx := x.1.isLt; omega⟩,
        ⟨canonicalResidue k x, by
          have hs := x.2.1.isLt
          have hu := x.2.2.isLt
          have hu' : x.2.2.val + 1 < k := by omega
          have hs' : x.2.1.val + 1 ≤ k ^ x.1.val := by omega
          have hm := Nat.mul_le_mul_left k hs'
          dsimp [canonicalResidue]
          rw [pow_succ]
          nlinarith⟩⟩

abbrev OmittedChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :=
  {i : ThroughLevelIndex k e // i ∉ Set.range (retainedChannel k e hk he)}

noncomputable def integralEvaluation (k e : ℕ) :
    (ThroughLevelIndex k e →₀ ℤ) →ₗ[ℤ] IntegralSpan k e :=
  Finsupp.linearCombination ℤ
    (fun i => ⟨throughLevelFamily k e i, Submodule.subset_span ⟨i, rfl⟩⟩)

/-- The literal integral coordinate basis, elementary relation basis, and rank. -/
theorem allBaseIntegralCoordinateAndRelationBasis
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    (∃ c : Module.Basis (CanonicalIndex k e) ℤ (IntegralSpan k e),
      ∀ i, (c i : ℕ → ℚ) = canonicalFamily k e i) ∧
    (∃ b : Module.Basis (OmittedChannel k e hk he) ℤ
        (LinearMap.ker (integralEvaluation k e)),
      ∀ o, ∃ j : CanonicalIndex k e, ∃ a : ℕ,
        throughLevelFamily k e o.val = (a : ℤ) • canonicalFamily k e j ∧
        (b o : ThroughLevelIndex k e →₀ ℤ) =
          Finsupp.single o.val 1 - Finsupp.single (retainedChannel k e hk he j) (a : ℤ)) ∧
    Module.finrank ℤ (LinearMap.ker (integralEvaluation k e)) =
      ∑ j ∈ Finset.range (e - 1), k ^ (j + 1) := by
  exact ErdosProblems.Erdos249.PaperCompleteR8.displayed_integral_normal_form k e hk he

end Erdos249257.ExternalVerification249TotientKernelBasis
