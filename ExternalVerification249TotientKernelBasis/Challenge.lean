/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge: the all-base totient kernel basis, rank and relation module

Fix an integer base `k ≥ 2`.  For `j r : ℕ` write

  `F_{j,r} : ℕ → ℚ`,  `F_{j,r} n = φ (k^j * n + r)`

for the `(j, r)` section of Euler's totient in base `k`.  The *`k`-kernel through
level `e`* is the finite family `{F_{j,r} : j ≤ e, r < k^j}`.  It has
`1 + k + ⋯ + k^e` members, and they are far from independent: the zero-residue
channels satisfy `F_{j+1,0} = k^j · F_{1,0}`, and a residue divisible by `k`
drops one level with an exact rational scalar.

Three theorems are stated here.

* `allSlopeAffineTotientFormsLinearIndependent` is the underlying separation
  input: totient values along positive, pairwise non-proportional affine forms
  are `ℚ`-linearly independent, with no parity, primitivity or coprimality
  hypothesis on the slopes.
* `allBaseTotientKernelBasisRankAndRelationDimension` is the structure theorem.
  The canonical index takes the two zero-residue channels `F_{0,0}`, `F_{1,0}`
  together with one channel per residue `1 ≤ r < k^j` with `k ∤ r` at each level
  `1 ≤ j ≤ e`.  That family is independent, it spans the whole level-`e` kernel,
  it therefore carries a basis of the span, the span has dimension exactly
  `k^e + 1`, and the module of `ℚ`-linear relations among the `1 + k + ⋯ + k^e`
  unreduced channels has dimension exactly `k + k^2 + ⋯ + k^{e-1}`.

Note the residue condition is `k ∤ r`, not `Nat.Coprime k r`: at a composite base
a canonical residue may share a proper prime factor with `k`.

These are unconditional theorems about `Nat.totient`.  Neither asserts anything
about the binary totient series `∑ φ(n)/2^n`, and Erdős #249 remains open.  The
rational relation-module statement gives its dimension. The integral extension
also constructs a basis of elementary two-term reduction relations.
-/

namespace Erdos249257.ExternalVerification249TotientKernelBasis

open Module

/-! ## Affine totient forms -/

/-- **All-slope affine independence.**  For positive affine forms `a i · n + b i`
that are pairwise non-proportional, the totient sequences `n ↦ φ(a i n + b i)`
are linearly independent over `ℚ`. -/
theorem allSlopeAffineTotientFormsLinearIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) :
    LinearIndependent ℚ (fun (i : ι) (n : ℕ) => (Nat.totient (a i * n + b i) : ℚ)) := by
  sorry

/-! ## The base-`k` totient kernel -/

/-- The `(j, r)` base-`k` kernel channel `n ↦ φ(k^j n + r)`, viewed over `ℚ`. -/
def kernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  (Nat.totient (k ^ j * n + r) : ℚ)

/-- The canonical level-`e` index: two zero-residue base channels, and one
channel per canonical residue at each level `1, …, e`.  A canonical residue at
level `j + 1` is written `k * s + (u + 1)` with `s < k^j` and `u < k - 1`, which
is exactly the parametrisation of `1 ≤ r < k^(j+1)` with `k ∤ r`. -/
abbrev CanonicalIndex (k e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)

/-- The canonical residue `k * s + (u + 1)` named by a positive-level index. -/
def canonicalResidue (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ :=
  k * x.2.1.val + (x.2.2.val + 1)

/-- The canonical level-`e` family of base-`k` totient channels. -/
def canonicalFamily (k e : ℕ) : CanonicalIndex k e → ℕ → ℚ
  | Sum.inl i => kernelSeq k i.val 0
  | Sum.inr x => kernelSeq k (x.1.val + 1) (canonicalResidue k x)

/-- The complete base-`k` kernel index through level `e`, before any reduction:
every pair `(j, r)` with `j ≤ e` and `r < k^j`. -/
abbrev ThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)

/-- Every base-`k` section `n ↦ φ(k^j n + r)` at levels `0, …, e`. -/
def throughLevelFamily (k e : ℕ) : ThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => kernelSeq k j.val r.val

/-- Evaluation of a formal `ℚ`-combination of the symbols `E_{j,r}`, `j ≤ e`,
`r < k^j`, at the corresponding kernel channels.  Its kernel is the module of
`ℚ`-linear relations among the unreduced level-`e` channels. -/
noncomputable def relationMap (k e : ℕ) :
    (ThroughLevelIndex k e → ℚ) →ₗ[ℚ] (ℕ → ℚ) :=
  Fintype.linearCombination ℚ (throughLevelFamily k e)

/-- **The all-base totient kernel structure theorem.**  For every integer base
`k ≥ 2` and every depth `e ≥ 1`:

1. the canonical family is `ℚ`-linearly independent;
2. it spans the whole unreduced level-`e` kernel;
3. it therefore indexes a basis of that span;
4. the span has dimension exactly `k^e + 1`;
5. the relation module has dimension exactly `∑_{1 ≤ j < e} k^j`.

Part 5 is the complement of part 4 inside the `∑_{j ≤ e} k^j` unreduced
channels.  It states the dimension of the relation space only; it does not
assert that any particular family of relations generates it. -/
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
  sorry

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
  sorry

end Erdos249257.ExternalVerification249TotientKernelBasis
