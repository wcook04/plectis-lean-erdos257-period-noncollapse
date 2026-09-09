import ErdosProblems.Erdos249.PaperCompleteR7.KernelIntegral
import ErdosProblems.Erdos249.PaperCompleteR8.UnitPivotBasis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib

set_option autoImplicit false

/-!
# The integral relation-module basis missing from the paper

New r8 proof source. The r7 coordinate basis is reused unchanged. The map below
has the free Z-module on ALL channels as its domain and the actual integral
span as its codomain. Its kernel has the unit-pivot basis, not just a spanning
set. Maximal reductions are identified by uniqueness of canonical coordinates.

No local compilation was possible. Pinned Mathlib source comments identify
APIs opened at 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR8

open scoped BigOperators
open Erdos249257
open ErdosProblems.Erdos249.PaperCompleteR7

abbrev IntegralChannelSpan (k e : ℕ) :=
  Submodule.span ℤ (Set.range (allBaseThroughLevelFamily k e))

/-- The literal retained channel indices, not an arbitrary preimage of a
sequence that might also be represented by an omitted channel. -/
def retainedChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    AllBaseCanonicalIndex k e → AllBaseThroughLevelIndex k e
  | Sum.inl i =>
      ⟨⟨i.val, by have hi := i.isLt; omega⟩,
        ⟨0, pow_pos (by omega : 0 < k) _⟩⟩
  | Sum.inr x =>
      ⟨⟨x.1.val + 1, by have hx := x.1.isLt; omega⟩,
        ⟨allBaseCanonicalResidue k x, allBaseCanonicalResidue_lt k hk x⟩⟩

theorem retainedChannel_value (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (j : AllBaseCanonicalIndex k e) :
    allBaseThroughLevelFamily k e (retainedChannel k e hk he j) =
      allBaseCanonicalFamily k e j := by
  cases j with
  | inl j => rfl
  | inr j => rfl

/-- Finite normal coefficients, supplied by the already-proved integral
spanning theorem. Independence makes them unique; no rational rounding occurs. -/
noncomputable def integralNormalCoefficients (k e : ℕ) (hk : 2 ≤ k)
    (i : AllBaseThroughLevelIndex k e) : AllBaseCanonicalIndex k e →₀ ℤ :=
  Classical.choose
    (Finsupp.mem_span_range_iff_exists_finsupp.mp
      (allBaseTotientKernelSeq_mem_int_span k e hk i.1.val
        (Nat.le_of_lt_succ i.1.isLt) i.2.val i.2.isLt))

theorem integralNormalCoefficients_spec (k e : ℕ) (hk : 2 ≤ k)
    (i : AllBaseThroughLevelIndex k e) :
    Finsupp.linearCombination ℤ (allBaseCanonicalFamily k e)
      (integralNormalCoefficients k e hk i) = allBaseThroughLevelFamily k e i := by
  exact Classical.choose_spec
    (Finsupp.mem_span_range_iff_exists_finsupp.mp
      (allBaseTotientKernelSeq_mem_int_span k e hk i.1.val
        (Nat.le_of_lt_succ i.1.isLt) i.2.val i.2.isLt))

/-- The unit-pivot system takes values in the integral span itself. -/
noncomputable def integralRelationSystem (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    UnitPivot.System ℤ (AllBaseThroughLevelIndex k e)
      (AllBaseCanonicalIndex k e) (IntegralChannelSpan k e) where
  value i := ⟨allBaseThroughLevelFamily k e i, Submodule.subset_span ⟨i, rfl⟩⟩
  keep := retainedChannel k e hk he
  independent := by
    -- Mathlib/LinearAlgebra/LinearIndependent/Defs.lean: of_comp.
    apply LinearIndependent.of_comp (IntegralChannelSpan k e).subtype
    have hfun :
        (fun j => allBaseThroughLevelFamily k e (retainedChannel k e hk he j)) =
          allBaseCanonicalFamily k e := funext (retainedChannel_value k e hk he)
    change LinearIndependent ℤ
      (fun j => allBaseThroughLevelFamily k e (retainedChannel k e hk he j))
    rw [hfun]
    exact int_linearIndependent_allBaseCanonicalFamily k e hk
  coeff := integralNormalCoefficients k e hk
  reconstruct := by
    intro i
    apply Subtype.ext
    -- Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean:
    -- Finsupp.apply_linearCombination transports the subtype map through a sum.
    change (IntegralChannelSpan k e).subtype
      (Finsupp.linearCombination ℤ
        (fun j => (⟨allBaseThroughLevelFamily k e (retainedChannel k e hk he j),
          Submodule.subset_span ⟨retainedChannel k e hk he j, rfl⟩⟩ :
            IntegralChannelSpan k e)) (integralNormalCoefficients k e hk i)) = _
    rw [Finsupp.apply_linearCombination]
    have hfun :
        (fun j => allBaseThroughLevelFamily k e (retainedChannel k e hk he j)) =
          allBaseCanonicalFamily k e := funext (retainedChannel_value k e hk he)
    change Finsupp.linearCombination ℤ
      (fun j => allBaseThroughLevelFamily k e (retainedChannel k e hk he j))
        (integralNormalCoefficients k e hk i) = allBaseThroughLevelFamily k e i
    rw [hfun]
    exact integralNormalCoefficients_spec k e hk i

noncomputable def integralChannelEvaluation (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :=
  (integralRelationSystem k e hk he).evaluation

noncomputable abbrev IntegralRelations (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :=
  LinearMap.ker (integralChannelEvaluation k e hk he)

abbrev OmittedIntegralChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :=
  (integralRelationSystem k e hk he).Omitted

/-- The requested relation basis, with one vector for each omitted channel. -/
noncomputable def integralRelationBasis (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Module.Basis (OmittedIntegralChannel k e hk he) ℤ (IntegralRelations k e hk he) :=
  (integralRelationSystem k e hk he).relationBasis

theorem integralRelationBasis_apply (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (i : OmittedIntegralChannel k e hk he) :
    (integralRelationBasis k e hk he i : AllBaseThroughLevelIndex k e →₀ ℤ) =
      Finsupp.single i.val 1 -
        (integralRelationSystem k e hk he).includeKept
          (integralNormalCoefficients k e hk i.val) :=
  (integralRelationSystem k e hk he).relationBasis_apply i

/-- Evaluation really is onto the integral span, rather than a formal map to
an unspecified ambient module. -/
theorem integralChannelEvaluation_surjective (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Function.Surjective (integralChannelEvaluation k e hk he) := by
  intro x
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp x.property
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change (IntegralChannelSpan k e).subtype
    (Finsupp.linearCombination ℤ (integralRelationSystem k e hk he).value c) = x.val
  rw [Finsupp.apply_linearCombination]
  exact hc

/-- Elementary identity for the number of omitted coordinates. -/
private theorem channel_count_split (k d : ℕ) :
    (∑ j ∈ Finset.range (d + 2), k ^ j) =
      k ^ (d + 1) + 1 + ∑ j ∈ Finset.range d, k ^ (j + 1) := by
  induction d with
  | zero => simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, zero_add, add_zero]; omega
  | succ d ih =>
      have ht : (∑ j ∈ Finset.range (d + 1 + 2), k ^ j) =
          (∑ j ∈ Finset.range (d + 2), k ^ j) + k ^ (d + 2) := by
        simpa only [Nat.add_assoc] using
          (Finset.sum_range_succ (fun j => k ^ j) (d + 2))
      have hm : (∑ j ∈ Finset.range (d + 1), k ^ (j + 1)) =
          (∑ j ∈ Finset.range d, k ^ (j + 1)) + k ^ (d + 1) :=
        Finset.sum_range_succ _ _
      rw [ht, ih, hm]
      have hexp : d + 1 + 1 = d + 2 := by omega
      rw [hexp]
      omega

theorem card_omittedIntegralChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Fintype.card (OmittedIntegralChannel k e hk he) =
      ∑ j ∈ Finset.range (e - 1), k ^ (j + 1) := by
  classical
  have hcount := (integralRelationSystem k e hk he).card_omitted_add_card_kept
  change Fintype.card (OmittedIntegralChannel k e hk he) +
    Fintype.card (AllBaseCanonicalIndex k e) =
      Fintype.card (AllBaseThroughLevelIndex k e) at hcount
  rw [card_allBaseCanonicalIndex k e (by omega), card_allBaseThroughLevelIndex] at hcount
  have hsplit := channel_count_split k (e - 1)
  have h₁ : e - 1 + 1 = e := Nat.sub_add_cancel he
  have h₂ : e - 1 + 2 = e + 1 := by omega
  rw [h₁, h₂] at hsplit
  omega

/-- Exact integral rank; this follows from the exhibited basis and its pivots. -/
theorem finrank_integralRelations (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Module.finrank ℤ (IntegralRelations k e hk he) =
      ∑ j ∈ Finset.range (e - 1), k ^ (j + 1) := by
  classical
  -- Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean:
  -- Module.finrank_eq_card_basis applies over Z, not just over fields.
  rw [Module.finrank_eq_card_basis (integralRelationBasis k e hk he)]
  exact card_omittedIntegralChannel k e hk he

/-- Combined displayed statement: coordinate basis AND relation basis AND rank. -/
theorem integral_normal_form_complete (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Nonempty (Module.Basis (AllBaseCanonicalIndex k e) ℤ (IntegralChannelSpan k e)) ∧
    (∃ b : Module.Basis (OmittedIntegralChannel k e hk he) ℤ
        (IntegralRelations k e hk he),
      ∀ i, (b i : AllBaseThroughLevelIndex k e →₀ ℤ) =
        Finsupp.single i.val 1 -
          (integralRelationSystem k e hk he).includeKept
            (integralNormalCoefficients k e hk i.val)) ∧
    Module.finrank ℤ (IntegralRelations k e hk he) =
      ∑ j ∈ Finset.range (e - 1), k ^ (j + 1) := by
  exact ⟨⟨integralTotientKernelBasis k e hk he⟩,
    ⟨integralRelationBasis k e hk he, integralRelationBasis_apply k e hk he⟩,
    finrank_integralRelations k e hk he⟩

/-! ## Identification with the literal elementary reductions on the page -/

/-- Every channel at level at least two with a residue divisible by k is omitted. -/
theorem channel_omitted_of_dvd (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (i : AllBaseThroughLevelIndex k e) (hi : 2 ≤ i.1.val) (hdiv : k ∣ i.2.val) :
    i ∉ Set.range (retainedChannel k e hk he) := by
  rintro ⟨b, hb⟩
  cases b with
  | inl b =>
      have hlevel := congrArg (fun z : AllBaseThroughLevelIndex k e => z.1.val) hb
      change b.val = i.1.val at hlevel
      have hbnd := b.isLt
      omega
  | inr b =>
      have hres := congrArg (fun z : AllBaseThroughLevelIndex k e => z.2.val) hb
      change allBaseCanonicalResidue k b = i.2.val at hres
      exact allBaseCanonicalResidue_not_dvd k hk b (hres.symm ▸ hdiv)

/-- Any supplied canonical target and scalar identity produce the exact
maximal-reduction basis vector. This includes the printed Euler-product scalar;
the next theorem gives that scalar's integral value. -/
theorem integral_scalar_reduction_row (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (o : OmittedIntegralChannel k e hk he) (b : AllBaseCanonicalIndex k e) (a : ℤ)
    (h : allBaseThroughLevelFamily k e o.val = a • allBaseCanonicalFamily k e b) :
    (integralRelationBasis k e hk he o : AllBaseThroughLevelIndex k e →₀ ℤ) =
      Finsupp.single o.val 1 - Finsupp.single (retainedChannel k e hk he b) a := by
  refine ((integralRelationSystem k e hk he).relationBasis_apply _).trans ?_
  apply (integralRelationSystem k e hk he).row_of_scalar_reduction
  apply Subtype.ext
  change allBaseThroughLevelFamily k e o.val =
    a • allBaseThroughLevelFamily k e (retainedChannel k e hk he b)
  rw [retainedChannel_value]
  exact h

/-- The zero-residue basis vector has exactly its advertised two entries. -/
theorem integral_zero_reduction_row (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (j : ℕ) (hj : 2 ≤ j) (hje : j ≤ e) :
    let i : AllBaseThroughLevelIndex k e :=
      ⟨⟨j, by omega⟩, ⟨0, pow_pos (by omega : 0 < k) _⟩⟩
    let o : OmittedIntegralChannel k e hk he :=
      ⟨i, channel_omitted_of_dvd k e hk he i hj (dvd_zero k)⟩
    (integralRelationBasis k e hk he o : AllBaseThroughLevelIndex k e →₀ ℤ) =
      Finsupp.single i 1 -
        Finsupp.single (retainedChannel k e hk he (Sum.inl 1)) (k ^ (j - 1) : ℤ) := by
  dsimp only
  apply integral_scalar_reduction_row k e hk he _ (Sum.inl 1) (k ^ (j - 1) : ℤ)
  change allBaseTotientKernelSeq k j 0 =
    (k ^ (j - 1) : ℤ) • allBaseTotientKernelSeq k 1 0
  have h := allBase_zero_integral k (by omega : 0 < k) (j - 1)
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
  rw [hj'] at h
  exact h

/-- An integer expression for the maximal-power Euler-product coefficient. -/
def integralPowerScalar (k t u : ℕ) : ℕ :=
  k ^ (t - 1) * integralStepScalar k u

theorem integralPowerScalar_cast (k t u : ℕ) (hk : 2 ≤ k) (ht : 1 ≤ t) :
    (integralPowerScalar k t u : ℚ) =
      (k : ℚ) ^ t * missingEulerProduct k u := by
  have hstep := stepScalar_cast k u (by omega : 0 < k)
  rw [stepScalar_eulerProduct k u (by omega : 0 < k)] at hstep
  have hpow : (k : ℚ) ^ (t - 1) * k = (k : ℚ) ^ t := by
    rw [← pow_succ, Nat.sub_add_cancel ht]
  change ((k ^ (t - 1) * integralStepScalar k u : ℕ) : ℚ) = _
  rw [Nat.cast_mul, Nat.cast_pow, hstep]
  rw [← mul_assoc, hpow]

theorem integral_maximal_power_reduction (k j t u : ℕ) (hk : 2 ≤ k)
    (ht : 1 ≤ t) (htj : t < j) :
    allBaseTotientKernelSeq k j (k ^ t * u) =
      (integralPowerScalar k t u : ℤ) • allBaseTotientKernelSeq k (j - t) u := by
  have h := paper_maximal_power_reduction k j t u hk ht htj
  rw [← integralPowerScalar_cast k t u hk ht] at h
  ext n
  have hn := congrFun h n
  simpa only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul,
    Int.cast_natCast] using hn


/-- A positive residue not divisible by the base names a retained channel.
The arithmetic construction is the same Euclidean digit decomposition as the
repaired r7 spanning proof, but returns the index rather than span membership. -/
theorem canonical_family_contains_nondiv (k e h u : ℕ) (hk : 2 ≤ k)
    (hh : 1 ≤ h) (hhe : h ≤ e) (hu : u < k ^ h) (hku : ¬ k ∣ u) :
    ∃ b : AllBaseCanonicalIndex k e,
      allBaseCanonicalFamily k e b = allBaseTotientKernelSeq k h u := by
  have hkpos : 0 < k := by omega
  obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := ⟨h - 1, (Nat.sub_add_cancel hh).symm⟩
  obtain ⟨s, v, hvpos, hvlt, rfl⟩ :
      ∃ s v, 0 < v ∧ v < k ∧ u = k * s + v := by
    refine ⟨u / k, u % k, ?_, Nat.mod_lt _ hkpos, (Nat.div_add_mod u k).symm⟩
    rcases Nat.eq_zero_or_pos (u % k) with hz | hp
    · exact False.elim (hku (Nat.dvd_of_mod_eq_zero hz))
    · exact hp
  have hs : s < k ^ j := by
    have hmul : k * s < k * k ^ j := by
      have hb : k * s + v < k * k ^ j := by
        calc
          k * s + v < k ^ (j + 1) := hu
          _ = k * k ^ j := by ring
      omega
    exact lt_of_mul_lt_mul_left hmul (Nat.zero_le k)
  refine ⟨Sum.inr ⟨⟨j, by omega⟩, (⟨s, hs⟩, ⟨v - 1, by omega⟩)⟩, ?_⟩
  simp only [allBaseCanonicalFamily, allBaseCanonicalResidue]
  congr 1
  omega

/-- Every original channel reduces to ONE canonical channel with an integer
scalar. This is stronger than membership in the canonical integer span. -/
theorem scalar_canonical_reduction (k e : ℕ) (hk : 2 ≤ k) :
    ∀ j : ℕ, j ≤ e → ∀ r : ℕ, r < k ^ j →
      ∃ b : AllBaseCanonicalIndex k e, ∃ a : ℕ,
        allBaseTotientKernelSeq k j r = (a : ℤ) • allBaseCanonicalFamily k e b := by
  have hkpos : 0 < k := by omega
  intro j
  induction j with
  | zero =>
      intro hje r hr
      have hr0 : r = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using hr
      subst r
      exact ⟨Sum.inl 0, 1, (one_smul ℤ _).symm⟩
  | succ j ih =>
      intro hje r hr
      by_cases hr0 : r = 0
      · subst r
        exact ⟨Sum.inl 1, k ^ j, allBase_zero_integral k hkpos j⟩
      · by_cases hkr : k ∣ r
        · obtain ⟨u, rfl⟩ := hkr
          have hulk : u < k ^ j := by
            have hm : k * u < k * k ^ j := by
              calc
                k * u < k ^ (j + 1) := hr
                _ = k * k ^ j := by ring
            exact lt_of_mul_lt_mul_left hm (Nat.zero_le k)
          have hj : 1 ≤ j := by
            by_contra hn
            have hj0 : j = 0 := by omega
            rw [hj0, pow_zero] at hulk
            have hu0 : u = 0 := Nat.lt_one_iff.mp hulk
            exact hr0 (by rw [hu0, mul_zero])
          obtain ⟨b, a, ha⟩ := ih (by omega) u hulk
          refine ⟨b, integralStepScalar k u * a, ?_⟩
          rw [allBase_step_integral k hkpos j u hj, ha, smul_smul, Nat.cast_mul]
        · obtain ⟨b, hb⟩ := canonical_family_contains_nondiv k e (j + 1) r hk
              (by omega) hje hr hkr
          exact ⟨b, 1, by rw [Nat.cast_one, one_smul, hb]⟩

/-- Each actual basis vector is a literal two-term unit-pivot reduction.
There is no undisplayed many-term coordinate choice in this conclusion. -/
theorem integralRelationBasis_two_term (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (o : OmittedIntegralChannel k e hk he) :
    ∃ b : AllBaseCanonicalIndex k e, ∃ a : ℕ,
      allBaseThroughLevelFamily k e o.val = (a : ℤ) • allBaseCanonicalFamily k e b ∧
      (integralRelationBasis k e hk he o : AllBaseThroughLevelIndex k e →₀ ℤ) =
        Finsupp.single o.val 1 - Finsupp.single (retainedChannel k e hk he b) (a : ℤ) := by
  obtain ⟨b, a, ha⟩ := scalar_canonical_reduction k e hk o.val.1.val
    (Nat.le_of_lt_succ o.val.1.isLt) o.val.2.val o.val.2.isLt
  exact ⟨b, a, ha, integral_scalar_reduction_row k e hk he o b a ha⟩

/-- The nonzero maximal-power row has the paper's Euler-product coefficient,
with a proved canonical target. The residue and level hypotheses merely name
an omitted channel; there is no linear-independence hypothesis to discharge. -/
theorem integral_maximal_reduction_row (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (o : OmittedIntegralChannel k e hk he) (t u : ℕ)
    (ht : 1 ≤ t) (htj : t < o.val.1.val)
    (hres : o.val.2.val = k ^ t * u) (hku : ¬ k ∣ u) :
    ∃ b : AllBaseCanonicalIndex k e,
      allBaseCanonicalFamily k e b = allBaseTotientKernelSeq k (o.val.1.val - t) u ∧
      (integralPowerScalar k t u : ℚ) = (k : ℚ)^t * missingEulerProduct k u ∧
      (integralRelationBasis k e hk he o : AllBaseThroughLevelIndex k e →₀ ℤ) =
        Finsupp.single o.val 1 -
          Finsupp.single (retainedChannel k e hk he b) (integralPowerScalar k t u : ℤ) := by
  have hsplit : k ^ t * k ^ (o.val.1.val - t) = k ^ o.val.1.val := by
    rw [← pow_add]
    congr 1
    omega
  have hu : u < k ^ (o.val.1.val - t) := by
    have hm : k ^ t * u < k ^ t * k ^ (o.val.1.val - t) := by
      rw [hsplit, ← hres]
      exact o.val.2.isLt
    exact lt_of_mul_lt_mul_left hm (Nat.zero_le _)
  obtain ⟨b, hb⟩ := canonical_family_contains_nondiv k e (o.val.1.val - t) u hk
    (by omega) (by have hj := o.val.1.isLt; omega) hu hku
  refine ⟨b, hb, integralPowerScalar_cast k t u hk ht, ?_⟩
  apply integral_scalar_reduction_row k e hk he o b (integralPowerScalar k t u)
  change allBaseTotientKernelSeq k o.val.1.val o.val.2.val = _
  rw [hres, hb]
  exact integral_maximal_power_reduction k o.val.1.val t u hk ht htj

/-- The coordinate basis has the literal canonical family as its values. -/
theorem integralTotientKernelBasis_values (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (i : AllBaseCanonicalIndex k e) :
    (integralTotientKernelBasis k e hk he i : ℕ → ℚ) = allBaseCanonicalFamily k e i := by
  -- Mathlib/LinearAlgebra/Basis/{Basic,Defs}.lean; Submodule/Equiv.lean.
  simp only [integralTotientKernelBasis, Module.Basis.map_apply,
    LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply]

/-- Complete displayed integral normal form, now including the elementary
basis vectors of the kernel and its exact rank. -/
theorem displayed_integral_normal_form (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    (∃ c : Module.Basis (AllBaseCanonicalIndex k e) ℤ (IntegralChannelSpan k e),
      ∀ i, (c i : ℕ → ℚ) = allBaseCanonicalFamily k e i) ∧
    (∃ b : Module.Basis (OmittedIntegralChannel k e hk he) ℤ
        (IntegralRelations k e hk he),
      ∀ o, ∃ j : AllBaseCanonicalIndex k e, ∃ a : ℕ,
        allBaseThroughLevelFamily k e o.val = (a : ℤ) • allBaseCanonicalFamily k e j ∧
        (b o : AllBaseThroughLevelIndex k e →₀ ℤ) =
          Finsupp.single o.val 1 - Finsupp.single (retainedChannel k e hk he j) (a : ℤ)) ∧
    Module.finrank ℤ (IntegralRelations k e hk he) =
      ∑ j ∈ Finset.range (e - 1), k ^ (j + 1) := by
  exact ⟨⟨integralTotientKernelBasis k e hk he,
      integralTotientKernelBasis_values k e hk he⟩,
    ⟨integralRelationBasis k e hk he, integralRelationBasis_two_term k e hk he⟩,
    finrank_integralRelations k e hk he⟩

end ErdosProblems.Erdos249.PaperCompleteR8
