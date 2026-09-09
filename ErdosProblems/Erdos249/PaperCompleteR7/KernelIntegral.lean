import Erdos249257.AllBaseTotientKernel
import Mathlib

/-!
# Integral coordinates and the paper's Euler-product scalar

Targets: thm:kkernelrank and the integral-basis clause of
cor:integral-normal-form. The rational basis is reused without reproving its
CRT independence theorem. Its integral span is proved separately: rational
spanning alone would not establish the assertion over Z.

Build status: complete proof-source candidates; NOT COMPILED in this return.
The assertion that the named relation rows form a basis is NOT hidden inside
this file's integral coordinate theorem. Its remaining integration is recorded
separately in the coverage file.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7

open scoped BigOperators
open Erdos249257

/-- The integer multiplier in a one-step composite-base reduction. -/
def integralStepScalar (k u : ℕ) : ℕ :=
  (Nat.totient k / Nat.totient (Nat.gcd k u)) * Nat.gcd k u

/-- Divisibility of totients makes the rational-looking scalar integral. -/
theorem stepScalar_cast (k u : ℕ) (hk : 0 < k) :
    (integralStepScalar k u : ℚ) =
      ((Nat.totient k * Nat.gcd k u : ℕ) : ℚ) /
        (Nat.totient (Nat.gcd k u) : ℚ) := by
  have hd := Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left k u)
  have hg : 0 < Nat.totient (Nat.gcd k u) :=
    Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left u hk)
  have hgQ : (Nat.totient (Nat.gcd k u) : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hn := Nat.div_mul_cancel hd
  have hnQ : ((Nat.totient k / Nat.totient (Nat.gcd k u) : ℕ) : ℚ) *
      (Nat.totient (Nat.gcd k u) : ℚ) = (Nat.totient k : ℚ) := by
    exact_mod_cast hn
  unfold integralStepScalar
  push_cast
  apply (eq_div_iff hgQ).mpr
  calc
    _ = (((Nat.totient k / Nat.totient (Nat.gcd k u) : ℕ) : ℚ) *
          (Nat.totient (Nat.gcd k u) : ℚ)) * (Nat.gcd k u : ℚ) := by ring
    _ = _ := by rw [hnQ]

/-- Z-module form of the existing rational one-step relation. -/
theorem allBase_step_integral (k : ℕ) (hk : 0 < k) (h u : ℕ) (hh : 1 ≤ h) :
    allBaseTotientKernelSeq k (h + 1) (k * u) =
      (integralStepScalar k u : ℤ) • allBaseTotientKernelSeq k h u := by
  rw [allBaseTotientKernel_step k hk h u hh, ← stepScalar_cast k u hk]
  ext n
  simp [Pi.smul_apply, zsmul_eq_mul]

/-- The zero-channel reduction also holds over the integers. -/
theorem allBase_zero_integral (k : ℕ) (hk : 0 < k) (j : ℕ) :
    allBaseTotientKernelSeq k (j + 1) 0 =
      (k ^ j : ℤ) • allBaseTotientKernelSeq k 1 0 := by
  rw [allBaseTotientKernel_zero_residue k hk j]
  ext n
  simp [Pi.smul_apply, zsmul_eq_mul]

/-- Integer spanning, with no denominator-clearing premise. -/
theorem allBaseTotientKernelSeq_mem_int_span (k e : ℕ) (hk : 2 ≤ k) :
    ∀ j : ℕ, j ≤ e → ∀ r : ℕ, r < k ^ j →
      allBaseTotientKernelSeq k j r ∈
        Submodule.span ℤ (Set.range (allBaseCanonicalFamily k e)) := by
  have hkpos : 0 < k := by omega
  intro j
  induction j with
  | zero =>
      intro _ r hr
      have hr0 : r = 0 := by simpa using hr
      subst r
      exact Submodule.subset_span ⟨Sum.inl 0, rfl⟩
  | succ j ih =>
      intro hje r hr
      by_cases hr0 : r = 0
      · subst r
        rw [allBase_zero_integral k hkpos j]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl 1, rfl⟩)
      · by_cases hkr : k ∣ r
        · obtain ⟨u, rfl⟩ := hkr
          have hu0 : 0 < u := by
            rcases Nat.eq_zero_or_pos u with rfl | h
            · simp at hr0
            · exact h
          have hulk : u < k ^ j := by
            have hmul : k * u < k * k ^ j := by
              calc k * u < k ^ (j + 1) := hr
                _ = k * k ^ j := by ring
            exact lt_of_mul_lt_mul_left hmul (Nat.zero_le k)
          have hj1 : 1 ≤ j := by
            by_contra hcon
            have hj0 : j = 0 := by omega
            subst j
            simp only [pow_zero] at hulk
            omega
          rw [allBase_step_integral k hkpos j u hj1]
          exact Submodule.smul_mem _ _ (ih (by omega) u hulk)
        · have hjlt : j < e := by omega
          obtain ⟨s, u, hu_pos, hu_lt, rfl⟩ :
              ∃ s u, 0 < u ∧ u < k ∧ r = k * s + u := by
            refine ⟨r / k, r % k, ?_, Nat.mod_lt _ hkpos, (Nat.div_add_mod r k).symm⟩
            rcases Nat.eq_zero_or_pos (r % k) with h | h
            · exact absurd (Nat.dvd_of_mod_eq_zero h) hkr
            · exact h
          have hs_lt : s < k ^ j := by
            have hmul : k * s < k * k ^ j := by
              have hb : k * s + u < k * k ^ j := by
                calc k * s + u < k ^ (j + 1) := hr
                  _ = k * k ^ j := by ring
              omega
            exact lt_of_mul_lt_mul_left hmul (Nat.zero_le k)
          refine Submodule.subset_span
            ⟨Sum.inr ⟨⟨j, hjlt⟩, (⟨s, hs_lt⟩, ⟨u - 1, by omega⟩)⟩, ?_⟩
          simp only [allBaseCanonicalFamily, allBaseCanonicalResidue]
          congr 1
          omega

theorem int_span_allBaseThroughLevelFamily_eq (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Submodule.span ℤ (Set.range (allBaseThroughLevelFamily k e)) =
      Submodule.span ℤ (Set.range (allBaseCanonicalFamily k e)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨j, r⟩, rfl⟩
    exact allBaseTotientKernelSeq_mem_int_span k e hk j.val
      (Nat.le_of_lt_succ j.isLt) r.val r.isLt
  · exact Submodule.span_mono
      (range_allBaseCanonicalFamily_subset_throughLevel k e hk he)

theorem int_linearIndependent_allBaseCanonicalFamily (k e : ℕ) (hk : 2 ≤ k) :
    LinearIndependent ℤ (allBaseCanonicalFamily k e) :=
  (linearIndependent_allBaseCanonicalFamily k e hk).restrict_scalars' ℤ

/-- An actual Z-basis, not merely a rational basis with integer generators. -/
noncomputable def integralTotientKernelBasis (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Module.Basis (AllBaseCanonicalIndex k e) ℤ
      (Submodule.span ℤ (Set.range (allBaseThroughLevelFamily k e))) :=
  (Module.Basis.span (int_linearIndependent_allBaseCanonicalFamily k e hk)).map
    (LinearEquiv.ofEq _ _ (int_span_allBaseThroughLevelFamily_eq k e hk he).symm)

/-! ## The exact Euler-product multiplier on the page -/

/-- The product is over primes dividing k but not dividing u. -/
def missingEulerProduct (k u : ℕ) : ℚ :=
  ∏ p ∈ k.primeFactors.filter (fun p => ¬ p ∣ u), (1 - (p : ℚ)⁻¹)

/-- Separate common content primes before dividing the Euler products. -/
theorem stepScalar_eulerProduct (k u : ℕ) (hk : 0 < k) :
    ((Nat.totient k * Nat.gcd k u : ℕ) : ℚ) /
        (Nat.totient (Nat.gcd k u) : ℚ) =
      (k : ℚ) * missingEulerProduct k u := by
  classical
  let g := Nat.gcd k u
  let A := k.primeFactors.filter (fun p => p ∣ u)
  let B := k.primeFactors.filter (fun p => ¬ p ∣ u)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left u hk
  have hA : g.primeFactors = A := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_filter, A, g]
    constructor
    · rintro ⟨hp, hpg, hgn⟩
      exact ⟨⟨hp, hpg.trans (Nat.gcd_dvd_left k u), hk.ne'⟩,
        hpg.trans (Nat.gcd_dvd_right k u)⟩
    · rintro ⟨⟨hp, hpk, hkn⟩, hpu⟩
      exact ⟨hp, Nat.dvd_gcd hpk hpu, hg.ne'⟩
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    exact (Finset.mem_filter.mp hpb).2 (Finset.mem_filter.mp hpa).2
  have hunion : A ∪ B = k.primeFactors := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, A, B]
    tauto
  have hprod : (∏ p ∈ k.primeFactors, (1 - (p : ℚ)⁻¹)) =
      (∏ p ∈ A, (1 - (p : ℚ)⁻¹)) * (∏ p ∈ B, (1 - (p : ℚ)⁻¹)) := by
    rw [← hunion, Finset.prod_union hdisj]
  have hkphi := Nat.totient_eq_mul_prod_factors k
  have hgphi := Nat.totient_eq_mul_prod_factors g
  rw [hprod] at hkphi
  rw [hA] at hgphi
  have hφg : (Nat.totient g : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hg).ne'
  change ((Nat.totient k * g : ℕ) : ℚ) / (Nat.totient g : ℚ) = _
  apply (div_eq_iff hφg).2
  push_cast
  change (Nat.totient k : ℚ) * (g : ℚ) =
    ((k : ℚ) * (∏ p ∈ B, (1 - (p : ℚ)⁻¹))) * (Nat.totient g : ℚ)
  rw [hkphi, hgphi]
  ring

/-- Maximality is not needed for the scalar identity itself. Choosing u with
k not dividing u makes the right-hand section canonical, exactly as in the paper. -/
theorem allBase_power_residue_euler (k h t u : ℕ) (hk : 2 ≤ k)
    (hh : 1 ≤ h) (ht : 1 ≤ t) :
    allBaseTotientKernelSeq k (h + t) (k ^ t * u) =
      ((k : ℚ) ^ t * missingEulerProduct k u) • allBaseTotientKernelSeq k h u := by
  have hkpos : 0 < k := by omega
  have hstep := allBaseTotientKernel_step k hkpos h u hh
  rw [stepScalar_eulerProduct k u hkpos] at hstep
  have hpow : (k : ℚ) ^ (t - 1) * (k : ℚ) = (k : ℚ) ^ t := by
    rw [← pow_succ, Nat.sub_add_cancel ht]
  ext n
  have harg : k ^ (h + t) * n + k ^ t * u = k ^ t * (k ^ h * n + u) := by
    rw [pow_add]
    ring
  have hp := allBase_totient_pow_mul_eq k hkpos (k ^ h * n + u) t ht
  have hs := congrFun hstep n
  have harg1 : k ^ (h + 1) * n + k * u = k * (k ^ h * n + u) := by ring
  simp only [allBaseTotientKernelSeq, Pi.smul_apply, smul_eq_mul, harg1] at hs
  simp only [allBaseTotientKernelSeq, Pi.smul_apply, smul_eq_mul, harg]
  rw [hp]
  push_cast
  rw [hs]
  calc
    (k : ℚ) ^ (t - 1) * ((k : ℚ) * missingEulerProduct k u *
        (Nat.totient (k ^ h * n + u) : ℚ)) =
      ((k : ℚ) ^ (t - 1) * k) * missingEulerProduct k u *
        (Nat.totient (k ^ h * n + u) : ℚ) := by ring
    _ = _ := by rw [hpow]

/-- Main theorem's exact scalar at j-t. The range assumptions in the note
supply t<j; the formula does not need the stronger maximality assumption. -/
theorem paper_maximal_power_reduction (k j t u : ℕ) (hk : 2 ≤ k)
    (ht : 1 ≤ t) (htj : t < j) :
    allBaseTotientKernelSeq k j (k ^ t * u) =
      ((k : ℚ) ^ t * missingEulerProduct k u) • allBaseTotientKernelSeq k (j - t) u := by
  simpa only [Nat.sub_add_cancel (Nat.le_of_lt htj)] using
    allBase_power_residue_euler k (j - t) t u hk (by omega) ht

end ErdosProblems.Erdos249.PaperCompleteR7
