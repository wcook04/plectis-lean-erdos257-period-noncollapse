import ErdosProblems.Erdos68.ConstantOnlyMissCertificates
import ErdosProblems.Erdos68.SecondLayerDigit
import ErdosProblems.Erdos68.FactorialDigitRigidity
import Mathlib.NumberTheory.Real.Irrational

/-!
# Erdős #68: full companion-orbit rationality boundary

This module promotes the pointwise companion-floor arithmetic to the infinite
rationality statement.  The fixed companion constant is

`C = ∑_{n≥2} 1/(n!(n!−1)) = S - (exp 1 - 2)`.

The target normal form is that `S` is rational exactly when
`⌊m! C⌋ ≡ -2 (mod m)` eventually.  The forward direction uses the positive
sub-unit remainder in the exponential series.  The reverse direction uses
the equivalent canonical digit tail `d_m(C)=m-2` and the telescoping identity

`∑_{m>N} ((m-2)+1)/m! = 1/N!`.

No cofinal escape claim is made here.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- The canonical factorial digit, normalized as the corresponding summand
of the factorial expansion.  The two initial indices are suppressed because
the mixed-radix expansion starts at radix two. -/
noncomputable def canonicalDigitTerm (x : ℝ) (m : ℕ) : ℝ :=
  if 2 ≤ m then
    (canonicalDigit x m : ℝ) / (m.factorial : ℝ)
  else 0

/-- Canonical factorial digit terms are summable.  The pointwise majorant is
`m / m!`, a shifted exponential series. -/
theorem summable_canonicalDigitTerm (x : ℝ) :
    Summable (canonicalDigitTerm x) := by
  have hmajorant :
      Summable (fun m : ℕ => (m : ℝ) / (m.factorial : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    convert Real.summable_pow_div_factorial 1 using 1
    funext n
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    simp
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hmajorant
  · by_cases hm : 2 ≤ m
    · rw [canonicalDigitTerm, if_pos hm]
      exact div_nonneg
        (by exact_mod_cast canonicalDigit_nonneg x m (by omega))
        (by positivity)
    · simp [canonicalDigitTerm, hm]
  · by_cases hm : 2 ≤ m
    · rw [canonicalDigitTerm, if_pos hm]
      have hdigit : (canonicalDigit x m : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (canonicalDigit_lt_radix x m (by omega)).le
      exact div_le_div_of_nonneg_right hdigit (by positivity)
    · simp only [canonicalDigitTerm, if_neg hm]
      exact div_nonneg (by positivity) (by positivity)

/-- The partial sum of normalized canonical digits is exactly the digit sum
appearing in `factorial_expansion_partial`. -/
theorem sum_range_succ_canonicalDigitTerm (x : ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), canonicalDigitTerm x m) =
      ∑ m ∈ Finset.Icc 2 N,
        (canonicalDigit x m : ℝ) / (m.factorial : ℝ) := by
  calc
    (∑ m ∈ Finset.range (N + 1), canonicalDigitTerm x m) =
        ∑ m ∈ Finset.Icc 2 N, canonicalDigitTerm x m := by
      symm
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢
        omega
      · intro m hmRange hmIcc
        have hmSmall : ¬2 ≤ m := by
          intro hmTwo
          apply hmIcc
          simp only [Finset.mem_Icc]
          have hmLt : m < N + 1 := Finset.mem_range.mp hmRange
          omega
        simp [canonicalDigitTerm, hmSmall]
    _ = ∑ m ∈ Finset.Icc 2 N,
          (canonicalDigit x m : ℝ) / (m.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [canonicalDigitTerm, if_pos (Finset.mem_Icc.mp hm).1]

/-- The explicit remainder in the finite factorial expansion tends to zero. -/
theorem tendsto_canonicalRemainder_div_factorial_zero (x : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => canonicalRemainder x N / (N.factorial : ℝ))
      Filter.atTop (nhds 0) := by
  have hfacTop :
      Filter.Tendsto (fun N : ℕ => (N.factorial : ℝ))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop
  have hinv :
      Filter.Tendsto (fun N : ℕ => 1 / (N.factorial : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hfacTop
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N =>
      div_nonneg (canonicalRemainder_nonneg x N) (by positivity)
  · exact Filter.Eventually.of_forall fun N =>
      div_le_div_of_nonneg_right
        (canonicalRemainder_lt_one x N).le (by positivity)
  · exact hinv

/-- Every real number is the sum of its integer part and the convergent
series of its canonical factorial digits. -/
theorem tsum_canonicalDigitTerm (x : ℝ) :
    (∑' m : ℕ, canonicalDigitTerm x m) = x - (⌊x⌋ : ℝ) := by
  have hpartial :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ m ∈ Finset.Icc 2 N,
            (canonicalDigit x m : ℝ) / (m.factorial : ℝ))
        Filter.atTop (nhds (x - (⌊x⌋ : ℝ))) := by
    have hrem := tendsto_canonicalRemainder_div_factorial_zero x
    have hconst :
        Filter.Tendsto (fun _ : ℕ => x - (⌊x⌋ : ℝ))
          Filter.atTop (nhds (x - (⌊x⌋ : ℝ))) :=
      tendsto_const_nhds
    have htarget :
        Filter.Tendsto
          (fun N : ℕ =>
            (x - (⌊x⌋ : ℝ)) -
              canonicalRemainder x N / (N.factorial : ℝ))
          Filter.atTop (nhds (x - (⌊x⌋ : ℝ))) := by
      simpa using hconst.sub hrem
    apply htarget.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hexpansion := factorial_expansion_partial x N hN
    linarith
  have hseries := summable_canonicalDigitTerm x
  have hsumLimit := hseries.hasSum.tendsto_sum_nat
  have hshifted := hsumLimit.comp (Filter.tendsto_add_atTop_nat 1)
  have hpartialRange :
      Filter.Tendsto
        (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), canonicalDigitTerm x m)
        Filter.atTop (nhds (x - (⌊x⌋ : ℝ))) := by
    apply hpartial.congr'
    exact Filter.Eventually.of_forall fun N =>
      (sum_range_succ_canonicalDigitTerm x N).symm
  exact tendsto_nhds_unique hshifted hpartialRange

/-- The canonical factorial digits sum to the fractional part of `x`. -/
theorem hasSum_canonicalDigitTerm (x : ℝ) :
    HasSum (canonicalDigitTerm x) (x - (⌊x⌋ : ℝ)) := by
  rw [← tsum_canonicalDigitTerm x]
  exact (summable_canonicalDigitTerm x).hasSum

/-- The exponential tail beyond `m`. -/
noncomputable def unitFactTail (m : ℕ) : ℝ :=
  ∑' k : ℕ, (1 : ℝ) / ((m + 1 + k).factorial : ℝ)

/-- The exponential tail scaled by `m!`. -/
noncomputable def unitFactScaledTail (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * unitFactTail m

theorem summable_unitFactTail (m : ℕ) :
    Summable (fun k : ℕ => (1 : ℝ) / ((m + 1 + k).factorial : ℝ)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n.factorial : ℝ)) := by
    simpa using Real.summable_pow_div_factorial 1
  have hs := (summable_nat_add_iff (m + 1)).2 h
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

theorem unitFactTail_pos (m : ℕ) : 0 < unitFactTail m := by
  exact (summable_unitFactTail m).tsum_pos (fun k => by positivity) 0 (by positivity)

private theorem unitFactTail_term_lt_telescope {m k : ℕ} (hm : 2 ≤ m) :
    (1 : ℝ) / ((m + 1 + k).factorial : ℝ) <
      1 / ((m + k).factorial : ℝ) - 1 / ((m + k + 1).factorial : ℝ) := by
  have hidx : m + 1 + k = m + k + 1 := by omega
  rw [hidx]
  have hfacNat : (m + k + 1).factorial =
      (m + k + 1) * (m + k).factorial := Nat.factorial_succ (m + k)
  have hfac : ((m + k + 1).factorial : ℝ) =
      (m + k + 1 : ℝ) * ((m + k).factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [hfac]
  have hA : (0 : ℝ) < ((m + k).factorial : ℝ) := by positivity
  have hB : (0 : ℝ) < (m + k + 1 : ℝ) := by positivity
  have hmk : (2 : ℝ) ≤ m + k := by
    exact_mod_cast (show 2 ≤ m + k by omega)
  field_simp
  nlinarith

theorem unitFactTail_lt_one_div_factorial {m : ℕ} (hm : 2 ≤ m) :
    unitFactTail m < (1 : ℝ) / (m.factorial : ℝ) := by
  let source : ℕ → ℝ := fun k => (1 : ℝ) / ((m + 1 + k).factorial : ℝ)
  let majorant : ℕ → ℝ := fun k =>
    (1 : ℝ) / ((m + k).factorial : ℝ) - 1 / ((m + k + 1).factorial : ℝ)
  have hsource_nonneg : ∀ k, 0 ≤ source k := by
    intro k
    simp only [source]
    positivity
  have hle : ∀ k, source k ≤ majorant k := by
    intro k
    exact (unitFactTail_term_lt_telescope (m := m) (k := k) hm).le
  have hstrict : source 0 < majorant 0 :=
    unitFactTail_term_lt_telescope (m := m) (k := 0) hm
  have hmajorant : Summable majorant := by
    simpa [majorant, Nat.add_assoc] using
      (_root_.Erdos68.hasSum_factorial_telescope m).summable
  have hsum := Summable.tsum_lt_tsum_of_nonneg (i := 0)
    hsource_nonneg hle hstrict hmajorant
  have hmajValue : (∑' k, majorant k) = (1 : ℝ) / (m.factorial : ℝ) :=
    (_root_.Erdos68.hasSum_factorial_telescope m).tsum_eq
  rw [hmajValue] at hsum
  simpa [unitFactTail, source] using hsum

theorem unitFactScaledTail_pos_lt_one {m : ℕ} (hm : 2 ≤ m) :
    0 < unitFactScaledTail m ∧ unitFactScaledTail m < 1 := by
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  constructor
  · exact mul_pos hfac (unitFactTail_pos m)
  · unfold unitFactScaledTail
    calc
      (m.factorial : ℝ) * unitFactTail m <
          (m.factorial : ℝ) * (1 / (m.factorial : ℝ)) :=
        mul_lt_mul_of_pos_left (unitFactTail_lt_one_div_factorial hm) hfac
      _ = 1 := by field_simp

theorem unitFact_tsum_eq_expPrefix_add_tail (m : ℕ) (hm : 2 ≤ m) :
    (∑' n : ℕ, unitFactTerm n) =
      (factorialExpPrefix m : ℝ) + unitFactTail m := by
  have hsplit := summable_unitFactTerm.sum_add_tsum_nat_add (m + 1)
  rw [← hsplit]
  congr 1
  · have hset : Finset.Icc 2 m =
        (Finset.range (m + 1)).filter (fun n => 2 ≤ n) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
      omega
    calc
      ∑ n ∈ Finset.range (m + 1), unitFactTerm n =
          ∑ n ∈ Finset.Icc 2 m, (1 : ℝ) / (n.factorial : ℝ) := by
        rw [hset, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases h2 : 2 ≤ n
        · simp [unitFactTerm, h2]
        · simp [unitFactTerm, h2]
      _ = (factorialExpPrefix m : ℝ) := by
        unfold factorialExpPrefix
        push_cast
        rfl
  · unfold unitFactTail
    apply tsum_congr
    intro k
    have hk : 2 ≤ k + (m + 1) := by omega
    rw [unitFactTerm, if_pos hk]
    congr 3 <;> omega

theorem unitFact_tsum_scaled_decomposition (m : ℕ) (hm : 2 ≤ m) :
    (m.factorial : ℝ) * (∑' n : ℕ, unitFactTerm n) =
      (factorialExpScaled m : ℝ) + unitFactScaledTail m := by
  rw [unitFact_tsum_eq_expPrefix_add_tail m hm, mul_add]
  unfold unitFactScaledTail
  congr 1
  have h := factorial_mul_expPrefix_eq_scaled m
  exact_mod_cast h

/-- Rationality of `x + (e - 2)` forces the exceptional residue `-2`
eventually along the factorial orbit of `x`. -/
theorem eventually_facFloor_mod_neg_two_of_not_irrational_add_unitFact
    (x : ℝ) (hrat : ¬ Irrational (x + ∑' n, unitFactTerm n)) :
    ∃ M, ∀ m, M ≤ m → ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0 := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  refine ⟨max 3 (r.den + 1), ?_⟩
  intro m hm
  have hm3 : 3 ≤ m := by omega
  have hqm1 : r.den ≤ m - 1 := by omega
  let K : ℤ := (((m - 1).factorial / r.den : ℕ) : ℤ) * r.num
  have hclearQ := factorial_scaled_rational_eq_intCast r.num r.den_pos hqm1
  have hpredScaled :
      ((m - 1).factorial : ℝ) * (x + ∑' n, unitFactTerm n) = (K : ℝ) := by
    rw [hr, Rat.cast_def]
    exact_mod_cast hclearQ
  have hfacNat : m.factorial = m * (m - 1).factorial := by
    have hi : m - 1 + 1 = m := by omega
    simpa only [hi] using Nat.factorial_succ (m - 1)
  have htotalScaled :
      (m.factorial : ℝ) * (x + ∑' n, unitFactTerm n) =
        (((m : ℤ) * K : ℤ) : ℝ) := by
    rw [show (m.factorial : ℝ) =
      (m : ℝ) * ((m - 1).factorial : ℝ) by exact_mod_cast hfacNat]
    push_cast
    rw [mul_assoc, hpredScaled]
  have hunitScaled := unitFact_tsum_scaled_decomposition m (by omega)
  have hJ :
      (m.factorial : ℝ) * x =
        (((m : ℤ) * K - (factorialExpScaled m : ℤ) : ℤ) : ℝ) -
          unitFactScaledTail m := by
    push_cast at htotalScaled hunitScaled ⊢
    linarith
  obtain ⟨hrpos, hrlt⟩ := unitFactScaledTail_pos_lt_one (m := m) (by omega)
  have hs := factorialExpScaled_step (m := m) (by omega)
  have hsZ : (factorialExpScaled m : ℤ) =
      (m : ℤ) * (factorialExpScaled (m - 1) : ℤ) + 1 := by
    exact_mod_cast hs
  have hEmod : (factorialExpScaled m : ℤ) % (m : ℤ) = 1 := by
    rw [hsZ]
    calc
      ((m : ℤ) * (factorialExpScaled (m - 1) : ℤ) + 1) % (m : ℤ) =
          (1 + (factorialExpScaled (m - 1) : ℤ) * (m : ℤ)) % (m : ℤ) := by
        congr 1
        ring
      _ = 1 % (m : ℤ) := by rw [Int.add_mul_emod_self_right]
      _ = 1 := Int.emod_eq_of_lt (by omega)
        (by exact_mod_cast (show 1 < m by omega))
  have h := floor_mod_eq_neg_two_of_mul_sub_int_sub_small m K
    (factorialExpScaled m : ℤ) ((m.factorial : ℝ) * x)
    (unitFactScaledTail m) hJ hrpos hrlt hEmod
  simpa [facFloor] using h

private theorem canonicalDigitTerm_add_unitFactTerm_eq_telescope_of_digit_sub_two
    {x : ℝ} {m : ℕ} (hm : 3 ≤ m)
    (hdigit : canonicalDigit x m = (m : ℤ) - 2) :
    canonicalDigitTerm x m + unitFactTerm m =
      (1 : ℝ) / ((m - 1).factorial : ℝ) - 1 / (m.factorial : ℝ) := by
  rw [canonicalDigitTerm, if_pos (by omega), unitFactTerm, if_pos (by omega), hdigit]
  have hfacNat : m.factorial = m * (m - 1).factorial := by
    have hidx : m - 1 + 1 = m := by omega
    simpa only [hidx] using Nat.factorial_succ (m - 1)
  have hfac : (m.factorial : ℝ) =
      (m : ℝ) * ((m - 1).factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [hfac]
  push_cast
  field_simp
  ring

/-- Eventual exceptional digits make `x + (e - 2)` rational. -/
theorem not_irrational_add_unitFact_of_eventually_canonicalDigit_eq_sub_two
    (x : ℝ)
    (hdigits : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → canonicalDigit x m = (m : ℤ) - 2) :
    ¬ Irrational (x + (∑' n : ℕ, unitFactTerm n)) := by
  obtain ⟨M, hM⟩ := hdigits
  let N : ℕ := max M 3
  have hMN : M ≤ N := by simp [N]
  have hN3 : 3 ≤ N := by simp [N]
  let f : ℕ → ℝ := fun m => canonicalDigitTerm x m + unitFactTerm m
  have hfHasSum :
      HasSum f ((x - (⌊x⌋ : ℝ)) + (∑' n : ℕ, unitFactTerm n)) := by
    exact (hasSum_canonicalDigitTerm x).add summable_unitFactTerm.hasSum
  have hf : Summable f := hfHasSum.summable
  have htail : (∑' k : ℕ, f (k + N)) =
      (1 : ℝ) / ((N - 1).factorial : ℝ) := by
    calc
      (∑' k : ℕ, f (k + N)) =
          ∑' k : ℕ, ((1 : ℝ) / (((N - 1) + k).factorial : ℝ) -
            1 / (((N - 1) + k + 1).factorial : ℝ)) := by
        apply tsum_congr
        intro k
        have hkn : 3 ≤ k + N := by omega
        have hMkn : M ≤ k + N := by omega
        have hd : canonicalDigit x (k + N) = (k + N : ℤ) - 2 :=
          hM (k + N) hMkn
        rw [show f (k + N) =
          canonicalDigitTerm x (k + N) + unitFactTerm (k + N) by rfl]
        rw [canonicalDigitTerm_add_unitFactTerm_eq_telescope_of_digit_sub_two hkn hd]
        have hi1 : k + N - 1 = (N - 1) + k := by omega
        have hi2 : k + N = (N - 1) + k + 1 := by omega
        rw [hi1, hi2]
      _ = (1 : ℝ) / ((N - 1).factorial : ℝ) :=
        (_root_.Erdos68.hasSum_factorial_telescope (N - 1)).tsum_eq
  have hsplit := hf.sum_add_tsum_nat_add N
  have htotal : (∑' m : ℕ, f m) =
      (∑ m ∈ Finset.range N, f m) +
        (1 : ℝ) / ((N - 1).factorial : ℝ) := by
    rw [← hsplit, htail]
  let q : ℚ := (⌊x⌋ : ℚ) +
    ∑ m ∈ Finset.range N,
      (if 2 ≤ m then (canonicalDigit x m : ℚ) / (m.factorial : ℚ) +
        1 / (m.factorial : ℚ) else 0) +
    1 / ((N - 1).factorial : ℚ)
  have hqcast : (q : ℝ) =
      (⌊x⌋ : ℝ) + (∑ m ∈ Finset.range N, f m) +
        (1 : ℝ) / ((N - 1).factorial : ℝ) := by
    unfold q f canonicalDigitTerm unitFactTerm
    push_cast
    apply congrArg (fun z : ℝ =>
      (⌊x⌋ : ℝ) + z + 1 / ((N - 1).factorial : ℝ))
    apply Finset.sum_congr rfl
    intro m hm
    by_cases h2 : 2 ≤ m <;> simp [h2]
  have hvalue : x + (∑' n : ℕ, unitFactTerm n) = (q : ℝ) := by
    have hsumValue := hfHasSum.tsum_eq
    rw [htotal] at hsumValue
    rw [hqcast]
    linarith
  rw [hvalue]
  exact Rat.not_irrational q

/-- Eventual exceptional floor residues are exactly eventual exceptional
canonical digits. -/
theorem eventually_facFloor_mod_neg_two_iff_eventually_canonicalDigit_eq_sub_two
    (x : ℝ) :
    (∃ M, ∀ m, M ≤ m → ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0) ↔
      (∃ M, ∀ m, M ≤ m → canonicalDigit x m = (m : ℤ) - 2) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨max M 3, ?_⟩
    intro m hm
    apply canonicalDigit_eq_sub_two_of_facFloor_mod_eq_neg_two x (by omega)
    exact hM m (by omega)
  · rintro ⟨M, hM⟩
    exact ⟨M, fun m hm =>
      facFloor_mod_eq_neg_two_of_canonicalDigit_eq_sub_two x m (hM m hm)⟩

/-- The generic fixed-orbit rationality boundary in canonical-digit form. -/
theorem not_irrational_add_unitFact_iff_eventually_canonicalDigit_eq_sub_two
    (x : ℝ) :
    ¬ Irrational (x + ∑' n, unitFactTerm n) ↔
      ∃ M, ∀ m, M ≤ m → canonicalDigit x m = (m : ℤ) - 2 := by
  constructor
  · intro hrat
    exact (eventually_facFloor_mod_neg_two_iff_eventually_canonicalDigit_eq_sub_two x).mp
      (eventually_facFloor_mod_neg_two_of_not_irrational_add_unitFact x hrat)
  · exact not_irrational_add_unitFact_of_eventually_canonicalDigit_eq_sub_two x

/-- The generic fixed-orbit rationality boundary in floor-residue form. -/
theorem not_irrational_add_unitFact_iff_eventually_facFloor_mod_neg_two
    (x : ℝ) :
    ¬ Irrational (x + ∑' n, unitFactTerm n) ↔
      ∃ M, ∀ m, M ≤ m → ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0 := by
  rw [not_irrational_add_unitFact_iff_eventually_canonicalDigit_eq_sub_two]
  exact (eventually_facFloor_mod_neg_two_iff_eventually_canonicalDigit_eq_sub_two x).symm

/-- The Erdős #68 series is rational exactly when the companion factorial
orbit is eventually concentrated in the exceptional residue `-2`. -/
theorem not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two :
    ¬ Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ M, ∀ m, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0 := by
  rw [← companionConstant_add_unitFact_eq_series]
  exact not_irrational_add_unitFact_iff_eventually_facFloor_mod_neg_two companionConstant

/-- The exact open boundary: irrationality of the Erdős #68 series is
equivalent to cofinally many escapes from the exceptional residue. -/
theorem irrational_factorialGapSeries_iff_cofinal_companion_floor_misses :
    Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B, ∃ m, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0 := by
  constructor
  · intro hirr B
    by_contra hnone
    push Not at hnone
    have hev : ∃ M, ∀ m, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0 := by
      exact ⟨B + 1, fun m hm => hnone m (by omega)⟩
    exact
      (not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two.mpr hev)
        hirr
  · intro hcof
    by_contra hrat
    obtain ⟨M, hM⟩ :=
      not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two.mp hrat
    obtain ⟨m, hm, hmiss⟩ := hcof M
    exact hmiss (hM m (by omega))

/-- The anchored unit-factorial series is exactly `exp 1 - 2`. -/
theorem tsum_unitFactTerm_eq_exp_one_sub_two :
    (∑' n : ℕ, unitFactTerm n) = Real.exp 1 - 2 := by
  let u : ℕ → ℝ := fun n => (1 : ℝ) / (n.factorial : ℝ)
  have hu : Summable u := by
    have h :=
      NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) (1 : ℝ)
    simpa [u, div_eq_mul_inv] using h
  have hexp : Real.exp 1 = ∑' n : ℕ, (1 : ℝ) / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    simp only [one_pow]
  let low : ℕ → ℝ := fun n => if n < 2 then u n else 0
  have hlow : Summable low := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hu
    · simp only [low]
      split <;> positivity
    · simp only [low]
      split
      · exact le_rfl
      · positivity
  have hlowValue : (∑' n : ℕ, low n) = 2 := by
    rw [tsum_eq_sum (s := Finset.range 2)]
    · norm_num [Finset.sum_range_succ, low, u]
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      simp only [low]
      rw [if_neg (by omega)]
  have hdecomp :
      (∑' n : ℕ, unitFactTerm n) + (∑' n : ℕ, low n) =
        ∑' n : ℕ, u n := by
    rw [← summable_unitFactTerm.tsum_add hlow]
    apply tsum_congr
    intro n
    by_cases hn : 2 ≤ n
    · rw [unitFactTerm, if_pos hn]
      simp only [low, u]
      rw [if_neg (by omega)]
      ring
    · have hlt : n < 2 := by omega
      rw [unitFactTerm, if_neg hn]
      simp only [low, u]
      rw [if_pos hlt]
      simp
  rw [hlowValue] at hdecomp
  rw [show (∑' n : ℕ, u n) = Real.exp 1 by simpa [u] using hexp.symm]
    at hdecomp
  linarith

#print axioms tsum_unitFactTerm_eq_exp_one_sub_two
#print axioms tsum_canonicalDigitTerm
#print axioms not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two
#print axioms irrational_factorialGapSeries_iff_cofinal_companion_floor_misses

end ErdosProblems.Erdos68
