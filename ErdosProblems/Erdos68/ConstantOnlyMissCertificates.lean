import ErdosProblems.Erdos68.CompanionConstantBridge

/-!
# Erdős #68: constant-only miss certificates

Let `C = ∑' n, compConstTerm n`.  The companion carrier has the form

`F_m = m! * C - δ_m`,

where `δ_m` is the positive scaled tail.  Once `0 < δ_m < 1`, subtracting the
tail can move the floor down by at most one.  The correct alternatives are

`⌊F_m⌋ = ⌊m! * C⌋`  or  `⌊F_m⌋ = ⌊m! * C⌋ - 1`.

Consequently it is enough to exclude the two adjacent residues `-2` and `-1`
for `⌊m! * C⌋` modulo `m`.  This formulation deliberately uses two floors of
the same fixed constant; it does not use a ceil, since `⌈J⌉ - 1 = ⌊J⌋` when
`J` is nonintegral and therefore misses the possible downward crossing.

The theorem below is the exact floor/congruence consumer.  A companion-tail
estimate may supply its `F_m = J - δ`, `0 < δ < 1` hypotheses without changing
the arithmetic proof.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- The fixed companion constant whose factorial orbit controls the carry
congruence. -/
noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, compConstTerm n

/-- The named companion constant differs from the original series by exactly
the anchored unit-factorial series. -/
theorem companionConstant_add_unitFact_eq_series :
    companionConstant + (∑' n : ℕ, unitFactTerm n) =
      _root_.Erdos68.factorialGapSeries := by
  simpa [companionConstant] using companion_tsum_add_unitFact_eq_series

/-- A positive companion term on its actual support. -/
theorem compConstTerm_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < compConstTerm n := by
  rw [compConstTerm, if_pos hn]
  have hfac : (1 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.one_lt_factorial.mpr hn
  apply one_div_pos.mpr
  push_cast
  exact mul_pos (by positivity) (by linarith)

/-- A factorial-scale floor and its canonical radix digit have the same
residue modulo the current radix, even after the `+2` normalization used by
the companion orbit. -/
theorem facFloor_add_two_emod_eq_canonicalDigit_add_two_emod
    (x : ℝ) (m : ℕ) :
    ((facFloor x m + 2 : ℤ) % (m : ℤ)) =
      ((canonicalDigit x m + 2 : ℤ) % (m : ℤ)) := by
  unfold canonicalDigit
  simp [Int.add_emod, Int.sub_emod]

/-- The eventual digit pattern `m-2` is the factorial-digit form of the
companion orbit's distinguished residue `-2`. -/
theorem facFloor_mod_eq_neg_two_of_canonicalDigit_eq_sub_two
    (x : ℝ) (m : ℕ)
    (hdigit : canonicalDigit x m = (m : ℤ) - 2) :
    ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0 := by
  rw [facFloor_add_two_emod_eq_canonicalDigit_add_two_emod, hdigit]
  simpa only [sub_add_cancel] using (Int.emod_self : (m : ℤ) % (m : ℤ) = 0)

/-- Conversely, at every radix at least three the distinguished floor residue
forces the unique canonical digit `m-2`. -/
theorem canonicalDigit_eq_sub_two_of_facFloor_mod_eq_neg_two
    (x : ℝ) {m : ℕ} (hm : 3 ≤ m)
    (hmod : ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0) :
    canonicalDigit x m = (m : ℤ) - 2 := by
  rw [facFloor_add_two_emod_eq_canonicalDigit_add_two_emod] at hmod
  have hd0 : 0 ≤ canonicalDigit x m :=
    canonicalDigit_nonneg x m (by omega)
  have hdlt : canonicalDigit x m < (m : ℤ) :=
    canonicalDigit_lt_radix x m (by omega)
  have hsum0 : 0 ≤ canonicalDigit x m + 2 := by omega
  by_cases hbelow : canonicalDigit x m + 2 < (m : ℤ)
  · have hrem := Int.emod_eq_of_lt hsum0 hbelow
    rw [hrem] at hmod
    omega
  · have hge : (m : ℤ) ≤ canonicalDigit x m + 2 := by omega
    have htwo : canonicalDigit x m + 2 < 2 * (m : ℤ) := by omega
    have hshift0 : 0 ≤ canonicalDigit x m + 2 - (m : ℤ) := by omega
    have hshiftlt : canonicalDigit x m + 2 - (m : ℤ) < (m : ℤ) := by omega
    have hrem :
        (canonicalDigit x m + 2) % (m : ℤ) =
          canonicalDigit x m + 2 - (m : ℤ) := by
      calc
        (canonicalDigit x m + 2) % (m : ℤ) =
            ((canonicalDigit x m + 2 - (m : ℤ)) + (m : ℤ)) % (m : ℤ) := by
              congr 1
              ring
        _ = (canonicalDigit x m + 2 - (m : ℤ)) % (m : ℤ) := by
              simp [Int.add_emod]
        _ = canonicalDigit x m + 2 - (m : ℤ) :=
              Int.emod_eq_of_lt hshift0 hshiftlt
    rw [hrem] at hmod
    omega

/-- Subtracting a quantity strictly between zero and one changes a real floor
by either zero or exactly one. -/
theorem floor_sub_small_eq_or_eq_sub_one (J δ : ℝ)
    (hδpos : 0 < δ) (hδlt : δ < 1) :
    ⌊J - δ⌋ = ⌊J⌋ ∨ ⌊J - δ⌋ = ⌊J⌋ - 1 := by
  have hlower : J - 1 < J - δ := by linarith
  have hupper : J - δ < J := by linarith
  have hfloorLower : ⌊J⌋ - 1 ≤ ⌊J - δ⌋ := by
    rw [← Int.floor_sub_one]
    exact Int.floor_mono hlower.le
  have hfloorUpper : ⌊J - δ⌋ ≤ ⌊J⌋ :=
    Int.floor_mono hupper.le
  omega

/-- The two-residue form of the small-subtraction floor lemma. -/
theorem floor_sub_small_mod_ne_zero
    (J δ : ℝ) (m : ℕ)
    (hδpos : 0 < δ) (hδlt : δ < 1)
    (hfloor : ((⌊J⌋ + 2 : ℤ) % (m : ℤ)) ≠ 0)
    (hpred : ((⌊J⌋ + 1 : ℤ) % (m : ℤ)) ≠ 0) :
    ((⌊J - δ⌋ + 2 : ℤ) % (m : ℤ)) ≠ 0 := by
  rcases floor_sub_small_eq_or_eq_sub_one J δ hδpos hδlt with hsame | hdown
  · simpa [hsame] using hfloor
  · rw [hdown]
    have harg : (⌊J⌋ - 1 + 2 : ℤ) = ⌊J⌋ + 1 := by ring
    rw [harg]
    exact hpred

/-- Arithmetic core of the rationality-only one-residue normal form.  If `J`
is an integral multiple of `m`, minus an integer congruent to one, minus a
strictly sub-unit positive remainder, then its floor is `-2` modulo `m`.

For the companion orbit the intended data are
`J = m! * companionConstant`, the multiple comes from a hypothetical rational
value of the original series, the integer is the truncated exponential sum,
and the remainder is the positive tail of `m! * exp 1`. -/
theorem floor_mod_eq_neg_two_of_mul_sub_int_sub_small
    (m : ℕ) (K E : ℤ) (J r : ℝ)
    (hJ : J = (((m : ℤ) * K - E : ℤ) : ℝ) - r)
    (hrpos : 0 < r) (hrlt : r < 1)
    (hEmod : E % (m : ℤ) = 1) :
    ((⌊J⌋ + 2 : ℤ) % (m : ℤ)) = 0 := by
  have hfloor : ⌊J⌋ = (m : ℤ) * K - E - 1 := by
    rw [hJ]
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  rw [hfloor]
  have hE : E = 1 + (m : ℤ) * (E / (m : ℤ)) := by
    have hdiv := Int.emod_add_mul_ediv E (m : ℤ)
    rw [hEmod] at hdiv
    omega
  rw [hE]
  ring_nf
  rw [← mul_sub]
  exact Int.mul_emod_right _ _

/-- **Corrected constant-only carry-miss interface.**  If the rational carrier
is a positive sub-unit tail below `J`, and the floor of `J` avoids the two
adjacent residue classes `-2` and `-1`, then the carry at `m` is non-unit.

The intended specialization is `J = m! * companionConstant`; the statement is
kept in decomposition form so that any independently proved tail estimate can
feed it directly. -/
theorem factorialGapStepCarry_ne_one_of_constant_floor_residues
    {m : ℕ} (hm : 3 ≤ m) (J δ : ℝ)
    (hdecomp : (scaledPrefixFrac m : ℝ) = J - δ)
    (hδpos : 0 < δ) (hδlt : δ < 1)
    (hfloor : ((⌊J⌋ + 2 : ℤ) % (m : ℤ)) ≠ 0)
    (hpred : ((⌊J⌋ + 1 : ℤ) % (m : ℤ)) ≠ 0) :
    factorialGapStepCarry m ≠ 1 := by
  have hmissReal : ((⌊(scaledPrefixFrac m : ℝ)⌋ + 2 : ℤ) % (m : ℤ)) ≠ 0 := by
    rw [hdecomp]
    exact floor_sub_small_mod_ne_zero J δ m hδpos hδlt hfloor hpred
  intro hunit
  have hhit :=
    (factorialGapStepCarry_eq_one_iff_floor_frac_congruence hm).mp hunit
  apply hmissReal
  norm_cast at hhit ⊢

#print axioms floor_sub_small_eq_or_eq_sub_one
#print axioms floor_sub_small_mod_ne_zero
#print axioms floor_mod_eq_neg_two_of_mul_sub_int_sub_small
#print axioms factorialGapStepCarry_ne_one_of_constant_floor_residues
#print axioms facFloor_add_two_emod_eq_canonicalDigit_add_two_emod
#print axioms facFloor_mod_eq_neg_two_of_canonicalDigit_eq_sub_two
#print axioms canonicalDigit_eq_sub_two_of_facFloor_mod_eq_neg_two

end ErdosProblems.Erdos68
