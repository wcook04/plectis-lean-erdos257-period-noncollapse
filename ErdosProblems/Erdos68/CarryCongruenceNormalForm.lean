import ErdosProblems.Erdos68.FactorialGapPlateauCore

/-!
# Erdős #68: carry congruence normal form

The strict successor splits exactly:

`N_m = ⌊m!·P_m⌋ + 1 = E_m + ⌊F_m⌋ + 1`

where `P_m = factorialGapPrefix m`, `E_m = ∑_{n=2}^{m} m!/n! ∈ ℤ`, and
`F_m = ∑_{n=2}^{m} (m!/n!)/(n!−1)`.  Since every term of `E_m` except the
`n = m` summand is divisible by `m`, we get `E_m ≡ 1 (mod m)`, hence the
**carry congruence normal form**

`unit carry at m  ⟺  ⌊F_m⌋ ≡ −2 (mod m)`,

i.e. the frontier predicate "m does not divide the strict successor" is a
congruence test on one explicit rational floor.  Moreover

`F_m = m!·C_m`,   `C_m = ∑_{n=2}^{m} 1/(n!(n!−1))`,

so the test only involves partial sums of the fixed constant series
`C_∞ = lim C_m`; the telescoping identity `1/(n!(n!−1)) = 1/(n!−1) − 1/n!`
identifies that limit with `S − (e − 2)` analytically (documented outside
this module).

No cofinality claim is made here.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- Integer part of the factorially scaled prefix. -/
def scaledPrefixInt (m : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 m, m.factorial / n.factorial

/-- Fractional carrier of the factorially scaled prefix. -/
noncomputable def scaledPrefixFrac (m : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 2 m,
    (((m.factorial / n.factorial : ℕ) : ℚ)) / (((n.factorial : ℚ) - 1))

/-- Partial sums of the companion constant series `C_m`. -/
noncomputable def compConstPartial (m : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 2 m,
    1 / (((n.factorial : ℚ)) * ((n.factorial : ℚ) - 1))

theorem factorialGapPrefix_mul_eq_split (m : ℕ) (hm : 2 ≤ m) :
    ((m.factorial : ℚ)) * factorialGapPrefix m =
      ((scaledPrefixInt m : ℚ) + scaledPrefixFrac m) := by
  unfold factorialGapPrefix scaledPrefixInt scaledPrefixFrac
  rw [Finset.mul_sum]
  rw [Nat.cast_sum (R := ℚ)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
  have hdvd : n.factorial ∣ m.factorial :=
    Nat.factorial_dvd_factorial hnm
  let d : ℕ := m.factorial / n.factorial
  have hd : d * n.factorial = m.factorial := Nat.div_mul_cancel hdvd
  have hcast : (((m.factorial : ℕ) : ℚ)) = (d : ℚ) * ((n.factorial : ℚ)) := by
    exact_mod_cast hd.symm
  have hdenNe : ((n.factorial : ℚ) - 1) ≠ 0 := by
    have h1 : (1 : ℕ) < n.factorial := Nat.one_lt_factorial.mpr hn2
    have h2 : (0 : ℚ) < (n.factorial : ℚ) - 1 := by
      have hfacQ : (1 : ℚ) < (n.factorial : ℚ) := by
        exact_mod_cast h1
      linarith
    exact ne_of_gt h2
  field_simp
  simpa [d] using hcast

theorem strictSuccessorRat_eq_split (m : ℕ) (hm : 2 ≤ m) :
    strictFacTopRat (factorialGapPrefix m) m =
      scaledPrefixInt m + ⌊scaledPrefixFrac m⌋ + 1 := by
  have hsplit := factorialGapPrefix_mul_eq_split m hm
  unfold strictFacTopRat
  show ⌊((m.factorial : ℕ) : ℚ) * factorialGapPrefix m⌋ + 1 = _
  rw [hsplit, Int.floor_natCast_add]

theorem scaledPrefixInt_mod_eq_one {m : ℕ} (hm : 3 ≤ m) :
    scaledPrefixInt m % m = 1 := by
  have hfacSplit : ∀ n ∈ Finset.Icc 2 (m - 1),
      ((m.factorial / n.factorial : ℕ))
        = m * ((m - 1).factorial / n.factorial) := by
    intro n hn
    have hnn : n ≤ m - 1 := (Finset.mem_Icc.mp hn).2
    have hfac : m.factorial = m * (m - 1).factorial := by
      have hidx : m - 1 + 1 = m := by omega
      calc m.factorial = (m - 1 + 1).factorial := by rw [hidx]
        _ = (m - 1 + 1) * (m - 1).factorial := Nat.factorial_succ _
        _ = m * (m - 1).factorial := by rw [hidx]
    rw [hfac]
    exact Nat.mul_div_assoc (k := n.factorial) m
      (Nat.factorial_dvd_factorial hnn)
  have hinsert : Finset.Icc 2 m = insert m (Finset.Icc 2 (m - 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  unfold scaledPrefixInt
  rw [hinsert, Finset.sum_insert]
  · rw [Nat.div_self (by positivity)]
    have hsum : (∑ x ∈ Finset.Icc 2 (m - 1),
        ((m.factorial / x.factorial : ℕ)))
        = m * ∑ x ∈ Finset.Icc 2 (m - 1),
            ((m - 1).factorial / x.factorial) := by
      calc
        ∑ x ∈ Finset.Icc 2 (m - 1), m.factorial / x.factorial =
            ∑ x ∈ Finset.Icc 2 (m - 1),
              m * ((m - 1).factorial / x.factorial) := by
                refine Finset.sum_congr rfl fun x hx => ?_
                exact hfacSplit x hx
        _ = m * ∑ x ∈ Finset.Icc 2 (m - 1),
              ((m - 1).factorial / x.factorial) := by
                rw [Finset.mul_sum]
    rw [hsum, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [Finset.mem_Icc]
    omega

/-- The integral carrier obeys the exact factorial-radix recurrence. -/
theorem scaledPrefixInt_succ {m : ℕ} (hm : 2 ≤ m) :
    scaledPrefixInt (m + 1) = (m + 1) * scaledPrefixInt m + 1 := by
  have hinsert :
      Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : m + 1 ∉ Finset.Icc 2 m := by
    simp only [Finset.mem_Icc]
    omega
  unfold scaledPrefixInt
  rw [hinsert, Finset.sum_insert hnotmem]
  have hterminal : (m + 1).factorial / (m + 1).factorial = 1 := by
    exact Nat.div_self (Nat.factorial_pos (m + 1))
  rw [hterminal]
  have hscale :
      ∑ n ∈ Finset.Icc 2 m, (m + 1).factorial / n.factorial =
        (m + 1) * ∑ n ∈ Finset.Icc 2 m, m.factorial / n.factorial := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Nat.factorial_succ]
    exact Nat.mul_div_assoc (m + 1)
      (Nat.factorial_dvd_factorial (Finset.mem_Icc.mp hn).2)
  rw [hscale]
  omega

/-- Two radix steps expose a quadratic-modulus residue: the integral carrier
at `m+1` is always `m+2` modulo `m(m+1)`. -/
theorem scaledPrefixInt_succ_mod_mul_eq_add_two {m : ℕ} (hm : 3 ≤ m) :
    scaledPrefixInt (m + 1) % (m * (m + 1)) = m + 2 := by
  have hmod := scaledPrefixInt_mod_eq_one hm
  have hdecomp :
      scaledPrefixInt m = m * (scaledPrefixInt m / m) + 1 := by
    have h := Nat.mod_add_div (scaledPrefixInt m) m
    rw [hmod] at h
    omega
  rw [scaledPrefixInt_succ (by omega), hdecomp]
  have hrearrange :
      (m + 1) * (m * (scaledPrefixInt m / m) + 1) + 1 =
        (m + 2) + (scaledPrefixInt m / m) * (m * (m + 1)) := by
    ring
  rw [hrearrange,
    Nat.mul_comm (scaledPrefixInt m / m) (m * (m + 1)),
    Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by nlinarith)

/-- **Carry congruence normal form.**  The unit carry at index `m` is
exactly the congruence `⌊F_m⌋ ≡ −2 (mod m)` on the fractional carrier. -/
theorem factorialGapStepCarry_eq_one_iff_floor_frac_congruence {m : ℕ}
    (hm : 3 ≤ m) :
    factorialGapStepCarry m = 1 ↔
      ((⌊scaledPrefixFrac m⌋ + 2 : ℤ) % (m : ℤ)) = 0 := by
  have hm2 : 2 ≤ m := by omega
  have hem : scaledPrefixInt m % m = 1 := scaledPrefixInt_mod_eq_one hm
  have hcast : ((scaledPrefixInt m : ℤ) % (m : ℤ)) =
      ((scaledPrefixInt m % m : ℕ) : ℤ) := (Int.natCast_emod _ _).symm
  have hE1 : ((scaledPrefixInt m : ℤ) % (m : ℤ)) = 1 := by
    rw [hcast, hem]; norm_num
  have key : ((scaledPrefixInt m : ℤ) +
        ⌊scaledPrefixFrac m⌋ + 1) % (m : ℤ) =
      ((⌊scaledPrefixFrac m⌋ + 2 : ℤ) % (m : ℤ)) := by
    have hEdecomp : (scaledPrefixInt m : ℤ) =
        1 + (m : ℤ) * ((scaledPrefixInt m : ℤ) / (m : ℤ)) := by
      have hdiv := Int.emod_add_ediv (scaledPrefixInt m : ℤ) (m : ℤ)
      rw [hE1] at hdiv
      omega
    rw [hEdecomp]
    calc
      ((1 + (m : ℤ) * ((scaledPrefixInt m : ℤ) / (m : ℤ))) +
          ⌊scaledPrefixFrac m⌋ + 1) % (m : ℤ) =
        ((⌊scaledPrefixFrac m⌋ + 2) +
          ((scaledPrefixInt m : ℤ) / (m : ℤ)) * (m : ℤ)) % (m : ℤ) := by
            congr 1
            ring
      _ = (⌊scaledPrefixFrac m⌋ + 2) % (m : ℤ) := by
        rw [Int.add_mul_emod_self_right]
  rw [factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm,
    strictSuccessorRat_eq_split m hm2, Int.dvd_iff_emod_eq_zero, key]

/-- **Zero-carry congruence normal form.**  The lower rare carry at index
`m` is exactly the adjacent residue class
`⌊factorialGapScaledFrac m⌋ ≡ -1 (mod m)`.  Together with the unit-carry
criterion above, the two exceptional carry values are consecutive companion
floor residues. -/
theorem factorialGapStepCarry_eq_zero_iff_floor_frac_congruence {m : ℕ}
    (hm : 3 ≤ m) :
    factorialGapStepCarry m = 0 ↔
      ((⌊scaledPrefixFrac m⌋ + 1 : ℤ) % (m : ℤ)) = 0 := by
  let N : ℤ := strictFacTopRat (factorialGapPrefix m) m
  let P : ℤ := strictFacTopRat (factorialGapPrefix (m - 1)) (m - 1)
  let E : ℤ := scaledPrefixInt m
  let f : ℤ := ⌊scaledPrefixFrac m⌋
  let q : ℤ := (scaledPrefixInt m / m : ℕ)
  have hm2 : 2 ≤ m := by omega
  have hsplit : N = E + f + 1 := by
    dsimp [N, E, f]
    exact strictSuccessorRat_eq_split m hm2
  have hstep :
      N = (m : ℤ) * P + 1 - factorialGapStepCarry m := by
    have h := strictFacTop_factorialGapPrefix_step (m := m) hm2
    rw [strictFacTop_ratCast, strictFacTop_ratCast] at h
    simpa [N, P, mul_comm] using h
  have hem : scaledPrefixInt m % m = 1 := scaledPrefixInt_mod_eq_one hm
  have hnatDecomp :
      scaledPrefixInt m = m * (scaledPrefixInt m / m) + 1 := by
    have hdiv := Nat.mod_add_div (scaledPrefixInt m) m
    rw [hem] at hdiv
    omega
  have hE : E = (m : ℤ) * q + 1 := by
    dsimp [E, q]
    exact_mod_cast hnatDecomp
  constructor
  · intro hb
    apply Int.dvd_iff_emod_eq_zero.mp
    refine ⟨P - q, ?_⟩
    dsimp [f]
    rw [hb] at hstep
    linear_combination hstep - hsplit - hE
  · intro hmod
    have hdvd : (m : ℤ) ∣ f + 1 := by
      exact Int.dvd_iff_emod_eq_zero.mpr hmod
    obtain ⟨z, hz⟩ := hdvd
    have hcarryDvd : (m : ℤ) ∣ factorialGapStepCarry m := by
      refine ⟨P - q - z, ?_⟩
      linear_combination hstep - hsplit - hE - hz
    have hbounds := factorialGapStepCarry_bounds hm
    apply Int.eq_zero_of_abs_lt_dvd hcarryDvd
    rw [abs_lt]
    constructor <;> omega

/-- The companion carrier is itself a non-autonomous factorial orbit.  The
new endpoint contributes the tiny positive kick `1 / ((m+1)!-1)`. -/
theorem scaledPrefixFrac_succ {m : ℕ} (hm : 2 ≤ m) :
    scaledPrefixFrac (m + 1) =
      (m + 1 : ℚ) * scaledPrefixFrac m +
        1 / ((((m + 1).factorial : ℕ) : ℚ) - 1) := by
  have hset :
      Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : m + 1 ∉ Finset.Icc 2 m := by
    simp only [Finset.mem_Icc]
    omega
  have hfac : (m + 1).factorial = (m + 1) * m.factorial :=
    Nat.factorial_succ m
  unfold scaledPrefixFrac
  rw [hset, Finset.sum_insert hnotmem]
  rw [Nat.div_self (by positivity)]
  have hsum :
      ∑ n ∈ Finset.Icc 2 m,
          (((m + 1).factorial / n.factorial : ℕ) : ℚ) /
            ((n.factorial : ℚ) - 1) =
        (m + 1 : ℚ) *
          ∑ n ∈ Finset.Icc 2 m,
            (((m.factorial / n.factorial : ℕ) : ℚ) /
              ((n.factorial : ℚ) - 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
    have hdvd : n.factorial ∣ m.factorial :=
      Nat.factorial_dvd_factorial hnm
    rw [hfac, Nat.mul_div_assoc (m + 1) hdvd]
    push_cast
    ring
  rw [hsum]
  ring

/-- After removing the integral part of the current carrier, the next carrier
floor splits into the old floor multiplied by the new radix and one local
digit.  This is the exact thin-cylinder coordinate for consecutive carries. -/
theorem floor_scaledPrefixFrac_succ {m : ℕ} (hm : 2 ≤ m) :
    ⌊scaledPrefixFrac (m + 1)⌋ =
      (m + 1 : ℤ) * ⌊scaledPrefixFrac m⌋ +
        ⌊(m + 1 : ℚ) * Int.fract (scaledPrefixFrac m) +
          1 / ((((m + 1).factorial : ℕ) : ℚ) - 1)⌋ := by
  rw [scaledPrefixFrac_succ hm]
  have hsplit : scaledPrefixFrac m =
      (⌊scaledPrefixFrac m⌋ : ℚ) + Int.fract (scaledPrefixFrac m) :=
    (Int.floor_add_fract (scaledPrefixFrac m)).symm
  have harg :
      (m + 1 : ℚ) * scaledPrefixFrac m +
          1 / ((((m + 1).factorial : ℕ) : ℚ) - 1) =
        (((m + 1 : ℤ) * ⌊scaledPrefixFrac m⌋ : ℤ) : ℚ) +
          ((m + 1 : ℚ) * Int.fract (scaledPrefixFrac m) +
            1 / ((((m + 1).factorial : ℕ) : ℚ) - 1)) := by
    nth_rewrite 1 [hsplit]
    push_cast
    ring
  rw [harg, Int.floor_intCast_add]

/-- The successor unit carry is a congruence on one local digit of the
companion orbit.  The old integral carrier disappears modulo the new radix. -/
theorem factorialGapStepCarry_succ_eq_one_iff_local_digit_congruence
    {m : ℕ} (hm : 3 ≤ m) :
    factorialGapStepCarry (m + 1) = 1 ↔
      ((⌊(m + 1 : ℚ) * Int.fract (scaledPrefixFrac m) +
          1 / ((((m + 1).factorial : ℕ) : ℚ) - 1)⌋ + 2 : ℤ) %
        (m + 1 : ℤ)) = 0 := by
  rw [factorialGapStepCarry_eq_one_iff_floor_frac_congruence (by omega),
    floor_scaledPrefixFrac_succ (by omega)]
  have key :
      (((m + 1 : ℤ) * ⌊scaledPrefixFrac m⌋ +
            ⌊(m + 1 : ℚ) * Int.fract (scaledPrefixFrac m) +
              1 / ((((m + 1).factorial : ℕ) : ℚ) - 1)⌋ + 2) %
          (m + 1 : ℤ)) =
        ((⌊(m + 1 : ℚ) * Int.fract (scaledPrefixFrac m) +
              1 / ((((m + 1).factorial : ℕ) : ℚ) - 1)⌋ + 2) %
          (m + 1 : ℤ)) := by
    calc
      (((m + 1 : ℤ) * ⌊scaledPrefixFrac m⌋ +
            ⌊(m + 1 : ℚ) * Int.fract (scaledPrefixFrac m) +
              1 / ((((m + 1).factorial : ℕ) : ℚ) - 1)⌋ + 2) %
          (m + 1 : ℤ)) =
        ((⌊(m + 1 : ℚ) * Int.fract (scaledPrefixFrac m) +
              1 / ((((m + 1).factorial : ℕ) : ℚ) - 1)⌋ + 2) +
            ⌊scaledPrefixFrac m⌋ * (m + 1 : ℤ)) % (m + 1 : ℤ) := by
              congr 1
              ring
      _ = ((⌊(m + 1 : ℚ) * Int.fract (scaledPrefixFrac m) +
              1 / ((((m + 1).factorial : ℕ) : ℚ) - 1)⌋ + 2) %
            (m + 1 : ℤ)) := by
        rw [Int.add_mul_emod_self_right]
  push_cast at key ⊢
  rw [key]

theorem scaledPrefixFrac_eq_compConstPartial_mul (m : ℕ) (hm : 2 ≤ m) :
    scaledPrefixFrac m =
      (m.factorial : ℚ) * compConstPartial m := by
  unfold scaledPrefixFrac compConstPartial
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hdvd : n.factorial ∣ m.factorial :=
    Nat.factorial_dvd_factorial (Finset.mem_Icc.mp hn).2
  let d : ℕ := m.factorial / n.factorial
  have hd : d * n.factorial = m.factorial := Nat.div_mul_cancel hdvd
  have hcast : (((m.factorial : ℕ) : ℚ)) = (d : ℚ) * ((n.factorial : ℚ)) := by
    exact_mod_cast hd.symm
  have h1 : (1 : ℕ) < n.factorial := Nat.one_lt_factorial.mpr
    (Finset.mem_Icc.mp hn).1
  have h2 : (0 : ℚ) < (n.factorial : ℚ) - 1 := by
    have hfacQ : (1 : ℚ) < (n.factorial : ℚ) := by
      exact_mod_cast h1
    linarith
  have hdenNe : (((n.factorial : ℚ) - 1) ≠ 0 ∧
      (((n.factorial : ℚ)) * ((n.factorial : ℚ) - 1)) ≠ 0) :=
    ⟨ne_of_gt h2, mul_ne_zero (by positivity) (ne_of_gt h2)⟩
  field_simp
  rw [← hcast]

#print axioms factorialGapPrefix_mul_eq_split
#print axioms strictSuccessorRat_eq_split
#print axioms scaledPrefixInt_mod_eq_one
#print axioms factorialGapStepCarry_eq_one_iff_floor_frac_congruence
#print axioms factorialGapStepCarry_eq_zero_iff_floor_frac_congruence
#print axioms scaledPrefixFrac_succ
#print axioms floor_scaledPrefixFrac_succ
#print axioms factorialGapStepCarry_succ_eq_one_iff_local_digit_congruence
#print axioms scaledPrefixFrac_eq_compConstPartial_mul

end ErdosProblems.Erdos68
