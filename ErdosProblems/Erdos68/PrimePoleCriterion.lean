import ErdosProblems.Erdos68.PrimeZeroBranch
import ErdosProblems.Erdos68.PrimePoleDenominator

/-!
# Erdős #68: finite prime-pole survival

This module isolates the exact finite cancellation law for a prime power in
the denominator of a factorial-gap prefix.  At the largest displayed
`q`-adic exponent, all lower-exponent summands vanish modulo `q`; the full
prime power survives prefix reduction precisely when the reciprocal sum of
the maximal-hit cofactors is nonzero.

The statement is deliberately finite.  It assigns no `q`-adic value to the
infinite real tail, and nonvanishing of one local residue is not by itself an
irrationality proof.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- Common-denominator numerator of the factorial-gap prefix when the literal
prefix LCM is used as denominator. -/
def factorialGapPrefixLCMNumerator (M : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 M,
    factorialGapPrefixLCM M / (n.factorial - 1)

/-- Indices at which the exact `q`-adic exponent of `n! - 1` is `e`. -/
def factorialGapMaxHits (q M e : ℕ) : Finset ℕ :=
  (Finset.Icc 2 M).filter fun n =>
    q ^ e ∣ n.factorial - 1 ∧
      ¬q ^ (e + 1) ∣ n.factorial - 1

/-- Sum modulo `q` of the inverses of the maximal-hit cofactors. -/
def factorialGapPrincipalResidue (q M e : ℕ) : ZMod q :=
  ∑ n ∈ factorialGapMaxHits q M e,
    (((n.factorial - 1) / q ^ e : ℕ) : ZMod q)⁻¹

/-- Every displayed factorial gap divides the literal prefix LCM. -/
theorem factorialGap_dvd_prefixLCM
    {M n : ℕ} (hn : n ∈ Finset.Icc 2 M) :
    n.factorial - 1 ∣ factorialGapPrefixLCM M := by
  exact Finset.dvd_lcm hn

private theorem factorialGap_pos_of_mem_Icc
    {M n : ℕ} (hn : n ∈ Finset.Icc 2 M) :
    0 < n.factorial - 1 := by
  exact Nat.sub_pos_of_lt
    (Nat.one_lt_factorial.mpr (Finset.mem_Icc.mp hn).1)

/-- If `q^e` divides a positive common multiple but a positive divisor has
smaller `q`-valuation, the quotient by that divisor still contains `q`. -/
private theorem prime_dvd_div_of_factorization_lt
    {q e d L : ℕ}
    (hq : q.Prime)
    (hdPos : 0 < d)
    (hLPos : 0 < L)
    (hdL : d ∣ L)
    (hqeL : q ^ e ∣ L)
    (hdLt : d.factorization q < e) :
    q ∣ L / d := by
  have hLNe : L ≠ 0 := hLPos.ne'
  have hdNe : d ≠ 0 := hdPos.ne'
  have hquotPos : 0 < L / d :=
    Nat.div_pos (Nat.le_of_dvd hLPos hdL) hdPos
  have hLe : e ≤ L.factorization q :=
    (hq.pow_dvd_iff_le_factorization hLNe).1 hqeL
  have hfact :
      (L / d).factorization q =
        L.factorization q - d.factorization q := by
    simpa using DFunLike.congr_fun (Nat.factorization_div hdL) q
  apply (hq.dvd_iff_one_le_factorization hquotPos.ne').2
  rw [hfact]
  omega

/-- The literal prefix lcm is positive, including the empty prefix. -/
theorem factorialGapPrefixLCM_pos (M : ℕ) : 0 < factorialGapPrefixLCM M := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro n hn
  exact (factorialGap_pos_of_mem_Icc hn).ne'

/-- The exact rational prefix is represented by the literal lcm numerator. -/
theorem factorialGapPrefix_eq_lcm_ratio (M : ℕ) :
    factorialGapPrefix M =
      (factorialGapPrefixLCMNumerator M : ℚ) / factorialGapPrefixLCM M := by
  have hL : (factorialGapPrefixLCM M : ℚ) ≠ 0 := by
    exact_mod_cast (factorialGapPrefixLCM_pos M).ne'
  unfold factorialGapPrefix factorialGapPrefixLCMNumerator
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n.factorial := Nat.factorial_pos n
  have hd : ((n.factorial - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (factorialGap_pos_of_mem_Icc hn).ne'
  rw [Nat.cast_div_charZero (factorialGap_dvd_prefixLCM hn)]
  have hcast : ((n.factorial - 1 : ℕ) : ℚ) = (n.factorial : ℚ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  rw [← hcast]
  field_simp

/-- At the maximal displayed prime exponent, the lcm cofactor is a unit
modulo the prime. -/
theorem factorialGapPrefixLCM_cofactor_not_dvd
    {q M e : ℕ} (hq : q.Prime)
    (hmax : ∀ n ∈ Finset.Icc 2 M, ¬q ^ (e + 1) ∣ n.factorial - 1)
    (hattain : ∃ n ∈ Finset.Icc 2 M, q ^ e ∣ n.factorial - 1) :
    ¬q ∣ factorialGapPrefixLCM M / q ^ e := by
  obtain ⟨n, hn, he⟩ := hattain
  have hqeL := he.trans (factorialGap_dvd_prefixLCM hn)
  have hlt : (factorialGapPrefixLCM M).factorization q < e + 1 := by
    apply finset_lcm_factorization_lt_of_all_lt (by omega)
      (fun n hn => factorialGap_pos_of_mem_Icc hn)
    intro n hn
    exact lt_of_not_ge fun hge => hmax n hn
      ((hq.pow_dvd_iff_le_factorization (factorialGap_pos_of_mem_Icc hn).ne').2 hge)
  intro hdiv
  have hsucc : q ^ (e + 1) ∣ factorialGapPrefixLCM M := by
    have hmul := Nat.mul_dvd_mul_left (q ^ e) hdiv
    rw [Nat.mul_div_cancel' hqeL] at hmul
    simpa only [pow_succ] using hmul
  have hge := (hq.pow_dvd_iff_le_factorization (factorialGapPrefixLCM_pos M).ne').1 hsucc
  omega

/-- **Prime-pole numerator formula.**  If `e` is the positive maximum
`q`-adic exponent among the displayed factorial gaps, the common-denominator
numerator modulo `q` is the LCM cofactor times the reciprocal sum of the
maximal-hit cofactors. -/
theorem factorialGapPrefixLCMNumerator_mod_prime
    {q M e : ℕ}
    (hq : q.Prime)
    (he : 1 ≤ e)
    (hmax :
      ∀ n ∈ Finset.Icc 2 M,
        ¬q ^ (e + 1) ∣ n.factorial - 1)
    (hattain :
      ∃ n ∈ Finset.Icc 2 M,
        q ^ e ∣ n.factorial - 1) :
    (factorialGapPrefixLCMNumerator M : ZMod q) =
      ((factorialGapPrefixLCM M / q ^ e : ℕ) : ZMod q) *
        factorialGapPrincipalResidue q M e := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  let L := factorialGapPrefixLCM M
  let qe := q ^ e
  let W := L / qe
  have hgapPos :
      ∀ n ∈ Finset.Icc 2 M, 0 < n.factorial - 1 := by
    intro n hn
    exact factorialGap_pos_of_mem_Icc hn
  have hLPos : 0 < L := by
    apply Nat.pos_of_ne_zero
    apply (Finset.lcm_ne_zero_iff).2
    intro n hn
    exact (hgapPos n hn).ne'
  obtain ⟨a, ha, hqea⟩ := hattain
  have haL : a.factorial - 1 ∣ L :=
    factorialGap_dvd_prefixLCM ha
  have hqeL : qe ∣ L := hqea.trans haL
  have hqePos : 0 < qe := pow_pos hq.pos e
  have hqeMulW : qe * W = L := Nat.mul_div_cancel' hqeL
  unfold factorialGapPrefixLCMNumerator factorialGapPrincipalResidue
  push_cast
  change
    (∑ n ∈ Finset.Icc 2 M,
        (L / (n.factorial - 1) : ℕ) : ZMod q) =
      (W : ZMod q) *
        ∑ n ∈ factorialGapMaxHits q M e,
          (((n.factorial - 1) / qe : ℕ) : ZMod q)⁻¹
  rw [Finset.mul_sum]
  unfold factorialGapMaxHits
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  let d := n.factorial - 1
  have hdPos : 0 < d := hgapPos n hn
  have hdL : d ∣ L := factorialGap_dvd_prefixLCM hn
  have hnotSucc : ¬q ^ (e + 1) ∣ d := hmax n hn
  change
    ((L / d : ℕ) : ZMod q) =
      if qe ∣ d ∧ ¬q ^ (e + 1) ∣ d then
        (W : ZMod q) * (((d / qe : ℕ) : ZMod q)⁻¹)
      else 0
  by_cases hqeD : qe ∣ d
  · have hUNotDvd : ¬q ∣ d / qe := by
      intro hqU
      have hmul : qe * q ∣ qe * (d / qe) :=
        Nat.mul_dvd_mul_left qe hqU
      have hqeMul : qe * (d / qe) = d := Nat.mul_div_cancel' hqeD
      apply hnotSucc
      rw [pow_succ]
      simpa [hqeMul] using hmul
    have hUNe : ((d / qe : ℕ) : ZMod q) ≠ 0 := by
      simpa [ZMod.natCast_eq_zero_iff] using hUNotDvd
    have hdivIdentity :
        (d / qe) * (L / d) = W := by
      have hleft : qe * ((d / qe) * (L / d)) = L := by
        calc
          qe * ((d / qe) * (L / d)) =
              (qe * (d / qe)) * (L / d) := by ring
          _ = d * (L / d) := by rw [Nat.mul_div_cancel' hqeD]
          _ = L := Nat.mul_div_cancel' hdL
      have hright : qe * W = L := hqeMulW
      exact Nat.eq_of_mul_eq_mul_left hqePos (hleft.trans hright.symm)
    have hdivIdentityZ :
        ((d / qe : ℕ) : ZMod q) * (L / d : ℕ) = (W : ZMod q) := by
      simpa only [Nat.cast_mul] using
        congrArg (fun x : ℕ => (x : ZMod q)) hdivIdentity
    simp [hqeD, hnotSucc]
    rw [← hdivIdentityZ]
    field_simp
  · have hdLt : d.factorization q < e := by
      exact lt_of_not_ge fun hge =>
        hqeD ((hq.pow_dvd_iff_le_factorization hdPos.ne').2 hge)
    have hqQuot : q ∣ L / d :=
      prime_dvd_div_of_factorization_lt hq hdPos hLPos hdL hqeL hdLt
    have hcastZero : ((L / d : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hqQuot
    simp [hqeD, hcastZero]


/-- The full prime power survives in the reduced denominator of the actual
rational prefix exactly when the maximal-hit inverse sum is nonzero. -/
theorem factorialGapPrefix_den_full_prime_power_iff
    {q M e : ℕ} (hq : q.Prime) (he : 1 ≤ e)
    (hmax : ∀ n ∈ Finset.Icc 2 M, ¬q ^ (e + 1) ∣ n.factorial - 1)
    (hattain : ∃ n ∈ Finset.Icc 2 M, q ^ e ∣ n.factorial - 1) :
    (factorialGapPrefix M).den.factorization q =
        (factorialGapPrefixLCM M).factorization q ↔
      factorialGapPrincipalResidue q M e ≠ 0 := by
  letI : Fact q.Prime := ⟨hq⟩
  have hqL : q ∣ factorialGapPrefixLCM M := by
    obtain ⟨n, hn, hdiv⟩ := hattain
    exact (dvd_pow_self q (by omega : e ≠ 0)).trans
      (hdiv.trans (factorialGap_dvd_prefixLCM hn))
  rw [factorialGapPrefix_eq_lcm_ratio,
    natRatio_den_factorization_eq_iff hq (factorialGapPrefixLCM_pos M) hqL]
  have hW : ((factorialGapPrefixLCM M / q ^ e : ℕ) : ZMod q) ≠ 0 := by
    intro hzero
    exact factorialGapPrefixLCM_cofactor_not_dvd hq hmax hattain
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  have hB := factorialGapPrefixLCMNumerator_mod_prime hq he hmax hattain
  rw [← ZMod.natCast_eq_zero_iff (factorialGapPrefixLCMNumerator M) q, hB]
  exact mul_ne_zero_iff.trans (and_iff_right hW)

/-- The three displayed cofactors cancel modulo 139. -/
theorem primePoleResidue_139_cancel :
    ((6 : ZMod 139)⁻¹ + (49 : ZMod 139)⁻¹ + (73 : ZMod 139)⁻¹) = 0 := by
  decide

/-- The three displayed cofactors cancel modulo 2593. -/
theorem primePoleResidue_2593_cancel :
    ((1508 : ZMod 2593)⁻¹ + (1566 : ZMod 2593)⁻¹ +
      (1678 : ZMod 2593)⁻¹) = 0 := by
  decide

end ErdosProblems.Erdos68
