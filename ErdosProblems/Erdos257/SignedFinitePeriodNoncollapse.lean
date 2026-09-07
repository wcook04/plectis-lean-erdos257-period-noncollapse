import Mathlib
import Erdos257PeriodNoncollapse.CertificateKernel

/-!
# Signed finite-period noncollapse and cyclotomic exact-order lifts

Type B r4, ordinary arithmetic now Lean-checked in this contained module.

* If `ℓ ∣ Φ_n(b)` then `ord_{ℓ^e}(b) = n` for `e = v_ℓ(b^n-1)`.
* Unit-coefficient signed sums `∑_{n∈F} ε_n/(b^n-1)` have reduced denominator
  `D` satisfying `ord_D(b) = lcm(F)`.
* The SupportWordStructureLab claim that a non-Mersenne prime cannot be a
  finite Mersenne denominator is false: `1/3 + 1/15 = 2/5`.

This does not close universal #257 or the rational targets `1/2`, `1/21`.
The unsigned theorem `finite_period_noncollapse_rat_den` remains the
existing flagship finite-period statement.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse
open Polynomial

/-! ## Finite counterexample to the non-Mersenne prime-denominator claim -/

theorem one_div_three_add_one_div_fifteen_eq_two_div_five :
    (1 : ℚ) / ((2 : ℚ) ^ 2 - 1) + 1 / ((2 : ℚ) ^ 4 - 1) = 2 / 5 := by
  norm_num

theorem two_div_five_den :
    ((1 : ℚ) / ((2 : ℚ) ^ 2 - 1) + 1 / ((2 : ℚ) ^ 4 - 1)).den = 5 := by
  norm_num

theorem not_two_pow_eq_six (e : ℕ) : 2 ^ e ≠ 6 := by
  match e with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | n + 3 =>
    have h8 : 8 ≤ 2 ^ (n + 3) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left 3 n)
    omega

/-- `5` is a non-Mersenne prime which is nevertheless the reduced denominator
of the finite Mersenne sum `1/3 + 1/15`. -/
theorem five_is_nonMersenne_finite_mersenne_denominator :
    ((1 : ℚ) / ((2 : ℚ) ^ 2 - 1) + 1 / ((2 : ℚ) ^ 4 - 1)).den = 5 ∧
      Nat.Prime 5 ∧ ¬ ∃ e : ℕ, 5 + 1 = 2 ^ e := by
  refine ⟨two_div_five_den, Nat.prime_five, ?_⟩
  rintro ⟨e, he⟩
  exact not_two_pow_eq_six e (by omega)

/-- Arbitrary integer coefficients need not preserve the period: the lcm is
`2` but the reduced denominator is `1`. -/
theorem one_plus_three_over_three_eq_two :
    (1 : ℚ) / ((2 : ℚ) ^ 1 - 1) + 3 / ((2 : ℚ) ^ 2 - 1) = 2 := by
  norm_num

theorem one_plus_three_over_three_den :
    ((1 : ℚ) / ((2 : ℚ) ^ 1 - 1) + 3 / ((2 : ℚ) ^ 2 - 1)).den = 1 := by
  norm_num

/-! ## Cyclotomic primes carry the full exact-order prime-power witness -/

theorem coprime_base_pow_sub_one {b n : ℕ} (hb : 2 ≤ b) (hn : n ≠ 0) :
    Nat.Coprime b (b ^ n - 1) := by
  have h1 : 1 ≤ b ^ n := Nat.one_le_pow n b (by omega)
  have hsub : b ^ n - (b ^ n - 1) = 1 := by omega
  have hgcd_dvd_pow : Nat.gcd b (b ^ n - 1) ∣ b ^ n :=
    (Nat.gcd_dvd_left _ _).trans (dvd_pow_self b hn)
  have hgcd_dvd_one : Nat.gcd b (b ^ n - 1) ∣ 1 := by
    simpa [hsub] using Nat.dvd_sub hgcd_dvd_pow (Nat.gcd_dvd_right _ _)
  exact Nat.dvd_one.mp hgcd_dvd_one

/-- If `ord_q(b) = n` for an odd prime `q`, the full cyclotomic valuation
`e = v_q(b^n-1)` is still an exact-order exponent. -/
theorem exactOrderPrimePowerWitness_of_order_full_val
    {b n q : ℕ}
    (hq : Nat.Prime q) (hq_odd : Odd q) (hb : 2 ≤ b)
    (hcop : Nat.Coprime b q)
    (hord : orderOf (ZMod.unitOfCoprime b hcop) = n)
    (hn : 0 < n) :
    ExactOrderPrimePowerWitness b n q ((b ^ n - 1).factorization q) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hchar : ∀ k : ℕ, q ∣ b ^ k - 1 ↔ n ∣ k := by
    intro k
    rw [← hord]
    exact (orderOf_dvd_iff_q_dvd_pow_sub_one hcop
      (Nat.one_le_pow k b (by omega))).symm
  have hLTE : ∀ t : ℕ, t ≠ 0 →
      (b ^ (n * t) - 1).factorization q
        = (b ^ n - 1).factorization q + t.factorization q := by
    intro t ht
    exact odd_prime_order_factorization_pow_sub_one hq hq_odd hcop hord.symm
      (Nat.one_lt_pow hn.ne' (by omega)) ht
  have hepos : 0 < (b ^ n - 1).factorization q := by
    have hdvd : q ∣ b ^ n - 1 := (hchar n).mpr dvd_rfl
    have hbn0 : b ^ n - 1 ≠ 0 :=
      (pow_sub_one_pos_of_ne_zero b n hb hn.ne').ne'
    exact hq.factorization_pos_of_dvd hbn0 hdvd
  refine ⟨hq, hepos, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp
  · have hbk_pos : 0 < b ^ k - 1 := pow_sub_one_pos_of_ne_zero b k hb hk_pos.ne'
    constructor
    · intro hdvd
      have hq_dvd : q ∣ b ^ k - 1 :=
        dvd_trans (dvd_pow_self q hepos.ne') hdvd
      exact (hchar k).mp hq_dvd
    · intro hdvd
      obtain ⟨t, rfl⟩ := hdvd
      have ht : t ≠ 0 := by
        rintro rfl
        simp at hk_pos
      have hval := hLTE t ht
      refine (hq.pow_dvd_iff_le_factorization hbk_pos.ne').mpr ?_
      rw [hval]
      exact Nat.le_add_right _ _

theorem cyclotomic_eval_dvd_pow_sub_one {n : ℕ} (_hn : 0 < n) (b : ℤ) :
    (cyclotomic n ℤ).eval b ∣ (b ^ n - 1) := by
  have hdiv : cyclotomic n ℤ ∣ X ^ n - 1 :=
    cyclotomic.dvd_X_pow_sub_one n ℤ
  simpa [eval_pow, eval_X, eval_one, eval_sub] using eval_dvd hdiv

/-- Type B A.1: a prime divisor of `Φ_n(b)` lifts to an exact-order prime
power `ℓ^e` with `e = v_ℓ(b^n-1)`. -/
theorem cyclotomic_prime_dvd_imp_exactOrder_full_val
    {b n q : ℕ} (hb : 2 ≤ b) (hn : 2 ≤ n) (hq : Nat.Prime q)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (b : ℤ)) :
    ExactOrderPrimePowerWitness b n q ((b ^ n - 1).factorization q) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hroot : (cyclotomic n (ZMod q)).IsRoot ((b : ℕ) : ZMod q) := by
    have hcast :
        (((cyclotomic n ℤ).eval ((b : ℕ) : ℤ) : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
    have hcomm : (cyclotomic n (ZMod q)).eval (((b : ℕ) : ℤ) : ZMod q)
        = (((cyclotomic n ℤ).eval ((b : ℕ) : ℤ) : ℤ) : ZMod q) := by
      rw [← map_cyclotomic_int n (ZMod q), eval_map]
      exact eval₂_at_apply (Int.castRingHom (ZMod q)) _
    have hbcast : (((b : ℕ) : ℤ) : ZMod q) = ((b : ℕ) : ZMod q) := by
      push_cast
      rfl
    show (cyclotomic n (ZMod q)).eval ((b : ℕ) : ZMod q) = 0
    rw [← hbcast, hcomm, hcast]
  obtain ⟨a, ha_eq⟩ :=
    orderOf_isRoot_cyclotomic_zmod_pow_mul hq n (by omega) _ hroot
  have hqb : ¬ q ∣ b := by
    intro hqb
    have hx0 : ((b : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff b q).mpr hqb
    have h1 : (cyclotomic n (ZMod q)).coeff 0 = 1 :=
      cyclotomic_coeff_zero (ZMod q) (by omega)
    have h0 : (cyclotomic n (ZMod q)).coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero]
      have hroot0 := hroot
      rw [IsRoot, hx0] at hroot0
      exact hroot0
    rw [h1] at h0
    exact one_ne_zero h0
  have hcop : Nat.Coprime b q := (hq.coprime_iff_not_dvd.mpr hqb).symm
  have hord_eq : orderOf (ZMod.unitOfCoprime b hcop)
      = orderOf ((b : ℕ) : ZMod q) := by
    conv_rhs => rw [← ZMod.coe_unitOfCoprime b hcop]
    exact orderOf_units.symm
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · have hn_eq : n = orderOf ((b : ℕ) : ZMod q) := by simpa using ha_eq
    have hq2 : q ≠ 2 := by
      intro hq2
      subst hq2
      have hb_odd : Odd b := by
        rcases Nat.even_or_odd b with he | ho
        · exact absurd he.two_dvd hqb
        · exact ho
      have hm1 : orderOf ((b : ℕ) : ZMod 2) = 1 := by
        have h2b1 : (2 : ℕ) ∣ b ^ 1 - 1 := by
          rcases hb_odd with ⟨j, hj⟩
          simp only [pow_one]
          exact ⟨j, by omega⟩
        have hdvd1 : orderOf (ZMod.unitOfCoprime b hcop) ∣ 1 :=
          (orderOf_dvd_iff_q_dvd_pow_sub_one hcop
            (Nat.one_le_pow 1 b (by omega))).mpr h2b1
        have h1 := Nat.dvd_one.mp hdvd1
        rw [hord_eq] at h1
        exact h1
      have : n = 1 := by rw [hn_eq, hm1]
      omega
    have hq_odd : Odd q := hq.odd_of_ne_two hq2
    have hord : orderOf (ZMod.unitOfCoprime b hcop) = n := by
      rw [hord_eq, ← hn_eq]
    exact exactOrderPrimePowerWitness_of_order_full_val hq hq_odd hb hcop hord
      (by omega)
  · by_cases hq2 : q = 2
    · subst hq2
      have hb_odd : Odd b := by
        rcases Nat.even_or_odd b with he | ho
        · exact absurd he.two_dvd hqb
        · exact ho
      have hm1 : orderOf ((b : ℕ) : ZMod 2) = 1 := by
        have h2b1 : (2 : ℕ) ∣ b ^ 1 - 1 := by
          rcases hb_odd with ⟨j, hj⟩
          simp only [pow_one]
          exact ⟨j, by omega⟩
        have hdvd1 : orderOf (ZMod.unitOfCoprime b hcop) ∣ 1 :=
          (orderOf_dvd_iff_q_dvd_pow_sub_one hcop
            (Nat.one_le_pow 1 b (by omega))).mpr h2b1
        have h1 := Nat.dvd_one.mp hdvd1
        rw [hord_eq] at h1
        exact h1
      have hn_eq : n = 2 ^ a := by
        rw [ha_eq, hm1, mul_one]
      have hw := exactOrderPrimePowerWitness_lift_two (b := b) (a := a) hb hb_odd ha_pos
      have hn_even : Even n := by
        rw [hn_eq, even_iff_two_dvd]
        exact dvd_pow_self 2 ha_pos.ne'
      have hval := two_adic_pow_sub_one_factorization_even
        (show 1 < b by omega) hb_odd (by omega : n ≠ 0) hn_even
      have hpow : n.factorization 2 = a := by
        rw [hn_eq, Nat.prime_two.factorization_pow]
        simp
      have hs : (b - 1).factorization 2 + (b + 1).factorization 2 + (a - 1)
          = (b ^ n - 1).factorization 2 := by
        have hsum : (b ^ n - 1).factorization 2 + 1
            = (b + 1).factorization 2 + (b - 1).factorization 2 + a := by
          rw [hval, hpow]
        omega
      rw [← hs, hn_eq]
      exact hw
    · have hq_odd : Odd q := hq.odd_of_ne_two hq2
      have hw := exactOrderPrimePowerWitness_lift_odd hq hq_odd hb hcop
        hord_eq.symm ha_pos
      have hn_eq : n = q ^ a * orderOf (ZMod.unitOfCoprime b hcop) := by
        rw [ha_eq, hord_eq]
      have hm : orderOf (ZMod.unitOfCoprime b hcop) ≠ 0 :=
        (orderOf_pos (ZMod.unitOfCoprime b hcop)).ne'
      have hmul : n = orderOf (ZMod.unitOfCoprime b hcop) * q ^ a := by
        rw [hn_eq, mul_comm]
      have hLTE := odd_prime_order_factorization_pow_sub_one hq hq_odd hcop
        rfl (Nat.one_lt_pow hm (by omega)) (pow_ne_zero a hq.pos.ne')
      rw [← hmul] at hLTE
      have hpow : (q ^ a).factorization q = a := by
        rw [hq.factorization_pow]
        simp
      have hs : (b ^ (orderOf (ZMod.unitOfCoprime b hcop)) - 1).factorization q + a
          = (b ^ n - 1).factorization q := by
        rw [hLTE, hpow]
      have hw' :
          ExactOrderPrimePowerWitness b
            (q ^ a * orderOf (ZMod.unitOfCoprime b hcop)) q
            ((b ^ orderOf (ZMod.unitOfCoprime b hcop) - 1).factorization q + a) := by
        simpa [hord_eq] using hw
      rw [← hs, hn_eq]
      exact hw'

theorem exactOrder_two_mod_nine :
    ExactOrderPrimePowerWitness 2 6 3 2 :=
  exactOrderPrimePowerWitness_of_orderOf
    (by decide) (by decide) (by decide) (by decide)
    (orderOf_two_unit_mod_nine_eq_six (by decide))

/-! ## Unique minimal valuation of a finite rational sum -/

lemma padicValRat_lt_sum_of_forall_lt
    {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (f : ℕ → ℚ) (v : ℤ)
    (hsum : ∑ i ∈ s, f i ≠ 0)
    (h : ∀ i ∈ s, v < padicValRat p (f i)) :
    v < padicValRat p (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp at hsum
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hsum ⊢
    by_cases hs0 : ∑ i ∈ s, f i = 0
    · simpa [hs0] using h a (Finset.mem_insert_self _ _)
    · refine lt_of_lt_of_le (lt_min ?_ ?_) (padicValRat.min_le_padicValRat_add (p := p) hsum)
      · exact h a (Finset.mem_insert_self _ _)
      · exact ih hs0 (fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma padicValRat_sum_eq_of_unique_min
    {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (f : ℕ → ℚ) {i0 : ℕ}
    (hi0 : i0 ∈ s)
    (hf0 : ∀ i ∈ s, f i ≠ 0)
    (hmin : ∀ i ∈ s, i ≠ i0 → padicValRat p (f i0) < padicValRat p (f i)) :
    padicValRat p (∑ i ∈ s, f i) = padicValRat p (f i0) := by
  classical
  rw [← Finset.sum_erase_add s f hi0]
  by_cases hrest : ∑ i ∈ s.erase i0, f i = 0
  · simp [hrest]
  · have hlt : padicValRat p (f i0)
        < padicValRat p (∑ i ∈ s.erase i0, f i) :=
      padicValRat_lt_sum_of_forall_lt (s.erase i0) f (padicValRat p (f i0)) hrest
        (fun i hi =>
          hmin i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
    have hsumne : ∑ i ∈ s.erase i0, f i + f i0 ≠ 0 := by
      intro hz
      have : ∑ i ∈ s.erase i0, f i = -f i0 := eq_neg_of_add_eq_zero_left hz
      have hval : padicValRat p (∑ i ∈ s.erase i0, f i)
          = padicValRat p (f i0) := by
        rw [this, padicValRat.neg]
      exact lt_irrefl _ (hval ▸ hlt)
    rw [add_comm]
    exact padicValRat.add_eq_of_lt (p := p) (by rwa [add_comm]) (hf0 i0 hi0) hrest hlt

lemma padicValRat_signed_atom
    {b n q : ℕ} [Fact q.Prime] (hb : 2 ≤ b) (hn : n ≠ 0)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    padicValRat q ((ε : ℚ) / ((b : ℚ) ^ n - 1))
      = - (padicValNat q (b ^ n - 1) : ℤ) := by
  have hden_ne : (b : ℚ) ^ n - 1 ≠ 0 := by
    have : (1 : ℚ) < (b : ℚ) ^ n := by
      have hbn : 1 < b ^ n := Nat.one_lt_pow hn (by omega)
      exact_mod_cast hbn
    linarith
  have hε0 : (ε : ℚ) ≠ 0 := by
    rcases hε with h | h <;> simp [h]
  have hεval : padicValRat q (ε : ℚ) = 0 := by
    rcases hε with h | h
    · simp [h, padicValRat.one]
    · simp [h, padicValRat.neg, padicValRat.one]
  rw [padicValRat.div hε0 hden_ne, hεval, zero_sub]
  have hcast : (b : ℚ) ^ n - 1 = ((b ^ n - 1 : ℕ) : ℚ) :=
    (natCast_pow_sub_one b n hb).symm
  rw [hcast, padicValRat.of_nat]

lemma padicValNat_den_eq_of_neg_val
    {p : ℕ} [hp : Fact p.Prime] {x : ℚ} (h : padicValRat p x < 0) :
    padicValNat p x.den = (-padicValRat p x).toNat := by
  have hx0 : x ≠ 0 := fun hx => by
    subst hx
    simp [padicValRat.zero] at h
  have hform := padicValRat_def p x
  have hdenpos : 0 < padicValNat p x.den := by
    have : (padicValInt p x.num : ℤ) - (padicValNat p x.den : ℤ) < 0 := by
      rwa [← hform]
    have hnum_nn : (0 : ℤ) ≤ padicValInt p x.num := Int.natCast_nonneg _
    omega
  have hpden : p ∣ x.den :=
    dvd_of_one_le_padicValNat (p := p) (Nat.succ_le_iff.mpr hdenpos)
  have hnot_num : ¬ p ∣ x.num.natAbs := by
    have hcop : Nat.Coprime x.num.natAbs x.den := x.reduced
    have hcp : Nat.Coprime x.num.natAbs p := hcop.coprime_dvd_right hpden
    exact hp.out.coprime_iff_not_dvd.mp hcp.symm
  have hnum0 : padicValInt p x.num = 0 := by
    simp [padicValInt, padicValNat.eq_zero_of_not_dvd hnot_num]
  have hval : padicValRat p x = - (padicValNat p x.den : ℤ) := by
    rw [hform, hnum0, Nat.cast_zero, zero_sub]
  rw [hval, neg_neg, Int.toNat_natCast]

/-! ## Signed finite-period noncollapse -/

noncomputable def signedFiniteErdosSum (F : Finset ℕ) (ε : ℕ → ℤ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, (ε n : ℚ) / ((b : ℚ) ^ n - 1)

lemma signed_atom_ne_zero
    {b n : ℕ} {ε : ℤ} (hb : 2 ≤ b) (hn : n ≠ 0) (hε : ε = 1 ∨ ε = -1) :
    (ε : ℚ) / ((b : ℚ) ^ n - 1) ≠ 0 := by
  have hden_ne : (b : ℚ) ^ n - 1 ≠ 0 := by
    have hbn : 1 < b ^ n := Nat.one_lt_pow hn (by omega)
    have : (1 : ℚ) < (b : ℚ) ^ n := by exact_mod_cast hbn
    linarith
  rcases hε with h | h <;> simp [h, hden_ne]

lemma den_one_div_pow_sub_one
    {b n : ℕ} (hb : 2 ≤ b) (hn : n ≠ 0) :
    ((1 : ℚ) / ((b : ℚ) ^ n - 1)).den = b ^ n - 1 := by
  have hpos : 0 < b ^ n - 1 := pow_sub_one_pos_of_ne_zero b n hb hn
  rw [← natCast_pow_sub_one b n hb]
  exact den_natCast_div_natCast_of_coprime 1 (b ^ n - 1) hpos.ne'
    (Nat.coprime_one_left _)

lemma den_signed_atom
    {b n : ℕ} {ε : ℤ} (hb : 2 ≤ b) (hn : n ≠ 0) (hε : ε = 1 ∨ ε = -1) :
    ((ε : ℚ) / ((b : ℚ) ^ n - 1)).den = b ^ n - 1 := by
  rcases hε with h | h
  · rw [h, Int.cast_one]
    exact den_one_div_pow_sub_one hb hn
  · rw [h, Int.cast_neg, Int.cast_one, neg_div, Rat.neg_den]
    exact den_one_div_pow_sub_one hb hn

lemma den_sum_dvd_finset_lcm
    (s : Finset ℕ) (f : ℕ → ℚ) :
    (∑ i ∈ s, f i).den ∣ s.lcm (fun i => (f i).den) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.lcm_insert]
    refine (Rat.add_den_dvd_lcm (f a) (∑ i ∈ s, f i)).trans ?_
    exact (Nat.lcm_dvd_iff.mpr ⟨Nat.dvd_lcm_left _ _,
      ih.trans (Nat.dvd_lcm_right _ _)⟩)

lemma signedFiniteErdosSum_den_dvd_pow_sub_one
    (F : Finset ℕ) (ε : ℕ → ℤ) (b : ℕ)
    (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hε : ∀ n ∈ F, ε n = 1 ∨ ε n = -1) :
    (signedFiniteErdosSum F ε b).den ∣ b ^ F.lcm id - 1 := by
  let f : ℕ → ℚ := fun n => (ε n : ℚ) / ((b : ℚ) ^ n - 1)
  have hden : (signedFiniteErdosSum F ε b).den ∣ F.lcm (fun n => (f n).den) := by
    simpa [signedFiniteErdosSum, f] using den_sum_dvd_finset_lcm F f
  have hlcm : F.lcm (fun n => (f n).den) ∣ b ^ F.lcm id - 1 := by
    refine Finset.lcm_dvd ?_
    intro n hn
    have hn0 : n ≠ 0 := fun h => h0 (h ▸ hn)
    have hatom : (f n).den = b ^ n - 1 := den_signed_atom hb hn0 (hε n hn)
    rw [hatom]
    exact Nat.pow_sub_one_dvd_pow_sub_one b (by simpa using Finset.dvd_lcm hn)
  exact hden.trans hlcm

lemma coprime_base_signedFiniteErdosSum
    (F : Finset ℕ) (ε : ℕ → ℤ) (b : ℕ)
    (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hε : ∀ n ∈ F, ε n = 1 ∨ ε n = -1) :
    Nat.Coprime b (signedFiniteErdosSum F ε b).den :=
  (coprime_base_pow_sub_one hb (lcm_ne_zero_of_zero_not_mem F h0)).coprime_dvd_right
    (signedFiniteErdosSum_den_dvd_pow_sub_one F ε b h0 hb hε)

lemma exists_divisibility_maximal_above
    (F : Finset ℕ) (h0 : 0 ∉ F) {m : ℕ} (hm : m ∈ F) :
    ∃ n ∈ F, m ∣ n ∧ ∀ k ∈ F, n ∣ k → k = n := by
  classical
  let S := F.filter (fun k => m ∣ k)
  have hS : S.Nonempty := ⟨m, Finset.mem_filter.mpr ⟨hm, dvd_rfl⟩⟩
  refine ⟨S.max' hS, (Finset.mem_filter.mp (S.max'_mem hS)).1,
    (Finset.mem_filter.mp (S.max'_mem hS)).2, ?_⟩
  intro k hkF hdvd
  have hk0 : k ≠ 0 := fun h => h0 (h ▸ hkF)
  have hkS : k ∈ S :=
    Finset.mem_filter.mpr ⟨hkF,
      dvd_trans (Finset.mem_filter.mp (S.max'_mem hS)).2 hdvd⟩
  exact le_antisymm (S.le_max' k hkS) (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd)

lemma signed_maximal_row_den_val
    {F : Finset ℕ} {ε : ℕ → ℤ} {b n q s : ℕ}
    (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hε : ∀ k ∈ F, ε k = 1 ∨ ε k = -1)
    (hnF : n ∈ F) (hn0 : n ≠ 0)
    (hmax : ∀ k ∈ F, n ∣ k → k = n)
    (hwit : ExactOrderPrimePowerWitness b n q s) :
    padicValRat q (signedFiniteErdosSum F ε b)
      = -((b ^ n - 1).factorization q : ℤ) ∧
    padicValNat q (signedFiniteErdosSum F ε b).den
      = (b ^ n - 1).factorization q ∧
    signedFiniteErdosSum F ε b ≠ 0 ∧
    q ^ s ∣ (signedFiniteErdosSum F ε b).den := by
  obtain ⟨hq, hs, hprofile⟩ := hwit
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  let S := signedFiniteErdosSum F ε b
  let f : ℕ → ℚ := fun k => (ε k : ℚ) / ((b : ℚ) ^ k - 1)
  have hf0 : ∀ k ∈ F, f k ≠ 0 := fun k hk =>
    signed_atom_ne_zero hb (fun h => h0 (h ▸ hk)) (hε k hk)
  have hbn0 : b ^ n - 1 ≠ 0 := (pow_sub_one_pos_of_ne_zero b n hb hn0).ne'
  have hs_le : s ≤ (b ^ n - 1).factorization q :=
    (hq.pow_dvd_iff_le_factorization hbn0).mp ((hprofile n).mpr dvd_rfl)
  have hmin : ∀ k ∈ F, k ≠ n → padicValRat q (f n) < padicValRat q (f k) := by
    intro k hkF hne
    have hk0 : k ≠ 0 := fun h => h0 (h ▸ hkF)
    have hother : (b ^ k - 1).factorization q < s := by
      by_contra hge
      have hge := Nat.le_of_not_lt hge
      have hdvd : q ^ s ∣ b ^ k - 1 :=
        (hq.pow_dvd_iff_le_factorization
          (pow_sub_one_pos_of_ne_zero b k hb hk0).ne').mpr hge
      exact hne (hmax k hkF ((hprofile k).mp hdvd))
    have hnval := padicValRat_signed_atom (q := q) hb hn0 (hε n hnF)
    have hkval := padicValRat_signed_atom (q := q) hb hk0 (hε k hkF)
    have hltN : ((b ^ k - 1).factorization q : ℤ)
        < ((b ^ n - 1).factorization q : ℤ) := by
      have : (b ^ k - 1).factorization q < (b ^ n - 1).factorization q :=
        lt_of_lt_of_le hother hs_le
      exact_mod_cast this
    simp only [f]
    rw [hnval, hkval, ← Nat.factorization_def (b ^ n - 1) hq,
      ← Nat.factorization_def (b ^ k - 1) hq]
    linarith
  have hSval : padicValRat q S = padicValRat q (f n) := by
    simpa [S, signedFiniteErdosSum, f] using
      padicValRat_sum_eq_of_unique_min F f hnF hf0 hmin
  have hnatom := padicValRat_signed_atom (q := q) hb hn0 (hε n hnF)
  have hnatom' : padicValRat q (f n) = -((b ^ n - 1).factorization q : ℤ) := by
    simp only [f]
    rw [hnatom, Nat.factorization_def (b ^ n - 1) hq]
  have hneg : padicValRat q S < 0 := by
    rw [hSval, hnatom']
    have : 0 < (b ^ n - 1).factorization q := lt_of_lt_of_le hs hs_le
    exact neg_lt_zero.mpr (by exact_mod_cast this)
  have hSne : S ≠ 0 := by
    intro h0S
    have hz : padicValRat q S = 0 := by simp [h0S]
    rw [hSval, hnatom'] at hz
    have hpos : 0 < (b ^ n - 1).factorization q := lt_of_lt_of_le hs hs_le
    have hlt : (-((b ^ n - 1).factorization q : ℤ)) < 0 :=
      neg_lt_zero.mpr (by exact_mod_cast hpos)
    rw [hz] at hlt
    exact lt_irrefl _ hlt
  have hden : padicValNat q S.den = (b ^ n - 1).factorization q := by
    have h := padicValNat_den_eq_of_neg_val (p := q) (x := S) hneg
    rw [h, hSval, hnatom', neg_neg, Int.toNat_natCast]
  have hpow : q ^ s ∣ S.den := by
    refine (hq.pow_dvd_iff_le_factorization S.den_pos.ne').mpr ?_
    rw [Nat.factorization_def S.den hq, hden]
    exact hs_le
  exact ⟨by simpa [S] using (hSval.trans hnatom'), by simpa [S] using hden,
    by simpa [S] using hSne, by simpa [S] using hpow⟩

/-- Type B A.2: unit-coefficient signed finite-period noncollapse. -/
theorem signed_finite_period_noncollapse
    (F : Finset ℕ) (ε : ℕ → ℤ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hε : ∀ n ∈ F, ε n = 1 ∨ ε n = -1) :
    signedFiniteErdosSum F ε b ≠ 0 ∧
      orderOf (ZMod.unitOfCoprime b
        (coprime_base_signedFiniteErdosSum F ε b h0 hb hε))
        = F.lcm id := by
  classical
  let S := signedFiniteErdosSum F ε b
  have hcop := coprime_base_signedFiniteErdosSum F ε b h0 hb hε
  have hden_dvd := signedFiniteErdosSum_den_dvd_pow_sub_one F ε b h0 hb hε
  have hL0 : F.lcm id ≠ 0 := lcm_ne_zero_of_zero_not_mem F h0
  have hpow1 : 1 ≤ b ^ F.lcm id := Nat.one_le_pow (F.lcm id) b (by omega)
  have hord_dvd_L :
      orderOf (ZMod.unitOfCoprime b hcop) ∣ F.lcm id :=
    (orderOf_dvd_iff_q_dvd_pow_sub_one hcop hpow1).mpr hden_dvd
  have hord_pos : 0 < orderOf (ZMod.unitOfCoprime b hcop) :=
    orderOf_pos (ZMod.unitOfCoprime b hcop)
  have hpow_ord : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop) :=
    Nat.one_le_pow _ b (Nat.succ_le_iff.mp (Nat.le_trans (by decide : 1 ≤ 2) hb))
  have hD_dvd_ord :
      S.den ∣ b ^ orderOf (ZMod.unitOfCoprime b hcop) - 1 :=
    (orderOf_dvd_iff_q_dvd_pow_sub_one hcop hpow_ord).mp dvd_rfl
  have hL_dvd_ord : F.lcm id ∣ orderOf (ZMod.unitOfCoprime b hcop) := by
    refine Finset.lcm_dvd ?_
    intro m hmF
    obtain ⟨n, hnF, hmn, hmax⟩ := exists_divisibility_maximal_above F h0 hmF
    have hn0 : n ≠ 0 := fun h => h0 (h ▸ hnF)
    by_cases hn1 : n = 1
    · subst hn1
      have hm1 : m = 1 := Nat.eq_one_of_dvd_one (by simpa using hmn)
      simpa [hm1] using
        (one_dvd (orderOf (ZMod.unitOfCoprime b hcop)) : 1 ∣ _)
    · have hn2 : 2 ≤ n := n.two_le_iff.mpr ⟨hn0, hn1⟩
      obtain ⟨q, s, hwit⟩ := exists_exactOrderPrimePowerWitness (b := b) (n := n) hb hn2
      have H := signed_maximal_row_den_val h0 hb hε hnF hn0 hmax hwit
      have hqsdvd : q ^ s ∣ b ^ orderOf (ZMod.unitOfCoprime b hcop) - 1 :=
        H.2.2.2.trans (by simpa [S] using hD_dvd_ord)
      have hn_dvd : n ∣ orderOf (ZMod.unitOfCoprime b hcop) :=
        (hwit.2.2 (orderOf (ZMod.unitOfCoprime b hcop))).mp hqsdvd
      exact dvd_trans hmn hn_dvd
  have hSne : S ≠ 0 := by
    obtain ⟨m, hmF⟩ := hF
    obtain ⟨n, hnF, _, hmax⟩ := exists_divisibility_maximal_above F h0 hmF
    by_cases hn1 : n = 1
    · subst hn1
      have hF1 : F = {1} := by
        ext k
        constructor
        · intro hk
          simp [hmax k hk (one_dvd k)]
        · intro hk
          simp only [Finset.mem_singleton] at hk
          subst hk
          exact hnF
      subst hF1
      simp only [S, signedFiniteErdosSum, Finset.sum_singleton]
      exact signed_atom_ne_zero hb (by decide) (hε 1 (by simp))
    · have hn0 : n ≠ 0 := fun h => h0 (h ▸ hnF)
      have hn2 : 2 ≤ n := n.two_le_iff.mpr ⟨hn0, hn1⟩
      obtain ⟨q, s, hwit⟩ := exists_exactOrderPrimePowerWitness (b := b) (n := n) hb hn2
      exact (signed_maximal_row_den_val h0 hb hε hnF hn0 hmax hwit).2.2.1
  refine ⟨hSne, ?_⟩
  exact dvd_antisymm hord_dvd_L hL_dvd_ord

/-- Type B A.7 for one cyclotomic prime on a divisibility-maximal row. -/
theorem signed_divisibility_maximal_cyclotomic_den_val
    (F : Finset ℕ) (ε : ℕ → ℤ) (b n q : ℕ)
    (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hε : ∀ k ∈ F, ε k = 1 ∨ ε k = -1)
    (hnF : n ∈ F) (hn2 : 2 ≤ n)
    (hmax : ∀ k ∈ F, n ∣ k → k = n)
    (hq : Nat.Prime q)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (b : ℤ)) :
    padicValNat q (signedFiniteErdosSum F ε b).den
      = (b ^ n - 1).factorization q := by
  have hn0 : n ≠ 0 := by omega
  have hwit := cyclotomic_prime_dvd_imp_exactOrder_full_val hb hn2 hq hdvd
  exact (signed_maximal_row_den_val h0 hb hε hnF hn0 hmax hwit).2.1

theorem lcm_lt_den_signedFiniteErdosSum
    (F : Finset ℕ) (ε : ℕ → ℤ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hε : ∀ n ∈ F, ε n = 1 ∨ ε n = -1)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (signedFiniteErdosSum F ε b).den := by
  have hmain := signed_finite_period_noncollapse F ε b hF h0 hb hε
  have hord :
      orderOf (ZMod.unitOfCoprime b
        (coprime_base_signedFiniteErdosSum F ε b h0 hb hε))
        = F.lcm id := hmain.2
  have hQ_pos : 0 < (signedFiniteErdosSum F ε b).den := Rat.den_pos _
  haveI : NeZero (signedFiniteErdosSum F ε b).den := ⟨hQ_pos.ne'⟩
  have hdvd :
      orderOf (ZMod.unitOfCoprime b
        (coprime_base_signedFiniteErdosSum F ε b h0 hb hε))
        ∣ Fintype.card (ZMod (signedFiniteErdosSum F ε b).den)ˣ :=
    orderOf_dvd_card
  rw [ZMod.card_units_eq_totient, hord] at hdvd
  have hle : F.lcm id ≤ ((signedFiniteErdosSum F ε b).den).totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr hQ_pos) hdvd
  have hQ1 : 1 < (signedFiniteErdosSum F ε b).den := by
    rcases Nat.lt_or_ge 1 (signedFiniteErdosSum F ε b).den with h | h
    · exact h
    · have hQ_eq : (signedFiniteErdosSum F ε b).den = 1 := by omega
      rw [hQ_eq, Nat.totient_one] at hle
      omega
  exact lt_of_le_of_lt hle (Nat.totient_lt _ hQ1)

end ErdosProblems.Erdos257
