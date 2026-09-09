import ErdosProblems.Erdos251.OrderLatticeDiagonal

/-!
# Erdős #251: the free-pair reduction

`FreePairStateCompressionLab.md` §1 states the free-pair property (F): under
rationality, once the dyadic part of the denominator has been shifted out,
`T_M - T_N ∈ ℤ` for **every** pair `M ≡ N (mod t)`, with `t` the multiplicative
order of `2` modulo the odd denominator, not only for a fixed offset `h`.
§2 then states the sharpened producer

> **(P)** for every `t ≥ 1` and every cutoff there are `M ≡ N (mod t)` beyond
> the cutoff with `T_M - T_N` not an integer,

and asserts that (P) is equivalent to irrationality.  The pieces were on disk
(`tailShift_integral_iff_orderOf_dvd`, `exists_odd_den_state`,
`tail_den_succ_eq_of_odd`); the named corollary and the equivalence were not.

This module lands both.

* `free_pair_integral_iff_modEq`: at and beyond an odd-denominator state,
  `T_M - T_N ∈ ℤ ↔ N ≡ M [MOD orderOf (2 : ZMod d)]`.  This is (F) with its
  converse, so the integral pairs are exactly one congruence lattice.
* `exists_free_pair_lattice`: every rational-valued orbit has such a cutoff
  and a positive modulus.
* `irrational_initial_iff_cofinalFreePairNonintegral`: for every real
  integer-digit dyadic tail orbit, `Irrational (T 0) ↔ (P)`.
* `irrational_primeGap_tsum_iff_cofinalFreePairNonintegral`: the same for the
  actual prime-gap series, with its real tail orbit `primeGapRealTail`.

The reading proved: "fractional part bounded away from `0`" in the lab's
wording of (P) is taken as nonintegrality of the pair difference.  That is the
weakest hypothesis in the direction (P) ⇒ irrational, and in the direction
irrational ⇒ (P) no uniform bound can be extracted, so the nonintegral form
is the exact equivalence the existing lemmas support.

Erdős #251 remains open: producing the misses in (P) is the missing input.
-/

namespace ErdosProblems.Erdos251

/-! ## Denominator stability past the odd state -/

/-- Once a tail state has odd reduced denominator, every later state has the
same reduced denominator. -/
theorem tail_den_eq_of_odd_of_le {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den) :
    ∀ k : ℕ, (T (N₀ + k)).den = (T N₀).den
  | 0 => rfl
  | k + 1 => by
      have ih := tail_den_eq_of_odd_of_le hrec hodd k
      rw [← Nat.add_assoc, tail_den_succ_eq_of_odd hrec (N₀ + k) (by rw [ih]; exact hodd), ih]

/-- The order of `2` modulo an odd tail denominator is positive: the Euler
shift is integral, so the order divides the positive totient. -/
theorem orderOf_two_zmod_den_pos {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ) (hodd : Odd (T N).den) :
    0 < orderOf (2 : ZMod (T N).den) := by
  have hInt := tailShift_integral_totient_of_odd_den hrec N hodd
  rw [tailShift_integral_iff_orderOf_dvd hrec] at hInt
  have htot : 0 < (T N).den.totient := Nat.totient_pos.mpr (T N).den_pos
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0] at hInt
  exact htot.ne' (zero_dvd_iff.mp hInt)

theorem ratIntegral_sub_comm (x y : ℚ) :
    RatIntegral (x - y) ↔ RatIntegral (y - x) := by
  constructor <;>
  · rintro ⟨z, hz⟩
    exact ⟨-z, by push_cast; linarith⟩

/-! ## (F) and its converse: the free-pair lattice -/

/-- One-sided form of the free-pair lattice, `N ≤ M`. -/
theorem free_pair_integral_iff_modEq_of_le {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den)
    {N M : ℕ} (hN : N₀ ≤ N) (hle : N ≤ M) :
    RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hden : (T N).den = (T N₀).den := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    exact tail_den_eq_of_odd_of_le hrec hodd k
  have hshift : T (N + h) - T N = tailShift T h N := rfl
  rw [hshift, tailShift_integral_iff_orderOf_dvd hrec N h, hden,
    Nat.modEq_iff_dvd' (Nat.le_add_right N h), Nat.add_sub_cancel_left]

/-- **The free-pair lattice (F) with its converse.**  At and beyond an
odd-denominator state with reduced denominator `d`, the difference of two tail
states is an integer exactly when the indices are congruent modulo the
multiplicative order of `2` modulo `d`.  The offset is free: `M - N` is any
multiple of the order, not a fixed `h`. -/
theorem free_pair_integral_iff_modEq {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den)
    {N M : ℕ} (hN : N₀ ≤ N) (hM : N₀ ≤ M) :
    RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] := by
  rcases le_total N M with hle | hle
  · exact free_pair_integral_iff_modEq_of_le hrec hodd hN hle
  · rw [ratIntegral_sub_comm, free_pair_integral_iff_modEq_of_le hrec hodd hM hle]
    exact ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩

/-- **Named corollary.**  Every rational-valued integer-digit dyadic tail
orbit has a cutoff `N₀` and a positive modulus `t` such that, beyond the
cutoff, `T_M - T_N ∈ ℤ ↔ M ≡ N (mod t)`.  The modulus is the order of `2`
modulo the stabilised odd denominator. -/
theorem exists_free_pair_lattice {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M →
      (RatIntegral (T M - T N) ↔ N ≡ M [MOD t]) := by
  obtain ⟨N₀, hodd⟩ := exists_odd_den_state hrec
  exact ⟨N₀, _, orderOf_two_zmod_den_pos hrec N₀ hodd,
    fun _ _ hN hM => free_pair_integral_iff_modEq hrec hodd hN hM⟩

/-- Actual-prime-gap instance: the rational candidate tail of any proposed
rational value `S` has a free-pair lattice. -/
theorem exists_free_pair_lattice_rationalPrimeGapTailState (S : ℚ) :
    ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M →
      (RatIntegral (rationalPrimeGapTailState S M - rationalPrimeGapTailState S N) ↔
        N ≡ M [MOD t]) :=
  exists_free_pair_lattice (rationalPrimeGapTailState_recurrence S)

/-! ## (P) and the equivalence with irrationality -/

/-- **(P)**: for every positive modulus and every cutoff, some pair of indices
beyond the cutoff, congruent modulo the modulus, has a nonintegral tail
difference. -/
def CofinalFreePairNonintegral (T : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N M : ℕ, N₀ ≤ N ∧ N₀ ≤ M ∧ N ≡ M [MOD t] ∧
    ¬ RealIntegral (T M - T N)

/-- The fixed-offset cofinal criterion implies (P): take `M = N + t`.  So (P)
is at most as strong as the recorded producer form. -/
theorem cofinalFreePairNonintegral_of_cofinalNonintegralTailShifts {T : ℕ → ℝ}
    (hescape : CofinalNonintegralTailShifts T) :
    CofinalFreePairNonintegral T := by
  intro t ht N₀
  obtain ⟨N, hN, hnon⟩ := hescape t ht N₀
  exact ⟨N, N + t, hN, hN.trans (Nat.le_add_right N t),
    (Nat.modEq_iff_dvd' (Nat.le_add_right N t)).2 (by simp), hnon⟩

theorem cofinalFreePairNonintegral_of_irrational {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (hirr : Irrational (T 0)) :
    CofinalFreePairNonintegral T :=
  cofinalFreePairNonintegral_of_cofinalNonintegralTailShifts
    ((irrational_initial_iff_cofinalNonintegralTailShifts hrec).1 hirr)

/-- (P) forces irrationality: a rational initial state has a free-pair lattice,
so every congruent pair beyond its cutoff has an integral difference. -/
theorem irrational_initial_of_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (hP : CofinalFreePairNonintegral T) :
    Irrational (T 0) := by
  by_contra hrat
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
  have hcast := realTail_eq_ratCast_rationalDyadicOrbit hrec q hq
  obtain ⟨N₀, t, ht, hlat⟩ := exists_free_pair_lattice (rationalDyadicOrbit_recurrence g q)
  obtain ⟨N, M, hN, hM, hmod, hnon⟩ := hP t ht N₀
  apply hnon
  obtain ⟨z, hz⟩ := (hlat N M hN hM).2 hmod
  refine ⟨z, ?_⟩
  rw [hcast M, hcast N]
  exact_mod_cast hz

/-- **`Irr ⟺ (P)`** for every real integer-digit dyadic tail orbit. -/
theorem irrational_initial_iff_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalFreePairNonintegral T :=
  ⟨cofinalFreePairNonintegral_of_irrational hrec,
    irrational_initial_of_cofinalFreePairNonintegral hrec⟩

/-- (P) and the fixed-offset criterion are therefore equivalent on every
integer-digit orbit, through irrationality. -/
theorem cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    CofinalFreePairNonintegral T ↔ CofinalNonintegralTailShifts T := by
  rw [← irrational_initial_iff_cofinalFreePairNonintegral hrec,
    irrational_initial_iff_cofinalNonintegralTailShifts hrec]

/-! ## The actual prime-gap series -/

/-- The real scaled tail of the actual prime-gap series after the first `N+1`
gaps: `T_N = Σ_{k ≥ 1} g_{N+k} / 2^k`. -/
noncomputable def primeGapRealTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) * ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1))

/-- The real prime-gap tail obeys the integer-digit dyadic recurrence with the
actual consecutive prime gaps as digits. -/
theorem primeGapRealTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) primeGapRealTail := by
  intro N
  have hsum : Summable (fun k : ℕ => primeGapDyadicTerm (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr summable_primeGapDyadicTerm
  have hsplit := hsum.tsum_eq_zero_add
  have hshift :
      (∑' k : ℕ, primeGapDyadicTerm (k + 1 + (N + 1))) =
        ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1 + 1)) := by
    congr 1
    funext k
    rw [show k + 1 + (N + 1) = k + (N + 1 + 1) by omega]
  rw [hshift] at hsplit
  simp only [primeGapRealTail]
  rw [hsplit, Nat.zero_add, primeGapDyadicTerm]
  push_cast
  simp only [pow_succ]
  field_simp
  ring

/-- The initial real tail is `2S - 1` with `S` the prime-gap series. -/
theorem primeGapRealTail_zero :
    primeGapRealTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 := by
  have hsplit := summable_primeGapDyadicTerm.tsum_eq_zero_add
  simp only [primeGapRealTail, Nat.zero_add, pow_one]
  rw [hsplit, primeGapDyadicTerm, primeGap0_zero]
  push_cast
  ring

/-- Irrationality of the prime-gap series is irrationality of its initial real
tail. -/
theorem irrational_primeGap_tsum_iff_irrational_primeGapRealTail_zero :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔ Irrational (primeGapRealTail 0) := by
  have h : primeGapRealTail 0 =
      ((2 : ℕ) : ℝ) * (∑' n : ℕ, primeGapDyadicTerm n) - ((1 : ℤ) : ℝ) := by
    rw [primeGapRealTail_zero]
    push_cast
    ring
  rw [h]
  constructor
  · intro hirr
    exact (hirr.natCast_mul (by norm_num : (2 : ℕ) ≠ 0)).sub_intCast 1
  · intro hirr
    exact (hirr.of_sub_intCast 1).of_natCast_mul 2

/-- **Erdős #251 in free-pair form.**  The consecutive-prime-gap dyadic series
is irrational exactly when, for every positive modulus `t` and every cutoff,
two tail indices beyond the cutoff and congruent modulo `t` have a nonintegral
scaled-tail difference.  Nothing here produces such pairs; the equivalence
is exact and the target remains open. -/
theorem irrational_primeGap_tsum_iff_cofinalFreePairNonintegral :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral primeGapRealTail := by
  rw [irrational_primeGap_tsum_iff_irrational_primeGapRealTail_zero]
  exact irrational_initial_iff_cofinalFreePairNonintegral primeGapRealTail_recurrence

#print axioms exists_free_pair_lattice
#print axioms irrational_initial_iff_cofinalFreePairNonintegral
#print axioms irrational_primeGap_tsum_iff_cofinalFreePairNonintegral

end ErdosProblems.Erdos251
