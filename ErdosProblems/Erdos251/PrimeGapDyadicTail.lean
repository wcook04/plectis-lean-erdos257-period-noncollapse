import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PowModTotient
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

/-!
# Erdős #251: prime-gap dyadic tails

Finite summation by parts rewrites the prime series in terms of consecutive
prime gaps.  An elementary polynomial bound for the `n`th prime then proves
unconditional convergence of both series and the exact infinite identity.

If the prime-gap sum is rational, its scaled tails form a rational dyadic
recurrence.  Denominator arithmetic forces one positive fixed tail shift to be
eventually integral, while the factorial construction proves that the actual
prime gaps are unbounded and not eventually periodic.  These facts do not by
themselves prove irrationality: a contradiction still requires smallness, or
cofinally many adjacent small mismatches, for the same fixed shift.  Neither
unboundedness nor nonperiodicity supplies that missing estimate.
-/

namespace ErdosProblems.Erdos251

/-- Zero-based prime enumeration. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- Zero-based consecutive prime gap. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

@[simp] theorem primeGap0_zero : primeGap0 0 = 1 := by
  simp [primeGap0, prime0, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three]

@[simp] theorem primeGap0_one : primeGap0 1 = 2 := by
  simp [primeGap0, prime0, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five]

/-- The classical factorial construction gives arbitrarily long prime-free
intervals, hence the actual consecutive-prime gaps are unbounded. -/
theorem exists_primeGap0_gt (M : ℕ) :
    ∃ n, M < primeGap0 n := by
  let width := M + 2
  let base := width.factorial
  let primeCount := Nat.count Nat.Prime (base + 2)
  have hbasePos : 0 < base := Nat.factorial_pos width
  have hcountPos : 0 < primeCount := by
    apply Nat.pos_of_ne_zero
    exact Nat.count_ne_iff_exists.mpr
      ⟨2, by simp [base, hbasePos], Nat.prime_two⟩
  let n := primeCount - 1
  have hnSucc : n + 1 = primeCount := by
    exact Nat.sub_add_cancel hcountPos
  have hprev : prime0 n < base + 2 := by
    rw [prime0]
    apply Nat.nth_lt_of_lt_count
    change primeCount - 1 < primeCount
    omega
  have hnextPrime : Nat.Prime (prime0 (n + 1)) := by
    rw [prime0]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
  have hnextLower : base + 2 ≤ prime0 (n + 1) := by
    rw [prime0, hnSucc]
    exact Nat.le_nth_count Nat.infinite_setOf_prime (base + 2)
  have hcomposite :
      ∀ i, 2 ≤ i → i ≤ width → ¬ Nat.Prime (base + i) := by
    intro i hiTwo hiWidth
    apply Nat.not_prime_of_dvd_of_lt (m := i)
    · simpa [base] using Nat.dvd_factorial (by omega) hiWidth
    · exact hiTwo
    · omega
  have hnext : base + width < prime0 (n + 1) := by
    by_contra h
    have hnextUpper : prime0 (n + 1) ≤ base + width := by omega
    let i := prime0 (n + 1) - base
    have hiTwo : 2 ≤ i := by omega
    have hiWidth : i ≤ width := by omega
    have hsplit : base + i = prime0 (n + 1) := by omega
    exact hcomposite i hiTwo hiWidth (hsplit ▸ hnextPrime)
  refine ⟨n, ?_⟩
  rw [primeGap0]
  omega

/-- Finite zero-based dyadic partial sum of a rational sequence. -/
def dyadicPartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, P i / 2 ^ (i + 1)

/-- The finite zero-based normalization with denominator `2^i`, matching the
displayed indexing used by the formal conjecture. -/
noncomputable def prime0DisplayedPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (prime0 i : ℚ) / 2 ^ i

/-- Exact factor-of-two indexing normalization: the zero-based displayed
partial sum is twice the convention with denominator `2^(i+1)`. -/
theorem prime0DisplayedPartialSumQ_eq_two_mul (n : ℕ) :
    prime0DisplayedPartialSumQ n =
      2 * dyadicPartialSumQ (fun i => (prime0 i : ℚ)) n := by
  rw [prime0DisplayedPartialSumQ, dyadicPartialSumQ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [pow_succ]
  field_simp

/-- Finite dyadic partial sum of the forward differences of a sequence. -/
def dyadicDifferencePartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (P (i + 1) - P i) / 2 ^ (i + 1)

@[simp] theorem dyadicPartialSumQ_succ (P : ℕ → ℚ) (n : ℕ) :
    dyadicPartialSumQ P (n + 1) =
      dyadicPartialSumQ P n + P n / 2 ^ (n + 1) := by
  rw [dyadicPartialSumQ, dyadicPartialSumQ, Finset.sum_range_succ]

@[simp] theorem dyadicDifferencePartialSumQ_succ (P : ℕ → ℚ) (n : ℕ) :
    dyadicDifferencePartialSumQ P (n + 1) =
      dyadicDifferencePartialSumQ P n +
        (P (n + 1) - P n) / 2 ^ (n + 1) := by
  rw [dyadicDifferencePartialSumQ, dyadicDifferencePartialSumQ,
    Finset.sum_range_succ]

/-- Exact finite summation by parts.  The endpoint term is retained, so the
theorem can be used before any analytic convergence argument. -/
theorem dyadicPartialSumQ_eq_start_add_differences
    (P : ℕ → ℚ) (n : ℕ) :
    dyadicPartialSumQ P (n + 1) =
      P 0 + dyadicDifferencePartialSumQ P n - P n / 2 ^ (n + 1) := by
  induction n with
  | zero =>
      simp [dyadicPartialSumQ, dyadicDifferencePartialSumQ]
      ring
  | succ n ih =>
      rw [dyadicPartialSumQ_succ, dyadicDifferencePartialSumQ_succ, ih]
      simp only [pow_succ]
      ring

/-- Consecutive zero-based primes are increasing. -/
theorem prime0_mono_step (n : ℕ) : prime0 n ≤ prime0 (n + 1) := by
  exact (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (Nat.le_succ n)

/-- Casting the natural prime gap agrees with subtraction in `ℚ`. -/
theorem primeGap0_cast (n : ℕ) :
    (primeGap0 n : ℚ) = (prime0 (n + 1) : ℚ) - prime0 n := by
  rw [primeGap0, Nat.cast_sub (prime0_mono_step n)]

/-- Finite dyadic partial sum of the actual consecutive prime gaps. -/
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)

@[simp] theorem primeGapPartialSumQ_succ (n : ℕ) :
    primeGapPartialSumQ (n + 1) =
      primeGapPartialSumQ n + (primeGap0 n : ℚ) / 2 ^ (n + 1) := by
  rw [primeGapPartialSumQ, primeGapPartialSumQ, Finset.sum_range_succ]

/-- Exact finite prime-gap reformulation, including the initial gap and the
endpoint correction.  Passing to an infinite series requires a separate proof
that the endpoint tends to zero. -/
theorem prime0_dyadic_summation_by_parts (n : ℕ) :
    dyadicPartialSumQ (fun i => (prime0 i : ℚ)) (n + 1) =
      2 + primeGapPartialSumQ n - (prime0 n : ℚ) / 2 ^ (n + 1) := by
  simpa [dyadicDifferencePartialSumQ, primeGapPartialSumQ, primeGap0_cast,
    prime0] using
    (dyadicPartialSumQ_eq_start_add_differences
      (fun i => (prime0 i : ℚ)) n)

/-! ## Infinite prime-gap reformulation -/

/-- The real term in the normalized zero-based prime series. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

/-- The term with denominator `2^n` used by the displayed formal
conjecture. -/
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n

/-- The real term in the corresponding consecutive-prime-gap series. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

/-- Infinite-series version of the exact factor-two normalization. -/
theorem primeDisplayedDyadicTerm_eq_two_mul (n : ℕ) :
    primeDisplayedDyadicTerm n = 2 * primeDyadicTerm n := by
  rw [primeDisplayedDyadicTerm, primeDyadicTerm, pow_succ]
  field_simp

/-- Each gap term is the dyadic discrete derivative of the prime term. -/
theorem primeGapDyadicTerm_eq (n : ℕ) :
    primeGapDyadicTerm n =
      2 * primeDyadicTerm (n + 1) - primeDyadicTerm n := by
  rw [primeGapDyadicTerm, primeDyadicTerm, primeDyadicTerm, primeGap0,
    Nat.cast_sub (prime0_mono_step n)]
  simp only [pow_succ]
  field_simp

/-! ### Unconditional convergence -/

/-- Any polynomial upper bound on the `n`th prime implies convergence of the
normalized prime series. -/
theorem summable_primeDyadicTerm_of_polynomial_growth
    (C k : ℕ)
    (hgrowth : ∀ n, prime0 n ≤ C * (n + 1) ^ k) :
    Summable primeDyadicTerm := by
  have hpoly :
      Summable
        (fun n : ℕ =>
          (n : ℝ) ^ k * ((1 / 2 : ℝ) ^ n)) := by
    exact summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
  have hshift :
      Summable
        (fun n : ℕ =>
          (((1 + n : ℕ) : ℝ) ^ k) *
            ((1 / 2 : ℝ) ^ (1 + n))) := by
    simpa only [Function.comp_apply] using
      hpoly.comp_injective (add_right_injective 1)
  have hmajor :
      Summable
        (fun n : ℕ =>
          (C : ℝ) *
            ((((1 + n : ℕ) : ℝ) ^ k) *
              ((1 / 2 : ℝ) ^ (1 + n))) ) :=
    hshift.mul_left (C : ℝ)
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro n
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · intro n
    have hgrowthR :
        (prime0 n : ℝ) ≤
          (C : ℝ) * (((1 + n : ℕ) : ℝ) ^ k) := by
      exact_mod_cast (by simpa [Nat.add_comm] using hgrowth n)
    rw [primeDyadicTerm]
    calc
      (prime0 n : ℝ) / 2 ^ (n + 1) ≤
          ((C : ℝ) * (((1 + n : ℕ) : ℝ) ^ k)) /
            2 ^ (n + 1) :=
        div_le_div_of_nonneg_right hgrowthR (by positivity)
      _ = (C : ℝ) *
          ((((1 + n : ℕ) : ℝ) ^ k) *
            ((1 / 2 : ℝ) ^ (1 + n))) := by
        rw [Nat.add_comm n 1]
        rw [one_div_pow]
        ring

/-- The central binomial coefficient is bounded by one factor `2m` for
each prime at most `2m`.  Multiplicities cause no loss here because the
complete prime-power contribution to a binomial coefficient is itself at
most its top parameter. -/
theorem centralBinom_le_two_mul_pow_primeCounting (m : ℕ) (hm : 0 < m) :
    m.centralBinom ≤
      (2 * m) ^ Nat.primeCounting (2 * m) := by
  have hfilter :
      (∏ p ∈ Finset.range (2 * m + 1) with p.Prime,
          p ^ m.centralBinom.factorization p) =
        ∏ p ∈ Finset.range (2 * m + 1),
          p ^ m.centralBinom.factorization p := by
    refine Finset.prod_filter_of_ne fun p _hp hne => ?_
    contrapose! hne
    rw [Nat.factorization_eq_zero_of_not_prime m.centralBinom hne, pow_zero]
  rw [← Nat.prod_pow_factorization_centralBinom, ← hfilter]
  calc
    (∏ p ∈ Finset.range (2 * m + 1) with p.Prime,
        p ^ m.centralBinom.factorization p) ≤
        ∏ _p ∈ Finset.filter Nat.Prime (Finset.range (2 * m + 1)),
          2 * m := by
      gcongr with p hp
      simpa [Nat.centralBinom] using
        (Nat.pow_factorization_choose_le (p := p) (k := m)
          (by omega : 0 < 2 * m))
    _ = (2 * m) ^
        (Finset.filter Nat.Prime (Finset.range (2 * m + 1))).card := by
      simp
    _ = (2 * m) ^ Nat.primeCounting (2 * m) := by
      simp only [Nat.primeCounting, Nat.primeCounting',
        Nat.count_eq_card_filter_range]

/-- A deliberately generous elementary inequality balancing the polynomial
test point `(n+5)^4` against central-binomial exponential growth. -/
theorem binomial_count_growth_bound (n : ℕ) :
    let m := (n + 5) ^ 4
    m * (2 * m) ^ n ≤ 4 ^ m := by
  let x := n + 5
  let m := x ^ 4
  have hxPow : x ≤ 2 ^ x := by
    induction x with
    | zero => simp
    | succ x ih =>
        rw [pow_succ]
        have hOne : 1 ≤ 2 ^ x := Nat.one_le_pow x 2 (by norm_num)
        omega
  have hExp : n + x * (4 * (n + 1)) ≤ 2 * m := by
    dsimp [x, m]
    nlinarith [sq_nonneg (n ^ 2 + 8 * n)]
  dsimp only
  change m * (2 * m) ^ n ≤ 4 ^ m
  calc
    m * (2 * m) ^ n =
        2 ^ n * x ^ (4 * (n + 1)) := by
      simp only [m, mul_pow, pow_mul, pow_add]
      ring
    _ ≤ 2 ^ n * (2 ^ x) ^ (4 * (n + 1)) := by
      gcongr
    _ = 2 ^ (n + x * (4 * (n + 1))) := by
      rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (2 * m) :=
      Nat.pow_le_pow_right (by norm_num) hExp
    _ = 4 ^ m := by
      norm_num [pow_mul]

/-- The prime-counting function exceeds `n` at the explicit polynomial
test point `2(n+5)^4`. -/
theorem lt_primeCounting_two_mul_fourth (n : ℕ) :
    n < Nat.primeCounting (2 * (n + 5) ^ 4) := by
  let m := (n + 5) ^ 4
  have hmFour : 4 ≤ m := by
    have hbase : 5 ≤ n + 5 := by omega
    have hpow := Nat.pow_le_pow_left hbase 4
    change 4 ≤ (n + 5) ^ 4
    calc
      4 ≤ 5 ^ 4 := by norm_num
      _ ≤ (n + 5) ^ 4 := hpow
  have hmPos : 0 < m := by omega
  have hcentral :
      4 ^ m < m * m.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom m hmFour
  have hcentralBound :
      m.centralBinom ≤
        (2 * m) ^ Nat.primeCounting (2 * m) :=
    centralBinom_le_two_mul_pow_primeCounting m hmPos
  have hgrowth : m * (2 * m) ^ n ≤ 4 ^ m := by
    simpa [m] using binomial_count_growth_bound n
  by_contra h
  have hcount : Nat.primeCounting (2 * m) ≤ n :=
    Nat.le_of_not_gt (by simpa [m] using h)
  have hpow :
      (2 * m) ^ Nat.primeCounting (2 * m) ≤ (2 * m) ^ n :=
    Nat.pow_le_pow_right (by positivity) hcount
  have :
      m * m.centralBinom ≤ m * (2 * m) ^ n :=
    (Nat.mul_le_mul_left m hcentralBound).trans
      (Nat.mul_le_mul_left m hpow)
  omega

/-- An unconditional polynomial upper bound for the zero-based `n`th prime.
It is intentionally loose but entirely elementary and sufficient for every
dyadic convergence argument in this module. -/
theorem prime0_le_polynomial (n : ℕ) :
    prime0 n ≤ 1250 * (n + 1) ^ 4 := by
  have hcount :
      n < Nat.count Nat.Prime (2 * (n + 5) ^ 4 + 1) := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using
      lt_primeCounting_two_mul_fourth n
  have hnth :
      prime0 n < 2 * (n + 5) ^ 4 + 1 := by
    rw [prime0]
    exact Nat.nth_lt_of_lt_count hcount
  have hbase : n + 5 ≤ 5 * (n + 1) := by omega
  have hpow := Nat.pow_le_pow_left hbase 4
  calc
    prime0 n ≤ 2 * (n + 5) ^ 4 := by omega
    _ ≤ 2 * (5 * (n + 1)) ^ 4 := Nat.mul_le_mul_left 2 hpow
    _ = 1250 * (n + 1) ^ 4 := by ring

/-- The normalized prime series converges unconditionally, using the explicit
elementary polynomial bound above. -/
theorem summable_primeDyadicTerm :
    Summable primeDyadicTerm :=
  summable_primeDyadicTerm_of_polynomial_growth 1250 4 prime0_le_polynomial

/-- Summability of the normalized prime series implies summability of the
corresponding consecutive-prime-gap series. -/
theorem summable_primeGapDyadicTerm_of_summable_primeDyadicTerm
    (hprime : Summable primeDyadicTerm) :
    Summable primeGapDyadicTerm := by
  have hshift : Summable (fun n => primeDyadicTerm (n + 1)) := by
    simpa [Nat.add_comm] using
      hprime.comp_injective (add_left_injective 1)
  exact ((hshift.mul_left 2).sub hprime).congr fun n =>
    (primeGapDyadicTerm_eq n).symm

/-- The actual consecutive-prime-gap dyadic series also converges
unconditionally. -/
theorem summable_primeGapDyadicTerm :
    Summable primeGapDyadicTerm :=
  summable_primeGapDyadicTerm_of_summable_primeDyadicTerm
    summable_primeDyadicTerm

/-- Exact infinite prime-gap reformulation.  Whenever the normalized prime
series is summable, its sum is `2` plus the sum of the actual consecutive
prime gaps. -/
theorem tsum_primeDyadicTerm_eq_two_add_primeGap
    (hprime : Summable primeDyadicTerm) :
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n := by
  have hshift : Summable (fun n => primeDyadicTerm (n + 1)) := by
    simpa [Nat.add_comm] using
      hprime.comp_injective (add_left_injective 1)
  have hsplit := hprime.sum_add_tsum_nat_add 1
  have hshiftSum :
      (∑' n : ℕ, primeDyadicTerm (n + 1)) =
        (∑' n : ℕ, primeDyadicTerm n) - 1 := by
    norm_num [primeDyadicTerm, prime0, Nat.nth_prime_zero_eq_two] at hsplit ⊢
    linarith
  have hgapSum :
      (∑' n : ℕ, primeGapDyadicTerm n) =
        2 * (∑' n : ℕ, primeDyadicTerm (n + 1)) -
          ∑' n : ℕ, primeDyadicTerm n := by
    simpa only [primeGapDyadicTerm_eq] using
      ((hshift.hasSum.mul_left 2).sub hprime.hasSum).tsum_eq
  rw [hgapSum, hshiftSum]
  ring

/-- Unconditional form of the exact infinite prime-gap reformulation. -/
theorem tsum_primeDyadicTerm_eq_two_add_primeGap_unconditional :
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n :=
  tsum_primeDyadicTerm_eq_two_add_primeGap summable_primeDyadicTerm

/-- Erdős #251 is therefore exactly equivalent to irrationality of the
consecutive-prime-gap dyadic series, once summability of the displayed prime
series is supplied. -/
theorem irrational_tsum_primeDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  rw [tsum_primeDyadicTerm_eq_two_add_primeGap hprime]
  exact irrational_natCast_add_iff

/-- The zero-based displayed series is `4` plus twice the normalized
prime-gap series. -/
theorem tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap
    (hprime : Summable primeDyadicTerm) :
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n := by
  calc
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
        2 * ∑' n : ℕ, primeDyadicTerm n :=
      (by simpa only [primeDisplayedDyadicTerm_eq_two_mul] using
        (hprime.hasSum.mul_left 2).tsum_eq)
    _ = 4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n := by
      rw [tsum_primeDyadicTerm_eq_two_add_primeGap hprime]
      ring

/-- Direct irrationality equivalence for the indexing used in the formal
conjecture. -/
theorem irrational_tsum_primeDisplayedDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  rw [tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap hprime]
  constructor
  · intro h
    exact (Irrational.of_natCast_add 4 h).of_natCast_mul 2
  · intro h
    exact (h.natCast_mul (by norm_num : (2 : ℕ) ≠ 0)).natCast_add 4

/-- The rational finite prime-gap sum casts exactly to the corresponding
finite real sum. -/
theorem primeGapPartialSumQ_cast (n : ℕ) :
    ((primeGapPartialSumQ n : ℚ) : ℝ) =
      ∑ i ∈ Finset.range n, primeGapDyadicTerm i := by
  simp [primeGapPartialSumQ, primeGapDyadicTerm]

/-! ## Exact tail-shift dynamics -/

/-- Abstract dyadic tail recurrence with integer digits.  The rational
candidate state below is an exact actual-gap instance; identifying a candidate
with the genuine infinite sum remains analytic. -/
def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

/-- The exact rational tail state attached to a proposed rational value `S`
of the prime-gap dyadic series.  It subtracts the first `N+1` gap terms and
rescales the remainder by `2^(N+1)`.  The definition is algebraic: no
summability or identification of `S` with an infinite sum is assumed. -/
noncomputable def rationalPrimeGapTailState (S : ℚ) (N : ℕ) : ℚ :=
  2 ^ (N + 1) * (S - primeGapPartialSumQ (N + 1))

/-- If the genuine real prime-gap sum equals the rational number `S`, the
algebraic candidate state is exactly the corresponding scaled real tail. -/
theorem cast_rationalPrimeGapTailState_eq_scaled_tsum_nat_add
    (S : ℚ)
    (hS : (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n)
    (N : ℕ) :
    ((rationalPrimeGapTailState S N : ℚ) : ℝ) =
      2 ^ (N + 1) *
        ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) := by
  rw [rationalPrimeGapTailState, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_sub, primeGapPartialSumQ_cast, hS]
  have hsplit :=
    summable_primeGapDyadicTerm.sum_add_tsum_nat_add (N + 1)
  rw [← hsplit]
  ring

/-- Non-irrationality therefore supplies a single rational candidate whose
states represent every scaled real tail. -/
theorem exists_rationalPrimeGapTailState_representation_of_not_irrational
    (h : ¬ Irrational (∑' n : ℕ, primeGapDyadicTerm n)) :
    ∃ S : ℚ,
      (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n ∧
      ∀ N,
        ((rationalPrimeGapTailState S N : ℚ) : ℝ) =
          2 ^ (N + 1) *
            ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) := by
  obtain ⟨S, hS⟩ := exists_rat_of_not_irrational h
  refine ⟨S, hS.symm, fun N => ?_⟩
  exact cast_rationalPrimeGapTailState_eq_scaled_tsum_nat_add
    S hS.symm N

/-- The proposed rational prime-gap tail satisfies the actual prime-gap
recurrence identically.  Under non-irrationality the preceding existence
theorem identifies this candidate with every scaled real tail; a contradiction
still requires a smallness statement for a suitable fixed shift. -/
theorem rationalPrimeGapTailState_recurrence (S : ℚ) :
    DyadicTailRecurrence (fun n => (primeGap0 n : ℤ))
      (rationalPrimeGapTailState S) := by
  intro N
  rw [rationalPrimeGapTailState, rationalPrimeGapTailState,
    primeGapPartialSumQ_succ]
  simp only [pow_succ]
  push_cast
  field_simp
  ring

@[simp] theorem rationalPrimeGapTailState_zero (S : ℚ) :
    rationalPrimeGapTailState S 0 = 2 * S - 1 := by
  simp [rationalPrimeGapTailState, primeGapPartialSumQ]
  ring

/-- Difference between two tail states separated by `h` steps. -/
def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

/-- Under a rationality witness, the rational tail shift is exactly the
difference of two scaled real tails. -/
theorem cast_rationalPrimeGapTailShift_eq_scaled_tsum_sub
    (S : ℚ)
    (hS : (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n)
    (h N : ℕ) :
    ((tailShift (rationalPrimeGapTailState S) h N : ℚ) : ℝ) =
      2 ^ (N + h + 1) *
          ∑' k : ℕ, primeGapDyadicTerm (k + (N + h + 1)) -
        2 ^ (N + 1) *
          ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) := by
  rw [tailShift, Rat.cast_sub,
    cast_rationalPrimeGapTailState_eq_scaled_tsum_nat_add S hS (N + h),
    cast_rationalPrimeGapTailState_eq_scaled_tsum_nat_add S hS N]

/-- The exact propagation identity for a fixed tail shift. -/
theorem tailShift_succ
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ) :
    tailShift T h (N + 1) =
      2 * tailShift T h N -
        ((g (N + h + 1) : ℚ) - (g (N + 1) : ℚ)) := by
  unfold tailShift
  rw [show N + 1 + h = (N + h) + 1 by omega,
    hrec (N + h), hrec N]
  ring

/-- A rational number is integral when it is the cast of an integer. -/
def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

/-- An integral multiplier of the proposed value remains an integral
multiplier of every actual prime-gap tail state.  This is the denominator
transport missing from a purely abstract recurrence: the initial gap is one,
and each later recurrence step subtracts an integer digit. -/
theorem ratIntegral_int_mul_rationalPrimeGapTailState
    (S : ℚ) (m : ℤ)
    (hS : RatIntegral ((m : ℚ) * S)) :
    ∀ N, RatIntegral ((m : ℚ) * rationalPrimeGapTailState S N)
  | 0 => by
      rcases hS with ⟨z, hz⟩
      refine ⟨2 * z - m, ?_⟩
      rw [rationalPrimeGapTailState_zero]
      calc
        (m : ℚ) * (2 * S - 1) = 2 * ((m : ℚ) * S) - m := by ring
        _ = ((2 * z - m : ℤ) : ℚ) := by rw [hz]; push_cast; ring
  | N + 1 => by
      rcases ratIntegral_int_mul_rationalPrimeGapTailState S m hS N with
        ⟨z, hz⟩
      refine ⟨2 * z - m * primeGap0 (N + 1), ?_⟩
      rw [(rationalPrimeGapTailState_recurrence S) N]
      calc
        (m : ℚ) *
            (2 * rationalPrimeGapTailState S N -
              ((primeGap0 (N + 1) : ℤ) : ℚ)) =
            2 * ((m : ℚ) * rationalPrimeGapTailState S N) -
              ((m * primeGap0 (N + 1) : ℤ) : ℚ) := by
                push_cast
                ring
        _ = ((2 * z - m * primeGap0 (N + 1) : ℤ) : ℚ) := by
          rw [hz]
          push_cast
          ring

/-- Integral scaling propagates through any integer-digit dyadic tail
recurrence. -/
theorem ratIntegral_int_mul_tailState_succ
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (m : ℤ) {N : ℕ}
    (hInt : RatIntegral ((m : ℚ) * T N)) :
    RatIntegral ((m : ℚ) * T (N + 1)) := by
  rcases hInt with ⟨z, hz⟩
  refine ⟨2 * z - m * g (N + 1), ?_⟩
  rw [hrec N]
  calc
    (m : ℚ) * (2 * T N - (g (N + 1) : ℚ)) =
        2 * ((m : ℚ) * T N) - ((m * g (N + 1) : ℤ) : ℚ) := by
      push_cast
      ring
    _ = ((2 * z - m * g (N + 1) : ℤ) : ℚ) := by
      rw [hz]
      push_cast
      ring

/-- Integral scaling at one tail index therefore persists at every later
index. -/
theorem ratIntegral_int_mul_tailState_add
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (m : ℤ) {N : ℕ}
    (hInt : RatIntegral ((m : ℚ) * T N)) :
    ∀ k, RatIntegral ((m : ℚ) * T (N + k))
  | 0 => by simpa using hInt
  | k + 1 => by
      simpa [Nat.add_assoc] using
        ratIntegral_int_mul_tailState_succ hrec m
          (ratIntegral_int_mul_tailState_add hrec m hInt k)

/-- The integer block accumulated through `h` dyadic tail steps beginning at
index `N`.  Recursively, this is
`g (N+1) * 2^(h-1) + ⋯ + g (N+h)`. -/
def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dyadicTailBlock g N h + g (N + h + 1)

/-- Iterating the tail recurrence for `h` steps gives the exact finite block
identity `T_(N+h) = 2^h T_N - B_(h,N)`. -/
theorem tail_iterate_eq_pow_mul_sub_block
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h := by
  induction h with
  | zero => simp [dyadicTailBlock]
  | succ h ih =>
      rw [show N + (h + 1) = (N + h) + 1 by omega, hrec (N + h), ih]
      simp only [dyadicTailBlock, pow_succ]
      push_cast
      ring

/-- The shifted-tail difference is a scaled copy of `T_N`, up to the explicit
integer block. -/
theorem tailShift_eq_scaled_sub_block
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    tailShift T h N =
      ((2 ^ h : ℚ) - 1) * T N - dyadicTailBlock g N h := by
  rw [tailShift, tail_iterate_eq_pow_mul_sub_block hrec]
  ring

/-- Subtracting an integer does not change whether a rational number is
integral. -/
theorem ratIntegral_sub_int_iff (x : ℚ) (z : ℤ) :
    RatIntegral (x - z) ↔ RatIntegral x := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + z, ?_⟩
    calc
      x = (x - (z : ℚ)) + z := by ring
      _ = (k : ℚ) + z := by rw [hk]
      _ = ((k + z : ℤ) : ℚ) := by push_cast; ring
  · rintro ⟨k, hk⟩
    refine ⟨k - z, ?_⟩
    rw [hk]
    push_cast
    ring

/-- Euler's congruence turns an odd reduced denominator into an explicit
integral multiplier: if `d = x.den` is odd, then
`(2^(phi d) - 1) * x` is an integer. -/
theorem ratIntegral_totientMultiplier_of_odd_den
    (x : ℚ) (hodd : Odd x.den) :
    RatIntegral (((2 : ℚ) ^ x.den.totient - 1) * x) := by
  have hcoprime : Nat.Coprime 2 x.den :=
    Nat.coprime_two_left.mpr hodd
  have hmod : 2 ^ x.den.totient ≡ 1 [MOD x.den] :=
    Nat.ModEq.pow_totient hcoprime
  have hone : 1 ≤ 2 ^ x.den.totient := Nat.one_le_two_pow
  have hdiv : x.den ∣ 2 ^ x.den.totient - 1 :=
    (Nat.modEq_iff_dvd' hone).mp hmod.symm
  obtain ⟨k, hk⟩ := hdiv
  have hkQ : (2 : ℚ) ^ x.den.totient - 1 = x.den * k := by
    exact_mod_cast hk
  refine ⟨(k : ℤ) * x.num, ?_⟩
  calc
    ((2 : ℚ) ^ x.den.totient - 1) * x =
        ((2 : ℚ) ^ x.den.totient - 1) *
          ((x.num : ℚ) / (x.den : ℚ)) := by rw [Rat.num_div_den]
    _ = ((x.den : ℚ) * k) * ((x.num : ℚ) / (x.den : ℚ)) := by
      rw [hkQ]
    _ = (((k : ℤ) * x.num : ℤ) : ℚ) := by
      field_simp [x.den_ne_zero]
      push_cast
      ring

/-- Split a rational denominator as `2^a * q` with odd `q`.  Euler's
multiplier for `q`, together with `2^(a+1)`, clears the entire denominator of
the candidate value. -/
theorem ratIntegral_scaled_of_den_eq_pow_two_mul_odd
    (S : ℚ) (a q : ℕ)
    (hden : S.den = 2 ^ a * q) (hodd : Odd q) :
    RatIntegral
      (((2 : ℚ) ^ q.totient - 1) * (2 : ℚ) ^ (a + 1) * S) := by
  have hqPos : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hq
    rw [hq, Nat.mul_zero] at hden
    exact S.den_ne_zero hden
  have hcoprime : Nat.Coprime 2 q :=
    Nat.coprime_two_left.mpr hodd
  have hmod : 2 ^ q.totient ≡ 1 [MOD q] :=
    Nat.ModEq.pow_totient hcoprime
  have hone : 1 ≤ 2 ^ q.totient := Nat.one_le_two_pow
  have hdiv : q ∣ 2 ^ q.totient - 1 :=
    (Nat.modEq_iff_dvd' hone).mp hmod.symm
  obtain ⟨k, hk⟩ := hdiv
  have hkQ : (2 : ℚ) ^ q.totient - 1 = q * k := by
    exact_mod_cast hk
  refine ⟨2 * (k : ℤ) * S.num, ?_⟩
  calc
    ((2 : ℚ) ^ q.totient - 1) * (2 : ℚ) ^ (a + 1) * S =
        ((2 : ℚ) ^ q.totient - 1) * (2 : ℚ) ^ (a + 1) *
          ((S.num : ℚ) / (S.den : ℚ)) := by rw [Rat.num_div_den]
    _ = (((2 * (k : ℤ) * S.num : ℤ) : ℚ)) := by
      rw [hkQ, hden]
      field_simp [ne_of_gt hqPos]
      push_cast
      ring

/-- At the index where the power-of-two part has been shifted away, the odd
Euler multiplier is integral on the actual prime-gap candidate tail. -/
theorem ratIntegral_multiplier_tail_at_twoExponent
    (S : ℚ) (a q : ℕ)
    (hden : S.den = 2 ^ a * q) (hodd : Odd q) :
    RatIntegral
      ((((2 : ℤ) ^ q.totient - 1 : ℤ) : ℚ) *
        rationalPrimeGapTailState S a) := by
  let m : ℤ := (2 : ℤ) ^ q.totient - 1
  have hscaled :
      RatIntegral
        ((m : ℚ) * (2 : ℚ) ^ (a + 1) * S) := by
    simpa [m] using
      ratIntegral_scaled_of_den_eq_pow_two_mul_odd S a q hden hodd
  rcases hscaled with ⟨z, hz⟩
  refine
    ⟨z - m * (2 : ℤ) ^ a -
        m * dyadicTailBlock (fun n => (primeGap0 n : ℤ)) 0 a, ?_⟩
  rw [show rationalPrimeGapTailState S a =
        rationalPrimeGapTailState S (0 + a) by simp,
    tail_iterate_eq_pow_mul_sub_block
      (rationalPrimeGapTailState_recurrence S) 0 a,
    rationalPrimeGapTailState_zero]
  change
    (m : ℚ) *
        ((2 : ℚ) ^ a * (2 * S - 1) -
          (dyadicTailBlock (fun n => (primeGap0 n : ℤ)) 0 a : ℚ)) =
      _
  calc
    (m : ℚ) *
        ((2 : ℚ) ^ a * (2 * S - 1) -
          (dyadicTailBlock (fun n => (primeGap0 n : ℤ)) 0 a : ℚ)) =
        (m : ℚ) * (2 : ℚ) ^ (a + 1) * S -
          (m : ℚ) * (2 : ℚ) ^ a -
          (m : ℚ) *
            (dyadicTailBlock (fun n => (primeGap0 n : ℤ)) 0 a : ℚ) := by
      rw [pow_succ]
      ring
    _ = ((z - m * (2 : ℤ) ^ a -
          m * dyadicTailBlock (fun n => (primeGap0 n : ℤ)) 0 a : ℤ) : ℚ) := by
      rw [hz]
      push_cast
      ring

/-! ### Denominator arithmetic and integral shifts -/

/-- Exact algebraic core of the integral-shift criterion: one tail shift is
integral exactly when `(2^h - 1) * T_N` is integral. -/
theorem tailShift_integral_iff_scaledTail
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔
      RatIntegral (((2 ^ h : ℚ) - 1) * T N) := by
  rw [tailShift_eq_scaled_sub_block hrec]
  exact ratIntegral_sub_int_iff _ _

/-- If a proposed rational prime-gap value has odd reduced denominator, one
fixed positive-period candidate supplied by Euler's theorem is integral at
every tail index.  Unlike the abstract per-state lemma below, the shift here
depends only on the denominator of `S`, not on `N`. -/
theorem rationalPrimeGapTailShift_integral_of_odd_den
    (S : ℚ) (hodd : Odd S.den) (N : ℕ) :
    RatIntegral
      (tailShift (rationalPrimeGapTailState S) S.den.totient N) := by
  let m : ℤ := (2 : ℤ) ^ S.den.totient - 1
  have hSm : RatIntegral ((m : ℚ) * S) := by
    simpa [m] using ratIntegral_totientMultiplier_of_odd_den S hodd
  have hmTail :=
    ratIntegral_int_mul_rationalPrimeGapTailState S m hSm N
  rw [tailShift_integral_iff_scaledTail
    (rationalPrimeGapTailState_recurrence S)]
  simpa [m] using hmTail

/-- Denominator decomposition upgrades the preceding odd-denominator
calculation to every rational candidate: after the power-of-two part has been
shifted out, one fixed Euler-period shift is integral at every later index. -/
theorem rationalPrimeGapTailShift_eventuallyIntegral_of_den_eq
    (S : ℚ) (a q : ℕ)
    (hden : S.den = 2 ^ a * q) (hodd : Odd q) :
    ∃ N₀, ∀ N, N₀ ≤ N →
      RatIntegral
        (tailShift (rationalPrimeGapTailState S) q.totient N) := by
  let m : ℤ := (2 : ℤ) ^ q.totient - 1
  have hmAt :
      RatIntegral ((m : ℚ) * rationalPrimeGapTailState S a) := by
    simpa [m] using
      ratIntegral_multiplier_tail_at_twoExponent S a q hden hodd
  refine ⟨a, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [tailShift_integral_iff_scaledTail
    (rationalPrimeGapTailState_recurrence S)]
  have hmTail :=
    ratIntegral_int_mul_tailState_add
      (rationalPrimeGapTailState_recurrence S) m hmAt k
  simpa [m] using hmTail

/-- Every rational candidate supplies a positive fixed shift which is
eventually integral along its actual prime-gap tail state.  The shift is the
totient of the odd part of the candidate denominator. -/
theorem rationalPrimeGapTailShift_eventuallyIntegral
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ∃ N₀, ∀ N, N₀ ≤ N →
        RatIntegral
          (tailShift (rationalPrimeGapTailState S) h N) := by
  let a := S.den.factorization 2
  let q := ordCompl[2] S.den
  have hden : S.den = 2 ^ a * q := by
    simpa [a, q] using
      (Nat.ordProj_mul_ordCompl_eq_self S.den 2).symm
  have hqOdd : Odd q := by
    exact Nat.coprime_two_left.mp
      (Nat.coprime_ordCompl Nat.prime_two S.den_ne_zero)
  have hqPos : 0 < q :=
    Nat.ordCompl_pos 2 S.den_ne_zero
  refine ⟨q.totient, Nat.totient_pos.mpr hqPos, ?_⟩
  exact
    rationalPrimeGapTailShift_eventuallyIntegral_of_den_eq
      S a q hden hqOdd

/-- If one tail state has odd reduced denominator `d`, its shift by
`Nat.totient d` steps is integral.  This is the explicit finite-algebraic
consequence of rationality supplied by Euler's theorem. -/
theorem tailShift_integral_totient_of_odd_den
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (hodd : Odd (T N).den) :
    RatIntegral (tailShift T (T N).den.totient N) := by
  rw [tailShift_integral_iff_scaledTail hrec]
  exact ratIntegral_totientMultiplier_of_odd_den (T N) hodd

/-- Once a fixed tail shift is integral, the recurrence keeps it integral at
the next index.  This is the exact finite algebra behind the eventual-shift
criterion; no prime-distribution input is used. -/
theorem tailShift_integral_succ
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {h N : ℕ}
    (hInt : RatIntegral (tailShift T h N)) :
    RatIntegral (tailShift T h (N + 1)) := by
  rcases hInt with ⟨z, hz⟩
  refine ⟨2 * z - (g (N + h + 1) - g (N + 1)), ?_⟩
  rw [tailShift_succ hrec, hz]
  push_cast
  ring

/-- Integrality therefore propagates through every later index. -/
theorem tailShift_integral_add
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {h N : ℕ}
    (hInt : RatIntegral (tailShift T h N)) :
    ∀ k, RatIntegral (tailShift T h (N + k))
  | 0 => by simpa using hInt
  | k + 1 => by
      simpa [Nat.add_assoc] using
        tailShift_integral_succ hrec (tailShift_integral_add hrec hInt k)

/-! ## Eventual integrality collapses under a shrinking shift -/

/-- An integral rational lying strictly between `-1` and `1` is zero. -/
theorem ratIntegral_eq_zero_of_neg_one_lt_of_lt_one
    {x : ℚ} (hInt : RatIntegral x) (hlow : -1 < x) (hhigh : x < 1) :
    x = 0 := by
  rcases hInt with ⟨z, rfl⟩
  have hzlow : (-1 : ℤ) < z := by exact_mod_cast hlow
  have hzhigh : z < (1 : ℤ) := by exact_mod_cast hhigh
  have : z = 0 := by omega
  simp [this]

/-- If one fixed tail shift is eventually integral and eventually lies in the
open unit interval around zero, then that shift is eventually identically
zero.  This is the discrete rigidity step needed to turn an analytic
small-shift estimate into exact arithmetic information. -/
theorem tailShift_eventually_zero_of_eventually_integral_of_eventually_small
    {T : ℕ → ℚ} {h : ℕ}
    (hInt : ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))
    (hsmall : ∃ N₀, ∀ N, N₀ ≤ N →
      -1 < tailShift T h N ∧ tailShift T h N < 1) :
    ∃ N₀, ∀ N, N₀ ≤ N → tailShift T h N = 0 := by
  rcases hInt with ⟨NInt, hInt⟩
  rcases hsmall with ⟨NSmall, hsmall⟩
  refine ⟨max NInt NSmall, fun N hN => ?_⟩
  exact ratIntegral_eq_zero_of_neg_one_lt_of_lt_one
    (hInt N ((le_max_left _ _).trans hN))
    (hsmall N ((le_max_right _ _).trans hN)).1
    (hsmall N ((le_max_right _ _).trans hN)).2

/-- For an integer-digit dyadic recurrence, eventual integrality plus an
eventually small fixed shift forces the digit sequence to be eventually
periodic with that shift. -/
theorem digits_eventually_periodic_of_eventually_integralTailShift_of_eventually_small
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hInt : ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))
    (hsmall : ∃ N₀, ∀ N, N₀ ≤ N →
      -1 < tailShift T h N ∧ tailShift T h N < 1) :
    ∃ N₀, ∀ N, N₀ ≤ N → g (N + h + 1) = g (N + 1) := by
  obtain ⟨N₀, hzero⟩ :=
    tailShift_eventually_zero_of_eventually_integral_of_eventually_small
      hInt hsmall
  refine ⟨N₀, fun N hN => ?_⟩
  have hstep := tailShift_succ hrec h N
  rw [hzero N hN, hzero (N + 1) (hN.trans (Nat.le_succ N))] at hstep
  have hcast :
      (g (N + h + 1) : ℚ) = (g (N + 1) : ℚ) := by
    linarith
  exact_mod_cast hcast

/-- Contrapositive form: if the digit sequence is not eventually periodic
with shift `h`, an eventually small `h`-shift cannot also be eventually
integral. -/
theorem not_eventuallyIntegralTailShift_of_eventually_small_of_not_periodic
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hsmall : ∃ N₀, ∀ N, N₀ ≤ N →
      -1 < tailShift T h N ∧ tailShift T h N < 1)
    (hnotPeriodic :
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → g (N + h + 1) = g (N + 1)) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  intro hInt
  exact hnotPeriodic
    (digits_eventually_periodic_of_eventually_integralTailShift_of_eventually_small
      hrec h hInt hsmall)

/-- A single adjacent pair of small shifts with unequal corresponding digits
already excludes simultaneous integrality. -/
theorem tailShift_not_both_integral_of_small_pair_of_digit_ne
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (hsmall :
      (-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
      (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1))
    (hdigit : g (N + h + 1) ≠ g (N + 1)) :
    ¬ (RatIntegral (tailShift T h N) ∧
      RatIntegral (tailShift T h (N + 1))) := by
  rintro ⟨hIntN, hIntSucc⟩
  have hzeroN : tailShift T h N = 0 :=
    ratIntegral_eq_zero_of_neg_one_lt_of_lt_one
      hIntN hsmall.1.1 hsmall.1.2
  have hzeroSucc : tailShift T h (N + 1) = 0 :=
    ratIntegral_eq_zero_of_neg_one_lt_of_lt_one
      hIntSucc hsmall.2.1 hsmall.2.2
  have hstep := tailShift_succ hrec h N
  rw [hzeroN, hzeroSucc] at hstep
  apply hdigit
  have hcast :
      (g (N + h + 1) : ℚ) = (g (N + 1) : ℚ) := by
    linarith
  exact_mod_cast hcast

/-- To rule out eventual integrality of a fixed shift, it is enough to find
beyond every level one adjacent pair of strictly small shifts whose
corresponding digits differ. -/
theorem not_eventuallyIntegralTailShift_of_cofinal_small_mismatch
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hsupply : ∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
       (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  rintro ⟨N₀, hInt⟩
  obtain ⟨N, hN, hsmall, hdigit⟩ := hsupply N₀
  exact tailShift_not_both_integral_of_small_pair_of_digit_ne
    hrec h N hsmall hdigit
    ⟨hInt N hN, hInt (N + 1) (hN.trans (Nat.le_succ N))⟩

/-- Consecutive prime gaps cannot become periodic with any positive period.
The proof combines the exact factorial prime-free intervals above with the
finite range of a periodic natural-valued sequence. -/
theorem primeGap0_not_eventually_periodic
    {h : ℕ} (hpos : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      primeGap0 (N + h + 1) = primeGap0 (N + 1) := by
  rintro ⟨N₀, hperiodic⟩
  let f : ℕ → ℕ := fun k => primeGap0 (N₀ + 1 + k)
  have hf : Function.Periodic f h := by
    intro k
    have hk := hperiodic (N₀ + k) (Nat.le_add_right N₀ k)
    simpa [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
  let periodBound := ∑ i ∈ Finset.range h, f i
  let initialBound := ∑ i ∈ Finset.range (N₀ + 1), primeGap0 i
  obtain ⟨n, hn⟩ := exists_primeGap0_gt (periodBound + initialBound)
  have hnLate : N₀ + 1 ≤ n := by
    by_contra h
    have hnMem : n ∈ Finset.range (N₀ + 1) := Finset.mem_range.mpr (by omega)
    have hnInitial : primeGap0 n ≤ initialBound := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hnMem
    omega
  let k := n - (N₀ + 1)
  have hkEq : N₀ + 1 + k = n := by
    exact Nat.add_sub_of_le hnLate
  have hkMem : k % h ∈ Finset.range h :=
    Finset.mem_range.mpr (Nat.mod_lt k hpos)
  have hkBound : f k ≤ periodBound := by
    calc
      f k = f (k % h) := (hf.map_mod_nat k).symm
      _ ≤ periodBound :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hkMem
  change primeGap0 (N₀ + 1 + k) ≤ periodBound at hkBound
  rw [hkEq] at hkBound
  omega

/-- For the actual prime gaps, an eventually small positive tail shift cannot
also be eventually integral: together those properties would force eventual
periodicity, contradicting the factorial gap theorem. -/
theorem primeGapTailShift_not_eventuallyIntegral_of_eventually_small
    {T : ℕ → ℚ} {h : ℕ}
    (hrec : DyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) T)
    (hpos : 0 < h)
    (hsmall : ∃ N₀, ∀ N, N₀ ≤ N →
      -1 < tailShift T h N ∧ tailShift T h N < 1) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  apply not_eventuallyIntegralTailShift_of_eventually_small_of_not_periodic
    hrec h hsmall
  intro hperiodic
  apply primeGap0_not_eventually_periodic hpos
  rcases hperiodic with ⟨N₀, hperiodic⟩
  refine ⟨N₀, fun N hN => ?_⟩
  exact_mod_cast hperiodic N hN

/-- No rational candidate with odd reduced denominator can have an eventually
small Euler-period tail shift along the actual consecutive prime gaps.  Under
non-irrationality this candidate is the genuine scaled tail, but no theorem
here supplies the required eventual smallness. -/
theorem rationalPrimeGapTailShift_not_eventually_small_of_odd_den
    (S : ℚ) (hodd : Odd S.den) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      -1 <
          tailShift (rationalPrimeGapTailState S) S.den.totient N ∧
        tailShift (rationalPrimeGapTailState S) S.den.totient N < 1 := by
  intro hsmall
  have hpos : 0 < S.den.totient :=
    Nat.totient_pos.mpr S.den_pos
  apply primeGapTailShift_not_eventuallyIntegral_of_eventually_small
    (rationalPrimeGapTailState_recurrence S) hpos hsmall
  exact ⟨0, fun N _hN =>
    rationalPrimeGapTailShift_integral_of_odd_den S hodd N⟩

/-- Every rational `S` has some positive fixed tail shift which cannot
eventually remain in the open unit interval: denominator arithmetic makes that
shift eventually integral, while eventual smallness would force the actual
prime gaps to become periodic.  This is compatible with rationality; it
identifies a shift for which smallness must fail. -/
theorem rationalPrimeGapTail_has_positive_shift_not_eventually_small
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ¬ ∃ N₀, ∀ N, N₀ ≤ N →
        -1 < tailShift (rationalPrimeGapTailState S) h N ∧
          tailShift (rationalPrimeGapTailState S) h N < 1 := by
  obtain ⟨h, hpos, hInt⟩ :=
    rationalPrimeGapTailShift_eventuallyIntegral S
  refine ⟨h, hpos, ?_⟩
  intro hsmall
  exact
    primeGapTailShift_not_eventuallyIntegral_of_eventually_small
      (rationalPrimeGapTailState_recurrence S) hpos hsmall hInt

/-- Actual-prime-gap specialization of the cofinal small-mismatch criterion. -/
theorem primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch
    {T : ℕ → ℚ} (h : ℕ)
    (hrec : DyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) T)
    (hsupply : ∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
       (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
      primeGap0 (N + h + 1) ≠ primeGap0 (N + 1)) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  apply not_eventuallyIntegralTailShift_of_cofinal_small_mismatch hrec h
  intro N₀
  obtain ⟨N, hN, hsmall, hdigit⟩ := hsupply N₀
  refine ⟨N, hN, hsmall, ?_⟩
  exact_mod_cast hdigit

/-! ## Unrestricted carries need not produce periodic coefficients -/

/-- The coefficient emitted by an unrestricted integer carry. -/
def carryCoeff (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  2 * K n - K (n + 1)

/-- The finite dyadic series emitted by `carryCoeff`. -/
def carryPartialSum (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, carryCoeff K i / 2 ^ (i + 1)

/-- Exact finite telescoping for an arbitrary rational-valued carry. -/
theorem carryPartialSum_eq (K : ℕ → ℚ) (n : ℕ) :
    carryPartialSum K n = K 0 - K n / 2 ^ n := by
  induction n with
  | zero => simp [carryPartialSum]
  | succ n ih =>
      rw [carryPartialSum, Finset.sum_range_succ]
      change carryPartialSum K n + carryCoeff K n / 2 ^ (n + 1) = _
      rw [ih]
      simp only [carryCoeff, pow_succ]
      ring

/-- The carry `K n = n` emits the linear coefficient stream `n - 1`. -/
theorem carryCoeff_natCast_eq (n : ℕ) :
    carryCoeff (fun j => (j : ℚ)) n = (n : ℚ) - 1 := by
  simp [carryCoeff]
  ring

/-- The partial sums emitted by the linear carry have the exact endpoint
`-n / 2^n`; in particular their ordinary real limit is rational once the
standard exponential-dominance limit is applied. -/
theorem carryPartialSum_natCast_eq (n : ℕ) :
    carryPartialSum (fun j => (j : ℚ)) n = -((n : ℚ) / 2 ^ n) := by
  simpa using carryPartialSum_eq (fun j => (j : ℚ)) n

/-- The coefficient stream emitted by the linear carry cannot become periodic
with any positive period. -/
theorem carryCoeff_natCast_not_eventually_periodic
    {h : ℕ} (hpos : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      carryCoeff (fun j => (j : ℚ)) (N + h) =
        carryCoeff (fun j => (j : ℚ)) N := by
  rintro ⟨N₀, hperiodic⟩
  have heq := hperiodic N₀ (le_refl N₀)
  rw [carryCoeff_natCast_eq, carryCoeff_natCast_eq] at heq
  have hposQ : (0 : ℚ) < h := by exact_mod_cast hpos
  push_cast at heq
  linarith

/-- Natural-valued carries emit nonnegative coefficients when the next carry
is at most twice the current one. -/
def natCarryCoeff (K : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * K n - K (n + 1)

theorem natCarryCoeff_cast
    (K : ℕ → ℕ) (n : ℕ) (hK : K (n + 1) ≤ 2 * K n) :
    (natCarryCoeff K n : ℚ) =
      carryCoeff (fun j => (K j : ℚ)) n := by
  simp [natCarryCoeff, carryCoeff, Nat.cast_sub hK]

/-! ## Denominator normal forms for rational tail recurrences -/

/-- Doubling a reduced rational removes exactly the common factor of its
denominator with `2`. -/
theorem den_two_mul (x : ℚ) :
    ((2 : ℚ) * x).den = x.den / Nat.gcd 2 x.den := by
  rw [Rat.mul_den]
  simp only [Rat.den_ofNat, Rat.num_ofNat, one_mul, Int.natAbs_mul]
  change x.den / Nat.gcd (2 * x.num.natAbs) x.den =
    x.den / Nat.gcd 2 x.den
  congr 1
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hgprod :
          Nat.gcd (2 * x.num.natAbs) x.den ∣
            2 * x.num.natAbs := Nat.gcd_dvd_left _ _
      have hgden :
          Nat.gcd (2 * x.num.natAbs) x.den ∣ x.den :=
        Nat.gcd_dvd_right _ _
      have hcop :
          Nat.Coprime (Nat.gcd (2 * x.num.natAbs) x.den)
            x.num.natAbs :=
        (x.reduced.of_dvd_right hgden).symm
      exact hcop.dvd_mul_right.mp hgprod
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact (Nat.gcd_dvd_left 2 x.den).mul_right x.num.natAbs
    · exact Nat.gcd_dvd_right _ _

/-- Exact one-step denominator dynamics for a rational dyadic tail: the next
denominator is the current denominator divided by its gcd with `2`. -/
theorem tail_den_succ
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ) :
    (T (N + 1)).den = (T N).den / Nat.gcd 2 (T N).den := by
  have hden := congrArg Rat.den (hrec N)
  simpa [den_two_mul] using hden

/-- An odd rational tail denominator is unchanged by the next recurrence
step. Since it remains odd, the same conclusion can then be iterated. -/
theorem tail_den_succ_eq_of_odd
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (hodd : Odd (T N).den) :
    (T (N + 1)).den = (T N).den := by
  rw [tail_den_succ hrec]
  rw [hodd.coprime_two_left.gcd_eq_one, Nat.div_one]

/-- An even rational tail denominator loses exactly one factor of `2` at the
next recurrence step. -/
theorem tail_den_succ_eq_half_of_even
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (heven : Even (T N).den) :
    (T (N + 1)).den = (T N).den / 2 := by
  rw [tail_den_succ hrec]
  rw [Nat.gcd_eq_left_iff_dvd.mpr (even_iff_two_dvd.mp heven)]

/-- A rational number is integral exactly when its reduced denominator is
one. -/
theorem ratIntegral_iff_den_eq_one (x : ℚ) :
    RatIntegral x ↔ x.den = 1 := by
  constructor
  · rintro ⟨z, rfl⟩
    simp
  · intro hden
    refine ⟨x.num, ?_⟩
    exact (Rat.den_eq_one_iff x).mp hden |>.symm

/-- Multiplication by a natural number clears a rational denominator exactly
when that denominator divides the multiplier. -/
theorem ratIntegral_nat_mul_iff_den_dvd (x : ℚ) (m : ℕ) :
    RatIntegral ((m : ℚ) * x) ↔ x.den ∣ m := by
  rw [ratIntegral_iff_den_eq_one]
  have hrepr :
      (m : ℚ) * x =
        ((((m : ℤ) * x.num : ℤ) : ℚ) / (x.den : ℤ)) := by
    calc
      (m : ℚ) * x =
          (m : ℚ) * ((x.num : ℚ) / (x.den : ℚ)) := by
            rw [Rat.num_div_den]
      _ = ((((m : ℤ) * x.num : ℤ) : ℚ) / (x.den : ℤ)) := by
            push_cast
            ring
  rw [hrepr, Rat.den_div_intCast_eq_one_iff _ _]
  · rw [Int.natCast_dvd]
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    exact x.reduced.symm.dvd_mul_right
  · exact Int.ofNat_ne_zero.mpr x.den_ne_zero

/-- Exact denominator classification of all integral shift lengths.  A shift
by `h` steps is integral precisely when the reduced denominator of the current
tail divides the Mersenne number `2^h - 1`. -/
theorem tailShift_integral_iff_den_dvd_mersenne
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔ (T N).den ∣ 2 ^ h - 1 := by
  rw [tailShift_integral_iff_scaledTail hrec]
  have hone : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  simpa [Nat.cast_sub hone] using
    (ratIntegral_nat_mul_iff_den_dvd (T N) (2 ^ h - 1))

/-- Congruence form of the exact shift-length classification: the integral
shifts are precisely the exponents for which `2^h` is congruent to `1` modulo
the current reduced denominator. -/
theorem tailShift_integral_iff_two_pow_modEq_one
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔
      2 ^ h ≡ 1 [MOD (T N).den] := by
  rw [tailShift_integral_iff_den_dvd_mersenne hrec]
  have hone : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  constructor
  · intro hdiv
    exact ((Nat.modEq_iff_dvd' hone).mpr hdiv).symm
  · intro hmod
    exact (Nat.modEq_iff_dvd' hone).mp hmod.symm

/-- Repeated doubling removes the entire power-of-two part of a rational
denominator.  The remaining reduced denominator is therefore odd. -/
theorem exists_twoPow_mul_odd_den (q : ℚ) :
    ∃ k : ℕ, Odd (((2 : ℚ) ^ k * q).den) := by
  obtain ⟨k, m, hm, hden⟩ :=
    Nat.exists_eq_two_pow_mul_odd q.den_ne_zero
  have hm0 : m ≠ 0 := by
    intro hmzero
    simp [hmzero] at hden
  have hdenQ : (q.den : ℚ) = (2 : ℚ) ^ k * m := by
    exact_mod_cast hden
  have hq :
      (2 : ℚ) ^ k * q = (q.num : ℚ) / (m : ℚ) := by
    calc
      (2 : ℚ) ^ k * q =
          (2 : ℚ) ^ k * ((q.num : ℚ) / (q.den : ℚ)) := by
            rw [q.num_div_den]
      _ = (q.num : ℚ) / (m : ℚ) := by
        rw [hdenQ]
        field_simp [hm0]
  have hcoprime : Nat.Coprime q.num.natAbs m := by
    exact q.reduced.of_dvd_right ⟨2 ^ k, by rw [hden, Nat.mul_comm]⟩
  refine ⟨k, ?_⟩
  rw [hq]
  have hdenm :
      ((q.num : ℚ) / (m : ℚ)).den = m := by
    have hdenmZ := Rat.den_div_eq_of_coprime
      (a := q.num) (b := (m : ℤ))
      (by simpa only [Int.natCast_pos] using Nat.pos_of_ne_zero hm0)
      (by simpa using hcoprime)
    exact_mod_cast hdenmZ
  rw [hdenm]
  exact hm

/-- Every rational-valued dyadic tail recurrence has an odd-denominator state.
The index is exactly the number of doublings needed to clear the initial
power-of-two denominator. -/
theorem exists_odd_den_state
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ N : ℕ, Odd (T N).den := by
  obtain ⟨N, hodd⟩ := exists_twoPow_mul_odd_den (T 0)
  refine ⟨N, ?_⟩
  have hstate := tail_iterate_eq_pow_mul_sub_block hrec 0 N
  have hdenEq :
      (T N).den = (((2 : ℚ) ^ N * T 0).den) := by
    simpa using congrArg Rat.den hstate
  rw [hdenEq]
  exact hodd

/-- Rationality forces one fixed positive shift to be integral from some point
onwards.  This is the rational-side obstruction paired with any
prime-specific cofinal nonintegrality theorem. -/
theorem exists_eventually_integral_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ h N : ℕ, 0 < h ∧
      ∀ k, RatIntegral (tailShift T h (N + k)) := by
  obtain ⟨N, hodd⟩ := exists_odd_den_state hrec
  let h := (T N).den.totient
  have hh : 0 < h := Nat.totient_pos.mpr (T N).den_pos
  refine ⟨h, N, hh, ?_⟩
  exact tailShift_integral_add hrec
    (tailShift_integral_totient_of_odd_den hrec N hodd)

/-! ## Real tail orbits -/

/-- Real-valued version of the dyadic tail recurrence. -/
def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

/-- Difference between two real tail states separated by `h` steps. -/
def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

/-- A real number is integral when it is the cast of an integer. -/
def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

/-- Rational orbit with prescribed initial state and integer digits. -/
def rationalDyadicOrbit (g : ℕ → ℤ) (q : ℚ) : ℕ → ℚ
  | 0 => q
  | N + 1 => 2 * rationalDyadicOrbit g q N - g (N + 1)

theorem rationalDyadicOrbit_recurrence (g : ℕ → ℤ) (q : ℚ) :
    DyadicTailRecurrence g (rationalDyadicOrbit g q) := by
  intro N
  rfl

/-- A real recurrence with rational initial state is the real cast of the
corresponding rational recurrence at every later index. -/
theorem realTail_eq_ratCast_rationalDyadicOrbit
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (q : ℚ)
    (hzero : T 0 = q) :
    ∀ N, T N = (rationalDyadicOrbit g q N : ℝ)
  | 0 => by simpa [rationalDyadicOrbit] using hzero
  | N + 1 => by
      rw [hrec N, rationalDyadicOrbit,
        realTail_eq_ratCast_rationalDyadicOrbit hrec q hzero N]
      push_cast
      rfl

/-- Cofinal failure of integral shifts for every fixed positive length. -/
def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)

/-- Cofinal nonintegrality for every fixed positive shift rules out a rational
initial state: rationality produces one fixed positive shift that is integral
at every sufficiently late index.  The converse is recorded after the
pointwise classifier below. -/
theorem irrational_initial_of_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T)
    (hescape : CofinalNonintegralTailShifts T) :
    Irrational (T 0) := by
  by_contra hnot
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hnot
  have hcast := realTail_eq_ratCast_rationalDyadicOrbit hrec q hq
  obtain ⟨h, N₀, hh, hInt⟩ :=
    exists_eventually_integral_tailShift
      (rationalDyadicOrbit_recurrence g q)
  obtain ⟨N, hN, hnon⟩ := hescape h hh N₀
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  apply hnon
  obtain ⟨z, hz⟩ := hInt k
  refine ⟨z, ?_⟩
  have hzR := congrArg ((↑) : ℚ → ℝ) hz
  simpa [realTailShift, tailShift, hcast] using hzR

/-- A finite approximation certifies nonintegrality when its error is no
larger than `R` and the approximation stays farther than `R` from every
integer. -/
theorem not_ratIntegral_of_approximation_gap
    (full approx R : ℚ)
    (herror : |full - approx| ≤ R)
    (hgap : ∀ z : ℤ, R < |approx - z|) :
    ¬ RatIntegral full := by
  rintro ⟨z, rfl⟩
  have hle : |approx - (z : ℚ)| ≤ R := by
    simpa [abs_sub_comm] using herror
  exact (not_lt_of_ge hle) (hgap z)

/-! ## Exact rationality classification for real dyadic tail orbits -/

/-- Iterating a real dyadic tail recurrence produces the same integer block as
in the rational orbit. -/
theorem real_tail_iterate_eq_pow_mul_sub_block
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h := by
  induction h with
  | zero => simp [dyadicTailBlock]
  | succ h ih =>
      rw [show N + (h + 1) = (N + h) + 1 by omega, hrec (N + h), ih]
      simp only [dyadicTailBlock, pow_succ]
      push_cast
      ring

/-- A real tail difference is a nonzero integer multiple of its initial state,
up to the explicit integer block. -/
theorem realTailShift_eq_scaled_sub_block
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    realTailShift T h N =
      ((2 ^ h : ℝ) - 1) * T N - dyadicTailBlock g N h := by
  rw [realTailShift, real_tail_iterate_eq_pow_mul_sub_block hrec]
  ring

/-- Exact classifier for an integer-digit dyadic tail orbit: the initial state
is rational if and only if one positive-length tail difference is integral.
For a rational state, choose `h` so that the Mersenne multiplier `2^h - 1`
clears the odd part of its denominator.  Conversely, the block identity has
nonzero multiplier `2^h - 1`, so one integral shift recovers rationality. -/
theorem not_irrational_initial_iff_exists_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N) := by
  constructor
  · intro hrat
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
    have hcast := realTail_eq_ratCast_rationalDyadicOrbit hrec q hq
    obtain ⟨h, N, hh, hInt⟩ :=
      exists_eventually_integral_tailShift
        (rationalDyadicOrbit_recurrence g q)
    refine ⟨h, N, hh, ?_⟩
    obtain ⟨z, hz⟩ := hInt 0
    refine ⟨z, ?_⟩
    have hzR := congrArg ((↑) : ℚ → ℝ) hz
    simpa [realTailShift, tailShift, hcast] using hzR
  · rintro ⟨h, N, hh, z, hz⟩
    have hpowNat : 1 < 2 ^ h := Nat.one_lt_two_pow hh.ne'
    have hpowR : (1 : ℝ) < (2 : ℝ) ^ h := by exact_mod_cast hpowNat
    have hfactor : (2 : ℝ) ^ h - 1 ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt hpowR)
    let qN : ℚ :=
      ((z + dyadicTailBlock g N h : ℤ) : ℚ) / ((2 : ℚ) ^ h - 1)
    have hTN : T N = (qN : ℝ) := by
      rw [realTailShift_eq_scaled_sub_block hrec] at hz
      dsimp [qN]
      push_cast
      field_simp [hfactor]
      linarith
    let q0 : ℚ :=
      (qN + dyadicTailBlock g 0 N) / (2 : ℚ) ^ N
    have hpow0 : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
    have hT0 : T 0 = (q0 : ℝ) := by
      have hiterate := real_tail_iterate_eq_pow_mul_sub_block hrec 0 N
      simp only [Nat.zero_add] at hiterate
      dsimp [q0]
      push_cast
      field_simp [hpow0]
      rw [hTN] at hiterate
      linarith
    rw [hT0]
    exact q0.not_irrational

/-- Equivalent eventual form of the classifier: rationality is exactly the
existence of a fixed positive shift that is integral at every later index. -/
theorem not_irrational_initial_iff_exists_eventually_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧
        ∀ k, RealIntegral (realTailShift T h (N + k)) := by
  constructor
  · intro hrat
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
    have hcast := realTail_eq_ratCast_rationalDyadicOrbit hrec q hq
    obtain ⟨h, N, hh, hInt⟩ :=
      exists_eventually_integral_tailShift
        (rationalDyadicOrbit_recurrence g q)
    refine ⟨h, N, hh, fun k => ?_⟩
    obtain ⟨z, hz⟩ := hInt k
    refine ⟨z, ?_⟩
    have hzR := congrArg ((↑) : ℚ → ℝ) hz
    simpa [realTailShift, tailShift, hcast] using hzR
  · rintro ⟨h, N, hh, hInt⟩
    exact
      (not_irrational_initial_iff_exists_integral_positive_tailShift hrec).2
        ⟨h, N, hh, hInt 0⟩

/-- Exact irrationality normal form: an integer-digit dyadic tail starts at an
irrational value exactly when none of its positive-length tail differences is
an integer. -/
theorem irrational_initial_iff_all_positive_tailShifts_nonintegral
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        ¬ RealIntegral (realTailShift T h N) := by
  constructor
  · intro hirr h hh N hInt
    exact
      (not_irrational_initial_iff_exists_integral_positive_tailShift hrec).2
        ⟨h, N, hh, hInt⟩ hirr
  · intro hnone
    by_contra hrat
    obtain ⟨h, N, hh, hInt⟩ :=
      (not_irrational_initial_iff_exists_integral_positive_tailShift hrec).1 hrat
    exact hnone h hh N hInt

/-- Exact cofinal form of the irrationality classifier.  For an integer-digit
dyadic tail recurrence, irrationality of the initial state is equivalent to
finding, beyond every basepoint, a nonintegral tail difference of each fixed
positive length. -/
theorem irrational_initial_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalNonintegralTailShifts T := by
  constructor
  · intro hirr h hh N₀
    refine ⟨N₀, le_rfl, ?_⟩
    exact
      (irrational_initial_iff_all_positive_tailShifts_nonintegral hrec).1
        hirr h hh N₀
  · exact irrational_initial_of_cofinalNonintegralTailShifts hrec

/-! ## Polynomial-gap countermodel to coarse prime-gap inputs -/

/-- A positive even polynomial gap word.  It is not the actual prime-gap word;
it is an exact stress test for attempts using only coarse gap properties. -/
def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)

/-- The rational polynomial tail orbit paired with `polynomialGapWord`. -/
def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)

/-- The polynomial word and orbit obey the exact dyadic tail recurrence. -/
theorem polynomialTailOrbit_recurrence :
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit := by
  intro N
  simp only [polynomialGapWord, polynomialTailOrbit]
  push_cast
  ring

/-- Every polynomial countermodel gap is positive. -/
theorem polynomialGapWord_pos (n : ℕ) : 0 < polynomialGapWord n := by
  simp [polynomialGapWord]
  positivity

/-- Every polynomial countermodel gap is even. -/
theorem polynomialGapWord_even (n : ℕ) : ∃ k : ℤ, polynomialGapWord n = 2 * k := by
  refine ⟨(n ^ 2 + 4 * n + 2 : ℕ), ?_⟩
  simp [polynomialGapWord]

/-- Adjacent differences grow linearly and in particular never equal `±2`. -/
theorem polynomialGapWord_succ_sub (n : ℕ) :
    polynomialGapWord (n + 1) - polynomialGapWord n = ((4 * n + 10 : ℕ) : ℤ) := by
  simp only [polynomialGapWord]
  push_cast
  ring

theorem polynomialGapWord_adjacent_difference_ne_two (n : ℕ) :
    polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 := by
  rw [polynomialGapWord_succ_sub]
  omega

theorem polynomialGapWord_adjacent_difference_ne_neg_two (n : ℕ) :
    polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2 := by
  rw [polynomialGapWord_succ_sub]
  omega

/-- The word is strictly increasing, hence unbounded and not eventually
periodic; this is stronger than merely inserting isolated large gaps. -/
theorem polynomialGapWord_strictMono : StrictMono polynomialGapWord := by
  exact strictMono_nat_of_lt_succ fun n => by
    have h := polynomialGapWord_succ_sub n
    omega

/-- Every tail state is integral, so every fixed tail shift is integral. -/
theorem polynomialTailOrbit_integral (n : ℕ) : RatIntegral (polynomialTailOrbit n) := by
  refine ⟨(2 * (n + 4) ^ 2 : ℕ), ?_⟩
  simp [polynomialTailOrbit]

/-- The `h=1` digit required by an adjacent small-mismatch certificate is
never `±2` in this rational, positive, even, polynomially growing orbit. -/
theorem polynomialGapWord_no_adjacent_two_digit (N : ℕ) :
    polynomialGapWord (N + 2) - polynomialGapWord (N + 1) ≠ 2 ∧
      polynomialGapWord (N + 2) - polynomialGapWord (N + 1) ≠ -2 := by
  constructor
  · simpa [Nat.add_assoc] using polynomialGapWord_adjacent_difference_ne_two (N + 1)
  · simpa [Nat.add_assoc] using polynomialGapWord_adjacent_difference_ne_neg_two (N + 1)

/-- Every fixed tail shift of the polynomial countermodel is integral.  This
is the consumer-ready obstruction: positivity, evenness, strict growth, and
the dyadic recurrence do not force a nonintegral shift. -/
theorem polynomialTailOrbit_shift_integral (h N : ℕ) :
    RatIntegral (tailShift polynomialTailOrbit h N) := by
  rw [tailShift_integral_iff_scaledTail polynomialTailOrbit_recurrence]
  rcases polynomialTailOrbit_integral N with ⟨z, hz⟩
  refine ⟨(2 ^ h - 1) * z, ?_⟩
  rw [hz]
  push_cast
  ring

#print axioms polynomialTailOrbit_shift_integral

end ErdosProblems.Erdos251
