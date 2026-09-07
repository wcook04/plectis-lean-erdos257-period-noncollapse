import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Erdős #1049: finite q-binomial algebra for the 2004 small-p unit

Zudilin, Acta Arith. 111 (2004), displays (8)–(11).  After the published
integrality exponent `M` is removed, the second source coefficient is a
unit at `p = 0`.  The new algebra is the finite q-binomial theorem, the
vanishing range for exponents that hit `1`, and the constant term of
`(q^α; q)_n` for `α ≥ 1`.  This module Lean-checks those identities.  It
does not construct the source sums `A(p), B(p)`, does not prove
irrationality of `F(3/2)`, and is not the 2016 Hankel family.

The Gaussian binomial uses the same Pascal recurrence as
`AdelicHeightBridge.zudilinQBinomialPS`, as a ring element rather than a
power series.
-/

open scoped BigOperators
open Finset Polynomial

namespace ErdosProblems.Erdos1049

variable {R : Type*} [CommRing R]

/-! ## q-Pochhammer and Gaussian binomials -/

/-- Finite q-Pochhammer `(z; q)_n = ∏_{i=0}^{n-1} (1 - z q^i)`. -/
def qPochhammer (q z : R) : ℕ → R
  | 0 => 1
  | n + 1 => qPochhammer q z n * (1 - z * q ^ n)

@[simp] theorem qPochhammer_zero (q z : R) : qPochhammer q z 0 = 1 := rfl

theorem qPochhammer_succ (q z : R) (n : ℕ) :
    qPochhammer q z (n + 1) = qPochhammer q z n * (1 - z * q ^ n) := rfl

/-- If a displayed factor is `1 - 1`, the product vanishes. -/
theorem qPochhammer_eq_zero_of_exists (q z : R) {n i : ℕ}
    (hi : i < n) (hzi : z * q ^ i = 1) :
    qPochhammer q z n = 0 := by
  induction n with
  | zero => exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
      rw [qPochhammer]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [ih hlt, zero_mul]
      · simp [hzi]

/-- `(1; q)_n = 0` for `n > 0`.  Nonnegative-exponent form of the vanishing
range when `1 - r + h = 0`. -/
theorem qPochhammer_one (q : R) {n : ℕ} (hn : 0 < n) :
    qPochhammer q (1 : R) n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact qPochhammer_eq_zero_of_exists q 1 (Nat.zero_lt_succ m) (by simp)

/-- Polynomial form of the vanishing range: if `u < n` then the factor
`i = u` is zero.  Clearing `q^{u n}` in `(q^{-u}; q)_n` produces this product. -/
theorem prod_pow_sub_pow_eq_zero (q : R) {u n : ℕ} (h : u < n) :
    ∏ i ∈ range n, (q ^ u - q ^ i) = 0 :=
  prod_eq_zero (mem_range.mpr h) (sub_self _)

/-- Gaussian binomial by the Pascal recurrence
`[n+1 choose k+1]_q = [n choose k+1]_q + q^{n-k} [n choose k]_q`. -/
def gaussBinom (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0

@[simp] theorem gaussBinom_zero_right (q : R) :
    ∀ n, gaussBinom q n 0 = 1
  | 0 => rfl
  | _n + 1 => rfl

@[simp] theorem gaussBinom_zero_succ (q : R) (k : ℕ) :
    gaussBinom q 0 (k + 1) = 0 := rfl

theorem gaussBinom_succ (q : R) (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) =
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0 := rfl

theorem gaussBinom_eq_zero_of_lt (q : R) : ∀ {n k : ℕ}, n < k → gaussBinom q n k = 0
  | 0, 0, h => (Nat.lt_irrefl 0 h).elim
  | 0, k + 1, _ => rfl
  | n + 1, 0, h => (Nat.not_lt_zero _ h).elim
  | n + 1, k + 1, h => by
      have h1 : n < k + 1 := Nat.lt_of_succ_lt_succ (Nat.lt_succ_of_lt h)
      have h2 : ¬ k ≤ n := Nat.not_le.mpr (Nat.lt_of_succ_lt_succ h)
      rw [gaussBinom_succ, gaussBinom_eq_zero_of_lt q h1, if_neg h2, add_zero]

theorem gaussBinom_self (q : R) : ∀ n, gaussBinom q n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [gaussBinom_succ, gaussBinom_eq_zero_of_lt q (Nat.lt_succ_self n),
        if_pos le_rfl, gaussBinom_self q n, Nat.sub_self, pow_zero, one_mul,
        zero_add]

theorem gaussBinom_succ_of_le (q : R) {n j : ℕ} (hj : j ≤ n) :
    gaussBinom q (n + 1) (j + 1) =
      gaussBinom q n (j + 1) + q ^ (n - j) * gaussBinom q n j := by
  rw [gaussBinom_succ, if_pos hj]

theorem choose_two_succ (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  rw [show (j + 1).choose 2 = j.choose 1 + j.choose 2 from Nat.choose_succ_succ j 1,
    Nat.choose_one_right]
  omega

lemma sum_range_zero_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ∑ k ∈ range (n + 1), f k = f 0 + ∑ j ∈ range n, f (j + 1)
  | 0 => by simp
  | n + 1 => by
      rw [sum_range_succ, sum_range_zero_add f n, sum_range_succ, add_assoc]

/-! ## Finite q-binomial theorem -/

/-- The summand of `(z; q)_n = ∑_k [n choose k]_q (-1)^k q^{binom k 2} z^k`. -/
def qBinomialTerm (q z : R) (n k : ℕ) : R :=
  gaussBinom q n k * (-1 : R) ^ k * q ^ k.choose 2 * z ^ k

theorem qBinomialTerm_zero (q z : R) (n : ℕ) : qBinomialTerm q z n 0 = 1 := by
  simp [qBinomialTerm]

theorem qBinomialTerm_of_lt (q z : R) {n k : ℕ} (h : n < k) :
    qBinomialTerm q z n k = 0 := by
  simp [qBinomialTerm, gaussBinom_eq_zero_of_lt q h]

theorem qBinomialTerm_succ_split (q z : R) {n j : ℕ} (hj : j ≤ n) :
    qBinomialTerm q z (n + 1) (j + 1) =
      qBinomialTerm q z n (j + 1) +
        gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
          q ^ (j + 1).choose 2 * z ^ (j + 1) := by
  rw [qBinomialTerm, qBinomialTerm, gaussBinom_succ_of_le q hj]
  ring

theorem qBinomialTerm_shift_eq (q z : R) {n j : ℕ} (hj : j ≤ n) :
    gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
        q ^ (j + 1).choose 2 * z ^ (j + 1) =
      -z * q ^ n * qBinomialTerm q z n j := by
  have hpow : q ^ (n - j) * q ^ (j.choose 2 + j) = q ^ n * q ^ j.choose 2 := by
    rw [← pow_add, ← pow_add]
    congr 1
    have : n - j + j = n := Nat.sub_add_cancel hj
    omega
  simp only [qBinomialTerm, choose_two_succ, pow_succ]
  calc
    gaussBinom q n j * ((-1 : R) ^ j * -1) * q ^ (n - j) *
          q ^ (j.choose 2 + j) * (z ^ j * z) =
        gaussBinom q n j * (-1 : R) ^ j *
          (q ^ (n - j) * q ^ (j.choose 2 + j)) * z ^ j * -z := by
      ring
    _ = gaussBinom q n j * (-1 : R) ^ j * (q ^ n * q ^ j.choose 2) * z ^ j * -z := by
      rw [hpow]
    _ = -z * q ^ n * (gaussBinom q n j * (-1 : R) ^ j * q ^ j.choose 2 * z ^ j) := by
      ring

set_option maxHeartbeats 400000 in
/-- Finite q-binomial theorem.  Generating-function engine of Type B r4 (2.3). -/
theorem qPochhammer_eq_sum (q z : R) : ∀ n,
    qPochhammer q z n = ∑ k ∈ range (n + 1), qBinomialTerm q z n k
  | 0 => by
      simp [qPochhammer, qBinomialTerm]
  | n + 1 => by
      have ih := qPochhammer_eq_sum q z n
      have hA :
          ∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) =
            qPochhammer q z n - 1 := by
        have hshift := sum_range_zero_add (qBinomialTerm q z n) (n + 1)
        have hlast : qBinomialTerm q z n (n + 1) = 0 :=
          qBinomialTerm_of_lt q z (Nat.lt_succ_self n)
        have hsum :
            ∑ k ∈ range (n + 2), qBinomialTerm q z n k =
              ∑ k ∈ range (n + 1), qBinomialTerm q z n k := by
          rw [sum_range_succ, hlast, add_zero]
        have hn2 : n + 1 + 1 = n + 2 := by omega
        have hshift' :
            ∑ k ∈ range (n + 2), qBinomialTerm q z n k =
              qBinomialTerm q z n 0 +
                ∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) := by
          simpa [hn2] using hshift
        have h : qPochhammer q z n =
            1 + ∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) := by
          rw [ih, ← hsum, hshift', qBinomialTerm_zero]
        exact eq_sub_of_add_eq (by simpa [add_comm] using h.symm)
      have hB :
          ∑ j ∈ range (n + 1),
              gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                q ^ (j + 1).choose 2 * z ^ (j + 1) =
            -z * q ^ n * qPochhammer q z n := by
        have hcong :
            ∑ j ∈ range (n + 1),
                gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                  q ^ (j + 1).choose 2 * z ^ (j + 1) =
              ∑ j ∈ range (n + 1), -z * q ^ n * qBinomialTerm q z n j := by
          refine sum_congr rfl ?_
          intro j hj
          exact qBinomialTerm_shift_eq q z (Nat.lt_succ_iff.mp (mem_range.mp hj))
        rw [hcong, ← mul_sum, ih]
      have hsucc :
          ∑ j ∈ range (n + 1), qBinomialTerm q z (n + 1) (j + 1) =
            ∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) +
              ∑ j ∈ range (n + 1),
                gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                  q ^ (j + 1).choose 2 * z ^ (j + 1) := by
        have hcong :
            ∑ j ∈ range (n + 1), qBinomialTerm q z (n + 1) (j + 1) =
              ∑ j ∈ range (n + 1),
                (qBinomialTerm q z n (j + 1) +
                  gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                    q ^ (j + 1).choose 2 * z ^ (j + 1)) := by
          refine sum_congr rfl ?_
          intro j hj
          exact qBinomialTerm_succ_split q z (Nat.lt_succ_iff.mp (mem_range.mp hj))
        rw [hcong, sum_add_distrib]
      rw [qPochhammer]
      calc
        qPochhammer q z n * (1 - z * q ^ n) =
            qPochhammer q z n - z * q ^ n * qPochhammer q z n := by ring
        _ = 1 + ((qPochhammer q z n - 1) + -z * q ^ n * qPochhammer q z n) := by
            ring
        _ = qBinomialTerm q z (n + 1) 0 +
              (∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) +
                ∑ j ∈ range (n + 1),
                  gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                    q ^ (j + 1).choose 2 * z ^ (j + 1)) := by
            rw [qBinomialTerm_zero, hA, hB]
        _ = qBinomialTerm q z (n + 1) 0 +
              ∑ j ∈ range (n + 1), qBinomialTerm q z (n + 1) (j + 1) := by
            rw [hsucc]
        _ = ∑ k ∈ range (n + 2), qBinomialTerm q z (n + 1) k := by
            have hn2 : n + 1 + 1 = n + 2 := by omega
            simpa [hn2] using
              (sum_range_zero_add (qBinomialTerm q z (n + 1)) (n + 1)).symm

/-! ## Splitting `(q;q)_{m+k}` and the constant term at the small-p endpoint -/

theorem qPochhammer_q_add (q : R) (m : ℕ) : ∀ k,
    qPochhammer q q (m + k) =
      qPochhammer q q m * qPochhammer q (q ^ (m + 1)) k
  | 0 => by simp [qPochhammer]
  | k + 1 => by
      rw [Nat.add_succ, qPochhammer, qPochhammer_q_add q m k, qPochhammer,
        mul_assoc]
      congr 1
      simp [pow_succ, pow_add, mul_assoc, mul_comm]

lemma qPochhammer_X_constantCoeff :
    ∀ m, constantCoeff (qPochhammer (X : ℤ[X]) X m) = 1
  | 0 => by simp [qPochhammer]
  | m + 1 => by
      rw [qPochhammer, map_mul, qPochhammer_X_constantCoeff m, one_mul]
      change ((1 - X * X ^ m : ℤ[X]).coeff 0) = 1
      have hpow : X * X ^ m = (X : ℤ[X]) ^ (m + 1) := (pow_succ' (X : ℤ[X]) m).symm
      rw [coeff_sub, coeff_one, hpow, coeff_X_pow]
      simp

lemma qPochhammer_X_ne_zero (m : ℕ) :
    qPochhammer (X : ℤ[X]) X m ≠ 0 := by
  intro h
  have h1 := qPochhammer_X_constantCoeff m
  rw [h, map_zero] at h1
  exact one_ne_zero h1.symm

/-- Constant term of `(q^α; q)_n` is `1` whenever `α ≥ 1`.  This is the
constant contribution of `T_l` for `l ≤ t` in the source expansion (2.4). -/
theorem qPochhammer_Xpow_constantCoeff {α : ℕ} (hα : 0 < α) :
    ∀ n, constantCoeff (qPochhammer (X : ℤ[X]) (X ^ α) n) = 1
  | 0 => by simp [qPochhammer]
  | n + 1 => by
      rw [qPochhammer, map_mul, qPochhammer_Xpow_constantCoeff hα n, one_mul]
      have hne : α + n ≠ 0 := (Nat.add_pos_left hα n).ne'
      change ((1 - X ^ α * X ^ n : ℤ[X]).coeff 0) = 1
      have hpow : X ^ α * X ^ n = (X : ℤ[X]) ^ (α + n) := by rw [← pow_add]
      rw [coeff_sub, coeff_one, hpow, coeff_X_pow, if_neg hne.symm]
      simp

/-! ## Gaussian binomial times `(q;q)_k` -/

theorem gaussBinom_mul_qPochhammer_qPochhammer (q : R) :
    ∀ n k, k ≤ n →
      gaussBinom q n k * qPochhammer q q k * qPochhammer q q (n - k) =
        qPochhammer q q n
  | 0, k, hk => by
      have : k = 0 := Nat.le_zero.mp hk
      subst this
      simp [qPochhammer]
  | n + 1, 0, _hk => by simp [qPochhammer]
  | n + 1, k + 1, hk => by
      have hk' : k ≤ n := Nat.succ_le_succ_iff.mp hk
      by_cases hkn : k + 1 ≤ n
      · have ih1 := gaussBinom_mul_qPochhammer_qPochhammer q n (k + 1) hkn
        have ih0 := gaussBinom_mul_qPochhammer_qPochhammer q n k
            (Nat.le_of_succ_le hkn)
        have hrec := gaussBinom_succ_of_le q hk'
        have hnk : n + 1 - (k + 1) = n - k := Nat.succ_sub_succ n k
        have hright :
            qPochhammer q q (n - k) =
              qPochhammer q q (n - (k + 1)) * (1 - q ^ (n - k)) := by
          have hdecomp : n - k = n - (k + 1) + 1 := by omega
          rw [hdecomp, qPochhammer]
          congr 1
          rw [← pow_succ']
        rw [hrec, hnk, add_mul, add_mul]
        have h1 :
            gaussBinom q n (k + 1) * qPochhammer q q (k + 1) *
                qPochhammer q q (n - k) =
              qPochhammer q q n * (1 - q ^ (n - k)) := by
          rw [hright]
          calc
            gaussBinom q n (k + 1) * qPochhammer q q (k + 1) *
                  (qPochhammer q q (n - (k + 1)) * (1 - q ^ (n - k))) =
                gaussBinom q n (k + 1) * qPochhammer q q (k + 1) *
                    qPochhammer q q (n - (k + 1)) * (1 - q ^ (n - k)) := by
              ring
            _ = qPochhammer q q n * (1 - q ^ (n - k)) := by
              rw [ih1]
        have h2 :
            q ^ (n - k) * gaussBinom q n k * qPochhammer q q (k + 1) *
                qPochhammer q q (n - k) =
              q ^ (n - k) * (1 - q ^ (k + 1)) * qPochhammer q q n := by
          rw [qPochhammer_succ, ← pow_succ']
          calc
            q ^ (n - k) * gaussBinom q n k *
                  (qPochhammer q q k * (1 - q ^ (k + 1))) *
                  qPochhammer q q (n - k) =
                q ^ (n - k) * (1 - q ^ (k + 1)) *
                  (gaussBinom q n k * qPochhammer q q k *
                    qPochhammer q q (n - k)) := by
              ring
            _ = q ^ (n - k) * (1 - q ^ (k + 1)) * qPochhammer q q n := by
              rw [ih0]
        rw [h1, h2, qPochhammer]
        have hpow : q ^ (n - k) * q ^ (k + 1) = q ^ (n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hq1 : q * q ^ n = q ^ (n + 1) := (pow_succ' q n).symm
        rw [hq1, ← hpow]
        ring
      · have hkEq : k = n := le_antisymm hk' (by omega)
        subst hkEq
        simp [gaussBinom_self, qPochhammer]

theorem gaussBinom_mul_qPochhammer_X {n k : ℕ} (h : k ≤ n) :
    gaussBinom (X : ℤ[X]) n k * qPochhammer X X k =
      qPochhammer X (X ^ (n - k + 1)) k := by
  have hfac := gaussBinom_mul_qPochhammer_qPochhammer (X : ℤ[X]) n k h
  have hsplit := qPochhammer_q_add (X : ℤ[X]) (n - k) k
  have hn : n - k + k = n := Nat.sub_add_cancel h
  apply mul_right_cancel₀ (qPochhammer_X_ne_zero (n - k))
  calc
    gaussBinom (X : ℤ[X]) n k * qPochhammer X X k * qPochhammer X X (n - k) =
        qPochhammer X X n := hfac
    _ = qPochhammer X X (n - k + k) := by rw [hn]
    _ = qPochhammer X X (n - k) * qPochhammer X (X ^ (n - k + 1)) k := hsplit
    _ = qPochhammer X (X ^ (n - k + 1)) k * qPochhammer X X (n - k) := mul_comm _ _

lemma eval₂_gaussBinom (q : R) : ∀ n k,
    eval₂ (Int.castRingHom R) q (gaussBinom (X : ℤ[X]) n k) = gaussBinom q n k
  | 0, 0 => by simp [gaussBinom]
  | 0, k + 1 => by simp [gaussBinom]
  | n + 1, 0 => by simp [gaussBinom]
  | n + 1, k + 1 => by
      rw [gaussBinom_succ, gaussBinom_succ, eval₂_add]
      split_ifs with h
      · rw [eval₂_mul, eval₂_pow, eval₂_X, eval₂_gaussBinom q n (k + 1),
          eval₂_gaussBinom q n k]
      · rw [eval₂_zero, eval₂_gaussBinom q n (k + 1)]

lemma eval₂_qPochhammer_X (q : R) : ∀ n,
    eval₂ (Int.castRingHom R) q (qPochhammer (X : ℤ[X]) X n) = qPochhammer q q n
  | 0 => by simp [qPochhammer]
  | n + 1 => by
      rw [qPochhammer, qPochhammer, eval₂_mul, eval₂_sub, eval₂_one, eval₂_mul,
        eval₂_pow, eval₂_X, eval₂_qPochhammer_X q n]

lemma eval₂_qPochhammer_Xpow (q : R) (m : ℕ) : ∀ n,
    eval₂ (Int.castRingHom R) q (qPochhammer X (X ^ m) n) =
      qPochhammer q (q ^ m) n
  | 0 => by simp [qPochhammer]
  | n + 1 => by
      rw [qPochhammer, qPochhammer, eval₂_mul, eval₂_sub, eval₂_one, eval₂_mul,
        eval₂_X_pow, eval₂_X_pow, eval₂_qPochhammer_Xpow q m n]

/-- Gaussian binomial times `(q;q)_k` recovers the truncated Pochhammer.
Division-free form of `{n \choose k}_q = (q^{n-k+1};q)_k / (q;q)_k`. -/
theorem gaussBinom_mul_qPochhammer (q : R) {n k : ℕ} (h : k ≤ n) :
    gaussBinom q n k * qPochhammer q q k =
      qPochhammer q (q ^ (n - k + 1)) k := by
  have hp := gaussBinom_mul_qPochhammer_X h
  have := congrArg (eval₂ (Int.castRingHom R) q) hp
  simpa [eval₂_mul, eval₂_gaussBinom, eval₂_qPochhammer_X,
    eval₂_qPochhammer_Xpow] using this

/-! ## Source identity (2.3), cleared of `(q;q)_{a-1}` -/

/-- Inner generating function `T` of Type B r4 (2.2), with nonnegative
exponent `α = t + 1 - l`. -/
def sourceInnerT (q : R) (a d v α : ℕ) : R :=
  ∑ j ∈ range v,
    (-1 : R) ^ j * q ^ (j.choose 2 + α * j) *
      gaussBinom q (v - 1) j * gaussBinom q (a + d + j - 1) (a - 1)

set_option maxHeartbeats 400000 in
/-- Cleared form of Type B r4 (2.3). -/
theorem sourceInnerT_qPochhammer (q : R) {a d v α : ℕ}
    (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer q q (a - 1) * sourceInnerT q a d v α =
      ∑ h ∈ range a,
        (-1 : R) ^ h * q ^ (h * (d + 1) + h.choose 2) *
          gaussBinom q (a - 1) h *
          qPochhammer q (q ^ (α + h)) (v - 1) := by
  unfold sourceInnerT
  rw [mul_sum]
  have hleft :
      ∑ j ∈ range v,
          qPochhammer q q (a - 1) *
            ((-1 : R) ^ j * q ^ (j.choose 2 + α * j) *
              gaussBinom q (v - 1) j * gaussBinom q (a + d + j - 1) (a - 1)) =
        ∑ j ∈ range v,
          (-1 : R) ^ j * q ^ (j.choose 2 + α * j) * gaussBinom q (v - 1) j *
            qPochhammer q (q ^ (d + j + 1)) (a - 1) := by
    refine sum_congr rfl ?_
    intro j _hj
    have hle : a - 1 ≤ a + d + j - 1 := by omega
    have hidx : a + d + j - 1 - (a - 1) + 1 = d + j + 1 := by omega
    have hg := gaussBinom_mul_qPochhammer q hle
    rw [hidx] at hg
    rw [← hg]
    ring
  rw [hleft]
  have hexp :
      ∑ j ∈ range v,
          (-1 : R) ^ j * q ^ (j.choose 2 + α * j) * gaussBinom q (v - 1) j *
            qPochhammer q (q ^ (d + j + 1)) (a - 1) =
        ∑ j ∈ range v,
          ∑ h ∈ range a, (-1 : R) ^ j * q ^ (j.choose 2 + α * j) *
            gaussBinom q (v - 1) j * qBinomialTerm q (q ^ (d + j + 1)) (a - 1) h := by
    refine sum_congr rfl ?_
    intro j _hj
    have ha' : a - 1 + 1 = a := Nat.sub_add_cancel ha
    rw [qPochhammer_eq_sum, ha', mul_sum]
  rw [hexp, Finset.sum_comm]
  refine sum_congr rfl ?_
  intro h _hh
  have hv' : v - 1 + 1 = v := Nat.sub_add_cancel hv
  have hfactor :
      ∑ j ∈ range v,
          (-1 : R) ^ j * q ^ (j.choose 2 + α * j) * gaussBinom q (v - 1) j *
            qBinomialTerm q (q ^ (d + j + 1)) (a - 1) h =
        (-1 : R) ^ h * q ^ (h * (d + 1) + h.choose 2) * gaussBinom q (a - 1) h *
          ∑ j ∈ range v, qBinomialTerm q (q ^ (α + h)) (v - 1) j := by
    have hcong :
        ∑ j ∈ range v,
            (-1 : R) ^ j * q ^ (j.choose 2 + α * j) * gaussBinom q (v - 1) j *
              qBinomialTerm q (q ^ (d + j + 1)) (a - 1) h =
          ∑ j ∈ range v,
            (-1 : R) ^ h * q ^ (h * (d + 1) + h.choose 2) * gaussBinom q (a - 1) h *
              qBinomialTerm q (q ^ (α + h)) (v - 1) j := by
      refine sum_congr rfl ?_
      intro j _hj
      simp [qBinomialTerm, pow_add, pow_mul, mul_pow, pow_one]
      ring
    rw [hcong, ← mul_sum]
  have hpoch :
      ∑ j ∈ range v, qBinomialTerm q (q ^ (α + h)) (v - 1) j =
        qPochhammer q (q ^ (α + h)) (v - 1) := by
    simpa [hv'] using (qPochhammer_eq_sum q (q ^ (α + h)) (v - 1)).symm
  rw [hfactor, hpoch]

end ErdosProblems.Erdos1049
