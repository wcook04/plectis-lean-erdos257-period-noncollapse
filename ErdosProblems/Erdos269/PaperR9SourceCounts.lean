import ErdosProblems.Erdos269.DyadicBlockThresholdPartition
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Exact source-count normalisation for certificate reconstruction

This module does not certify a generated list by fiat. It starts with the
library's actual strictSmoothPairs / strictSmoothExponents and proves the
one-dimensional pair count, cumulative pure-power count, threshold difference,
and complete ordered dyadic digit formula.

The executable pair evaluator uses successive division. It does not enumerate
a box of side `x` or compute real logarithms. Its boundary sweep is linear in the two exponent bounds. No unproved
logarithmic-interval or Euclidean floor-sum optimisation is used by this return.

Source APIs reused: RestrictedFloorSum.lean, strictSmoothShell_card,
restrictedPurePowerCount_eq_restrictedLogFloorSum, restrictedLogFloorSum_succ_sub;
Mathlib/Data/Nat/Log.lean; Lean src/Init/Data/Nat/Div/Basic.lean.
Finset.card_eq_sum_card_fiberwise is reused exactly as in the supplied
RestrictedFloorSum.lean:332.
All new proofs remain uncompiled.
-/
namespace ErdosProblems.Erdos269.PaperR9
open Finset

/-- The redundant source exponent bounds impose no additional restriction. -/
theorem mem_strictSmoothPairs_iff {q r x : ℕ} (hq : 1 < q) (hr : 1 < r)
    (e : ℕ × ℕ) :
    e ∈ strictSmoothPairs q r x ↔ q ^ e.1 * r ^ e.2 < x := by
  constructor
  · exact fun he => (mem_filter.mp he).2
  · intro h
    have hprod : 0 < q ^ e.1 * r ^ e.2 := by positivity
    have hqpow : q ^ e.1 ≤ q ^ e.1 * r ^ e.2 :=
      Nat.le_of_dvd hprod ⟨r ^ e.2, rfl⟩
    have hrpow : r ^ e.2 ≤ q ^ e.1 * r ^ e.2 :=
      Nat.le_of_dvd hprod ⟨q ^ e.1, by ring⟩
    have hi : e.1 < x := (Nat.lt_pow_self hq).trans_le (hqpow.trans h.le)
    have hj : e.2 < x := (Nat.lt_pow_self hr).trans_le (hrpow.trans h.le)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hi, mem_range.mpr hj⟩, h⟩

/-- Strict cutoffs are handled by `x-1`, so this formula also handles exact
prime-power coincidences correctly. No independence hypothesis is needed. -/
def pairCountFast (q r x : ℕ) : ℕ :=
  if x ≤ 1 then 0 else
    ∑ i ∈ range (Nat.log q (x - 1) + 1),
      (Nat.log r ((x - 1) / q ^ i) + 1)

theorem pairCountFast_correct {q r x : ℕ} (hq : 1 < q) (hr : 1 < r) :
    pairCountFast q r x = (strictSmoothPairs q r x).card := by
  classical
  by_cases hx : x ≤ 1
  · have hempty : strictSmoothPairs q r x = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      have he' := (mem_strictSmoothPairs_iff hq hr e).mp he
      have hp : 0 < q ^ e.1 * r ^ e.2 := by positivity
      omega
    simp [pairCountFast, hx, hempty]
  have hx1 : 1 < x := by omega
  have hN : x - 1 ≠ 0 := by omega
  let I := Nat.log q (x - 1)
  have hfirst : ∀ e ∈ strictSmoothPairs q r x, e.1 ≤ I := by
    intro e he
    have he' := (mem_strictSmoothPairs_iff hq hr e).mp he
    have hprod : 0 < q ^ e.1 * r ^ e.2 := by positivity
    have hpow := Nat.le_of_dvd hprod (show q ^ e.1 ∣ q ^ e.1 * r ^ e.2 from ⟨r ^ e.2, rfl⟩)
    apply Nat.le_log_of_pow_le hq
    omega
  have hquot : ∀ i ∈ range (I + 1), 0 < (x - 1) / q ^ i := by
    intro i hi
    have hi' : i ≤ I := by simpa only [mem_range, Nat.lt_succ_iff] using hi
    have hpow : q ^ i ≤ x - 1 := Nat.pow_le_of_le_log hN hi'
    exact Nat.div_pos hpow (by positivity)
  have hcard : (strictSmoothPairs q r x).card =
      ∑ i ∈ range (I + 1), ((strictSmoothPairs q r x).filter (fun e => e.1 = i)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro e he
    exact mem_range.mpr (Nat.lt_succ_of_le (hfirst e he))
  rw [pairCountFast, if_neg hx, hcard]
  change (∑ i ∈ range (I + 1), (Nat.log r ((x - 1) / q ^ i) + 1)) = _
  refine Finset.sum_congr (s₁ := range (I + 1)) (s₂ := range (I + 1))
    (f := fun i : ℕ => Nat.log r ((x - 1) / q ^ i) + 1)
    (g := fun i : ℕ => ((strictSmoothPairs q r x).filter (fun e => e.1 = i)).card) rfl ?_
  intro i hi
  have hQ := hquot i hi
  symm
  trans (range (Nat.log r ((x - 1) / q ^ i) + 1)).card
  · apply Finset.card_bij (fun e _ => e.2)
    · intro e he
      obtain ⟨he, hei⟩ := mem_filter.mp he
      have hv := (mem_strictSmoothPairs_iff hq hr e).mp he
      rw [hei] at hv
      have hvle : q ^ i * r ^ e.2 ≤ x - 1 := by omega
      have hmul : r ^ e.2 * q ^ i ≤ x - 1 := by simpa only [mul_comm] using hvle
      have hle : r ^ e.2 ≤ (x - 1) / q ^ i :=
        (Nat.le_div_iff_mul_le (by positivity : 0 < q ^ i)).mpr hmul
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_log_of_pow_le hr hle))
    · intro e he f hf hef
      have he' := (mem_filter.mp he).2
      have hf' := (mem_filter.mp hf).2
      exact Prod.ext (he'.trans hf'.symm) hef
    · intro j hj
      have hj' : j ≤ Nat.log r ((x - 1) / q ^ i) :=
        Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hp : r ^ j ≤ (x - 1) / q ^ i := Nat.pow_le_of_le_log hQ.ne' hj'
      have hmul := (Nat.le_div_iff_mul_le (by positivity : 0 < q ^ i)).mp hp
      refine ⟨(i, j), mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      apply (mem_strictSmoothPairs_iff hq hr (i, j)).mpr
      dsimp only
      have hvle : q ^ i * r ^ j ≤ x - 1 := by simpa only [mul_comm] using hmul
      omega
  · simp

/-- No repeated computation of `q^i`: each step divides the previous quotient. -/
def pairCountDivLoop (q r : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, N =>
    if N = 0 then 0 else Nat.log r N + 1 + pairCountDivLoop q r k (N / q)

theorem pairCountDivLoop_eq_sum (q r k N : ℕ) :
    pairCountDivLoop q r k N =
      ∑ i ∈ range k, if N / q ^ i = 0 then 0 else Nat.log r (N / q ^ i) + 1 := by
  induction k generalizing N with
  | zero => simp [pairCountDivLoop]
  | succ k ih =>
      by_cases hN : N = 0
      · simp [pairCountDivLoop, hN]
      rw [pairCountDivLoop, if_neg hN, ih, Finset.sum_range_succ']
      simp only [pow_zero, Nat.div_one, if_neg hN]
      rw [Nat.add_comm (Nat.log r N + 1)]
      apply congrArg (fun z : ℕ => z + (Nat.log r N + 1))
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Nat.div_div_eq_div_mul, ← pow_succ']

/-- Executable count of the ACTUAL strict pair set. -/
def pairCountExact (q r x : ℕ) : ℕ :=
  if x ≤ 1 then 0 else
    pairCountDivLoop q r (Nat.log q (x - 1) + 1) (x - 1)

theorem pairCountExact_correct {q r x : ℕ} (hq : 1 < q) (hr : 1 < r) :
    pairCountExact q r x = (strictSmoothPairs q r x).card := by
  rw [← pairCountFast_correct hq hr]
  by_cases hx : x ≤ 1
  · simp [pairCountExact, pairCountFast, hx]
  rw [pairCountExact, pairCountFast, if_neg hx, if_neg hx, pairCountDivLoop_eq_sum]
  refine Finset.sum_congr
    (s₁ := range (Nat.log q (x - 1) + 1)) (s₂ := range (Nat.log q (x - 1) + 1))
    (f := fun i : ℕ => if (x - 1) / q ^ i = 0 then (0 : ℕ) else Nat.log r ((x - 1) / q ^ i) + 1)
    (g := fun i : ℕ => Nat.log r ((x - 1) / q ^ i) + 1) rfl ?_
  intro i hi
  have hpow : q ^ i ≤ x - 1 := Nat.pow_le_of_le_log (by omega)
    (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hQ : 0 < (x - 1) / q ^ i := Nat.div_pos hpow (by positivity)
  dsimp only
  rw [if_neg hQ.ne']

/-- Decrease a certified upper power until it is the largest power below N.
The power is updated by exact division, rather than re-exponentiation. -/
def lowerPower (r : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, P, _ => (0, P)
  | j + 1, P, N =>
    if P ≤ N then (j + 1, P) else lowerPower r j (P / r) N

theorem lowerPower_correct (r j N : ℕ) (hr : 1 < r) (hN : 0 < N)
    (hu : N < r ^ (j + 1)) :
    lowerPower r j (r ^ j) N = (Nat.log r N, r ^ Nat.log r N) := by
  revert hu
  induction j with
  | zero =>
      intro hu
      have hlog : Nat.log r N = 0 := Nat.log_of_lt (by simpa using hu)
      simp only [lowerPower, hlog]
  | succ j ih =>
      intro hu
      by_cases hp : r ^ (j + 1) ≤ N
      · have hlog : Nat.log r N = j + 1 := Nat.log_eq_of_pow_le_of_lt_pow hp hu
        simp only [lowerPower, if_pos hp, hlog]
      · have hdiv : r ^ (j + 1) / r = r ^ j := by
          rw [pow_succ', Nat.mul_div_cancel_left _ (by omega)]
        rw [lowerPower, if_neg hp, hdiv]
        exact ih (by omega)

/-- Boundary sweep. On a correct state, both the q- and r-power exponents
only decrease, so no inner logarithm is recomputed. -/
def pairCountSweep (q r : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | k + 1, N, j, P =>
    if N = 0 then 0 else
      let jp := lowerPower r j P N
      jp.1 + 1 + pairCountSweep q r k (N / q) jp.1 jp.2

theorem pairCountSweep_correct (q r k N j : ℕ) (hr : 1 < r)
    (hu : N < r ^ (j + 1)) :
    pairCountSweep q r k N j (r ^ j) = pairCountDivLoop q r k N := by
  revert hu
  induction k generalizing N j with
  | zero => intro hu; rfl
  | succ k ih =>
      intro hu
      by_cases hN : N = 0
      · simp [pairCountSweep, pairCountDivLoop, hN]
      rw [pairCountSweep, if_neg hN, lowerPower_correct r j N hr (by omega) hu,
        pairCountDivLoop, if_neg hN]
      dsimp only
      congr 1
      exact ih (N / q) (Nat.log r N)
        ((Nat.div_le_self N q).trans_lt (Nat.lt_pow_succ_log_self hr N))

def pairCountChecked (q r x : ℕ) : ℕ :=
  if x ≤ 1 then 0 else
    let N := x - 1
    let j := Nat.log r N
    pairCountSweep q r (Nat.log q N + 1) N j (r ^ j)

theorem pairCountChecked_correct {q r x : ℕ} (hq : 1 < q) (hr : 1 < r) :
    pairCountChecked q r x = (strictSmoothPairs q r x).card := by
  rw [← pairCountExact_correct hq hr]
  by_cases hx : x ≤ 1
  · simp [pairCountChecked, pairCountExact, hx]
  rw [pairCountChecked, pairCountExact, if_neg hx, if_neg hx]
  dsimp only
  exact pairCountSweep_correct _ _ _ _ _ hr (Nat.lt_pow_succ_log_self hr _)

/-- This orientation of the cumulative count matches the integer generator. -/
def purePrefixCount (p q r e : ℕ) : ℕ :=
  ∑ k ∈ range e, pairCountChecked q r (p ^ (k + 1))

theorem purePrefixCount_correct {p q r : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 < r) (e : ℕ) :
    purePrefixCount p q r e = smoothCountLT p q r (p ^ e) := by
  have heq : ∀ a, smoothCountLT p q r (p ^ a) = restrictedLogFloorSum p q r a := by
    intro a
    exact restrictedPurePowerCount_eq_restrictedLogFloorSum p q r a hp (by omega) (by omega)
  induction e with
  | zero =>
      simp [purePrefixCount, smoothCountLT, strictSmoothExponents, smooth3Val,
        Nat.ne_of_gt (lt_trans Nat.zero_lt_one hp),
        Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq),
        Nat.ne_of_gt (lt_trans Nat.zero_lt_one hr)]
  | succ e ih =>
      have hd := restrictedLogFloorSum_succ_sub p q r e hp hq hr
      rw [← heq (e + 1), ← heq e, ← pairCountChecked_correct hq hr] at hd
      have hle : smoothCountLT p q r (p ^ e) ≤ smoothCountLT p q r (p ^ (e + 1)) :=
        Finset.card_le_card (strictSmoothExponents_mono p q r
          (Nat.pow_le_pow_right (by omega) (Nat.le_succ e)))
      change (∑ k ∈ range (e + 1), pairCountChecked q r (p ^ (k + 1))) = _
      rw [sum_range_succ]
      change purePrefixCount p q r e + pairCountChecked q r (p ^ (e + 1)) = _
      rw [ih]
      omega

theorem smoothCountLT_swap_first_third (p q r x : ℕ) :
    smoothCountLT p q r x = smoothCountLT r q p x := by
  classical
  unfold smoothCountLT
  apply Finset.card_bij (fun z _ => (z.2.2, z.2.1, z.1))
  · intro z hz
    obtain ⟨hb, hv⟩ := mem_filter.mp hz
    obtain ⟨hi, hjk⟩ := mem_product.mp hb
    obtain ⟨hj, hk⟩ := mem_product.mp hjk
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨hk, mem_product.mpr ⟨hj, hi⟩⟩, ?_⟩
    simpa [smooth3Val, mul_comm, mul_left_comm, mul_assoc] using hv
  · intro z hz w hw h
    have h1 := congrArg (fun e : ℕ × ℕ × ℕ => e.2.2) h
    have h2 := congrArg (fun e : ℕ × ℕ × ℕ => e.2.1) h
    have h3 := congrArg (fun e : ℕ × ℕ × ℕ => e.1) h
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro z hz
    obtain ⟨hb, hv⟩ := mem_filter.mp hz
    obtain ⟨hk, hji⟩ := mem_product.mp hb
    obtain ⟨hj, hi⟩ := mem_product.mp hji
    refine ⟨(z.2.2, z.2.1, z.1), ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨hi, mem_product.mpr ⟨hj, hk⟩⟩, ?_⟩
    simpa [smooth3Val, mul_comm, mul_left_comm, mul_assoc] using hv

/-- The threshold can be below the shell; truncated subtraction handles that
case, rather than imposing an unproved internal-jump premise. -/
theorem beforeThreshold_eq_prefix_sub (p a : ℕ) :
    dyadicBeforeThresholdCount235 p a =
      smoothCountLT 2 3 5 (p ^ Nat.log p (2 ^ (a + 1))) -
        smoothCountLT 2 3 5 (2 ^ a) := by
  let t := p ^ Nat.log p (2 ^ (a + 1))
  have ht : t ≤ 2 ^ (a + 1) := Nat.pow_log_le_self p (by positivity)
  have hset : ((dyadicSmoothShell235 a).filter (fun e =>
      smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < t)) = strictSmoothShell 2 3 5 (2 ^ a) t := by
    ext e
    simp only [mem_filter, mem_dyadicSmoothShell235_iff, strictSmoothShell,
      mem_sdiff, mem_strictSmoothExponents235_iff]
    omega
  change ((dyadicSmoothShell235 a).filter (fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < t)).card = _
  rw [hset]
  by_cases h : 2 ^ a ≤ t
  · exact strictSmoothShell_card 2 3 5 h
  · have hs : strictSmoothExponents 2 3 5 t ⊆ strictSmoothExponents 2 3 5 (2 ^ a) :=
      strictSmoothExponents_mono 2 3 5 (by omega)
    have hc := Finset.card_le_card hs
    have hempty : strictSmoothShell 2 3 5 (2 ^ a) t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨het, hen⟩ := Finset.mem_sdiff.mp he
      exact hen (hs het)
    rw [hempty, card_empty]
    exact (Nat.sub_eq_zero_of_le hc).symm

def orderedDigitExact (a : ℕ) : ℕ :=
  let f3 := Nat.log 3 (2 ^ (a + 1))
  let f5 := Nat.log 5 (2 ^ (a + 1))
  let c2 := purePrefixCount 2 3 5 a
  let d3 := purePrefixCount 3 2 5 f3 - c2
  let d5 := purePrefixCount 5 2 3 f5 - c2
  let w := pairCountChecked 3 5 (2 ^ (a + 1))
  if 3 ^ f3 ≤ 5 ^ f5 then w + 10 * d3 + 4 * d5 else w + 2 * d3 + 12 * d5

/-- All three cumulative counts, both order branches, and the terminal shell
width are identified with the actual library digit for EVERY a. -/
theorem orderedDigitExact_correct (a : ℕ) :
    orderedDigitExact a = dyadicOrderedBlockDigit235 a := by
  have hc2 := purePrefixCount_correct (p := 2) (q := 3) (r := 5)
    (by decide) (by decide) (by decide) a
  have hc3 := purePrefixCount_correct (p := 3) (q := 2) (r := 5)
    (by decide) (by decide) (by decide) (Nat.log 3 (2 ^ (a + 1)))
  rw [smoothCountLT_swap_first_second 3 2 5] at hc3
  have hc5 := purePrefixCount_correct (p := 5) (q := 2) (r := 3)
    (by decide) (by decide) (by decide) (Nat.log 5 (2 ^ (a + 1)))
  rw [smoothCountLT_swap_first_third 5 2 3, smoothCountLT_swap_first_second 3 2 5] at hc5
  have hwidth : pairCountChecked 3 5 (2 ^ (a + 1)) = (dyadicSmoothShell235 a).card := by
    have hd := restrictedLogFloorSum_succ_sub 2 3 5 a (by decide) (by decide) (by decide)
    have he : ∀ e, smoothCountLT 2 3 5 (2 ^ e) = restrictedLogFloorSum 2 3 5 e := by
      intro e
      exact restrictedPurePowerCount_eq_restrictedLogFloorSum 2 3 5 e
        (by decide) (by decide) (by decide)
    rw [← he (a + 1), ← he a] at hd
    rw [pairCountChecked_correct (by decide : 1 < 3) (by decide : 1 < 5)]
    rw [dyadicSmoothShell235, strictSmoothShell_card 2 3 5
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_succ a))]
    exact hd.symm
  unfold orderedDigitExact
  dsimp only
  rw [hc2, hc3, hc5, hwidth]
  simp only [dyadicOrderedBlockDigit235, beforeThreshold_eq_prefix_sub]

end ErdosProblems.Erdos269.PaperR9
