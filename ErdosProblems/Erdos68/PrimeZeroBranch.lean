import ErdosProblems.Erdos68.EndpointWeightedPrivateSupport
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Factorial
import Mathlib.NumberTheory.Wilson

/-!
# Erdős #68: the prime zero branch

This module develops three linked layers of the factorial-gap series.

First, exact prefix identities express the step carry through a binary
endpoint flag and the canonical factorial digit.  A unit carry is therefore
equivalent to one of two endpoint cylinders: a zero digit with two zero
flags, or the maximal digit with two one flags.

Second, reduced predecessor fractions are followed prime by prime.  The
formalized arithmetic includes prefix-private prime powers, accumulated
denominator factors, collision and residual cofactors, and exact finite
records at the primes `107` and `971`.  In particular, prefix-private
factorial-gap hits occur cofinally and the corresponding numerator
projections are nonzero under the stated divisibility hypotheses.

Third, a family of conditional theorems shows that sufficiently large
predecessor residues, supplied cofinally, would force irrationality.  The
module does **not** prove those quantitative lower bounds: a nonzero residue
is not enough.  It therefore proves no unconditional irrationality theorem
and does not settle Erdős #68.
-/

namespace ErdosProblems.Erdos68

/-! ## Scaled tails and endpoint flags -/

/-- The exact tail after `m`, scaled by `m!`. -/
noncomputable def factorialGapScaledTail (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * _root_.Erdos68.factorialGapTail m

/-- The scaled factorial-gap tail is positive. -/
theorem factorialGapScaledTail_pos
    {m : ℕ} (hm : 2 ≤ m) :
    0 < factorialGapScaledTail m := by
  unfold factorialGapScaledTail
  exact mul_pos (by positivity)
    (_root_.Erdos68.factorialGapTail_pos hm)

/-- The scaled factorial-gap tail is strictly smaller than one. -/
theorem factorialGapScaledTail_lt_one
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapScaledTail m < 1 := by
  have htail :=
    _root_.Erdos68.factorialGapTail_lt_one_div_factorial hm
  have hfacPos : (0 : ℝ) < m.factorial := by positivity
  have hmul := mul_lt_mul_of_pos_left htail hfacPos
  simpa [factorialGapScaledTail, ne_of_gt hfacPos] using hmul

/-- A sharper elementary tail width: after scaling by `m!`, the entire
future tail is less than `2 / m`. -/
theorem factorialGapScaledTail_lt_two_div
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapScaledTail m < 2 / (m : ℝ) := by
  have hsplit := factorialGapTail_eq_next_add_tail m
  have hnextTail :=
    _root_.Erdos68.factorialGapTail_lt_one_div_factorial
      (D := m + 1) (by omega)
  have hfacNat :
      (m + 1).factorial = (m + 1) * m.factorial :=
    Nat.factorial_succ m
  have hfac :
      ((m + 1).factorial : ℝ) =
        ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
    exact_mod_cast hfacNat
  have hsuccCast :
      ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    norm_num
  have hfacGt : (1 : ℝ) < m.factorial := by
    exact_mod_cast Nat.one_lt_factorial.mpr hm
  have hfacPos : (0 : ℝ) < m.factorial := by positivity
  have hmPos : (0 : ℝ) < m := by positivity
  have hsuccPos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hcast :
      (((((m + 1).factorial : ℤ) - 1 : ℤ)) : ℝ) =
        ((m + 1).factorial : ℝ) - 1 := by
    norm_num
  rw [hcast] at hsplit
  have hdenPos :
      (0 : ℝ) < ((m + 1).factorial : ℝ) - 1 := by
    have hsuccOne : (1 : ℝ) ≤ (m + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ m + 1 by omega)
    have hprodGt :
        (1 : ℝ) <
          ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
      calc
        (1 : ℝ) < (m.factorial : ℝ) := hfacGt
        _ = 1 * (m.factorial : ℝ) := by ring
        _ ≤ ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) :=
          mul_le_mul_of_nonneg_right hsuccOne hfacPos.le
    rw [hfac]
    linarith
  have hfirst :
      (m.factorial : ℝ) /
          (((m + 1).factorial : ℝ) - 1) <
        1 / (m : ℝ) := by
    rw [div_lt_div_iff₀ hdenPos hmPos, hfac, hsuccCast]
    ring_nf
    nlinarith
  have hsecond :
      (m.factorial : ℝ) *
          _root_.Erdos68.factorialGapTail (m + 1) <
        1 / ((m + 1 : ℕ) : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hnextTail hfacPos
    calc
      (m.factorial : ℝ) *
            _root_.Erdos68.factorialGapTail (m + 1) <
          (m.factorial : ℝ) /
            ((m + 1).factorial : ℝ) := by
              simpa [div_eq_mul_inv] using hmul
      _ = 1 / ((m + 1 : ℕ) : ℝ) := by
        rw [hfac]
        field_simp
  have hsimple :
      1 / (m : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) <
        2 / (m : ℝ) := by
    rw [hsuccCast]
    field_simp
    nlinarith
  unfold factorialGapScaledTail
  rw [hsplit]
  calc
    (m.factorial : ℝ) *
          (1 / (((m + 1).factorial : ℝ) - 1) +
            _root_.Erdos68.factorialGapTail (m + 1)) =
        (m.factorial : ℝ) /
            (((m + 1).factorial : ℝ) - 1) +
          (m.factorial : ℝ) *
            _root_.Erdos68.factorialGapTail (m + 1) := by ring
    _ < 1 / (m : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) :=
      add_lt_add hfirst hsecond
    _ < 2 / (m : ℝ) := hsimple

/-- The endpoint flag records whether the canonical remainder of the full
series lies above the exact scaled tail. -/
noncomputable def factorialGapEndpointFlag (m : ℕ) : ℤ :=
  if factorialGapScaledTail m ≤
      canonicalRemainder _root_.Erdos68.factorialGapSeries m
    then 1
    else 0

/-- Every endpoint flag is zero or one. -/
theorem factorialGapEndpointFlag_eq_zero_or_one (m : ℕ) :
    factorialGapEndpointFlag m = 0 ∨
      factorialGapEndpointFlag m = 1 := by
  unfold factorialGapEndpointFlag
  split <;> simp

/-- A zero endpoint flag is exactly strict containment below the scaled
tail. -/
theorem factorialGapEndpointFlag_eq_zero_iff (m : ℕ) :
    factorialGapEndpointFlag m = 0 ↔
      canonicalRemainder _root_.Erdos68.factorialGapSeries m <
        factorialGapScaledTail m := by
  simp [factorialGapEndpointFlag, not_le]

/-- A one endpoint flag is exactly containment at or above the scaled
tail. -/
theorem factorialGapEndpointFlag_eq_one_iff (m : ℕ) :
    factorialGapEndpointFlag m = 1 ↔
      factorialGapScaledTail m ≤
        canonicalRemainder _root_.Erdos68.factorialGapSeries m := by
  simp [factorialGapEndpointFlag]

/-- Exact scaled-tail recurrence after adjoining the `m`-th summand. -/
theorem factorialGapScaledTail_pred_recurrence
    {m : ℕ} (hm : 3 ≤ m) :
    (m : ℝ) * factorialGapScaledTail (m - 1) =
      1 + 1 / ((m.factorial : ℝ) - 1) +
        factorialGapScaledTail m := by
  have hsplit :=
    factorialGapTail_eq_next_add_tail (m - 1)
  have hsucc : m - 1 + 1 = m := by omega
  rw [hsucc] at hsplit
  have hcastSub :
      (((m.factorial : ℤ) - 1 : ℤ) : ℝ) =
        (m.factorial : ℝ) - 1 := by
    norm_num
  rw [hcastSub] at hsplit
  have hfacNat :
      m.factorial = m * (m - 1).factorial := by
    simpa [hsucc] using Nat.factorial_succ (m - 1)
  have hfac :
      (m.factorial : ℝ) =
        (m : ℝ) * ((m - 1).factorial : ℝ) := by
    exact_mod_cast hfacNat
  have hfacGt : (1 : ℝ) < m.factorial := by
    exact_mod_cast Nat.one_lt_factorial.mpr (by omega : 2 ≤ m)
  have hdenNe : (m.factorial : ℝ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hfacGt)
  have hfrac :
      (m.factorial : ℝ) / ((m.factorial : ℝ) - 1) =
        1 + 1 / ((m.factorial : ℝ) - 1) := by
    field_simp [hdenNe]
    ring
  unfold factorialGapScaledTail
  rw [hsplit]
  calc
    (m : ℝ) *
          (((m - 1).factorial : ℝ) *
            (1 / ((m.factorial : ℝ) - 1) +
              _root_.Erdos68.factorialGapTail m)) =
        (m.factorial : ℝ) *
          (1 / ((m.factorial : ℝ) - 1) +
            _root_.Erdos68.factorialGapTail m) := by
              rw [hfac]
              ring
    _ = (m.factorial : ℝ) / ((m.factorial : ℝ) - 1) +
          (m.factorial : ℝ) *
            _root_.Erdos68.factorialGapTail m := by ring
    _ = 1 + 1 / ((m.factorial : ℝ) - 1) +
          (m.factorial : ℝ) *
            _root_.Erdos68.factorialGapTail m := by rw [hfrac]

/-! ## The reduced rational predecessor state -/

/-- Exact rational version of the predecessor gap.  This is executable:
it uses only the finite prefix through `m - 1` and rational floor. -/
def factorialGapPredecessorGapRat (m : ℕ) : ℚ :=
  (strictFacTopRat (factorialGapPrefix (m - 1)) (m - 1) : ℚ) -
    ((m - 1).factorial : ℚ) * factorialGapPrefix (m - 1)

/-- The executable rational predecessor gap agrees with the real-valued
quantity used by the analytic carry reduction. -/
theorem factorialGapPredecessorGapRat_cast (m : ℕ) :
    ((factorialGapPredecessorGapRat m : ℚ) : ℝ) =
      factorialGapPredecessorGap m := by
  unfold factorialGapPredecessorGapRat factorialGapPredecessorGap
  rw [← strictFacTop_ratCast]
  norm_num

/-- The natural coefficient used by the factorial-block CRT package is
exactly the executable rational strict successor. -/
theorem factorialBlockCoefficient_cast_eq_strictFacTopRat (p : ℕ) :
    (factorialBlockCoefficient p : ℚ) =
      (strictFacTopRat (factorialGapPrefix (p - 1)) (p - 1) : ℚ) := by
  have h :=
    factorialBlockCoefficient_cast_eq_strictFacTop (p := p)
  rw [strictFacTop_ratCast] at h
  exact_mod_cast h

/-- The reduced scaled prefix whose strict upper-grid residue is the
predecessor gap. -/
def factorialGapPredecessorScaledRat (m : ℕ) : ℚ :=
  ((m - 1).factorial : ℚ) * factorialGapPrefix (m - 1)

/-- The reduced denominator of a finite rational sum divides the product of
the reduced denominators of its summands. -/
theorem rat_finset_sum_den_dvd_prod_den
    {α : Type*} (s : Finset α) (f : α → ℚ) :
    (∑ x ∈ s, f x).den ∣ (∏ x ∈ s, (f x).den) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact
        (Rat.add_den_dvd (f a) (∑ x ∈ s, f x)).trans
          (Nat.mul_dvd_mul_left (f a).den ih)

/-- A common multiple of all summand denominators is already a common
denominator for the reduced finite sum.  This retains least-common-multiple
rather than product-level valuation information. -/
theorem rat_finset_sum_den_dvd_of_dvd
    {α : Type*} (s : Finset α) (f : α → ℚ) {M : ℕ}
    (hdiv : ∀ x ∈ s, (f x).den ∣ M) :
    (∑ x ∈ s, f x).den ∣ M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact
        (Rat.add_den_dvd_lcm (f a) (∑ x ∈ s, f x)).trans
          (Nat.lcm_dvd
            (hdiv a (Finset.mem_insert_self a s))
            (ih fun x hx => hdiv x (Finset.mem_insert_of_mem hx)))

/-- Each literal factorial-gap reciprocal has its displayed positive
denominator already in lowest terms. -/
theorem factorialGapReciprocal_den
    {k : ℕ} (hk : 2 ≤ k) :
    (1 / ((k.factorial : ℚ) - 1)).den = k.factorial - 1 := by
  have hfacOne : 1 ≤ k.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hgapPos : 0 < k.factorial - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hk)
  have hcast :
      (k.factorial : ℚ) - 1 =
        ((k.factorial - 1 : ℕ) : ℚ) := by
    norm_num [Nat.cast_sub hfacOne]
  rw [hcast]
  simpa [one_div] using
    Rat.inv_natCast_den_of_pos hgapPos

/-- The denominator of the actual prefix divides the product of its literal
factorial-gap denominators. -/
theorem factorialGapPrefix_den_dvd_gapProduct (n : ℕ) :
    (factorialGapPrefix n).den ∣
      (∏ k ∈ Finset.Icc 2 n, (k.factorial - 1)) := by
  unfold factorialGapPrefix
  refine
    (rat_finset_sum_den_dvd_prod_den
      (Finset.Icc 2 n)
      (fun k => 1 / ((k.factorial : ℚ) - 1))).trans ?_
  have hprod :
      (∏ k ∈ Finset.Icc 2 n,
          (1 / ((k.factorial : ℚ) - 1)).den) =
        (∏ k ∈ Finset.Icc 2 n, (k.factorial - 1)) := by
    apply Finset.prod_congr rfl
    intro k hk
    exact factorialGapReciprocal_den (Finset.mem_Icc.mp hk).1
  rw [hprod]

/-- The least common multiple of the literal factorial-gap denominators
through one prefix endpoint. -/
def factorialGapPrefixLCM (n : ℕ) : ℕ :=
  (Finset.Icc 2 n).lcm fun k => k.factorial - 1

/-- The reduced denominator of the exact prefix divides the factorial-gap
least common multiple through the same endpoint. -/
theorem factorialGapPrefix_den_dvd_prefixLCM (n : ℕ) :
    (factorialGapPrefix n).den ∣ factorialGapPrefixLCM n := by
  unfold factorialGapPrefix factorialGapPrefixLCM
  apply rat_finset_sum_den_dvd_of_dvd
  intro k hk
  have hk2 : 2 ≤ k :=
    (Finset.mem_Icc.1 hk).1
  rw [factorialGapReciprocal_den hk2]
  exact Finset.dvd_lcm hk

/-- Integer factorial scaling cannot add denominator valuation, so the
actual reduced predecessor denominator is bounded by the same prefix LCM. -/
theorem factorialGapPredecessorScaledRat_den_dvd_prefixLCM (n : ℕ) :
    (factorialGapPredecessorScaledRat n).den ∣
      factorialGapPrefixLCM (n - 1) := by
  have hmul :=
    Rat.mul_den_dvd
      (((n - 1).factorial : ℕ) : ℚ)
      (factorialGapPrefix (n - 1))
  have hscaled :
      (factorialGapPredecessorScaledRat n).den ∣
        (factorialGapPrefix (n - 1)).den := by
    simpa [factorialGapPredecessorScaledRat] using hmul
  exact
    hscaled.trans
      (factorialGapPrefix_den_dvd_prefixLCM (n - 1))

/-- Taking a strict upper-grid complement changes the numerator but not the
reduced denominator. -/
@[simp] theorem factorialGapPredecessorGapRat_den (m : ℕ) :
    (factorialGapPredecessorGapRat m).den =
      (factorialGapPredecessorScaledRat m).den := by
  simp [
    factorialGapPredecessorGapRat,
    factorialGapPredecessorScaledRat
  ]

/-- A prime coprime to every earlier factorial gap is absent from the
reduced denominator of the scaled earlier prefix. -/
theorem not_dvd_factorialGapPredecessorScaledRat_den_of_prefixPrivate
    {m q : ℕ} (hq : q.Prime)
    (hprefix :
      ∀ k : ℕ, 2 ≤ k → k < m →
        Nat.Coprime q (k.factorial - 1)) :
    ¬q ∣ (factorialGapPredecessorScaledRat m).den := by
  intro hqScaled
  have hscaledDvdPrefix :
      (factorialGapPredecessorScaledRat m).den ∣
        (factorialGapPrefix (m - 1)).den := by
    have h :=
      Rat.mul_den_dvd
        (((m - 1).factorial : ℕ) : ℚ)
        (factorialGapPrefix (m - 1))
    simpa [factorialGapPredecessorScaledRat] using h
  have hqPrefix :
      q ∣ (factorialGapPrefix (m - 1)).den :=
    hqScaled.trans hscaledDvdPrefix
  have hqProduct :
      q ∣ (∏ k ∈ Finset.Icc 2 (m - 1), (k.factorial - 1)) :=
    hqPrefix.trans (factorialGapPrefix_den_dvd_gapProduct (m - 1))
  have hcopProduct :
      Nat.Coprime q
        (∏ k ∈ Finset.Icc 2 (m - 1), (k.factorial - 1)) := by
    apply Nat.Coprime.prod_right
    intro k hk
    have hkBounds := Finset.mem_Icc.mp hk
    exact hprefix k hkBounds.1 (by omega)
  exact (hq.coprime_iff_not_dvd.mp hcopProduct) hqProduct

/-- Integral numerator of the predecessor gap over the reduced denominator
of the scaled finite prefix.  The numerator lies in `1, ..., den`, with the
terminal value `den` representing an integral scaled prefix. -/
def factorialGapPredecessorGapNumerator (m : ℕ) : ℤ :=
  let q := factorialGapPredecessorScaledRat m
  (⌊q⌋ + 1) * q.den - q.num

/-- Natural-number representative of the positive reduced predecessor-gap
numerator, for modular projection onto denominator primes. -/
def factorialGapPredecessorGapNumeratorNat (m : ℕ) : ℕ :=
  (factorialGapPredecessorGapNumerator m).toNat

/-- The strict upper-grid residue numerator is always positive. -/
theorem factorialGapPredecessorGapNumerator_pos (m : ℕ) :
    0 < factorialGapPredecessorGapNumerator m := by
  unfold factorialGapPredecessorGapNumerator
  exact sub_pos.mpr
    (Rat.num_lt_succ_floor_mul_den
      (factorialGapPredecessorScaledRat m))

/-- The natural representative casts back to the integral numerator. -/
@[simp] theorem factorialGapPredecessorGapNumeratorNat_cast (m : ℕ) :
    (factorialGapPredecessorGapNumeratorNat m : ℤ) =
      factorialGapPredecessorGapNumerator m := by
  unfold factorialGapPredecessorGapNumeratorNat
  rw [Int.toNat_of_nonneg
    (factorialGapPredecessorGapNumerator_pos m).le]

/-- The strict upper-grid residue numerator is at most its reduced
denominator.  Equality is exactly the integral scaled-prefix convention. -/
theorem factorialGapPredecessorGapNumerator_le_den (m : ℕ) :
    factorialGapPredecessorGapNumerator m ≤
      (factorialGapPredecessorScaledRat m).den := by
  let q := factorialGapPredecessorScaledRat m
  change (⌊q⌋ + 1) * q.den - q.num ≤ q.den
  rw [Rat.floor_def']
  have hden : (q.den : ℤ) ≠ 0 := by positivity
  have hdiv := Int.ediv_mul_le q.num hden
  calc
    (q.num / (q.den : ℤ) + 1) * (q.den : ℤ) - q.num =
        q.num / (q.den : ℤ) * (q.den : ℤ) - q.num + q.den := by
          ring
    _ ≤ q.den := by linarith

/-- The reduced upper-grid residue numerator is coprime to its denominator,
which is the coprimality needed for the later finite CRT arguments. -/
theorem factorialGapPredecessorGapNumerator_isCoprime_den (m : ℕ) :
    IsCoprime
      (factorialGapPredecessorGapNumerator m)
      ((factorialGapPredecessorScaledRat m).den : ℤ) := by
  let q := factorialGapPredecessorScaledRat m
  have hcop : IsCoprime (-q.num) (q.den : ℤ) :=
    (Rat.isCoprime_num_den q).neg_left
  have hadd := hcop.add_mul_left_left (⌊q⌋ + 1)
  change IsCoprime ((⌊q⌋ + 1) * q.den - q.num) (q.den : ℤ)
  convert hadd using 1 <;> ring

/-- Every nontrivial divisor of the reduced denominator sees a nonzero
projection of the reduced predecessor-gap numerator. -/
theorem factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
    {m d : ℕ} (hd : 1 < d)
    (hdDen : d ∣ (factorialGapPredecessorScaledRat m).den) :
    factorialGapPredecessorGapNumeratorNat m % d ≠ 0 := by
  intro hzero
  have hdNumNat :
      d ∣ factorialGapPredecessorGapNumeratorNat m :=
    Nat.dvd_of_mod_eq_zero hzero
  have hdNum :
      (d : ℤ) ∣ factorialGapPredecessorGapNumerator m := by
    rw [← factorialGapPredecessorGapNumeratorNat_cast]
    exact_mod_cast hdNumNat
  have hdDenInt :
      (d : ℤ) ∣
        ((factorialGapPredecessorScaledRat m).den : ℤ) := by
    exact_mod_cast hdDen
  have hdUnitInt : IsUnit (d : ℤ) :=
    (factorialGapPredecessorGapNumerator_isCoprime_den m).isUnit_of_dvd'
      hdNum hdDenInt
  have hdUnitNat : IsUnit d :=
    Int.ofNat_isUnit.mp hdUnitInt
  exact (Nat.ne_of_gt hd) (Nat.isUnit_iff.mp hdUnitNat)

/-- Every prime factor of the reduced denominator sees a nonzero projection
of the reduced predecessor-gap numerator. -/
theorem factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_prime_dvd_den
    {m q : ℕ} (hq : q.Prime)
    (hqDen : q ∣ (factorialGapPredecessorScaledRat m).den) :
    factorialGapPredecessorGapNumeratorNat m % q ≠ 0 :=
  factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
    hq.one_lt hqDen

/-- A finite set of distinct prime factors of the actual reduced
denominator multiplies to an actual CRT divisor of that denominator. -/
theorem primeFinset_prod_dvd_factorialGapPredecessorScaledRat_den
    {m : ℕ} {s : Finset ℕ}
    (hprime : ∀ q ∈ s, q.Prime)
    (hdiv :
      ∀ q ∈ s, q ∣ (factorialGapPredecessorScaledRat m).den) :
    (∏ q ∈ s, q) ∣ (factorialGapPredecessorScaledRat m).den := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have haPrime : a.Prime :=
        hprime a (Finset.mem_insert_self a s)
      have hsPrime : ∀ q ∈ s, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hsDiv :
          ∀ q ∈ s, q ∣ (factorialGapPredecessorScaledRat m).den := by
        intro q hq
        exact hdiv q (Finset.mem_insert_of_mem hq)
      have haCoprime : Nat.Coprime a (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes haPrime (hsPrime q hq)).mpr
        intro haq
        subst q
        exact ha hq
      rw [Finset.prod_insert ha]
      exact
        (Nat.coprime_iff_isRelPrime.mp haCoprime).mul_dvd
          (hdiv a (Finset.mem_insert_self a s))
          (ih hsPrime hsDiv)

/-- A nonempty finite product of primes is a nontrivial modulus. -/
theorem one_lt_primeFinset_prod
    {s : Finset ℕ} (hs : s.Nonempty)
    (hprime : ∀ q ∈ s, q.Prime) :
    1 < ∏ q ∈ s, q := by
  obtain ⟨q, hq⟩ := hs
  have hqDvd : q ∣ ∏ r ∈ s, r :=
    Finset.dvd_prod_of_mem (fun r : ℕ => r) hq
  have hprodPos : 0 < ∏ r ∈ s, r :=
    Finset.prod_pos (fun r hr => (hprime r hr).pos)
  exact
    (hprime q hq).one_lt.trans_le
      (Nat.le_of_dvd hprodPos hqDvd)

/-- A finite nonempty set of surviving denominator primes therefore gives
a nonzero numerator projection modulo their full CRT product. -/
theorem factorialGapPredecessorGapNumeratorNat_mod_primeFinset_prod_ne_zero
    {m : ℕ} {s : Finset ℕ} (hs : s.Nonempty)
    (hprime : ∀ q ∈ s, q.Prime)
    (hdiv :
      ∀ q ∈ s, q ∣ (factorialGapPredecessorScaledRat m).den) :
    factorialGapPredecessorGapNumeratorNat m % (∏ q ∈ s, q) ≠ 0 :=
  factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
    (one_lt_primeFinset_prod hs hprime)
    (primeFinset_prod_dvd_factorialGapPredecessorScaledRat_den
      hprime hdiv)

/-- Exact numerator/denominator normal form of the finite predecessor gap. -/
theorem factorialGapPredecessorGapRat_eq_numerator_div_den (m : ℕ) :
    factorialGapPredecessorGapRat m =
      (factorialGapPredecessorGapNumerator m : ℚ) /
        (factorialGapPredecessorScaledRat m).den := by
  let q := factorialGapPredecessorScaledRat m
  change
    ((⌊q⌋ + 1 : ℤ) : ℚ) - q =
      (((⌊q⌋ + 1) * q.den - q.num : ℤ) : ℚ) / q.den
  conv_lhs =>
    rhs
    rw [← Rat.num_div_den q]
  have hden : (q.den : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- Exact rational recurrence for consecutive reduced predecessor gaps.
This is the finite arithmetic orbit underlying the interval checker: the
next gap is obtained by multiplying by the new radix, subtracting the
factorial error, and subtracting the integer carry. -/
theorem factorialGapPredecessorGapRat_succ_recurrence
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapPredecessorGapRat (m + 1) =
      (m : ℚ) * factorialGapPredecessorGapRat m -
        1 / ((m.factorial : ℚ) - 1) -
          (factorialGapStepCarry m : ℚ) := by
  have hstep :=
    strictFacTop_factorialGapPrefix_step (m := m) hm
  rw [strictFacTop_ratCast, strictFacTop_ratCast] at hstep
  have hstepQ :
      (strictFacTopRat (factorialGapPrefix m) m : ℚ) =
        (m : ℚ) *
            (strictFacTopRat
              (factorialGapPrefix (m - 1)) (m - 1) : ℚ) +
          1 - (factorialGapStepCarry m : ℚ) := by
    exact_mod_cast hstep
  have hprefix :=
    factorialGapPrefix_eq_prev_add (τ := m) hm
  have hfacNat :
      m.factorial = m * (m - 1).factorial := by
    have hsucc : m - 1 + 1 = m := by omega
    simpa only [hsucc] using Nat.factorial_succ (m - 1)
  have hfacQ :
      (m.factorial : ℚ) =
        (m : ℚ) * ((m - 1).factorial : ℚ) := by
    exact_mod_cast hfacNat
  have hden : (m.factorial : ℚ) - 1 ≠ 0 := by
    have hfacGt : (1 : ℚ) < m.factorial := by
      exact_mod_cast Nat.one_lt_factorial.mpr hm
    linarith
  have hden' :
      (m : ℚ) * ((m - 1).factorial : ℚ) - 1 ≠ 0 := by
    rw [← hfacQ]
    exact hden
  unfold factorialGapPredecessorGapRat
  simp only [Nat.add_sub_cancel]
  rw [hstepQ, hprefix, hfacQ]
  field_simp [hden']
  ring

/-- Consecutive coprime numerator/denominator pairs satisfy the same exact
rational recurrence. -/
theorem factorialGapPredecessorGapNumerator_succ_recurrence
    {m : ℕ} (hm : 2 ≤ m) :
    (factorialGapPredecessorGapNumerator (m + 1) : ℚ) /
          (factorialGapPredecessorScaledRat (m + 1)).den =
      (m : ℚ) *
          ((factorialGapPredecessorGapNumerator m : ℚ) /
            (factorialGapPredecessorScaledRat m).den) -
        1 / ((m.factorial : ℚ) - 1) -
          (factorialGapStepCarry m : ℚ) := by
  rw [
    ← factorialGapPredecessorGapRat_eq_numerator_div_den,
    ← factorialGapPredecessorGapRat_eq_numerator_div_den
  ]
  exact factorialGapPredecessorGapRat_succ_recurrence hm

/-- Conversely, the next reduced denominator always divides the old
denominator times the newly adjoined factorial gap. -/
theorem factorialGapPredecessorScaledRat_succ_den_dvd_den_mul_gap
    {m : ℕ} (hm : 2 ≤ m) :
    (factorialGapPredecessorScaledRat (m + 1)).den ∣
      (factorialGapPredecessorScaledRat m).den *
        (m.factorial - 1) := by
  let D : ℚ := factorialGapPredecessorGapRat m
  let X : ℚ := (m : ℚ) * D
  let Y : ℚ := 1 / ((m.factorial : ℚ) - 1)
  have hrec :=
    factorialGapPredecessorGapRat_succ_recurrence hm
  have hdenRec :
      (factorialGapPredecessorGapRat (m + 1)).den =
        (X - Y).den := by
    rw [hrec]
    simp only [Rat.sub_intCast_den]
    rfl
  have hX :
      X.den ∣ (factorialGapPredecessorScaledRat m).den := by
    have h :=
      Rat.mul_den_dvd (m : ℚ) D
    simpa [X, D] using h
  have hfacOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hgapPos : 0 < m.factorial - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hm)
  have hY :
      Y.den = m.factorial - 1 := by
    dsimp [Y]
    have hcast :
        (m.factorial : ℚ) - 1 =
          ((m.factorial - 1 : ℕ) : ℚ) := by
      norm_num [Nat.cast_sub hfacOne]
    rw [hcast]
    simpa [one_div] using
      Rat.inv_natCast_den_of_pos hgapPos
  rw [← factorialGapPredecessorGapRat_den (m + 1), hdenRec]
  exact
    (Rat.sub_den_dvd X Y).trans
      (mul_dvd_mul hX (by rw [hY]))

/-- The exact reduction factor removed when the raw denominator
`v_m * (m! - 1)` is normalized at the next endpoint. -/
def factorialGapPredecessorTransitionNormalizer (m : ℕ) : ℕ :=
  ((factorialGapPredecessorScaledRat m).den *
      (m.factorial - 1)) /
    (factorialGapPredecessorScaledRat (m + 1)).den

/-- The next reduced denominator times the transition normalizer is the
unreduced denominator produced by adjoining `1/(m!-1)`. -/
theorem
    factorialGapPredecessorScaledRat_succ_den_mul_transitionNormalizer
    {m : ℕ} (hm : 2 ≤ m) :
    (factorialGapPredecessorScaledRat (m + 1)).den *
        factorialGapPredecessorTransitionNormalizer m =
      (factorialGapPredecessorScaledRat m).den *
        (m.factorial - 1) := by
  unfold factorialGapPredecessorTransitionNormalizer
  exact
    Nat.mul_div_cancel'
      (factorialGapPredecessorScaledRat_succ_den_dvd_den_mul_gap hm)

/-- The exact transition normalizer is positive at every nontrivial
factorial-gap step. -/
theorem factorialGapPredecessorTransitionNormalizer_pos
    {m : ℕ} (hm : 2 ≤ m) :
    0 < factorialGapPredecessorTransitionNormalizer m := by
  have hgapPos : 0 < m.factorial - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hm)
  have hproductPos :
      0 <
        (factorialGapPredecessorScaledRat (m + 1)).den *
          factorialGapPredecessorTransitionNormalizer m := by
    rw [
      factorialGapPredecessorScaledRat_succ_den_mul_transitionNormalizer
        hm
    ]
    exact
      Nat.mul_pos
        (factorialGapPredecessorScaledRat m).den_pos
        hgapPos
  exact
    pos_of_mul_pos_right hproductPos
      (Nat.zero_le _)

/-- Clearing all positive denominators gives a pure integer recurrence for
the consecutive reduced pairs. -/
theorem factorialGapPredecessorGapNumerator_succ_recurrence_cleared
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapPredecessorGapNumerator (m + 1) *
          ((factorialGapPredecessorScaledRat m).den : ℤ) *
          ((m.factorial : ℤ) - 1) =
      (m : ℤ) * factorialGapPredecessorGapNumerator m *
            ((factorialGapPredecessorScaledRat (m + 1)).den : ℤ) *
            ((m.factorial : ℤ) - 1) -
        ((factorialGapPredecessorScaledRat m).den : ℤ) *
            ((factorialGapPredecessorScaledRat (m + 1)).den : ℤ) -
        factorialGapStepCarry m *
            ((factorialGapPredecessorScaledRat m).den : ℤ) *
            ((factorialGapPredecessorScaledRat (m + 1)).den : ℤ) *
            ((m.factorial : ℤ) - 1) := by
  have hrec :=
    factorialGapPredecessorGapNumerator_succ_recurrence hm
  have hVm :
      ((factorialGapPredecessorScaledRat m).den : ℚ) ≠ 0 := by
    positivity
  have hVs :
      ((factorialGapPredecessorScaledRat (m + 1)).den : ℚ) ≠ 0 := by
    positivity
  have hA :
      (m.factorial : ℚ) - 1 ≠ 0 := by
    have hfacGt : (1 : ℚ) < m.factorial := by
      exact_mod_cast Nat.one_lt_factorial.mpr hm
    linarith
  have hQ :
      (factorialGapPredecessorGapNumerator (m + 1) : ℚ) *
            (factorialGapPredecessorScaledRat m).den *
            ((m.factorial : ℚ) - 1) =
        (m : ℚ) * (factorialGapPredecessorGapNumerator m : ℚ) *
              (factorialGapPredecessorScaledRat (m + 1)).den *
              ((m.factorial : ℚ) - 1) -
          (factorialGapPredecessorScaledRat m).den *
              (factorialGapPredecessorScaledRat (m + 1)).den -
          (factorialGapStepCarry m : ℚ) *
              (factorialGapPredecessorScaledRat m).den *
              (factorialGapPredecessorScaledRat (m + 1)).den *
              ((m.factorial : ℚ) - 1) := by
    field_simp [hVm, hVs, hA] at hrec ⊢
    ring_nf at hrec ⊢
    exact hrec
  exact_mod_cast hQ

/-- After exposing the exact transition normalizer, the reduced numerator
obeys an integral recurrence with no next-denominator factor. -/
theorem
    factorialGapPredecessorGapNumerator_mul_transitionNormalizer
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapPredecessorGapNumerator (m + 1) *
          factorialGapPredecessorTransitionNormalizer m =
      (m : ℤ) * factorialGapPredecessorGapNumerator m *
            ((m.factorial : ℤ) - 1) -
        (factorialGapPredecessorScaledRat m).den -
        factorialGapStepCarry m *
          (factorialGapPredecessorScaledRat m).den *
            ((m.factorial : ℤ) - 1) := by
  let U : ℤ := factorialGapPredecessorGapNumerator m
  let U' : ℤ := factorialGapPredecessorGapNumerator (m + 1)
  let V : ℤ := (factorialGapPredecessorScaledRat m).den
  let V' : ℤ := (factorialGapPredecessorScaledRat (m + 1)).den
  let A : ℤ := (m.factorial : ℤ) - 1
  let G : ℤ := factorialGapPredecessorTransitionNormalizer m
  let b : ℤ := factorialGapStepCarry m
  have hclear :=
    factorialGapPredecessorGapNumerator_succ_recurrence_cleared hm
  change
    U' * V * A =
      (m : ℤ) * U * V' * A - V * V' - b * V * V' * A at hclear
  have hfactorNat :=
    factorialGapPredecessorScaledRat_succ_den_mul_transitionNormalizer hm
  have hfacOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hfactor : V' * G = V * A := by
    dsimp [V, V', A, G]
    have hfactorCast :=
      congrArg (fun x : ℕ => (x : ℤ)) hfactorNat
    simpa only [Nat.cast_mul, Nat.cast_sub hfacOne] using hfactorCast
  have hEq :
      V' * (U' * G) =
        V' * ((m : ℤ) * U * A - V - b * V * A) := by
    calc
      V' * (U' * G) = U' * (V' * G) := by ring
      _ = U' * (V * A) := by rw [hfactor]
      _ = U' * V * A := by ring
      _ = (m : ℤ) * U * V' * A - V * V' - b * V * V' * A :=
        hclear
      _ = V' * ((m : ℤ) * U * A - V - b * V * A) := by
        ring
  have hV'Ne : V' ≠ 0 := by
    dsimp [V']
    positivity
  have hcancel :=
    mul_left_cancel₀ hV'Ne hEq
  simpa [U, U', V, A, G, b] using hcancel

/-- At a newly adjoined divisor `d | m!-1`, the normalized next numerator
has a completely explicit congruence: multiplying it by the transition
normalizer gives `-v_m` modulo `d`.  The identity retains the reduction
factor omitted by the earlier qualitative nonvanishing statement. -/
theorem
    transitionNormalizer_mul_predecessorGapNumerator_modEq_neg_den
    {m d : ℕ} (hm : 2 ≤ m)
    (hdA : d ∣ m.factorial - 1) :
    Int.ModEq (d : ℤ)
      (factorialGapPredecessorTransitionNormalizer m *
        factorialGapPredecessorGapNumerator (m + 1))
      (-(factorialGapPredecessorScaledRat m).den : ℤ) := by
  have hnum :=
    factorialGapPredecessorGapNumerator_mul_transitionNormalizer hm
  rw [Int.modEq_iff_dvd]
  have hfacOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hdAZ :
      (d : ℤ) ∣ (m.factorial : ℤ) - 1 := by
    obtain ⟨t, ht⟩ := hdA
    refine ⟨(t : ℤ), ?_⟩
    have hcast :
        ((m.factorial - 1 : ℕ) : ℤ) =
          (m.factorial : ℤ) - 1 := by
      exact Nat.cast_sub hfacOne
    rw [← hcast]
    exact_mod_cast ht
  obtain ⟨t, ht⟩ := hdAZ
  refine ⟨
    -(m : ℤ) * factorialGapPredecessorGapNumerator m * t +
      factorialGapStepCarry m *
        (factorialGapPredecessorScaledRat m).den * t,
    ?_⟩
  rw [mul_comm
    (factorialGapPredecessorTransitionNormalizer m : ℤ)
    (factorialGapPredecessorGapNumerator (m + 1) : ℤ),
    hnum, ht]
  ring

/-- A genuinely new prime is also absent from the transition
normalizer.  Thus the exact entry congruence can be inverted modulo every
entering private prime; cancellation cannot hide in the normalizer. -/
theorem
    prime_coprime_factorialGapPredecessorTransitionNormalizer_of_dvd_gap
    {m q : ℕ} (hm : 2 ≤ m)
    (hq : q.Prime)
    (hqA : q ∣ m.factorial - 1)
    (hqV : ¬q ∣ (factorialGapPredecessorScaledRat m).den) :
    Nat.Coprime q
      (factorialGapPredecessorTransitionNormalizer m) := by
  apply hq.coprime_iff_not_dvd.mpr
  intro hqG
  have hmod :=
    transitionNormalizer_mul_predecessorGapNumerator_modEq_neg_den
      hm hqA
  have hqGZ :
      (q : ℤ) ∣
        (factorialGapPredecessorTransitionNormalizer m : ℤ) := by
    exact_mod_cast hqG
  have hqProdZ :
      (q : ℤ) ∣
        (factorialGapPredecessorTransitionNormalizer m : ℤ) *
          factorialGapPredecessorGapNumerator (m + 1) :=
    dvd_mul_of_dvd_left hqGZ _
  have hqDiffZ :=
    hmod.dvd
  have hqNegVZ :
      (q : ℤ) ∣
        (-(factorialGapPredecessorScaledRat m).den : ℤ) := by
    convert Int.dvd_add hqDiffZ hqProdZ using 1 <;> ring
  have hqVZ :
      (q : ℤ) ∣
        ((factorialGapPredecessorScaledRat m).den : ℤ) :=
    dvd_neg.mp hqNegVZ
  exact hqV (by exact_mod_cast hqVZ)

/-- Every old denominator prime that collides with the new radix or
factorial gap is absorbed by the transition normalizer.  This is the
prime-level converse to persistence away from both collision factors. -/
theorem prime_dvd_factorialGapPredecessorTransitionNormalizer_of_collision
    {m q : ℕ} (hm : 2 ≤ m)
    (hq : q.Prime)
    (hqV : q ∣ (factorialGapPredecessorScaledRat m).den)
    (hcollision : q ∣ m ∨ q ∣ m.factorial - 1) :
    q ∣ factorialGapPredecessorTransitionNormalizer m := by
  by_contra hqG
  have hden :=
    factorialGapPredecessorScaledRat_succ_den_mul_transitionNormalizer
      hm
  have hqDenProd :
      q ∣
        (factorialGapPredecessorScaledRat (m + 1)).den *
          factorialGapPredecessorTransitionNormalizer m := by
    rw [hden]
    exact dvd_mul_of_dvd_left hqV _
  have hqNextDen :
      q ∣ (factorialGapPredecessorScaledRat (m + 1)).den :=
    (hq.dvd_mul.mp hqDenProd).resolve_right hqG
  have hfacOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hqVZ :
      (q : ℤ) ∣
        ((factorialGapPredecessorScaledRat m).den : ℤ) := by
    exact_mod_cast hqV
  have hqFirstZ :
      (q : ℤ) ∣
        (m : ℤ) * factorialGapPredecessorGapNumerator m *
          ((m.factorial : ℤ) - 1) := by
    rcases hcollision with hqm | hqA
    · have hqmZ : (q : ℤ) ∣ (m : ℤ) := by
        exact_mod_cast hqm
      exact
        dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left hqmZ _)
          _
    · have hqAZ :
          (q : ℤ) ∣ (m.factorial : ℤ) - 1 := by
        have hqAZ' :
            (q : ℤ) ∣ ((m.factorial - 1 : ℕ) : ℤ) := by
          exact_mod_cast hqA
        simpa [Nat.cast_sub hfacOne] using hqAZ'
      simpa only [mul_assoc] using
        dvd_mul_of_dvd_right hqAZ
          ((m : ℤ) * factorialGapPredecessorGapNumerator m)
  have hqCarryZ :
      (q : ℤ) ∣
        factorialGapStepCarry m *
          (factorialGapPredecessorScaledRat m).den *
          ((m.factorial : ℤ) - 1) := by
    simpa only [mul_assoc] using
      dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right hqVZ
          (factorialGapStepCarry m))
        ((m.factorial : ℤ) - 1)
  have hnum :=
    factorialGapPredecessorGapNumerator_mul_transitionNormalizer
      hm
  have hqNumProdZ :
      (q : ℤ) ∣
        factorialGapPredecessorGapNumerator (m + 1) *
          (factorialGapPredecessorTransitionNormalizer m : ℤ) := by
    rw [hnum]
    exact
      Int.dvd_sub
        (Int.dvd_sub hqFirstZ hqVZ)
        hqCarryZ
  rw [← factorialGapPredecessorGapNumeratorNat_cast] at hqNumProdZ
  have hqNumProd :
      q ∣
        factorialGapPredecessorGapNumeratorNat (m + 1) *
          factorialGapPredecessorTransitionNormalizer m := by
    exact_mod_cast hqNumProdZ
  have hqNextNum :
      q ∣ factorialGapPredecessorGapNumeratorNat (m + 1) :=
    (hq.dvd_mul.mp hqNumProd).resolve_right hqG
  exact
    (factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_prime_dvd_den
      hq hqNextDen)
      (Nat.dvd_iff_mod_eq_zero.mp hqNextNum)

/-- Reduced denominators can lose factors at one step only through the new
radix `m` or the newly adjoined factorial gap `m! - 1`.  Equivalently,
every other factor of `v_m` persists into `v_(m+1)`. -/
theorem factorialGapPredecessorScaledRat_den_dvd_radix_gap_succ_den
    {m : ℕ} (hm : 2 ≤ m) :
    ((factorialGapPredecessorScaledRat m).den : ℤ) ∣
      (m : ℤ) *
        ((factorialGapPredecessorScaledRat (m + 1)).den : ℤ) *
        ((m.factorial : ℤ) - 1) := by
  let U : ℤ := factorialGapPredecessorGapNumerator m
  let U' : ℤ := factorialGapPredecessorGapNumerator (m + 1)
  let V : ℤ := (factorialGapPredecessorScaledRat m).den
  let V' : ℤ := (factorialGapPredecessorScaledRat (m + 1)).den
  let A : ℤ := (m.factorial : ℤ) - 1
  let b : ℤ := factorialGapStepCarry m
  have hclear :=
    factorialGapPredecessorGapNumerator_succ_recurrence_cleared hm
  change
    U' * V * A =
      (m : ℤ) * U * V' * A - V * V' - b * V * V' * A at hclear
  have hmainEq :
      (m : ℤ) * U * V' * A =
        U' * V * A + V * V' + b * V * V' * A := by
    linear_combination -hclear
  have hdivMain :
      V ∣ (m : ℤ) * U * V' * A := by
    refine ⟨U' * A + V' + b * V' * A, ?_⟩
    rw [hmainEq]
    ring
  have hdivMul :
      V ∣ U * ((m : ℤ) * V' * A) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hdivMain
  have hcop : IsCoprime U V := by
    exact factorialGapPredecessorGapNumerator_isCoprime_den m
  exact hcop.symm.dvd_of_dvd_mul_left hdivMul

/-- Composite-divisor form of denominator persistence.  Any full divisor
of `v_m` survives into `v_(m+1)` when it is coprime to both possible
absorption factors, the radix `m` and the new factorial gap `m! - 1`.
Unlike the prime-only form below, this retains prime-power valuations. -/
theorem dvd_factorialGapPredecessorScaledRat_succ_den_of_coprime
    {m d : ℕ} (hm : 2 ≤ m)
    (hdV : d ∣ (factorialGapPredecessorScaledRat m).den)
    (hdm : Nat.Coprime d m)
    (hdA : Nat.Coprime d (m.factorial - 1)) :
    d ∣ (factorialGapPredecessorScaledRat (m + 1)).den := by
  have hdenZ :=
    factorialGapPredecessorScaledRat_den_dvd_radix_gap_succ_den hm
  have hfacOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hdenN :
      (factorialGapPredecessorScaledRat m).den ∣
        m * (factorialGapPredecessorScaledRat (m + 1)).den *
          (m.factorial - 1) := by
    exact_mod_cast hdenZ
  have hdAll :
      d ∣ m *
        ((factorialGapPredecessorScaledRat (m + 1)).den *
          (m.factorial - 1)) := by
    simpa only [mul_assoc] using hdV.trans hdenN
  have hdRest :
      d ∣ (factorialGapPredecessorScaledRat (m + 1)).den *
        (m.factorial - 1) :=
    hdm.dvd_of_dvd_mul_left hdAll
  exact hdA.dvd_of_dvd_mul_right hdRest

/-! ## Prime-power persistence in consecutive denominators -/

/-- Prime-factor form of denominator persistence.  A prime already present
in `v_m` survives in `v_(m+1)` unless it is absorbed by `m` or by the new
denominator `m! - 1`. -/
theorem prime_dvd_factorialGapPredecessorScaledRat_succ_den
    {m q : ℕ} (hm : 2 ≤ m)
    (hq : q.Prime)
    (hqV : q ∣ (factorialGapPredecessorScaledRat m).den)
    (hqm : ¬q ∣ m)
    (hqA : ¬q ∣ m.factorial - 1) :
    q ∣ (factorialGapPredecessorScaledRat (m + 1)).den := by
  have hdenZ :=
    factorialGapPredecessorScaledRat_den_dvd_radix_gap_succ_den hm
  have hfacOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hdenN :
      (factorialGapPredecessorScaledRat m).den ∣
        m * (factorialGapPredecessorScaledRat (m + 1)).den *
          (m.factorial - 1) := by
    exact_mod_cast hdenZ
  have hqAll :
      q ∣ m *
        ((factorialGapPredecessorScaledRat (m + 1)).den *
          (m.factorial - 1)) := by
    simpa only [mul_assoc] using hqV.trans hdenN
  rcases hq.dvd_mul.mp hqAll with hqm' | hqRest
  · exact (hqm hqm').elim
  · rcases hq.dvd_mul.mp hqRest with hqSucc | hqA'
    · exact hqSucc
    · exact (hqA hqA').elim

/-- A genuinely new prime factor of the adjoined factorial gap enters the
next reduced denominator.  Cancellation is impossible because reducing the
old gap did not expose that prime: modulo `q`, the cleared recurrence leaves
only `v_m * v_(m+1)`. -/
theorem prime_dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap
    {m q : ℕ} (hm : 2 ≤ m)
    (hq : q.Prime)
    (hqA : q ∣ m.factorial - 1)
    (hqV : ¬q ∣ (factorialGapPredecessorScaledRat m).den) :
    q ∣ (factorialGapPredecessorScaledRat (m + 1)).den := by
  let U : ℤ := factorialGapPredecessorGapNumerator m
  let U' : ℤ := factorialGapPredecessorGapNumerator (m + 1)
  let V : ℤ := (factorialGapPredecessorScaledRat m).den
  let V' : ℤ := (factorialGapPredecessorScaledRat (m + 1)).den
  let A : ℤ := (m.factorial : ℤ) - 1
  let b : ℤ := factorialGapStepCarry m
  have hclear :=
    factorialGapPredecessorGapNumerator_succ_recurrence_cleared hm
  change
    U' * V * A =
      (m : ℤ) * U * V' * A - V * V' - b * V * V' * A at hclear
  have hprodEq :
      V * V' =
        (m : ℤ) * U * V' * A - b * V * V' * A - U' * V * A := by
    linear_combination hclear
  have hfacOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hqAZ : (q : ℤ) ∣ A := by
    dsimp [A]
    exact_mod_cast hqA
  obtain ⟨a, ha⟩ := hqAZ
  have hqProdZ : (q : ℤ) ∣ V * V' := by
    rw [hprodEq, ha]
    refine
      ⟨(m : ℤ) * U * V' * a - b * V * V' * a - U' * V * a, ?_⟩
    ring
  have hqProd :
      q ∣
        (factorialGapPredecessorScaledRat m).den *
          (factorialGapPredecessorScaledRat (m + 1)).den := by
    dsimp [V, V'] at hqProdZ
    exact_mod_cast hqProdZ
  rcases hq.dvd_mul.mp hqProd with hqOld | hqNext
  · exact (hqV hqOld).elim
  · exact hqNext

/-- Composite entry form.  Every divisor of the new factorial gap that is
coprime to the old reduced denominator enters the next reduced
denominator in full. -/
theorem dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap_coprime
    {m d : ℕ} (hm : 2 ≤ m)
    (hdA : d ∣ m.factorial - 1)
    (hdV : Nat.Coprime d
      (factorialGapPredecessorScaledRat m).den) :
    d ∣ (factorialGapPredecessorScaledRat (m + 1)).den := by
  let U : ℤ := factorialGapPredecessorGapNumerator m
  let U' : ℤ := factorialGapPredecessorGapNumerator (m + 1)
  let V : ℤ := (factorialGapPredecessorScaledRat m).den
  let V' : ℤ := (factorialGapPredecessorScaledRat (m + 1)).den
  let A : ℤ := (m.factorial : ℤ) - 1
  let b : ℤ := factorialGapStepCarry m
  have hclear :=
    factorialGapPredecessorGapNumerator_succ_recurrence_cleared hm
  change
    U' * V * A =
      (m : ℤ) * U * V' * A - V * V' - b * V * V' * A at hclear
  have hprodEq :
      V * V' =
        (m : ℤ) * U * V' * A - b * V * V' * A - U' * V * A := by
    linear_combination hclear
  have hfacOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hdAZ : (d : ℤ) ∣ A := by
    dsimp [A]
    exact_mod_cast hdA
  obtain ⟨a, ha⟩ := hdAZ
  have hdProdZ : (d : ℤ) ∣ V * V' := by
    rw [hprodEq, ha]
    refine
      ⟨(m : ℤ) * U * V' * a - b * V * V' * a - U' * V * a, ?_⟩
    ring
  have hdProd :
      d ∣
        (factorialGapPredecessorScaledRat m).den *
          (factorialGapPredecessorScaledRat (m + 1)).den := by
    dsimp [V, V'] at hdProdZ
    exact_mod_cast hdProdZ
  exact hdV.dvd_of_dvd_mul_left hdProd

/-- Every full prime power dividing a new factorial gap enters the next
reduced denominator when the underlying prime is absent from the old
denominator. -/
theorem prime_pow_dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap
    {m q e : ℕ} (hm : 2 ≤ m)
    (hq : q.Prime)
    (hqPowA : q ^ e ∣ m.factorial - 1)
    (hqV : ¬q ∣ (factorialGapPredecessorScaledRat m).den) :
    q ^ e ∣ (factorialGapPredecessorScaledRat (m + 1)).den := by
  apply
    dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap_coprime
      hm hqPowA
  exact (hq.coprime_pow_of_not_dvd hqV).symm

/-- Every prefix-private prime factor of `m! - 1` therefore enters the next
reduced predecessor denominator. -/
theorem prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_den
    {m q : ℕ} (hm : 2 ≤ m)
    (hq : q.Prime)
    (hqA : q ∣ m.factorial - 1)
    (hprefix :
      ∀ k : ℕ, 2 ≤ k → k < m →
        Nat.Coprime q (k.factorial - 1)) :
    q ∣ (factorialGapPredecessorScaledRat (m + 1)).den := by
  exact
    prime_dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap
      hm hq hqA
        (not_dvd_factorialGapPredecessorScaledRat_den_of_prefixPrivate
          hq hprefix)

/-- With one extra unit of size separation, a prefix-private prime not only
enters at `v_(m+1)` but survives automatically to `v_(m+2)`. -/
theorem prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_succ_den
    {m q : ℕ} (hm : 2 ≤ m)
    (hq : q.Prime)
    (hmq : m + 1 < q)
    (hqA : q ∣ m.factorial - 1)
    (hprefix :
      ∀ k : ℕ, 2 ≤ k → k < m →
        Nat.Coprime q (k.factorial - 1)) :
    q ∣ (factorialGapPredecessorScaledRat (m + 2)).den := by
  have hentry :
      q ∣ (factorialGapPredecessorScaledRat (m + 1)).den :=
    prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_den
      hm hq hqA hprefix
  have hqRadix : ¬q ∣ m + 1 := by
    intro hdiv
    have hqLe : q ≤ m + 1 :=
      Nat.le_of_dvd (by omega) hdiv
    omega
  have hqGap :
      ¬q ∣ (m + 1).factorial - 1 :=
    prime_not_dvd_succ_factorial_sub_one_of_dvd hq (by omega) hqA
  simpa [Nat.add_assoc] using
    prime_dvd_factorialGapPredecessorScaledRat_succ_den
      (m := m + 1) (by omega) hq hentry hqRadix hqGap

/-- Prefix privacy therefore retains the complete supplied prime-power
valuation at both consecutive endpoints. -/
theorem
    prefixPrivate_prime_pow_dvd_factorialGapPredecessorScaledRat_two_step_den
    {m q e : ℕ} (hm : 2 ≤ m)
    (hq : q.Prime)
    (hmq : m + 1 < q)
    (hqPowA : q ^ e ∣ m.factorial - 1)
    (hprefix :
      ∀ k : ℕ, 2 ≤ k → k < m →
        Nat.Coprime q (k.factorial - 1)) :
    q ^ e ∣ (factorialGapPredecessorScaledRat (m + 1)).den ∧
      q ^ e ∣ (factorialGapPredecessorScaledRat (m + 2)).den := by
  by_cases he : e = 0
  · subst e
    simp
  have hqA : q ∣ m.factorial - 1 := by
    exact (dvd_pow_self q he).trans hqPowA
  have hqOld :
      ¬q ∣ (factorialGapPredecessorScaledRat m).den :=
    not_dvd_factorialGapPredecessorScaledRat_den_of_prefixPrivate
      hq hprefix
  have hentry :
      q ^ e ∣ (factorialGapPredecessorScaledRat (m + 1)).den :=
    prime_pow_dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap
      hm hq hqPowA hqOld
  have hqRadix : ¬q ∣ m + 1 := by
    intro hdiv
    have hqLe : q ≤ m + 1 :=
      Nat.le_of_dvd (by omega) hdiv
    omega
  have hqGap :
      ¬q ∣ (m + 1).factorial - 1 :=
    prime_not_dvd_succ_factorial_sub_one_of_dvd hq (by omega) hqA
  have hpowRadix :
      Nat.Coprime (q ^ e) (m + 1) :=
    (hq.coprime_pow_of_not_dvd hqRadix).symm
  have hpowGap :
      Nat.Coprime (q ^ e) ((m + 1).factorial - 1) :=
    (hq.coprime_pow_of_not_dvd hqGap).symm
  exact
    ⟨hentry,
      dvd_factorialGapPredecessorScaledRat_succ_den_of_coprime
        (m := m + 1) (by omega) hentry hpowRadix hpowGap⟩

/-- All prefix-private primes selected from one factorial gap enter the
same next denominator.  Their squarefree product is therefore an actual
CRT modulus there, and reduced coprimality makes its numerator projection
nonzero. -/
theorem prefixPrivate_primeFinset_crt_entry
    {m : ℕ} (hm : 2 ≤ m) {s : Finset ℕ} (hs : s.Nonempty)
    (hprime : ∀ q ∈ s, q.Prime)
    (hgap : ∀ q ∈ s, q ∣ m.factorial - 1)
    (hprefix :
      ∀ q ∈ s, ∀ k : ℕ, 2 ≤ k → k < m →
        Nat.Coprime q (k.factorial - 1)) :
    (∏ q ∈ s, q) ∣
        (factorialGapPredecessorScaledRat (m + 1)).den ∧
      factorialGapPredecessorGapNumeratorNat (m + 1) %
          (∏ q ∈ s, q) ≠ 0 := by
  have hentry :
      ∀ q ∈ s,
        q ∣ (factorialGapPredecessorScaledRat (m + 1)).den := by
    intro q hqMem
    exact
      prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_den
        hm (hprime q hqMem) (hgap q hqMem)
          (hprefix q hqMem)
  exact
    ⟨primeFinset_prod_dvd_factorialGapPredecessorScaledRat_den
        hprime hentry,
      factorialGapPredecessorGapNumeratorNat_mod_primeFinset_prod_ne_zero
        hs hprime hentry⟩

/-- If every selected prefix-private prime is larger than `m + 1`, the
whole CRT modulus survives to the following endpoint as well.  Thus one
factorial gap can seed a common two-step modulus with nonzero numerator
projections at both endpoints. -/
theorem prefixPrivate_primeFinset_two_step_crt_anchors
    {m : ℕ} (hm : 2 ≤ m) {s : Finset ℕ} (hs : s.Nonempty)
    (hprime : ∀ q ∈ s, q.Prime)
    (hlarge : ∀ q ∈ s, m + 1 < q)
    (hgap : ∀ q ∈ s, q ∣ m.factorial - 1)
    (hprefix :
      ∀ q ∈ s, ∀ k : ℕ, 2 ≤ k → k < m →
        Nat.Coprime q (k.factorial - 1)) :
    (∏ q ∈ s, q) ∣
        (factorialGapPredecessorScaledRat (m + 1)).den ∧
      (∏ q ∈ s, q) ∣
        (factorialGapPredecessorScaledRat (m + 2)).den ∧
      factorialGapPredecessorGapNumeratorNat (m + 1) %
          (∏ q ∈ s, q) ≠ 0 ∧
      factorialGapPredecessorGapNumeratorNat (m + 2) %
          (∏ q ∈ s, q) ≠ 0 := by
  have hentry :
      ∀ q ∈ s,
        q ∣ (factorialGapPredecessorScaledRat (m + 1)).den := by
    intro q hqMem
    exact
      prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_den
        hm (hprime q hqMem) (hgap q hqMem)
          (hprefix q hqMem)
  have hnext :
      ∀ q ∈ s,
        q ∣ (factorialGapPredecessorScaledRat (m + 2)).den := by
    intro q hqMem
    exact
      prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_succ_den
        hm (hprime q hqMem) (hlarge q hqMem) (hgap q hqMem)
          (hprefix q hqMem)
  exact
    ⟨primeFinset_prod_dvd_factorialGapPredecessorScaledRat_den
        hprime hentry,
      primeFinset_prod_dvd_factorialGapPredecessorScaledRat_den
        hprime hnext,
      factorialGapPredecessorGapNumeratorNat_mod_primeFinset_prod_ne_zero
        hs hprime hentry,
      factorialGapPredecessorGapNumeratorNat_mod_primeFinset_prod_ne_zero
        hs hprime hnext⟩

/-! ## Prefix-private moduli and finite CRT anchors -/

/-- The canonical finite set of prime factors of `m! - 1` that are larger
than `m + 1` and absent from every earlier factorial gap. -/
def factorialGapLargePrefixPrivatePrimes (m : ℕ) : Finset ℕ :=
  (m.factorial - 1).primeFactors.filter fun q =>
    m + 1 < q ∧
      ∀ k ∈ Finset.Ico 2 m,
        Nat.Coprime q (k.factorial - 1)

/-- Membership in the canonical large prefix-private prime set. -/
theorem mem_factorialGapLargePrefixPrivatePrimes_iff
    {m q : ℕ} (hm : 2 ≤ m) :
    q ∈ factorialGapLargePrefixPrivatePrimes m ↔
      q.Prime ∧
      q ∣ m.factorial - 1 ∧
      m + 1 < q ∧
      ∀ k : ℕ, 2 ≤ k → k < m →
        Nat.Coprime q (k.factorial - 1) := by
  have hgapPos : 0 < m.factorial - 1 := by
    exact Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hm)
  simp only [
    factorialGapLargePrefixPrivatePrimes,
    Finset.mem_filter,
    Nat.mem_primeFactors,
    Finset.mem_Ico
  ]
  constructor
  · rintro ⟨⟨hq, hqGap, _hgapNe⟩, hlarge, hprefix⟩
    exact
      ⟨hq, hqGap, hlarge,
        fun k hk2 hkm => hprefix k ⟨hk2, hkm⟩⟩
  · rintro ⟨hq, hqGap, hlarge, hprefix⟩
    exact
      ⟨⟨hq, hqGap, hgapPos.ne'⟩, hlarge,
        fun k hk => hprefix k hk.1 hk.2⟩

/-- The squarefree product of all canonical large prefix-private prime
factors entering from `m! - 1`. -/
def factorialGapLargePrefixPrivateModulus (m : ℕ) : ℕ :=
  ∏ q ∈ factorialGapLargePrefixPrivatePrimes m, q

/-- The canonical prefix-private modulus with every selected prime retained
to its complete valuation in `m! - 1`.  This is the multiplicity-sensitive
replacement for the squarefree modulus above. -/
def factorialGapLargePrefixPrivatePowerModulus (m : ℕ) : ℕ :=
  ∏ q ∈ factorialGapLargePrefixPrivatePrimes m,
    q ^ (m.factorial - 1).factorization q

/-- The canonical prime-power modulus is an actual divisor of the
factorial gap from which it is assembled. -/
theorem factorialGapLargePrefixPrivatePowerModulus_dvd_gap
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapLargePrefixPrivatePowerModulus m ∣
      m.factorial - 1 := by
  have hgapNe : m.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hm)).ne'
  unfold factorialGapLargePrefixPrivatePowerModulus
  apply Finset.prod_dvd_of_isRelPrime
  · intro q hqMem r hrMem hqr
    have hqData :=
      (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
    have hrData :=
      (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hrMem
    exact
      Nat.coprime_iff_isRelPrime.mp
        (Nat.Coprime.pow_left _
          (Nat.Coprime.pow_right _
            ((Nat.coprime_primes hqData.1 hrData.1).2 hqr)))
  · intro q hqMem
    have hqPrime :=
      ((mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem).1
    exact
      (hqPrime.pow_dvd_iff_le_factorization hgapNe).2 le_rfl

/-- Every prime power in the canonical large prefix-private modulus survives
to full multiplicity inside the private quotient indexed by `m` in the
tailored block with parameter `m / 2 + 1`.  Hence the whole product divides
one quotient in that block. -/
theorem factorialGapLargePrefixPrivatePowerModulus_dvd_tailoredBlockPrivateQuotient
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapLargePrefixPrivatePowerModulus m ∣
      factorialBlockPrivateQuotient (m / 2 + 1) m := by
  have hgapNe : m.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hm)).ne'
  unfold factorialGapLargePrefixPrivatePowerModulus
  apply Finset.prod_dvd_of_isRelPrime
  · intro q hqMem r hrMem hqr
    have hqData :=
      (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
    have hrData :=
      (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hrMem
    exact
      Nat.coprime_iff_isRelPrime.mp
        (Nat.Coprime.pow_left _
          (Nat.Coprime.pow_right _
            ((Nat.coprime_primes hqData.1 hrData.1).2 hqr)))
  · intro q hqMem
    have hqData :=
      (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
    obtain ⟨hpLe, _hmMem, hunique⟩ :=
      prefixPrivate_factorialGap_unique_in_tailoredBlock
        hqData.1 hm hqData.2.1 hqData.2.2.2
    have hqPowGap :
        q ^ (m.factorial - 1).factorization q ∣
          factorialGapDenominator m := by
      simpa [factorialGapDenominator] using
        (hqData.1.pow_dvd_iff_le_factorization hgapNe).2 le_rfl
    unfold factorialBlockPrivateQuotient
    exact
      primePow_dvd_privateQuotient_of_unique_support
        hqData.1 hqPowGap
        (factorialBlockPrime_not_dvd_base_of_upper_hit
          hqData.1 hpLe
          (by
            simpa [factorialGapDenominator] using hqData.2.1))
        hunique

/-- Consequently the whole canonical prefix-private power product divides
the literal private modulus of the same tailored factorial block. -/
theorem factorialGapLargePrefixPrivatePowerModulus_dvd_tailoredBlockPrivateModulus
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapLargePrefixPrivatePowerModulus m ∣
      factorialBlockPrivateModulus (m / 2 + 1) := by
  have hmMem :
      m ∈ factorialBlockIndices (m / 2 + 1) := by
    unfold factorialBlockIndices
    simp only [Finset.mem_Icc]
    omega
  exact
    (factorialGapLargePrefixPrivatePowerModulus_dvd_tailoredBlockPrivateQuotient
      hm).trans
      (factorialBlockPrivateQuotient_dvd_privateModulus hmMem)

/-- Every individual prime selected by the canonical source set is
therefore an admissible factor of the tailored block private modulus. -/
theorem mem_factorialGapLargePrefixPrivatePrimes_dvd_tailoredBlockPrivateModulus
    {m q : ℕ} (hm : 2 ≤ m)
    (hqMem : q ∈ factorialGapLargePrefixPrivatePrimes m) :
    q ∣ factorialBlockPrivateModulus (m / 2 + 1) := by
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
  have hgapNe : m.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hm)).ne'
  have hfacPos :
      0 < (m.factorial - 1).factorization q :=
    hqData.1.factorization_pos_of_dvd hgapNe hqData.2.1
  have hqPowDvd :
      q ^ (m.factorial - 1).factorization q ∣
        factorialGapLargePrefixPrivatePowerModulus m := by
    unfold factorialGapLargePrefixPrivatePowerModulus
    exact Finset.dvd_prod_of_mem _ hqMem
  exact
    (dvd_pow_self q hfacPos.ne').trans
      (hqPowDvd.trans
        (factorialGapLargePrefixPrivatePowerModulus_dvd_tailoredBlockPrivateModulus
          hm))

/-- Two distinct selected primes give coprime factors of the tailored-block
private modulus, even when both divide the same private quotient. -/
theorem factorialGapLargePrefixPrivatePrimes_distinct_factor_pair_tailoredBlock
    {m q r : ℕ} (hm : 2 ≤ m)
    (hqMem : q ∈ factorialGapLargePrefixPrivatePrimes m)
    (hrMem : r ∈ factorialGapLargePrefixPrivatePrimes m)
    (hqr : q ≠ r) :
    q ∣ factorialBlockPrivateModulus (m / 2 + 1) ∧
      r ∣ factorialBlockPrivateModulus (m / 2 + 1) ∧
      Nat.Coprime q r := by
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
  have hrData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hrMem
  exact
    ⟨mem_factorialGapLargePrefixPrivatePrimes_dvd_tailoredBlockPrivateModulus
        hm hqMem,
      mem_factorialGapLargePrefixPrivatePrimes_dvd_tailoredBlockPrivateModulus
        hm hrMem,
      (Nat.coprime_primes hqData.1 hrData.1).2 hqr⟩

/-- In fact one selected prime is enough: the factors `1` and `q` give
projection moduli `R` and `R / q`, whose lcm recovers `R`.  Two nontrivial
selected primes are unnecessary. -/
theorem factorialGapLargePrefixPrivatePrimes_unit_factor_pair_tailoredBlock
    {m q : ℕ} (hm : 2 ≤ m)
    (hqMem : q ∈ factorialGapLargePrefixPrivatePrimes m) :
    1 ∣ factorialBlockPrivateModulus (m / 2 + 1) ∧
      q ∣ factorialBlockPrivateModulus (m / 2 + 1) ∧
      Nat.Coprime 1 q := by
  exact
    ⟨one_dvd _,
      mem_factorialGapLargePrefixPrivatePrimes_dvd_tailoredBlockPrivateModulus
        hm hqMem,
      Nat.coprime_one_left q⟩

/-- A single selected prefix-private prime makes the private modulus
nontrivial.  Under the displayed cofinal factor-pair scale inequality for
`(1,q)`, this suffices for irrationality. -/
theorem irrational_factorialGapSeries_of_cofinal_largePrefixPrivate_unitFactorPairFloor
    (hcert :
      ∀ B : ℕ, ∃ m q : ℕ,
        4 ≤ m ∧
        B < m / 2 + 1 ∧
        q ∈ factorialGapLargePrefixPrivatePrimes m ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockEndpointLcm (m / 2 + 1) <
          factorialBlockScale (m / 2 + 1) *
            factorialBlockComplementaryFactorPairFloor
              (m / 2 + 1) 1 q) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_complementaryFactorPairFloor_nat
  intro B
  obtain ⟨m, q, hm, hmLarge, hqMem, hscale⟩ :=
    hcert B
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff (by omega)).1 hqMem
  have hqDvd :
      q ∣ factorialBlockPrivateModulus (m / 2 + 1) :=
    mem_factorialGapLargePrefixPrivatePrimes_dvd_tailoredBlockPrivateModulus
      (by omega) hqMem
  have hR :
      1 < factorialBlockPrivateModulus (m / 2 + 1) := by
    exact
      hqData.1.one_lt.trans_le
        (Nat.le_of_dvd factorialBlockPrivateModulus_pos hqDvd)
  exact
    ⟨m / 2 + 1, 1, q, by omega, hmLarge,
      one_dvd _, hqDvd, Nat.coprime_one_left q, hR, hscale⟩

/-- A one-prime conditional irrationality theorem with its quantitative
hypothesis split into a global complementary-residue bound and a local
collision-cap bound. -/
theorem irrational_factorialGapSeries_of_cofinal_largePrefixPrivate_unitScaleSplit
    (hcert :
      ∀ B : ℕ, ∃ m q : ℕ,
        4 ≤ m ∧
        B < m / 2 + 1 ∧
        q ∈ factorialGapLargePrefixPrivatePrimes m ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockEndpointLcm (m / 2 + 1) <
          factorialBlockScale (m / 2 + 1) *
            complementaryProjectedResidue
              (factorialBlockTailNumerator (m / 2 + 1))
              (factorialBlockPrivateModulus (m / 2 + 1)) ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockCollisionCore (m / 2 + 1) * q <
          factorialBlockScale (m / 2 + 1)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_largePrefixPrivate_unitFactorPairFloor
  intro B
  obtain ⟨m, q, hm, hmLarge, hqMem, hglobal, hlocal⟩ :=
    hcert B
  have hqDvd :
      q ∣ factorialBlockPrivateModulus (m / 2 + 1) :=
    mem_factorialGapLargePrefixPrivatePrimes_dvd_tailoredBlockPrivateModulus
      (by omega) hqMem
  exact
    ⟨m, q, hm, hmLarge, hqMem,
      (factorialBlock_unitFactorPairFloor_scale_iff hqDvd).2
        ⟨hglobal, hlocal⟩⟩

/-- Canonical prime-power moduli born at distinct factorial gaps are
automatically coprime.  A prime selected at the later gap is prefix-private
from the entire earlier gap, while the earlier modulus divides that gap. -/
theorem
    factorialGapLargePrefixPrivatePowerModulus_coprime_of_lt
    {m k : ℕ} (hm : 2 ≤ m) (hmk : m < k) :
    Nat.Coprime
      (factorialGapLargePrefixPrivatePowerModulus m)
      (factorialGapLargePrefixPrivatePowerModulus k) := by
  have hk : 2 ≤ k := by omega
  unfold factorialGapLargePrefixPrivatePowerModulus
  apply Nat.Coprime.prod_right
  intro q hqMem
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff hk).1 hqMem
  have hqEarlierGap :
      Nat.Coprime q (m.factorial - 1) :=
    hqData.2.2.2 m hm hmk
  have hqEarlierModulus :
      Nat.Coprime
        q
        (∏ r ∈ factorialGapLargePrefixPrivatePrimes m,
          r ^ (m.factorial - 1).factorization r) :=
    hqEarlierGap.of_dvd_right
      (factorialGapLargePrefixPrivatePowerModulus_dvd_gap hm)
  exact hqEarlierModulus.symm.pow_right _

/-- Hence any finite set of source indices at least two carries a
pairwise-coprime family of canonical prime-power moduli. -/
theorem
    factorialGapLargePrefixPrivatePowerModulus_pairwise_coprime
    {s : Finset ℕ}
    (hlower : ∀ m ∈ s, 2 ≤ m) :
    (s : Set ℕ).Pairwise
      (fun m k =>
        Nat.Coprime
          (factorialGapLargePrefixPrivatePowerModulus m)
          (factorialGapLargePrefixPrivatePowerModulus k)) := by
  intro m hmMem k hkMem hmk
  rcases lt_or_gt_of_ne hmk with hmkLt | hkmLt
  · exact
      factorialGapLargePrefixPrivatePowerModulus_coprime_of_lt
        (hlower m hmMem) hmkLt
  · exact
      (factorialGapLargePrefixPrivatePowerModulus_coprime_of_lt
        (hlower k hkMem) hkmLt).symm

/-- Every selected prime is absent from the old reduced denominator, so
the full canonical prime-power modulus is coprime to that denominator. -/
theorem factorialGapLargePrefixPrivatePowerModulus_coprime_old_den
    {m : ℕ} (hm : 2 ≤ m) :
    Nat.Coprime
      (factorialGapLargePrefixPrivatePowerModulus m)
      (factorialGapPredecessorScaledRat m).den := by
  unfold factorialGapLargePrefixPrivatePowerModulus
  apply Nat.Coprime.prod_left
  intro q hqMem
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
  have hqOld :
      ¬q ∣ (factorialGapPredecessorScaledRat m).den :=
    not_dvd_factorialGapPredecessorScaledRat_den_of_prefixPrivate
      hqData.1 hqData.2.2.2
  exact
    (hqData.1.coprime_pow_of_not_dvd hqOld).symm

/-- The complete canonical prime-power modulus therefore enters the next
reduced denominator without valuation loss. -/
theorem factorialGapLargePrefixPrivatePowerModulus_dvd_succ_den
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapLargePrefixPrivatePowerModulus m ∣
      (factorialGapPredecessorScaledRat (m + 1)).den := by
  exact
    dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap_coprime
      hm
      (factorialGapLargePrefixPrivatePowerModulus_dvd_gap hm)
      (factorialGapLargePrefixPrivatePowerModulus_coprime_old_den hm)

/-- The canonical prime-power modulus is coprime to the intervening radix
because every selected prime is larger than `m + 1`. -/
theorem factorialGapLargePrefixPrivatePowerModulus_coprime_succ
    {m : ℕ} (hm : 2 ≤ m) :
    Nat.Coprime
      (factorialGapLargePrefixPrivatePowerModulus m)
      (m + 1) := by
  unfold factorialGapLargePrefixPrivatePowerModulus
  apply Nat.Coprime.prod_left
  intro q hqMem
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
  have hqRadix : ¬q ∣ m + 1 := by
    intro hdiv
    have hqLe : q ≤ m + 1 :=
      Nat.le_of_dvd (by omega) hdiv
    omega
  exact
    (hqData.1.coprime_pow_of_not_dvd hqRadix).symm

/-- A selected prime cannot hit the immediately following factorial gap,
so the complete canonical prime-power modulus is coprime to that gap. -/
theorem factorialGapLargePrefixPrivatePowerModulus_coprime_succ_gap
    {m : ℕ} (hm : 2 ≤ m) :
    Nat.Coprime
      (factorialGapLargePrefixPrivatePowerModulus m)
      ((m + 1).factorial - 1) := by
  unfold factorialGapLargePrefixPrivatePowerModulus
  apply Nat.Coprime.prod_left
  intro q hqMem
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
  have hqNextGap :
      ¬q ∣ (m + 1).factorial - 1 :=
    prime_not_dvd_succ_factorial_sub_one_of_dvd
      hqData.1 (by omega) hqData.2.1
  exact
    (hqData.1.coprime_pow_of_not_dvd hqNextGap).symm

/-- The complete canonical prime-power modulus survives at both
consecutive reduced-denominator endpoints. -/
theorem
    factorialGapLargePrefixPrivatePowerModulus_two_step_den_anchors
    {m : ℕ} (hm : 2 ≤ m) :
    factorialGapLargePrefixPrivatePowerModulus m ∣
        (factorialGapPredecessorScaledRat (m + 1)).den ∧
      factorialGapLargePrefixPrivatePowerModulus m ∣
        (factorialGapPredecessorScaledRat (m + 2)).den := by
  have hentry :
      factorialGapLargePrefixPrivatePowerModulus m ∣
        (factorialGapPredecessorScaledRat (m + 1)).den :=
    factorialGapLargePrefixPrivatePowerModulus_dvd_succ_den hm
  refine ⟨hentry, ?_⟩
  simpa [Nat.add_assoc] using
    dvd_factorialGapPredecessorScaledRat_succ_den_of_coprime
      (m := m + 1) (by omega) hentry
      (factorialGapLargePrefixPrivatePowerModulus_coprime_succ hm)
      (factorialGapLargePrefixPrivatePowerModulus_coprime_succ_gap hm)

/-- Nonemptiness of the selected prime set makes its complete
prime-power modulus nontrivial. -/
theorem one_lt_factorialGapLargePrefixPrivatePowerModulus
    {m : ℕ} (hm : 2 ≤ m)
    (hs : (factorialGapLargePrefixPrivatePrimes m).Nonempty) :
    1 < factorialGapLargePrefixPrivatePowerModulus m := by
  have hprime :
      ∀ q ∈ factorialGapLargePrefixPrivatePrimes m, q.Prime := by
    intro q hqMem
    exact
      ((mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem).1
  have hgapNe : m.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hm)).ne'
  have hdiv :
      factorialGapLargePrefixPrivateModulus m ∣
        factorialGapLargePrefixPrivatePowerModulus m := by
    unfold factorialGapLargePrefixPrivateModulus
      factorialGapLargePrefixPrivatePowerModulus
    apply Finset.prod_dvd_prod_of_dvd
    intro q hqMem
    have hqData :=
      (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
    have hfacPos :
        0 < (m.factorial - 1).factorization q :=
      hqData.1.factorization_pos_of_dvd hgapNe hqData.2.1
    exact dvd_pow_self q hfacPos.ne'
  have hpowerPos :
      0 < factorialGapLargePrefixPrivatePowerModulus m := by
    unfold factorialGapLargePrefixPrivatePowerModulus
    exact
      Finset.prod_pos
        (fun q hqMem =>
          pow_pos (hprime q hqMem).pos _)
  exact
    (one_lt_primeFinset_prod hs hprime).trans_le
      (Nat.le_of_dvd hpowerPos hdiv)

/-- A single supplied large prefix-private prime certifies that the
canonical set is nonempty. -/
theorem factorialGapLargePrefixPrivatePrimes_nonempty
    {m q : ℕ} (hm : 2 ≤ m)
    (hq : q.Prime)
    (hlarge : m + 1 < q)
    (hqGap : q ∣ m.factorial - 1)
    (hprefix :
      ∀ k : ℕ, 2 ≤ k → k < m →
        Nat.Coprime q (k.factorial - 1)) :
    (factorialGapLargePrefixPrivatePrimes m).Nonempty := by
  exact
    ⟨q,
      (mem_factorialGapLargePrefixPrivatePrimes_iff hm).2
        ⟨hq, hqGap, hlarge, hprefix⟩⟩

/-- Whenever the canonical set is nonempty, its full squarefree modulus
is present at two consecutive denominator endpoints and has nonzero
reduced-numerator projections at both. -/
theorem factorialGapLargePrefixPrivateModulus_two_step_crt_anchors
    {m : ℕ} (hm : 2 ≤ m)
    (hs : (factorialGapLargePrefixPrivatePrimes m).Nonempty) :
    factorialGapLargePrefixPrivateModulus m ∣
        (factorialGapPredecessorScaledRat (m + 1)).den ∧
      factorialGapLargePrefixPrivateModulus m ∣
        (factorialGapPredecessorScaledRat (m + 2)).den ∧
      factorialGapPredecessorGapNumeratorNat (m + 1) %
          factorialGapLargePrefixPrivateModulus m ≠ 0 ∧
      factorialGapPredecessorGapNumeratorNat (m + 2) %
          factorialGapLargePrefixPrivateModulus m ≠ 0 := by
  have hmem :
      ∀ q ∈ factorialGapLargePrefixPrivatePrimes m,
        q.Prime ∧
        q ∣ m.factorial - 1 ∧
        m + 1 < q ∧
        ∀ k : ℕ, 2 ≤ k → k < m →
          Nat.Coprime q (k.factorial - 1) := by
    intro q hqMem
    exact
      (mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem
  simpa [factorialGapLargePrefixPrivateModulus] using
    prefixPrivate_primeFinset_two_step_crt_anchors
      (m := m) hm hs
      (fun q hqMem => (hmem q hqMem).1)
      (fun q hqMem => (hmem q hqMem).2.2.1)
      (fun q hqMem => (hmem q hqMem).2.1)
      (fun q hqMem => (hmem q hqMem).2.2.2)

/-- The multiplicity-sensitive canonical modulus gives the same two
actual-denominator CRT anchors while retaining every selected valuation. -/
theorem
    factorialGapLargePrefixPrivatePowerModulus_two_step_crt_anchors
    {m : ℕ} (hm : 2 ≤ m)
    (hs : (factorialGapLargePrefixPrivatePrimes m).Nonempty) :
    factorialGapLargePrefixPrivatePowerModulus m ∣
        (factorialGapPredecessorScaledRat (m + 1)).den ∧
      factorialGapLargePrefixPrivatePowerModulus m ∣
        (factorialGapPredecessorScaledRat (m + 2)).den ∧
      factorialGapPredecessorGapNumeratorNat (m + 1) %
          factorialGapLargePrefixPrivatePowerModulus m ≠ 0 ∧
      factorialGapPredecessorGapNumeratorNat (m + 2) %
          factorialGapLargePrefixPrivatePowerModulus m ≠ 0 := by
  have hden :=
    factorialGapLargePrefixPrivatePowerModulus_two_step_den_anchors hm
  have hmodOne :
      1 < factorialGapLargePrefixPrivatePowerModulus m :=
    one_lt_factorialGapLargePrefixPrivatePowerModulus hm hs
  exact
    ⟨hden.1, hden.2,
      factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
        hmodOne hden.1,
      factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
        hmodOne hden.2⟩

/-- A cofinal supply of factorial gaps with a prime divisor beyond the
index yields cofinally many large-prime divisors of reduced predecessor
denominators.  The factorial-sized lower bound forces the least hit beyond
the requested cutoff. -/
theorem cofinal_large_prime_factorialGap_denominator_anchors
    (hsource :
      ∀ A : ℕ, ∃ q n : ℕ,
        q.Prime ∧
        2 ≤ n ∧
        A < n ∧
        q ∣ n.factorial - 1 ∧
        n < q) :
    ∀ B : ℕ, ∃ m q : ℕ,
      B < m ∧
      q.Prime ∧
      m < q ∧
      q ∣ (factorialGapPredecessorScaledRat (m + 1)).den := by
  intro B
  obtain ⟨q, n, hq, hn2, hnLarge, hqGap, hnq⟩ :=
    hsource B.factorial
  obtain ⟨m, hm2, _hmn, hmq, hqHit, hprefix⟩ :=
    exists_large_prefix_private_factorialGap_hit
      (C := 1) hq hn2 hqGap (by simpa using hnq)
  have hmLarge : B < m := by
    by_contra hnot
    have hmLe : m ≤ B :=
      Nat.le_of_not_gt hnot
    have hfacLe : m.factorial ≤ B.factorial :=
      Nat.factorial_le hmLe
    have hgapPos : 0 < m.factorial - 1 := by
      have hfacLower : (2 : ℕ).factorial ≤ m.factorial :=
        Nat.factorial_le hm2
      norm_num at hfacLower
      omega
    have hqLe : q ≤ m.factorial - 1 :=
      Nat.le_of_dvd hgapPos hqHit
    omega
  exact
    ⟨m, q, hmLarge, hq, by simpa using hmq,
      prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_den
        hm2 hq hqHit hprefix⟩

/-- A slightly stronger cofinal source hypothesis gives anchors that are
simultaneously present at two consecutive reduced-denominator endpoints.
The second endpoint costs no new factorial-gap distribution theorem: a
prime larger than `m + 1` cannot hit either the intervening radix or the
immediately following factorial gap. -/
theorem cofinal_large_prime_factorialGap_two_step_denominator_anchors
    (hsource :
      ∀ A : ℕ, ∃ q n : ℕ,
        q.Prime ∧
        2 ≤ n ∧
        A < n ∧
        q ∣ n.factorial - 1 ∧
        n + 1 < q) :
    ∀ B : ℕ, ∃ m q : ℕ,
      B < m ∧
      q.Prime ∧
      m + 1 < q ∧
      q ∣ (factorialGapPredecessorScaledRat (m + 1)).den ∧
      q ∣ (factorialGapPredecessorScaledRat (m + 2)).den := by
  intro B
  obtain ⟨q, n, hq, hn2, hnLarge, hqGap, hnq⟩ :=
    hsource B.factorial
  obtain ⟨m, hm2, _hmn, hmq, hqHit, hprefix⟩ :=
    exists_large_prefix_private_factorialGap_hit
      (C := 1) hq hn2 hqGap (by omega)
  have hmLarge : B < m := by
    by_contra hnot
    have hmLe : m ≤ B :=
      Nat.le_of_not_gt hnot
    have hfacLe : m.factorial ≤ B.factorial :=
      Nat.factorial_le hmLe
    have hgapPos : 0 < m.factorial - 1 := by
      have hfacLower : (2 : ℕ).factorial ≤ m.factorial :=
        Nat.factorial_le hm2
      norm_num at hfacLower
      omega
    have hqLe : q ≤ m.factorial - 1 :=
      Nat.le_of_dvd hgapPos hqHit
    omega
  have hmOneQ : m + 1 < q := by
    omega
  exact
    ⟨m, q, hmLarge, hq, hmOneQ,
      prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_den
        hm2 hq hqHit hprefix,
      prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_succ_den
        hm2 hq hmOneQ hqHit hprefix⟩

/-- Under the same cofinal hypothesis, the canonical large prefix-private
modulus—not merely one prime—divides two consecutive reduced denominators,
with nonzero combined numerator projections. -/
theorem cofinal_largePrefixPrivateModulus_two_step_crt_anchors
    (hsource :
      ∀ A : ℕ, ∃ q n : ℕ,
        q.Prime ∧
        2 ≤ n ∧
        A < n ∧
        q ∣ n.factorial - 1 ∧
        n + 1 < q) :
    ∀ B : ℕ, ∃ m : ℕ,
      B < m ∧
      (factorialGapLargePrefixPrivatePrimes m).Nonempty ∧
      factorialGapLargePrefixPrivateModulus m ∣
        (factorialGapPredecessorScaledRat (m + 1)).den ∧
      factorialGapLargePrefixPrivateModulus m ∣
        (factorialGapPredecessorScaledRat (m + 2)).den ∧
      factorialGapPredecessorGapNumeratorNat (m + 1) %
          factorialGapLargePrefixPrivateModulus m ≠ 0 ∧
      factorialGapPredecessorGapNumeratorNat (m + 2) %
          factorialGapLargePrefixPrivateModulus m ≠ 0 := by
  intro B
  obtain ⟨q, n, hq, hn2, hnLarge, hqGap, hnq⟩ :=
    hsource B.factorial
  obtain ⟨m, hm2, hmn, _hmq, hqHit, hprefix⟩ :=
    exists_large_prefix_private_factorialGap_hit
      (C := 1) hq hn2 hqGap (by omega)
  have hmLarge : B < m := by
    by_contra hnot
    have hmLe : m ≤ B :=
      Nat.le_of_not_gt hnot
    have hfacLe : m.factorial ≤ B.factorial :=
      Nat.factorial_le hmLe
    have hgapPos : 0 < m.factorial - 1 := by
      have hfacLower : (2 : ℕ).factorial ≤ m.factorial :=
        Nat.factorial_le hm2
      norm_num at hfacLower
      omega
    have hqLe : q ≤ m.factorial - 1 :=
      Nat.le_of_dvd hgapPos hqHit
    omega
  have hmOneQ : m + 1 < q := by
    omega
  have hs :
      (factorialGapLargePrefixPrivatePrimes m).Nonempty :=
    factorialGapLargePrefixPrivatePrimes_nonempty
      hm2 hq hmOneQ hqHit hprefix
  exact
    ⟨m, hmLarge, hs,
      factorialGapLargePrefixPrivateModulus_two_step_crt_anchors
        hm2 hs⟩

/-- The conditional cofinal denominator divisors automatically give nonzero
projected numerators.  This is qualitative: no lower bound for the nonzero
residues follows. -/
theorem cofinal_large_prime_factorialGap_nonzero_numerator_projections
    (hsource :
      ∀ A : ℕ, ∃ q n : ℕ,
        q.Prime ∧
        2 ≤ n ∧
        A < n ∧
        q ∣ n.factorial - 1 ∧
        n < q) :
    ∀ B : ℕ, ∃ m q : ℕ,
      B < m ∧
      q.Prime ∧
      m < q ∧
      q ∣ (factorialGapPredecessorScaledRat (m + 1)).den ∧
      factorialGapPredecessorGapNumeratorNat (m + 1) % q ≠ 0 := by
  intro B
  obtain ⟨m, q, hmLarge, hq, hmq, hqDen⟩ :=
    cofinal_large_prime_factorialGap_denominator_anchors hsource B
  exact
    ⟨m, q, hmLarge, hq, hmq, hqDen,
      factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_prime_dvd_den
        hq hqDen⟩

/-! ## Accumulated private powers across finite intervals -/

/-- The full composite-divisor persistence law iterates across any finite
interval on which the divisor is coprime to every intervening radix and
factorial gap.  In particular, no prime-power valuation is lost merely by
transporting the modulus to a remote endpoint. -/
theorem dvd_factorialGapPredecessorScaledRat_den_of_interval_coprime
    {m n d : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hdV : d ∣ (factorialGapPredecessorScaledRat m).den)
    (havoid :
      ∀ j : ℕ, m ≤ j → j < n →
        Nat.Coprime d j ∧ Nat.Coprime d (j.factorial - 1)) :
    d ∣ (factorialGapPredecessorScaledRat n).den := by
  induction n, hmn using Nat.le_induction with
  | base =>
      exact hdV
  | succ n hmn ih =>
      have ihDen :
          d ∣ (factorialGapPredecessorScaledRat n).den :=
        ih (fun j hmj hjn =>
          havoid j hmj (hjn.trans (Nat.lt_succ_self n)))
      have hj := havoid n hmn (Nat.lt_succ_self n)
      exact
        dvd_factorialGapPredecessorScaledRat_succ_den_of_coprime
          (hm.trans hmn) ihDen hj.1 hj.2

/-- A nontrivial composite divisor transported through an avoidance
interval gives a nonzero endpoint numerator projection modulo the entire
divisor, not only modulo its radical. -/
theorem
    predecessorGapNumeratorNat_mod_ne_zero_of_interval_coprime
    {m n d : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hdOne : 1 < d)
    (hdV : d ∣ (factorialGapPredecessorScaledRat m).den)
    (havoid :
      ∀ j : ℕ, m ≤ j → j < n →
        Nat.Coprime d j ∧ Nat.Coprime d (j.factorial - 1)) :
    factorialGapPredecessorGapNumeratorNat n % d ≠ 0 := by
  apply
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
      hdOne
  exact
    dvd_factorialGapPredecessorScaledRat_den_of_interval_coprime
      hm hmn hdV havoid

/-- Heterogeneous accumulated-modulus assembly.  Each pairwise-coprime
composite component may enter at its own index and then travel through its
own avoidance interval; their product divides the common remote reduced
denominator. -/
theorem
    pairwiseCoprimeCompositeFinset_prod_dvd_den_of_interval_coprime
    {ι : Type*} {s : Finset ι}
    (start modulus : ι → ℕ) {n : ℕ}
    (hpair :
      (s : Set ι).Pairwise
        (fun i k => Nat.Coprime (modulus i) (modulus k)))
    (hstartLower :
      ∀ i ∈ s, 2 ≤ start i)
    (hstartLe :
      ∀ i ∈ s, start i ≤ n)
    (hstartDen :
      ∀ i ∈ s,
        modulus i ∣
          (factorialGapPredecessorScaledRat (start i)).den)
    (havoid :
      ∀ i ∈ s, ∀ j : ℕ, start i ≤ j → j < n →
        Nat.Coprime (modulus i) j ∧
          Nat.Coprime (modulus i) (j.factorial - 1)) :
    (∏ i ∈ s, modulus i) ∣
      (factorialGapPredecessorScaledRat n).den := by
  classical
  apply Finset.prod_dvd_of_isRelPrime
  · intro i hi k hk hik
    exact
      Nat.coprime_iff_isRelPrime.mp
        (hpair hi hk hik)
  · intro i hi
    exact
      dvd_factorialGapPredecessorScaledRat_den_of_interval_coprime
        (hstartLower i hi) (hstartLe i hi)
        (hstartDen i hi) (havoid i hi)

/-- If one accumulated component is nontrivial and all components are
positive, the common-endpoint numerator is nonzero modulo the full
heterogeneous product. -/
theorem
    predecessorGapNumeratorNat_mod_pairwiseCoprimeCompositeFinset_prod_ne_zero
    {ι : Type*} {s : Finset ι}
    (start modulus : ι → ℕ) {n : ℕ}
    (hpair :
      (s : Set ι).Pairwise
        (fun i k => Nat.Coprime (modulus i) (modulus k)))
    (hpositive :
      ∀ i ∈ s, 0 < modulus i)
    (hnontrivial :
      ∃ i ∈ s, 1 < modulus i)
    (hstartLower :
      ∀ i ∈ s, 2 ≤ start i)
    (hstartLe :
      ∀ i ∈ s, start i ≤ n)
    (hstartDen :
      ∀ i ∈ s,
        modulus i ∣
          (factorialGapPredecessorScaledRat (start i)).den)
    (havoid :
      ∀ i ∈ s, ∀ j : ℕ, start i ≤ j → j < n →
        Nat.Coprime (modulus i) j ∧
          Nat.Coprime (modulus i) (j.factorial - 1)) :
    factorialGapPredecessorGapNumeratorNat n %
        (∏ i ∈ s, modulus i) ≠ 0 := by
  classical
  have hprodDen :
      (∏ i ∈ s, modulus i) ∣
        (factorialGapPredecessorScaledRat n).den :=
    pairwiseCoprimeCompositeFinset_prod_dvd_den_of_interval_coprime
      start modulus hpair hstartLower hstartLe hstartDen havoid
  obtain ⟨i, hi, hiOne⟩ := hnontrivial
  have hiDvd :
      modulus i ∣ ∏ k ∈ s, modulus k :=
    Finset.dvd_prod_of_mem modulus hi
  have hprodPos :
      0 < ∏ k ∈ s, modulus k :=
    Finset.prod_pos hpositive
  have hprodOne :
      1 < ∏ k ∈ s, modulus k :=
    hiOne.trans_le (Nat.le_of_dvd hprodPos hiDvd)
  exact
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
      hprodOne hprodDen

/-- Canonical accumulated-modulus assembly.  The prime-power modulus born
at each selected factorial gap enters at `m + 1`; distinct birth moduli are
automatically coprime, so individual avoidance intervals are the only
remaining transport hypotheses needed at a common endpoint. -/
theorem
    factorialGapLargePrefixPrivatePowerModulus_finset_prod_dvd_den
    {s : Finset ℕ} {n : ℕ}
    (hlower : ∀ m ∈ s, 2 ≤ m)
    (hend : ∀ m ∈ s, m + 1 ≤ n)
    (havoid :
      ∀ m ∈ s, ∀ j : ℕ, m + 1 ≤ j → j < n →
        Nat.Coprime
            (factorialGapLargePrefixPrivatePowerModulus m) j ∧
          Nat.Coprime
            (factorialGapLargePrefixPrivatePowerModulus m)
            (j.factorial - 1)) :
    (∏ m ∈ s, factorialGapLargePrefixPrivatePowerModulus m) ∣
      (factorialGapPredecessorScaledRat n).den := by
  exact
    pairwiseCoprimeCompositeFinset_prod_dvd_den_of_interval_coprime
      (s := s)
      (start := fun m => m + 1)
      (modulus := factorialGapLargePrefixPrivatePowerModulus)
      (n := n)
      (factorialGapLargePrefixPrivatePowerModulus_pairwise_coprime
        hlower)
      (fun m hmMem =>
        Nat.le_succ_of_le (hlower m hmMem))
      hend
      (fun m hmMem =>
        factorialGapLargePrefixPrivatePowerModulus_dvd_succ_den
          (hlower m hmMem))
      havoid

/-- If at least one selected source gap has a canonical private prime,
the accumulated canonical product also gives a nonzero numerator
projection at the common endpoint. -/
theorem
    predecessorGapNumeratorNat_mod_largePrefixPrivatePowerModulus_finset_prod_ne_zero
    {s : Finset ℕ} {n : ℕ}
    (hlower : ∀ m ∈ s, 2 ≤ m)
    (hend : ∀ m ∈ s, m + 1 ≤ n)
    (hnonempty :
      ∃ m ∈ s,
        (factorialGapLargePrefixPrivatePrimes m).Nonempty)
    (havoid :
      ∀ m ∈ s, ∀ j : ℕ, m + 1 ≤ j → j < n →
        Nat.Coprime
            (factorialGapLargePrefixPrivatePowerModulus m) j ∧
          Nat.Coprime
            (factorialGapLargePrefixPrivatePowerModulus m)
            (j.factorial - 1)) :
    factorialGapPredecessorGapNumeratorNat n %
        (∏ m ∈ s, factorialGapLargePrefixPrivatePowerModulus m) ≠ 0 := by
  apply
    predecessorGapNumeratorNat_mod_pairwiseCoprimeCompositeFinset_prod_ne_zero
      (s := s)
      (start := fun m => m + 1)
      (modulus := factorialGapLargePrefixPrivatePowerModulus)
      (n := n)
      (factorialGapLargePrefixPrivatePowerModulus_pairwise_coprime
        hlower)
  · intro m hmMem
    exact
      Nat.pos_of_dvd_of_pos
        (factorialGapLargePrefixPrivatePowerModulus_dvd_gap
          (hlower m hmMem))
        (Nat.sub_pos_of_lt
          (Nat.one_lt_factorial.mpr (hlower m hmMem)))
  · obtain ⟨m, hmMem, hmNonempty⟩ := hnonempty
    exact
      ⟨m, hmMem,
        one_lt_factorialGapLargePrefixPrivatePowerModulus
          (hlower m hmMem) hmNonempty⟩
  · intro m hmMem
    exact Nat.le_succ_of_le (hlower m hmMem)
  · exact hend
  · intro m hmMem
    exact
      factorialGapLargePrefixPrivatePowerModulus_dvd_succ_den
        (hlower m hmMem)
  · exact havoid

/-- Canonical source indices whose complete private prime-power moduli are
still active at endpoint `n`.  Activity is exactly the absence of every
intervening radix and factorial-gap collision. -/
def factorialGapActivePrefixPrivatePowerSources (n : ℕ) : Finset ℕ :=
  (Finset.Ico 2 n).filter fun m =>
    ∀ j ∈ Finset.Ico (m + 1) n,
      Nat.Coprime
          (factorialGapLargePrefixPrivatePowerModulus m) j ∧
        Nat.Coprime
          (factorialGapLargePrefixPrivatePowerModulus m)
          (j.factorial - 1)

/-- Exact membership characterization for the canonical active-source
set. -/
theorem mem_factorialGapActivePrefixPrivatePowerSources_iff
    {m n : ℕ} :
    m ∈ factorialGapActivePrefixPrivatePowerSources n ↔
      2 ≤ m ∧
      m < n ∧
      ∀ j : ℕ, m + 1 ≤ j → j < n →
        Nat.Coprime
            (factorialGapLargePrefixPrivatePowerModulus m) j ∧
          Nat.Coprime
            (factorialGapLargePrefixPrivatePowerModulus m)
            (j.factorial - 1) := by
  simp only [
    factorialGapActivePrefixPrivatePowerSources,
    Finset.mem_filter,
    Finset.mem_Ico
  ]
  constructor
  · rintro ⟨⟨hm2, hmn⟩, hactive⟩
    exact
      ⟨hm2, hmn,
        fun j hmj hjn => hactive j ⟨hmj, hjn⟩⟩
  · rintro ⟨hm2, hmn, hactive⟩
    exact
      ⟨⟨hm2, hmn⟩,
        fun j hj => hactive j hj.1 hj.2⟩

/-- The canonical accumulated modulus at endpoint `n`: multiply the full
private prime-power modulus from every source that remains active there. -/
def factorialGapAccumulatedPrivatePowerModulus (n : ℕ) : ℕ :=
  ∏ m ∈ factorialGapActivePrefixPrivatePowerSources n,
    factorialGapLargePrefixPrivatePowerModulus m

/-- The canonical accumulated modulus is an actual divisor of the reduced
predecessor-gap denominator at its endpoint. -/
theorem factorialGapAccumulatedPrivatePowerModulus_dvd_den
    {n : ℕ} :
    factorialGapAccumulatedPrivatePowerModulus n ∣
      (factorialGapPredecessorScaledRat n).den := by
  have hlower :
      ∀ m ∈ factorialGapActivePrefixPrivatePowerSources n, 2 ≤ m := by
    intro m hmMem
    exact
      (mem_factorialGapActivePrefixPrivatePowerSources_iff.1
        hmMem).1
  have hend :
      ∀ m ∈ factorialGapActivePrefixPrivatePowerSources n,
        m + 1 ≤ n := by
    intro m hmMem
    have hmn :=
      (mem_factorialGapActivePrefixPrivatePowerSources_iff.1
        hmMem).2.1
    omega
  have havoid :
      ∀ m ∈ factorialGapActivePrefixPrivatePowerSources n,
        ∀ j : ℕ, m + 1 ≤ j → j < n →
          Nat.Coprime
              (factorialGapLargePrefixPrivatePowerModulus m) j ∧
            Nat.Coprime
              (factorialGapLargePrefixPrivatePowerModulus m)
              (j.factorial - 1) := by
    intro m hmMem
    exact
      (mem_factorialGapActivePrefixPrivatePowerSources_iff.1
        hmMem).2.2
  exact
    factorialGapLargePrefixPrivatePowerModulus_finset_prod_dvd_den
      hlower hend havoid

/-- An active source with at least one private prime makes the canonical
accumulated modulus nontrivial. -/
theorem one_lt_factorialGapAccumulatedPrivatePowerModulus
    {n : ℕ}
    (hnonempty :
      ∃ m ∈ factorialGapActivePrefixPrivatePowerSources n,
        (factorialGapLargePrefixPrivatePrimes m).Nonempty) :
    1 < factorialGapAccumulatedPrivatePowerModulus n := by
  obtain ⟨m, hmMem, hmNonempty⟩ := hnonempty
  have hm2 :
      2 ≤ m :=
    (mem_factorialGapActivePrefixPrivatePowerSources_iff.1
      hmMem).1
  have hmDvd :
      factorialGapLargePrefixPrivatePowerModulus m ∣
        factorialGapAccumulatedPrivatePowerModulus n := by
    exact
      Finset.dvd_prod_of_mem
        factorialGapLargePrefixPrivatePowerModulus hmMem
  have haccPos :
      0 < factorialGapAccumulatedPrivatePowerModulus n := by
    exact
      Nat.pos_of_dvd_of_pos
        factorialGapAccumulatedPrivatePowerModulus_dvd_den
        (factorialGapPredecessorScaledRat n).den_pos
  exact
    (one_lt_factorialGapLargePrefixPrivatePowerModulus hm2
      hmNonempty).trans_le
      (Nat.le_of_dvd haccPos hmDvd)

/-- At every endpoint with one nontrivial active source, the reduced
numerator has a nonzero projection modulo the canonical accumulated
modulus. -/
theorem
    predecessorGapNumeratorNat_mod_accumulatedPrivatePowerModulus_ne_zero
    {n : ℕ}
    (hnonempty :
      ∃ m ∈ factorialGapActivePrefixPrivatePowerSources n,
        (factorialGapLargePrefixPrivatePrimes m).Nonempty) :
    factorialGapPredecessorGapNumeratorNat n %
        factorialGapAccumulatedPrivatePowerModulus n ≠ 0 := by
  exact
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
      (one_lt_factorialGapAccumulatedPrivatePowerModulus hnonempty)
      factorialGapAccumulatedPrivatePowerModulus_dvd_den

/-! ## Componentwise private-prime sources -/

/-- A source-gap/prime pair.  The second coordinate is a prime selected
from the canonical private set born at the first coordinate. -/
abbrev FactorialGapPrivatePrimeSource := Σ _m : ℕ, ℕ

/-- The complete prime-power contribution carried by one source pair. -/
def factorialGapPrivatePrimeSourcePower
    (a : FactorialGapPrivatePrimeSource) : ℕ :=
  a.2 ^ (a.1.factorial - 1).factorization a.2

/-- At its birth step, every canonical private prime-power component is
coprime to the exact reduction normalizer and satisfies the explicit
normalized numerator congruence.  Hence the full prime-power projection,
not merely its prime reduction, is obtained by multiplying `-v_m` by an
invertible normalizer. -/
theorem factorialGapPrivatePrimeSourcePower_entry_projection
    {a : FactorialGapPrivatePrimeSource}
    (ha2 : 2 ≤ a.1)
    (haMem :
      a.2 ∈ factorialGapLargePrefixPrivatePrimes a.1) :
    Nat.Coprime
        (factorialGapPrivatePrimeSourcePower a)
        (factorialGapPredecessorTransitionNormalizer a.1) ∧
      Int.ModEq
        (factorialGapPrivatePrimeSourcePower a : ℤ)
        (factorialGapPredecessorTransitionNormalizer a.1 *
          factorialGapPredecessorGapNumerator (a.1 + 1))
        (-(factorialGapPredecessorScaledRat a.1).den : ℤ) := by
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff
      ha2).1 haMem
  have hqOld :
      ¬a.2 ∣
        (factorialGapPredecessorScaledRat a.1).den :=
    not_dvd_factorialGapPredecessorScaledRat_den_of_prefixPrivate
      hqData.1 hqData.2.2.2
  have hqG :
      Nat.Coprime a.2
        (factorialGapPredecessorTransitionNormalizer a.1) :=
    prime_coprime_factorialGapPredecessorTransitionNormalizer_of_dvd_gap
      ha2 hqData.1 hqData.2.1 hqOld
  have hgapNe : a.1.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt
        (Nat.one_lt_factorial.mpr ha2)).ne'
  have hpowerDvd :
      factorialGapPrivatePrimeSourcePower a ∣
        a.1.factorial - 1 := by
    unfold factorialGapPrivatePrimeSourcePower
    exact
      (hqData.1.pow_dvd_iff_le_factorization hgapNe).2 le_rfl
  exact
    ⟨by
      unfold factorialGapPrivatePrimeSourcePower
      exact hqG.pow_left _,
      transitionNormalizer_mul_predecessorGapNumerator_modEq_neg_den
        ha2 hpowerDvd⟩

/-- Canonical individual prime-power sources still active at endpoint
`n`.  Unlike the coarser source-index construction, one colliding prime
does not discard the other surviving primes born at the same gap. -/
def factorialGapActivePrivatePrimeSources
    (n : ℕ) : Finset FactorialGapPrivatePrimeSource :=
  ((Finset.Ico 2 n).sigma fun m =>
      factorialGapLargePrefixPrivatePrimes m).filter fun a =>
    ∀ j ∈ Finset.Ico (a.1 + 1) n,
      Nat.Coprime a.2 j ∧
        Nat.Coprime a.2 (j.factorial - 1)

/-- Exact membership characterization for active individual prime-power
sources. -/
theorem mem_factorialGapActivePrivatePrimeSources_iff
    {a : FactorialGapPrivatePrimeSource} {n : ℕ} :
    a ∈ factorialGapActivePrivatePrimeSources n ↔
      2 ≤ a.1 ∧
      a.1 < n ∧
      a.2 ∈ factorialGapLargePrefixPrivatePrimes a.1 ∧
      ∀ j : ℕ, a.1 + 1 ≤ j → j < n →
        Nat.Coprime a.2 j ∧
          Nat.Coprime a.2 (j.factorial - 1) := by
  simp only [
    factorialGapActivePrivatePrimeSources,
    Finset.mem_filter,
    Finset.mem_sigma,
    Finset.mem_Ico
  ]
  constructor
  · rintro ⟨⟨⟨hm2, hmn⟩, hqMem⟩, hactive⟩
    exact
      ⟨hm2, hmn, hqMem,
        fun j hmj hjn => hactive j ⟨hmj, hjn⟩⟩
  · rintro ⟨hm2, hmn, hqMem, hactive⟩
    exact
      ⟨⟨⟨hm2, hmn⟩, hqMem⟩,
        fun j hj => hactive j hj.1 hj.2⟩

/-- An already-born individual component survives one more endpoint
exactly when its prime avoids the new radix and the new factorial gap. -/
theorem
    mem_factorialGapActivePrivatePrimeSources_succ_iff_of_source_lt
    {a : FactorialGapPrivatePrimeSource} {n : ℕ}
    (han : a.1 < n) :
    a ∈ factorialGapActivePrivatePrimeSources (n + 1) ↔
      a ∈ factorialGapActivePrivatePrimeSources n ∧
      Nat.Coprime a.2 n ∧
      Nat.Coprime a.2 (n.factorial - 1) := by
  constructor
  · intro ha
    have haData :=
      mem_factorialGapActivePrivatePrimeSources_iff.1 ha
    have hnew :=
      haData.2.2.2 n (by omega) (by omega)
    refine ⟨?_, hnew.1, hnew.2⟩
    apply mem_factorialGapActivePrivatePrimeSources_iff.2
    refine ⟨haData.1, han, haData.2.2.1, ?_⟩
    intro j haj hjn
    exact haData.2.2.2 j haj (by omega)
  · rintro ⟨ha, hradix, hgap⟩
    have haData :=
      mem_factorialGapActivePrivatePrimeSources_iff.1 ha
    apply mem_factorialGapActivePrivatePrimeSources_iff.2
    refine ⟨haData.1, by omega, haData.2.2.1, ?_⟩
    intro j haj hjSucc
    by_cases hjn : j < n
    · exact haData.2.2.2 j haj hjn
    · have hjeq : j = n := by omega
      simpa [hjeq] using And.intro hradix hgap

/-- The components born at the new source gap are precisely the
canonical prefix-private primes of that gap.  Their avoidance interval at
the entry endpoint is empty. -/
theorem
    mk_mem_factorialGapActivePrivatePrimeSources_succ_iff
    {n q : ℕ} (hn : 2 ≤ n) :
    (⟨n, q⟩ : FactorialGapPrivatePrimeSource) ∈
        factorialGapActivePrivatePrimeSources (n + 1) ↔
      q ∈ factorialGapLargePrefixPrivatePrimes n := by
  constructor
  · intro h
    exact
      (mem_factorialGapActivePrivatePrimeSources_iff.1 h).2.2.1
  · intro hq
    apply mem_factorialGapActivePrivatePrimeSources_iff.2
    change
      2 ≤ n ∧
        n < n + 1 ∧
        q ∈ factorialGapLargePrefixPrivatePrimes n ∧
        ∀ j : ℕ, n + 1 ≤ j → j < n + 1 →
          Nat.Coprime q j ∧
            Nat.Coprime q (j.factorial - 1)
    refine ⟨hn, by omega, hq, ?_⟩
    intro j hnj hjSucc
    omega

/-- The already-active components that survive the transition from
endpoint `n` to endpoint `n + 1`. -/
def factorialGapSurvivingPrivatePrimeSources
    (n : ℕ) : Finset FactorialGapPrivatePrimeSource :=
  (factorialGapActivePrivatePrimeSources n).filter fun a =>
    Nat.Coprime a.2 n ∧
      Nat.Coprime a.2 (n.factorial - 1)

/-- The already-active components killed at the transition from endpoint
`n` to endpoint `n + 1` by a collision with the new radix or factorial
gap. -/
def factorialGapKilledPrivatePrimeSources
    (n : ℕ) : Finset FactorialGapPrivatePrimeSource :=
  (factorialGapActivePrivatePrimeSources n).filter fun a =>
    ¬(Nat.Coprime a.2 n ∧
      Nat.Coprime a.2 (n.factorial - 1))

/-- The components born from the new source gap `n! - 1`. -/
def factorialGapBornPrivatePrimeSources
    (n : ℕ) : Finset FactorialGapPrivatePrimeSource :=
  ({n} : Finset ℕ).sigma fun m =>
    factorialGapLargePrefixPrivatePrimes m

@[simp]
theorem mem_factorialGapSurvivingPrivatePrimeSources
    {a : FactorialGapPrivatePrimeSource} {n : ℕ} :
    a ∈ factorialGapSurvivingPrivatePrimeSources n ↔
      a ∈ factorialGapActivePrivatePrimeSources n ∧
      Nat.Coprime a.2 n ∧
      Nat.Coprime a.2 (n.factorial - 1) := by
  simp [factorialGapSurvivingPrivatePrimeSources]

@[simp]
theorem mem_factorialGapKilledPrivatePrimeSources
    {a : FactorialGapPrivatePrimeSource} {n : ℕ} :
    a ∈ factorialGapKilledPrivatePrimeSources n ↔
      a ∈ factorialGapActivePrivatePrimeSources n ∧
      ¬(Nat.Coprime a.2 n ∧
        Nat.Coprime a.2 (n.factorial - 1)) := by
  simp [factorialGapKilledPrivatePrimeSources]

@[simp]
theorem mem_factorialGapBornPrivatePrimeSources
    {a : FactorialGapPrivatePrimeSource} {n : ℕ} :
    a ∈ factorialGapBornPrivatePrimeSources n ↔
      a.1 = n ∧
      a.2 ∈ factorialGapLargePrefixPrivatePrimes n := by
  obtain ⟨m, q⟩ := a
  simp only [
    factorialGapBornPrivatePrimeSources,
    Finset.mem_sigma,
    Finset.mem_singleton
  ]
  constructor
  · rintro ⟨hmn, hq⟩
    exact ⟨hmn, by simpa [hmn] using hq⟩
  · rintro ⟨hmn, hq⟩
    exact ⟨hmn, by simpa [hmn] using hq⟩

/-- The old active set is partitioned exactly into survivors and killed
components. -/
theorem
    factorialGapSurvivingPrivatePrimeSources_union_killed
    (n : ℕ) :
    factorialGapSurvivingPrivatePrimeSources n ∪
        factorialGapKilledPrivatePrimeSources n =
      factorialGapActivePrivatePrimeSources n := by
  ext a
  simp only [
    Finset.mem_union,
    mem_factorialGapSurvivingPrivatePrimeSources,
    mem_factorialGapKilledPrivatePrimeSources
  ]
  tauto

/-- The survivor and killed portions of the active set are disjoint. -/
theorem
    factorialGapSurvivingPrivatePrimeSources_disjoint_killed
    (n : ℕ) :
    Disjoint
      (factorialGapSurvivingPrivatePrimeSources n)
      (factorialGapKilledPrivatePrimeSources n) := by
  rw [Finset.disjoint_left]
  intro a haSurvive haKilled
  have hsurvive :=
    (mem_factorialGapSurvivingPrivatePrimeSources.1 haSurvive).2
  have hkilled :=
    (mem_factorialGapKilledPrivatePrimeSources.1 haKilled).2
  exact hkilled hsurvive

/-- The successor active set consists exactly of the surviving old
components and the components born at the new source gap. -/
theorem
    factorialGapActivePrivatePrimeSources_succ_eq_surviving_union_born
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapActivePrivatePrimeSources (n + 1) =
      factorialGapSurvivingPrivatePrimeSources n ∪
        factorialGapBornPrivatePrimeSources n := by
  ext a
  constructor
  · intro ha
    have haData :=
      mem_factorialGapActivePrivatePrimeSources_iff.1 ha
    by_cases han : a.1 < n
    · apply Finset.mem_union_left
      exact
        (mem_factorialGapSurvivingPrivatePrimeSources).2
          ((mem_factorialGapActivePrivatePrimeSources_succ_iff_of_source_lt
            han).1 ha)
    · apply Finset.mem_union_right
      apply mem_factorialGapBornPrivatePrimeSources.2
      have hsource : a.1 = n := by omega
      exact
        ⟨hsource, by
          simpa [hsource] using haData.2.2.1⟩
  · intro ha
    rcases Finset.mem_union.1 ha with haSurvive | haBorn
    · have hdata :=
        mem_factorialGapSurvivingPrivatePrimeSources.1 haSurvive
      have han :=
        (mem_factorialGapActivePrivatePrimeSources_iff.1 hdata.1).2.1
      exact
        (mem_factorialGapActivePrivatePrimeSources_succ_iff_of_source_lt
          han).2 hdata
    · have hborn :=
        mem_factorialGapBornPrivatePrimeSources.1 haBorn
      obtain ⟨m, q⟩ := a
      change m = n ∧
        q ∈ factorialGapLargePrefixPrivatePrimes n at hborn
      rcases hborn with ⟨rfl, hq⟩
      exact
        (mk_mem_factorialGapActivePrivatePrimeSources_succ_iff
          hn).2 hq

/-- No component born at source `n` can already be an old survivor:
survivors have strictly smaller source index. -/
theorem
    factorialGapSurvivingPrivatePrimeSources_disjoint_born
    {n : ℕ} :
    Disjoint
      (factorialGapSurvivingPrivatePrimeSources n)
      (factorialGapBornPrivatePrimeSources n) := by
  rw [Finset.disjoint_left]
  intro a haSurvive haBorn
  have han :=
    (mem_factorialGapActivePrivatePrimeSources_iff.1
      (mem_factorialGapSurvivingPrivatePrimeSources.1
        haSurvive).1).2.1
  have heq :=
    (mem_factorialGapBornPrivatePrimeSources.1 haBorn).1
  omega

/-- Distinct active source pairs carry distinct primes, even if they were
born at different gaps.  Prefix privacy at the later gap rules out reuse
of every earlier gap prime. -/
theorem factorialGapActivePrivatePrimeSources_prime_ne
    {n : ℕ}
    {a b : FactorialGapPrivatePrimeSource}
    (ha : a ∈ factorialGapActivePrivatePrimeSources n)
    (hb : b ∈ factorialGapActivePrivatePrimeSources n)
    (hab : a ≠ b) :
    a.2 ≠ b.2 := by
  rcases a with ⟨m, q⟩
  rcases b with ⟨k, r⟩
  have haData :=
    mem_factorialGapActivePrivatePrimeSources_iff.1 ha
  have hbData :=
    mem_factorialGapActivePrivatePrimeSources_iff.1 hb
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff
      haData.1).1 haData.2.2.1
  have hrData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff
      hbData.1).1 hbData.2.2.1
  change q ≠ r
  rcases lt_trichotomy m k with hmk | hmk | hkm
  · intro hqr
    subst r
    have hqEarlier :
        Nat.Coprime q (m.factorial - 1) :=
      hrData.2.2.2 m haData.1 hmk
    exact
      (hqData.1.coprime_iff_not_dvd.mp hqEarlier)
        hqData.2.1
  · subst k
    intro hqr
    subst r
    exact hab rfl
  · intro hqr
    subst r
    have hqEarlier :
        Nat.Coprime q (k.factorial - 1) :=
      hqData.2.2.2 k hbData.1 hkm
    exact
      (hqData.1.coprime_iff_not_dvd.mp hqEarlier)
        hrData.2.1

/-- Active individual prime-power components are pairwise coprime. -/
theorem factorialGapActivePrivatePrimeSourcePowers_pairwise_coprime
    {n : ℕ} :
    (factorialGapActivePrivatePrimeSources n :
        Set FactorialGapPrivatePrimeSource).Pairwise
      (fun a b =>
        Nat.Coprime
          (factorialGapPrivatePrimeSourcePower a)
          (factorialGapPrivatePrimeSourcePower b)) := by
  intro a ha b hb hab
  have haData :=
    mem_factorialGapActivePrivatePrimeSources_iff.1 ha
  have hbData :=
    mem_factorialGapActivePrivatePrimeSources_iff.1 hb
  have hqPrime :=
    ((mem_factorialGapLargePrefixPrivatePrimes_iff
      haData.1).1 haData.2.2.1).1
  have hrPrime :=
    ((mem_factorialGapLargePrefixPrivatePrimes_iff
      hbData.1).1 hbData.2.2.1).1
  unfold factorialGapPrivatePrimeSourcePower
  exact
    Nat.Coprime.pow_left _
      (Nat.Coprime.pow_right _
        ((Nat.coprime_primes hqPrime hrPrime).2
          (factorialGapActivePrivatePrimeSources_prime_ne
            ha hb hab)))

/-- Every active individual component enters at the successor of its
source gap with its complete factorial-gap valuation. -/
theorem factorialGapPrivatePrimeSourcePower_dvd_entry_den
    {n : ℕ} {a : FactorialGapPrivatePrimeSource}
    (ha : a ∈ factorialGapActivePrivatePrimeSources n) :
    factorialGapPrivatePrimeSourcePower a ∣
      (factorialGapPredecessorScaledRat (a.1 + 1)).den := by
  have haData :=
    mem_factorialGapActivePrivatePrimeSources_iff.1 ha
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff
      haData.1).1 haData.2.2.1
  have hgapNe : a.1.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt
        (Nat.one_lt_factorial.mpr haData.1)).ne'
  have hqPow :
      a.2 ^ (a.1.factorial - 1).factorization a.2 ∣
        a.1.factorial - 1 :=
    (hqData.1.pow_dvd_iff_le_factorization hgapNe).2 le_rfl
  exact
    (prefixPrivate_prime_pow_dvd_factorialGapPredecessorScaledRat_two_step_den
      haData.1 hqData.1 hqData.2.2.1 hqPow
        hqData.2.2.2).1

/-- The complete canonical componentwise accumulator at endpoint `n`. -/
def factorialGapComponentwiseAccumulatedPrivatePowerModulus
    (n : ℕ) : ℕ :=
  ∏ a ∈ factorialGapActivePrivatePrimeSources n,
    factorialGapPrivatePrimeSourcePower a

/-- The product of the old components that survive the transition from
endpoint `n` to endpoint `n + 1`. -/
def factorialGapSurvivingPrivatePowerModulus
    (n : ℕ) : ℕ :=
  ∏ a ∈ factorialGapSurvivingPrivatePrimeSources n,
    factorialGapPrivatePrimeSourcePower a

/-- The product of the old components killed at the transition from
endpoint `n` to endpoint `n + 1`. -/
def factorialGapKilledPrivatePowerModulus
    (n : ℕ) : ℕ :=
  ∏ a ∈ factorialGapKilledPrivatePrimeSources n,
    factorialGapPrivatePrimeSourcePower a

/-- The squarefree prime-label product of the components killed at one
transition. -/
def factorialGapKilledPrivatePrimeModulus
    (n : ℕ) : ℕ :=
  ∏ a ∈ factorialGapKilledPrivatePrimeSources n, a.2

/-- The complete killed prime-power mass actually visible in the exact
transition normalizer. -/
def factorialGapKilledTransitionGcd (n : ℕ) : ℕ :=
  Nat.gcd
    (factorialGapKilledPrivatePowerModulus n)
    (factorialGapPredecessorTransitionNormalizer n)

/-- The excess killed prime-power multiplicity left after cancelling
everything visible in the transition normalizer. -/
def factorialGapKilledMultiplicityDefect (n : ℕ) : ℕ :=
  factorialGapKilledPrivatePowerModulus n /
    factorialGapKilledTransitionGcd n

/-- The transition normalizer after removing the complete common factor
with the killed prime-power product. -/
def factorialGapReducedTransitionNormalizer (n : ℕ) : ℕ :=
  factorialGapPredecessorTransitionNormalizer n /
    factorialGapKilledTransitionGcd n

/-- The part of the new factorial gap not selected into the canonical
prefix-private prime-power birth modulus. -/
def factorialGapUnselectedBirthCofactor (n : ℕ) : ℕ :=
  (n.factorial - 1) /
    factorialGapLargePrefixPrivatePowerModulus n

/-- The selected birth modulus and its complementary cofactor recover the
entire new factorial gap. -/
theorem
    factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapLargePrefixPrivatePowerModulus n *
        factorialGapUnselectedBirthCofactor n =
      n.factorial - 1 := by
  unfold factorialGapUnselectedBirthCofactor
  exact
    Nat.mul_div_cancel'
      (factorialGapLargePrefixPrivatePowerModulus_dvd_gap hn)

/-- The selected birth modulus is positive at every nontrivial
factorial-gap step. -/
theorem factorialGapLargePrefixPrivatePowerModulus_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < factorialGapLargePrefixPrivatePowerModulus n := by
  exact
    Nat.pos_of_dvd_of_pos
      (factorialGapLargePrefixPrivatePowerModulus_dvd_gap hn)
      (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hn))

/-- The complementary unselected part of a nontrivial factorial gap is
positive. -/
theorem factorialGapUnselectedBirthCofactor_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < factorialGapUnselectedBirthCofactor n := by
  have hproductPos :
      0 <
        factorialGapLargePrefixPrivatePowerModulus n *
          factorialGapUnselectedBirthCofactor n := by
    rw [
      factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
        hn
    ]
    exact Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hn)
  exact
    pos_of_mul_pos_right hproductPos
      (Nat.zero_le _)

/-- A prime appearing in the unselected part of `n! - 1` is either the
boundary prime `n + 1` or already appeared in an earlier factorial gap.
Thus the birth cofactor contains only boundary/repeat support, while every
genuinely new prime larger than the boundary is selected into `P_n` with
its complete valuation. -/
theorem prime_dvd_unselectedBirthCofactor_boundary_or_repeat
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n) :
    q = n + 1 ∨
      ∃ k : ℕ, 2 ≤ k ∧ k < n ∧ q ∣ k.factorial - 1 := by
  have hfactor :=
    factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
      hn
  have hqGap : q ∣ n.factorial - 1 := by
    rw [← hfactor]
    exact dvd_mul_of_dvd_right hqBirth _
  have hqGt : n < q :=
    prime_dvd_factorial_sub_one_gt hq hqGap
  have hqNotSelected :
      q ∉ factorialGapLargePrefixPrivatePrimes n := by
    intro hqSelected
    have hgapNe : n.factorial - 1 ≠ 0 := by
      exact
        (Nat.sub_pos_of_lt
          (Nat.one_lt_factorial.mpr hn)).ne'
    have hpowDvdSelected :
        q ^ (n.factorial - 1).factorization q ∣
          factorialGapLargePrefixPrivatePowerModulus n := by
      unfold factorialGapLargePrefixPrivatePowerModulus
      exact
        Finset.dvd_prod_of_mem
          (fun r =>
            r ^ (n.factorial - 1).factorization r)
          hqSelected
    have hpowSuccDvdGap :
        q ^ ((n.factorial - 1).factorization q + 1) ∣
          n.factorial - 1 := by
      rw [pow_succ]
      have hdiv :
          q ^ (n.factorial - 1).factorization q * q ∣
            factorialGapLargePrefixPrivatePowerModulus n *
              factorialGapUnselectedBirthCofactor n :=
        mul_dvd_mul hpowDvdSelected hqBirth
      rwa [hfactor] at hdiv
    have hcontra :
        (n.factorial - 1).factorization q + 1 ≤
          (n.factorial - 1).factorization q :=
      (hq.pow_dvd_iff_le_factorization hgapNe).1
        hpowSuccDvdGap
    omega
  by_cases hboundary : q = n + 1
  · exact Or.inl hboundary
  · right
    have hlarge : n + 1 < q := by omega
    have hnotPrefix :
        ¬∀ k : ℕ, 2 ≤ k → k < n →
          Nat.Coprime q (k.factorial - 1) := by
      intro hprefix
      exact
        hqNotSelected
          ((mem_factorialGapLargePrefixPrivatePrimes_iff hn).2
            ⟨hq, hqGap, hlarge, hprefix⟩)
    have hexists :
        ∃ k : ℕ, 2 ≤ k ∧ k < n ∧
          ¬Nat.Coprime q (k.factorial - 1) := by
      by_contra hnone
      push_neg at hnone
      exact
        hnotPrefix
          (fun k hk2 hkn => hnone k hk2 hkn)
    obtain ⟨k, hk2, hkn, hnotCoprime⟩ := hexists
    refine ⟨k, hk2, hkn, ?_⟩
    by_contra hnotDvd
    exact
      hnotCoprime
        (hq.coprime_iff_not_dvd.mpr hnotDvd)

/-! ## Cofinal private hits and reflected collisions -/

/-- Every prime `q ≥ 5` is an automatic linear-size divisor of the
factorial gap two indices earlier: `q ∣ (q - 2)! - 1`.  This Wilson
boundary family explains why an upper bound of shape
`p(n! - 1) < (1 + ε)n` on an infinite subsequence does not by itself
produce private support or irrationality. -/
theorem prime_dvd_factorial_two_before_sub_one
    {q : ℕ}
    (hq : q.Prime)
    (hq5 : 5 ≤ q) :
    q ∣ (q - 2).factorial - 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  have hwilson :
      ((q - 1).factorial : ZMod q) = -1 :=
    ZMod.wilsons_lemma q
  have hfacNat :
      (q - 1).factorial =
        (q - 1) * (q - 2).factorial := by
    have hpred : q - 2 + 1 = q - 1 := by omega
    rw [← hpred]
    exact Nat.factorial_succ (q - 2)
  have hfacCast :
      ((q - 1 : ℕ) : ZMod q) *
          ((q - 2).factorial : ZMod q) = -1 := by
    rw [← Nat.cast_mul, ← hfacNat]
    exact hwilson
  have hpredCast :
      ((q - 1 : ℕ) : ZMod q) = -1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have htwoBeforeCast :
      ((q - 2).factorial : ZMod q) = 1 := by
    rw [hpredCast] at hfacCast
    calc
      ((q - 2).factorial : ZMod q) =
          -((-1 : ZMod q) * ((q - 2).factorial : ZMod q)) := by ring
      _ = -(-1) := by rw [hfacCast]
      _ = 1 := by ring
  have hmod :
      (q - 2).factorial ≡ 1 [MOD q] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).1 (by
      simpa using htwoBeforeCast)
  have hone : 1 ≤ (q - 2).factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact (Nat.modEq_iff_dvd' hone).1 hmod.symm

/-- Product of the literal factorial gaps through `B`.  This is the
finite counting scale for first-hit arguments: every prime already seen
by time `B` divides this one integer. -/
def factorialGapDenominatorProduct (B : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 B, (k.factorial - 1)

/-- The finite factorial-gap product is positive. -/
theorem factorialGapDenominatorProduct_pos (B : ℕ) :
    0 < factorialGapDenominatorProduct B := by
  unfold factorialGapDenominatorProduct
  apply Finset.prod_pos
  intro k hk
  have hk2 : 2 ≤ k :=
    (Finset.mem_Icc.mp hk).1
  exact Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hk2)

/-- Prime-product pigeonhole for factorial gaps.  If a finite set of
distinct primes has product larger than all gaps through `B`, at least
one of those primes has not occurred in any factorial gap through `B`.

This finite pigeonhole statement compares prime-product growth with the
elementary size of `factorialGapDenominatorProduct B`, without assuming a
large prime factor at a preselected index. -/
theorem exists_prime_avoiding_factorialGapProduct_of_lt
    {B : ℕ} {s : Finset ℕ}
    (hprime : ∀ q ∈ s, q.Prime)
    (hlt :
      factorialGapDenominatorProduct B <
        ∏ q ∈ s, q) :
    ∃ q ∈ s, ¬q ∣ factorialGapDenominatorProduct B := by
  by_contra hnot
  push_neg at hnot
  have hpair :
      (s : Set ℕ).Pairwise
        (Function.onFun Nat.Coprime id) := by
    intro q hqs r hrs hqr
    exact
      (Nat.coprime_primes
        (hprime q hqs)
        (hprime r hrs)).2 hqr
  have hprodDvd :
      (∏ q ∈ s, q) ∣
        factorialGapDenominatorProduct B := by
    have hlcmDvd :
        s.lcm id ∣ factorialGapDenominatorProduct B :=
      Finset.lcm_dvd fun q hqs => hnot q hqs
    simpa only [Finset.lcm_eq_prod hpair] using hlcmDvd
  have hle :
      (∏ q ∈ s, q) ≤
        factorialGapDenominatorProduct B :=
    Nat.le_of_dvd
      (factorialGapDenominatorProduct_pos B)
      hprodDvd
  omega

/-- Wilson's automatic hit at `q - 2`, combined with the prime-product
pigeonhole, produces a genuinely prefix-private hit after `B` while
retaining the explicit upper bound `m ≤ q - 2`.

Thus an asymptotic comparison between a prime product and the elementary
gap product yields cofinal private anchors whose supporting prime is
controlled from above by the chosen prime window.  This complements
large-prime-factor theorems, which control the prime from below but may
lose all upper control when passing to the least hit. -/
theorem exists_late_prefixPrivate_factorialGap_hit_of_primeProduct_lt
    {B : ℕ} {s : Finset ℕ}
    (hprime : ∀ q ∈ s, q.Prime)
    (hfive : ∀ q ∈ s, 5 ≤ q)
    (hlt :
      factorialGapDenominatorProduct B <
        ∏ q ∈ s, q) :
    ∃ q ∈ s, ∃ m,
      B < m ∧
        m ≤ q - 2 ∧
        q.Prime ∧
        q ∣ m.factorial - 1 ∧
        ∀ k, 2 ≤ k → k < m →
          Nat.Coprime q (k.factorial - 1) := by
  obtain ⟨q, hqs, hqAvoid⟩ :=
    exists_prime_avoiding_factorialGapProduct_of_lt
      hprime hlt
  have hq : q.Prime :=
    hprime q hqs
  have hq5 : 5 ≤ q :=
    hfive q hqs
  have hqHit :
      q ∣ (q - 2).factorial - 1 :=
    prime_dvd_factorial_two_before_sub_one hq hq5
  obtain ⟨m, hm2, hmq, _hmqZero, hmHit, hprefix⟩ :=
    exists_large_prefix_private_factorialGap_hit
      (p := q) (n := q - 2) (C := 0)
      hq (by omega) hqHit (by simpa using hq.pos)
  have hBm : B < m := by
    by_contra hnot
    have hmB : m ≤ B :=
      Nat.le_of_not_gt hnot
    have hmMem : m ∈ Finset.Icc 2 B :=
      Finset.mem_Icc.mpr ⟨hm2, hmB⟩
    apply hqAvoid
    exact hmHit.trans
      (Finset.dvd_prod_of_mem
        (fun k : ℕ => k.factorial - 1)
        hmMem)
  exact
    ⟨q, hqs, m, hBm, hmq, hq, hmHit, hprefix⟩

/-- Cofinal prefix-private factorial-gap primes are unconditional.  Given a
cutoff `B`, choose a prime `q ≥ B! + 5`; Wilson supplies the hit at `q - 2`.
The least hit for `q` cannot occur at or below `B`, since then the prime
would be at most `B! - 1`.

Thus cofinal private support needs no external large-prime-factor theorem.
Quantitative applications still need a sharper estimate, such as the
prime-product pigeonhole above, to control `q` relative to its least hit. -/
theorem cofinal_prefixPrivate_factorialGap_hits :
    ∀ B : ℕ, ∃ q m : ℕ,
      B < m ∧
        q.Prime ∧
        m < q ∧
        q ∣ m.factorial - 1 ∧
        ∀ k, 2 ≤ k → k < m →
          Nat.Coprime q (k.factorial - 1) := by
  intro B
  obtain ⟨q, hqLower, hq⟩ :=
    Nat.exists_infinite_primes (B.factorial + 5)
  have hq5 : 5 ≤ q := by
    omega
  have hqHit :
      q ∣ (q - 2).factorial - 1 :=
    prime_dvd_factorial_two_before_sub_one hq hq5
  obtain ⟨m, hm2, hmq, _hmqZero, hmHit, hprefix⟩ :=
    exists_large_prefix_private_factorialGap_hit
      (p := q) (n := q - 2) (C := 0)
      hq (by omega) hqHit (by simpa using hq.pos)
  have hBm : B < m := by
    by_contra hnot
    have hmB : m ≤ B :=
      Nat.le_of_not_gt hnot
    have hfacLe :
        m.factorial ≤ B.factorial :=
      Nat.factorial_le hmB
    have hgapPos :
        0 < m.factorial - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hm2)
    have hqLe :
        q ≤ m.factorial - 1 :=
      Nat.le_of_dvd hgapPos hmHit
    omega
  exact
    ⟨q, m, hBm, hq, by omega, hmHit, hprefix⟩

/-- Wilson reflection for an odd factorial-gap index.  If a prime `q > n`
divides `n! - 1`, then the complementary factorial at `q - n - 1` is also
`1` modulo `q`.  This is the exact collision mechanism behind the
`n! - 1` extension of Stewart's small-prime-factor subsequence: such a
factor is not automatically prefix-private. -/
theorem prime_dvd_reflected_factorialGap_of_odd
    {q n : ℕ}
    (hq : q.Prime)
    (hn : Odd n)
    (hnq : n < q)
    (hqdvd : q ∣ n.factorial - 1) :
    q ∣ (q - n - 1).factorial - 1 := by
  have hfacOne : 1 ≤ n.factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hmod :
      n.factorial ≡ 1 [MOD q] := by
    exact ((Nat.modEq_iff_dvd' hfacOne).2 hqdvd).symm
  have hcast :
      (n.factorial : ZMod q) = 1 :=
    by
      simpa using
        (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  letI : Fact q.Prime := ⟨hq⟩
  have hwilson :
      ((q - 1).factorial : ZMod q) = -1 :=
    ZMod.wilsons_lemma q
  have hnlePred : n ≤ q - 1 := by omega
  have hfactorialNat :
      (q - 1 - n).factorial * (q - 1).descFactorial n =
        (q - 1).factorial :=
    Nat.factorial_mul_descFactorial hnlePred
  have hfactorialCast :
      ((q - 1 - n).factorial : ZMod q) *
          ((q - 1).descFactorial n : ZMod q) =
        ((q - 1).factorial : ZMod q) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun x : ℕ => (x : ZMod q)) hfactorialNat
  have hprod :
      ((q - 1 - n).factorial : ZMod q) * (-1) = -1 := by
    simpa [ZMod.cast_descFactorial (show n ≤ q by omega),
      hn.neg_one_pow, hcast] using hfactorialCast.trans hwilson
  have hrefCast :
      ((q - 1 - n).factorial : ZMod q) = 1 := by
    calc
      ((q - 1 - n).factorial : ZMod q) =
          -(((q - 1 - n).factorial : ZMod q) * (-1)) := by ring
      _ = -(-1) := by rw [hprod]
      _ = 1 := by ring
  have hrefMod :
      (q - 1 - n).factorial ≡ 1 [MOD q] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).1 (by
      simpa using hrefCast)
  have hrefOne : 1 ≤ (q - 1 - n).factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hrefDvd :
      q ∣ (q - 1 - n).factorial - 1 :=
    (Nat.modEq_iff_dvd' hrefOne).1 hrefMod.symm
  have hindex : q - 1 - n = q - n - 1 := by omega
  simpa [hindex] using hrefDvd

/-- If the reflected index lies in the same factorial block and
`q < 2n + 1`, the two distinct full `q`-hits force `q` into the block's
collision core.  In particular, a Stewart-scale divisor `q < 1.381n`
cannot be counted as private support merely from its size. -/
theorem prime_dvd_factorialBlockCollisionCore_of_odd_reflection
    {p q n : ℕ}
    (hq : q.Prime)
    (hn : Odd n)
    (hpn : p ≤ n)
    (hnmem : n ∈ factorialBlockIndices p)
    (hrefmem : q - n - 1 ∈ factorialBlockIndices p)
    (hqUpper : q < 2 * n + 1)
    (hqdvd : q ∣ n.factorial - 1) :
    q ∣ factorialBlockCollisionCore p := by
  have hnq : n < q :=
    prime_dvd_factorial_sub_one_gt hq hqdvd
  have href :
      q ∣ (q - n - 1).factorial - 1 :=
    prime_dvd_reflected_factorialGap_of_odd
      hq hn hnq hqdvd
  have hqden :
      q ∣ factorialGapDenominator n := by
    simpa [factorialGapDenominator] using hqdvd
  have htwo :
      q ^ 1 ∣ factorialBlockCollisionCore p := by
    apply
      (factorialBlock_primePower_dvd_collisionCore_iff_two_hits
        hq (by norm_num) hpn hqden).2
    refine ⟨n, hnmem, q - n - 1, hrefmem, ?_, ?_, ?_⟩
    · omega
    · simpa [factorialGapDenominator] using hqdvd
    · simpa [factorialGapDenominator] using href
  simpa using htwo

/-- A reflected upper-half collision survives predecessor-factorial
normalization: the same prime `q` lies in the normalized collision core,
not only in the unnormalised core. -/
theorem prime_dvd_factorialBlockNormalizedCollisionCore_of_odd_reflection
    {p q n : ℕ}
    (hq : q.Prime)
    (hn : Odd n)
    (hpn : p ≤ n)
    (hnmem : n ∈ factorialBlockIndices p)
    (hrefmem : q - n - 1 ∈ factorialBlockIndices p)
    (hqUpper : q < 2 * n + 1)
    (hqdvd : q ∣ n.factorial - 1) :
    q ∣ factorialBlockNormalizedCollisionCore p := by
  have hqden :
      q ∣ factorialGapDenominator n := by
    simpa [factorialGapDenominator] using hqdvd
  exact
    factorialBlockPrime_dvd_normalizedCollisionCore_of_upper_hit_of_dvd_collisionCore
      hq hpn hqden
      (prime_dvd_factorialBlockCollisionCore_of_odd_reflection
        hq hn hpn hnmem hrefmem hqUpper hqdvd)

/-- Incidence-count form of the reflected collision: the prime `q` hits at
least two displayed factorial gaps in the block. -/
theorem one_lt_factorialBlockPrimeHitCount_of_odd_reflection
    {p q n : ℕ}
    (hq : q.Prime)
    (hn : Odd n)
    (hpn : p ≤ n)
    (hnmem : n ∈ factorialBlockIndices p)
    (hrefmem : q - n - 1 ∈ factorialBlockIndices p)
    (hqUpper : q < 2 * n + 1)
    (hqdvd : q ∣ n.factorial - 1) :
    1 <
      ((factorialBlockIndices p).filter fun i =>
        q ∣ factorialGapDenominator i).card := by
  have hqden :
      q ∣ factorialGapDenominator n := by
    simpa [factorialGapDenominator] using hqdvd
  have hnorm :
      q ^ 1 ∣ factorialBlockNormalizedCollisionCore p := by
    simpa using
      (prime_dvd_factorialBlockNormalizedCollisionCore_of_odd_reflection
        hq hn hpn hnmem hrefmem hqUpper hqdvd)
  have hcount :=
    (factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount
      hq (by norm_num) hpn hqden).1 hnorm
  simpa using hcount

/-- Wilson's theorem excludes the apparent boundary exception: for
`n ≥ 2`, the prime `n + 1` cannot divide `n! - 1`. -/
theorem prime_succ_not_dvd_factorial_sub_one
    {n : ℕ} (hn : 2 ≤ n)
    (hprime : (n + 1).Prime) :
    ¬(n + 1) ∣ n.factorial - 1 := by
  intro hdiv
  have hfacOne : 1 ≤ n.factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hmod :
      n.factorial ≡ 1 [MOD n + 1] := by
    exact
      ((Nat.modEq_iff_dvd' hfacOne).2 hdiv).symm
  have hcast :
      (n.factorial : ZMod (n + 1)) = 1 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  letI : Fact (n + 1).Prime := ⟨hprime⟩
  have hwilson :
      (n.factorial : ZMod (n + 1)) = -1 := by
    simpa using (ZMod.wilsons_lemma (n + 1))
  have honeNeg :
      (1 : ZMod (n + 1)) = -1 :=
    hcast.symm.trans hwilson
  have htwoZero :
      (2 : ZMod (n + 1)) = 0 := by
    calc
      (2 : ZMod (n + 1)) = 1 + 1 := by norm_num
      _ = -1 + 1 := congrArg (fun x => x + 1) honeNeg
      _ = 0 := neg_add_cancel 1
  have hsuccDvdTwo : n + 1 ∣ 2 :=
    (ZMod.natCast_eq_zero_iff _ _).1 htwoZero
  have hsuccLeTwo : n + 1 ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hsuccDvdTwo
  omega

/-- A prefix-private Wilson endpoint is globally private, not merely private
inside one chosen block.  If `q - 2` is the first index whose factorial is
one modulo the prime `q`, then it is also the last: Wilson excludes `q - 1`,
while every factorial from `q` onward is zero modulo `q`.

This feeds the terminal-owner computational probe.  Two primes satisfying
this hypothesis at comparable scales give two factorial-gap support channels
which can never later enter a collision core. -/
theorem prime_terminal_factorialGap_hit_iff
    {q k : ℕ}
    (hq : q.Prime)
    (hq5 : 5 ≤ q)
    (hprefix :
      ∀ j : ℕ, 2 ≤ j → j < q - 2 →
        Nat.Coprime q (j.factorial - 1))
    (hk2 : 2 ≤ k) :
    q ∣ k.factorial - 1 ↔ k = q - 2 := by
  constructor
  · intro hqk
    by_cases hlt : k < q - 2
    · exact False.elim
        ((hq.coprime_iff_not_dvd.mp (hprefix k hk2 hlt)) hqk)
    by_cases heq : k = q - 2
    · exact heq
    have hgt : q - 2 < k := by omega
    by_cases hpred : k = q - 1
    · subst k
      have hsucc : q - 1 + 1 = q := by omega
      have hnotRaw :=
        prime_succ_not_dvd_factorial_sub_one
          (n := q - 1) (by omega) (by rw [hsucc]; exact hq)
      have hnot : ¬q ∣ (q - 1).factorial - 1 := by
        simpa only [hsucc] using hnotRaw
      exact False.elim (hnot hqk)
    have hqkLe : q ≤ k := by omega
    have hqFac : q ∣ k.factorial :=
      Nat.dvd_factorial hq.pos hqkLe
    have hfacCoprime : Nat.Coprime k.factorial (k.factorial - 1) :=
      (Nat.coprime_self_sub_right (Nat.factorial_pos k)).2
        (Nat.coprime_one_right k.factorial)
    have hqCoprime : Nat.Coprime q (k.factorial - 1) :=
      hfacCoprime.of_dvd_left hqFac
    exact False.elim ((hq.coprime_iff_not_dvd.mp hqCoprime) hqk)
  · intro hk
    subst k
    exact prime_dvd_factorial_two_before_sub_one hq hq5

/-- Consequently every prime in the unselected birth cofactor is repeat
support from a strictly earlier factorial gap. -/
theorem prime_dvd_unselectedBirthCofactor_repeat
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n) :
    ∃ k : ℕ, 2 ≤ k ∧ k < n ∧ q ∣ k.factorial - 1 := by
  rcases
      prime_dvd_unselectedBirthCofactor_boundary_or_repeat
        hn hq hqBirth with hboundary | hrepeat
  · have hfactor :=
      factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
        hn
    have hqGap : q ∣ n.factorial - 1 := by
      rw [← hfactor]
      exact dvd_mul_of_dvd_right hqBirth _
    subst q
    exact
      (prime_succ_not_dvd_factorial_sub_one hn hq hqGap).elim
  · exact hrepeat

/-- Conversely, a prime dividing both the current factorial gap and one
strictly earlier gap cannot be selected as prefix-private, so its complete
current support remains in the unselected birth cofactor. -/
theorem prime_dvd_unselectedBirthCofactor_of_repeat
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqGap : q ∣ n.factorial - 1)
    (hrepeat :
      ∃ k : ℕ, 2 ≤ k ∧ k < n ∧ q ∣ k.factorial - 1) :
    q ∣ factorialGapUnselectedBirthCofactor n := by
  obtain ⟨k, hk2, hkn, hqEarlier⟩ := hrepeat
  have hqNotSelected :
      q ∉ factorialGapLargePrefixPrivatePrimes n := by
    intro hqSelected
    have hqData :=
      (mem_factorialGapLargePrefixPrivatePrimes_iff hn).1 hqSelected
    exact
      (hq.coprime_iff_not_dvd.mp
        (hqData.2.2.2 k hk2 hkn))
        hqEarlier
  have hqCoprimeSelected :
      Nat.Coprime q
        (factorialGapLargePrefixPrivatePowerModulus n) := by
    unfold factorialGapLargePrefixPrivatePowerModulus
    apply Nat.Coprime.prod_right
    intro r hrMem
    have hrPrime :=
      ((mem_factorialGapLargePrefixPrivatePrimes_iff hn).1 hrMem).1
    have hqr : q ≠ r := by
      intro hEq
      subst r
      exact hqNotSelected hrMem
    exact
      (Nat.coprime_primes hq hrPrime).2 hqr
        |>.pow_right _
  have hqProduct :
      q ∣
        factorialGapLargePrefixPrivatePowerModulus n *
          factorialGapUnselectedBirthCofactor n := by
    rw [
      factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
        hn
    ]
    exact hqGap
  rcases hq.dvd_mul.mp hqProduct with hqSelected | hqBirth
  · exact
      (hq.coprime_iff_not_dvd.mp hqCoprimeSelected hqSelected).elim
  · exact hqBirth

/-- Repeat support in the unselected birth cofactor is separated from the
current endpoint by at least one whole factorial gap.  Moreover it is visible
in the exact intervening descending-factorial collision and obeys the
corresponding power bound. -/
theorem prime_dvd_unselectedBirthCofactor_interval_collision
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n) :
    ∃ k : ℕ, 2 ≤ k ∧ k + 1 < n ∧
      q ∣ n.descFactorial (n - k) - 1 ∧
      q ≤ n ^ (n - k) := by
  obtain ⟨k, hk2, hkn, hqOld⟩ :=
    prime_dvd_unselectedBirthCofactor_repeat hn hq hqBirth
  have hfactor :=
    factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
      hn
  have hqGap : q ∣ n.factorial - 1 := by
    rw [← hfactor]
    exact dvd_mul_of_dvd_right hqBirth _
  have hkFar : k + 1 < n := by
    have hnotNext :=
      prime_not_dvd_succ_factorial_sub_one_of_dvd
        hq (by omega : 1 ≤ k) hqOld
    by_contra hnotFar
    have hEq : n = k + 1 := by omega
    exact hnotNext (by simpa only [hEq] using hqGap)
  have hqGcd :
      q ∣ Nat.gcd (k.factorial - 1) (n.factorial - 1) :=
    Nat.dvd_gcd hqOld hqGap
  have hqDesc :
      q ∣ n.descFactorial (n - k) - 1 := by
    have hEq :=
      gcd_factorial_sub_one_eq_descFactorial_sub_one hkn
    have hqDescGcd :
        q ∣ Nat.gcd (k.factorial - 1)
          (n.descFactorial (n - k) - 1) := by
      rwa [← hEq]
    exact
      dvd_trans hqDescGcd
        (Nat.gcd_dvd_right
          (k.factorial - 1)
          (n.descFactorial (n - k) - 1))
  have hgapPos : 0 < k.factorial - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hk2)
  have hgcdPos :
      0 < Nat.gcd (k.factorial - 1) (n.factorial - 1) :=
    Nat.gcd_pos_of_pos_left _ hgapPos
  have hqLeGcd :
      q ≤ Nat.gcd (k.factorial - 1) (n.factorial - 1) :=
    Nat.le_of_dvd hgcdPos hqGcd
  have hgcdLe :
      Nat.gcd (k.factorial - 1) (n.factorial - 1) ≤
        n ^ (n - k) :=
    _root_.Erdos68.gcd_factorial_sub_one_le_pow_gap hk2 hkn
  exact ⟨k, hk2, hkFar, hqDesc, hqLeGcd.trans hgcdLe⟩

/-- Once two factors are individually `1` modulo `q`, their product is
`1` modulo `q²` exactly when their first-order quotient residues cancel.
This is the elementary linearization behind nonterminal factorial square
hits. -/
theorem square_dvd_mul_sub_one_iff_quotient_balance
    {q a b A B : ℕ} (hqPos : 0 < q)
    (ha : a = 1 + q * A)
    (hb : b = 1 + q * B) :
    q ^ 2 ∣ a * b - 1 ↔ q ∣ A + B := by
  have hshape :
      a * b - 1 = q * ((A + B) + q * (A * B)) := by
    rw [ha, hb]
    calc
      (1 + q * A) * (1 + q * B) - 1 =
          (1 + q * ((A + B) + q * (A * B))) - 1 := by
        congr 1
        ring
      _ = q * ((A + B) + q * (A * B)) := by omega
  rw [hshape, pow_two]
  have hquadratic : q ∣ q * (A * B) :=
    dvd_mul_right q (A * B)
  constructor
  · intro hsq
    have htail :
        q ∣ (A + B) + q * (A * B) :=
      Nat.dvd_of_mul_dvd_mul_left hqPos hsq
    exact (Nat.dvd_add_iff_left hquadratic).mpr htail
  · intro hbalance
    have htail :
        q ∣ (A + B) + q * (A * B) :=
      (Nat.dvd_add_iff_left hquadratic).mp hbalance
    obtain ⟨t, ht⟩ := htail
    refine ⟨t, ?_⟩
    rw [ht]
    ring

/-- Nonterminal square-lift criterion.  If a prime `q`
already divides both factorial gaps at `k<n`, then the intervening
descending factorial is also `1` modulo `q`.  The later hit lifts from
`q` to `q²` exactly when the two first-order quotient residues—one from
`k!` and one from the intervening factorial block—sum to zero modulo
`q`. -/
theorem
    factorialGap_square_dvd_later_iff_blockQuotient_balance
    {k n q : ℕ} (hkn : k < n) (hq : q.Prime)
    (hqEarlier : q ∣ k.factorial - 1)
    (hqLater : q ∣ n.factorial - 1) :
    q ^ 2 ∣ n.factorial - 1 ↔
      q ∣
        (k.factorial - 1) / q +
          (n.descFactorial (n - k) - 1) / q := by
  let D := n.descFactorial (n - k)
  have hk : n - k ≤ n := Nat.sub_le _ _
  have hfactorial :
      k.factorial * D = n.factorial := by
    have h := Nat.factorial_mul_descFactorial hk
    simpa [D, Nat.sub_sub_self (Nat.le_of_lt hkn)] using h
  have hqGcd :
      q ∣ Nat.gcd (k.factorial - 1) (n.factorial - 1) :=
    Nat.dvd_gcd hqEarlier hqLater
  have hqBlock : q ∣ D - 1 := by
    have hEq :=
      gcd_factorial_sub_one_eq_descFactorial_sub_one hkn
    have hqDescGcd :
        q ∣ Nat.gcd (k.factorial - 1) (D - 1) := by
      simpa [D, hEq] using hqGcd
    exact hqDescGcd.trans (Nat.gcd_dvd_right _ _)
  have hfacShape :
      k.factorial =
        1 + q * ((k.factorial - 1) / q) := by
    have hmul :
        (k.factorial - 1) / q * q =
          k.factorial - 1 :=
      Nat.div_mul_cancel hqEarlier
    rw [Nat.mul_comm] at hmul
    have hfacOne : 1 ≤ k.factorial :=
      Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    omega
  have hblockShape :
      D = 1 + q * ((D - 1) / q) := by
    have hmul :
        (D - 1) / q * q = D - 1 :=
      Nat.div_mul_cancel hqBlock
    rw [Nat.mul_comm] at hmul
    have hDOne : 1 ≤ D := by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hk))
    omega
  simpa [D, hfactorial] using
    (square_dvd_mul_sub_one_iff_quotient_balance
      hq.pos hfacShape hblockShape)

/-- A prime supported by the unselected cofactor cannot simultaneously be
one of the selected prefix-private birth primes. -/
theorem prime_not_mem_largePrefixPrivatePrimes_of_dvd_unselectedBirthCofactor
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n) :
    q ∉ factorialGapLargePrefixPrivatePrimes n := by
  intro hqSelected
  have hgapNe : n.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt
        (Nat.one_lt_factorial.mpr hn)).ne'
  have hpowDvdSelected :
      q ^ (n.factorial - 1).factorization q ∣
        factorialGapLargePrefixPrivatePowerModulus n := by
    unfold factorialGapLargePrefixPrivatePowerModulus
    exact
      Finset.dvd_prod_of_mem
        (fun r =>
          r ^ (n.factorial - 1).factorization r)
        hqSelected
  have hfactor :=
    factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
      hn
  have hpowSuccDvdGap :
      q ^ ((n.factorial - 1).factorization q + 1) ∣
        n.factorial - 1 := by
    rw [pow_succ]
    have hdiv :
        q ^ (n.factorial - 1).factorization q * q ∣
          factorialGapLargePrefixPrivatePowerModulus n *
            factorialGapUnselectedBirthCofactor n :=
      mul_dvd_mul hpowDvdSelected hqBirth
    rwa [hfactor] at hdiv
  have hcontra :
      (n.factorial - 1).factorization q + 1 ≤
        (n.factorial - 1).factorization q :=
    (hq.pow_dvd_iff_le_factorization hgapNe).1
      hpowSuccDvdGap
  omega

/-- The unselected cofactor retains the complete current-gap valuation of
each prime in its support: no part of a repeated prime power is removed by
the selected birth product. -/
theorem primePower_dvd_unselectedBirthCofactor_of_prime_dvd
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n) :
    q ^ (n.factorial - 1).factorization q ∣
      factorialGapUnselectedBirthCofactor n := by
  have hgapNe : n.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt
        (Nat.one_lt_factorial.mpr hn)).ne'
  have hqNotSelected :=
    prime_not_mem_largePrefixPrivatePrimes_of_dvd_unselectedBirthCofactor
      hn hq hqBirth
  have hqCoprimeSelected :
      Nat.Coprime q
        (factorialGapLargePrefixPrivatePowerModulus n) := by
    unfold factorialGapLargePrefixPrivatePowerModulus
    rw [Nat.coprime_prod_right_iff]
    intro r hr
    have hrPrime :
        r.Prime :=
      ((mem_factorialGapLargePrefixPrivatePrimes_iff hn).1 hr).1
    have hqr : q ≠ r := by
      intro heq
      subst r
      exact hqNotSelected hr
    exact
      ((Nat.coprime_primes hq hrPrime).2 hqr).pow_right _
  have hpowDvdGap :
      q ^ (n.factorial - 1).factorization q ∣
        n.factorial - 1 :=
    (hq.pow_dvd_iff_le_factorization hgapNe).2 le_rfl
  have hfactor :=
    factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
      hn
  have hpowDvdMul :
      q ^ (n.factorial - 1).factorization q ∣
        factorialGapLargePrefixPrivatePowerModulus n *
          factorialGapUnselectedBirthCofactor n := by
    rwa [hfactor]
  exact
    (hqCoprimeSelected.pow_left
      ((n.factorial - 1).factorization q)).dvd_of_dvd_mul_left
        hpowDvdMul

/-! ## Killed multiplicities and residual-cofactor recurrences -/

/-- Every killed source prime divides its complete source power. -/
theorem prime_dvd_factorialGapPrivatePrimeSourcePower_of_mem_killed
    {n : ℕ} {a : FactorialGapPrivatePrimeSource}
    (ha : a ∈ factorialGapKilledPrivatePrimeSources n) :
    a.2 ∣ factorialGapPrivatePrimeSourcePower a := by
  have haActive :=
    (mem_factorialGapKilledPrivatePrimeSources.1 ha).1
  have haData :=
    mem_factorialGapActivePrivatePrimeSources_iff.1 haActive
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff
      haData.1).1 haData.2.2.1
  have hgapNe : a.1.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt
        (Nat.one_lt_factorial.mpr haData.1)).ne'
  have hexpPos :
      0 < (a.1.factorial - 1).factorization a.2 :=
    hqData.1.factorization_pos_of_dvd hgapNe hqData.2.1
  unfold factorialGapPrivatePrimeSourcePower
  exact dvd_pow_self a.2 hexpPos.ne'

/-- The squarefree killed-prime modulus divides the complete killed
prime-power product. -/
theorem
    factorialGapKilledPrivatePrimeModulus_dvd_killedPrivatePowerModulus
    (n : ℕ) :
    factorialGapKilledPrivatePrimeModulus n ∣
      factorialGapKilledPrivatePowerModulus n := by
  unfold
    factorialGapKilledPrivatePrimeModulus
    factorialGapKilledPrivatePowerModulus
  apply Finset.prod_dvd_prod_of_dvd
  intro a ha
  exact
    prime_dvd_factorialGapPrivatePrimeSourcePower_of_mem_killed ha

/-- The killed transition gcd times the reduced normalizer recovers the
original transition normalizer exactly. -/
theorem
    factorialGapKilledTransitionGcd_mul_reducedTransitionNormalizer
    (n : ℕ) :
    factorialGapKilledTransitionGcd n *
        factorialGapReducedTransitionNormalizer n =
      factorialGapPredecessorTransitionNormalizer n := by
  unfold
    factorialGapKilledTransitionGcd
    factorialGapReducedTransitionNormalizer
  exact
    Nat.mul_div_cancel'
      (Nat.gcd_dvd_right
        (factorialGapKilledPrivatePowerModulus n)
        (factorialGapPredecessorTransitionNormalizer n))

/-- The killed transition gcd times the multiplicity defect recovers the
full killed prime-power product exactly. -/
theorem
    factorialGapKilledTransitionGcd_mul_killedMultiplicityDefect
    (n : ℕ) :
    factorialGapKilledTransitionGcd n *
        factorialGapKilledMultiplicityDefect n =
      factorialGapKilledPrivatePowerModulus n := by
  unfold
    factorialGapKilledTransitionGcd
    factorialGapKilledMultiplicityDefect
  exact
    Nat.mul_div_cancel'
      (Nat.gcd_dvd_left
        (factorialGapKilledPrivatePowerModulus n)
        (factorialGapPredecessorTransitionNormalizer n))

/-- The complete killed prime-power product is positive, including when the
killed set is empty. -/
theorem factorialGapKilledPrivatePowerModulus_pos (n : ℕ) :
    0 < factorialGapKilledPrivatePowerModulus n := by
  unfold factorialGapKilledPrivatePowerModulus
  exact
    Finset.prod_pos
      (fun a ha => by
        unfold factorialGapPrivatePrimeSourcePower
        have haActive :=
          (mem_factorialGapKilledPrivatePrimeSources.1 ha).1
        have haData :=
          mem_factorialGapActivePrivatePrimeSources_iff.1 haActive
        have hqData :=
          (mem_factorialGapLargePrefixPrivatePrimes_iff
            haData.1).1 haData.2.2.1
        exact pow_pos hqData.1.pos _)

/-- The surviving prime-power product is positive, including when no old
component survives the transition. -/
theorem factorialGapSurvivingPrivatePowerModulus_pos (n : ℕ) :
    0 < factorialGapSurvivingPrivatePowerModulus n := by
  unfold factorialGapSurvivingPrivatePowerModulus
  exact
    Finset.prod_pos
      (fun a ha => by
        unfold factorialGapPrivatePrimeSourcePower
        have haActive :=
          (mem_factorialGapSurvivingPrivatePrimeSources.1 ha).1
        have haData :=
          mem_factorialGapActivePrivatePrimeSources_iff.1 haActive
        have hqData :=
          (mem_factorialGapLargePrefixPrivatePrimes_iff
            haData.1).1 haData.2.2.1
        exact pow_pos hqData.1.pos _)

/-- Dividing the killed prime-power product by its transition gcd leaves a
positive multiplicity defect. -/
theorem factorialGapKilledMultiplicityDefect_pos (n : ℕ) :
    0 < factorialGapKilledMultiplicityDefect n := by
  have hproductPos :
      0 <
        factorialGapKilledTransitionGcd n *
          factorialGapKilledMultiplicityDefect n := by
    rw [
      factorialGapKilledTransitionGcd_mul_killedMultiplicityDefect
    ]
    exact factorialGapKilledPrivatePowerModulus_pos n
  exact
    pos_of_mul_pos_right hproductPos
      (Nat.zero_le _)

/-- Every prime in the excess-kill defect comes from one exact old active
source component killed at the current transition.  Its label therefore
collides with either the current radix `n` or the current factorial gap
`n! - 1`; the defect introduces no third support mechanism. -/
theorem prime_dvd_killedMultiplicityDefect_source_collision
    {n q : ℕ} (hq : q.Prime)
    (hqDefect : q ∣ factorialGapKilledMultiplicityDefect n) :
    ∃ a : FactorialGapPrivatePrimeSource,
      a ∈ factorialGapKilledPrivatePrimeSources n ∧
      a.2 = q ∧
      (q ∣ n ∨ q ∣ n.factorial - 1) := by
  have hfactor :=
    factorialGapKilledTransitionGcd_mul_killedMultiplicityDefect n
  have hqKilledPower :
      q ∣ factorialGapKilledPrivatePowerModulus n := by
    rw [← hfactor]
    exact dvd_mul_of_dvd_right hqDefect _
  unfold factorialGapKilledPrivatePowerModulus at hqKilledPower
  obtain ⟨a, ha, hqSourcePower⟩ :=
    (hq.prime.dvd_finset_prod_iff
      factorialGapPrivatePrimeSourcePower).1 hqKilledPower
  have hqLabel : q ∣ a.2 := by
    unfold factorialGapPrivatePrimeSourcePower at hqSourcePower
    exact hq.dvd_of_dvd_pow hqSourcePower
  have haKilled :=
    mem_factorialGapKilledPrivatePrimeSources.1 ha
  have haData :=
    mem_factorialGapActivePrivatePrimeSources_iff.1 haKilled.1
  have haPrime :
      a.2.Prime :=
    ((mem_factorialGapLargePrefixPrivatePrimes_iff
      haData.1).1 haData.2.2.1).1
  have hlabelEq : a.2 = q :=
    (Nat.prime_dvd_prime_iff_eq hq haPrime).1 hqLabel |>.symm
  have hcollision :
      a.2 ∣ n ∨ a.2 ∣ n.factorial - 1 := by
    by_cases han : a.2 ∣ n
    · exact Or.inl han
    · right
      by_contra haGap
      exact
        haKilled.2
          ⟨haPrime.coprime_iff_not_dvd.mpr han,
            haPrime.coprime_iff_not_dvd.mpr haGap⟩
  exact
    ⟨a, ha, hlabelEq, by simpa only [hlabelEq] using hcollision⟩

/-- Dividing the positive transition normalizer by the killed transition gcd
leaves a positive reduced outflow. -/
theorem factorialGapReducedTransitionNormalizer_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < factorialGapReducedTransitionNormalizer n := by
  have hproductPos :
      0 <
        factorialGapKilledTransitionGcd n *
          factorialGapReducedTransitionNormalizer n := by
    rw [
      factorialGapKilledTransitionGcd_mul_reducedTransitionNormalizer
    ]
    exact factorialGapPredecessorTransitionNormalizer_pos hn
  exact
    pos_of_mul_pos_right hproductPos
      (Nat.zero_le _)

/-- After cancelling the full killed/transition gcd, the remaining killed
multiplicity defect and reduced transition normalizer are coprime. -/
theorem
    factorialGapKilledMultiplicityDefect_coprime_reducedTransitionNormalizer
    {n : ℕ} (hn : 2 ≤ n) :
    Nat.Coprime
      (factorialGapKilledMultiplicityDefect n)
      (factorialGapReducedTransitionNormalizer n) := by
  have hGcdPos :
      0 <
        Nat.gcd
          (factorialGapKilledPrivatePowerModulus n)
          (factorialGapPredecessorTransitionNormalizer n) :=
    Nat.gcd_pos_of_pos_right _
      (factorialGapPredecessorTransitionNormalizer_pos hn)
  simpa [
    factorialGapKilledMultiplicityDefect,
    factorialGapReducedTransitionNormalizer,
    factorialGapKilledTransitionGcd
  ] using
    (Nat.coprime_div_gcd_div_gcd hGcdPos)

/-- The active accumulator factors into the components that survive the
next transition and those killed there. -/
theorem
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_eq_surviving_mul_killed
    (n : ℕ) :
    factorialGapComponentwiseAccumulatedPrivatePowerModulus n =
      factorialGapSurvivingPrivatePowerModulus n *
        factorialGapKilledPrivatePowerModulus n := by
  unfold
    factorialGapComponentwiseAccumulatedPrivatePowerModulus
    factorialGapSurvivingPrivatePowerModulus
    factorialGapKilledPrivatePowerModulus
  rw [
    ← factorialGapSurvivingPrivatePrimeSources_union_killed n,
    Finset.prod_union
      (factorialGapSurvivingPrivatePrimeSources_disjoint_killed n)
  ]

/-- A prime occurring in the current unselected birth mass is coprime to
the product of all old components that survive this same transition.
Indeed, every survivor is coprime to the complete current factorial gap. -/
theorem
    factorialGapSurvivingPrivatePowerModulus_coprime_of_prime_dvd_birth
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n) :
    Nat.Coprime q (factorialGapSurvivingPrivatePowerModulus n) := by
  have hbirthFactor :=
    factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
      hn
  have hqGap : q ∣ n.factorial - 1 := by
    rw [← hbirthFactor]
    exact dvd_mul_of_dvd_right hqBirth _
  unfold factorialGapSurvivingPrivatePowerModulus
  apply Nat.Coprime.prod_right
  intro a ha
  have haSurvives :=
    mem_factorialGapSurvivingPrivatePrimeSources.1 ha
  have hqLabel :
      Nat.Coprime q a.2 :=
    (haSurvives.2.2.of_dvd_right hqGap).symm
  unfold factorialGapPrivatePrimeSourcePower
  exact hqLabel.pow_right _

/-- At a repeated-birth prime, every active old component with that label
is killed, so the complete old accumulator valuation is exactly the killed
valuation.  This separates the old residual multiplicity from the
multiplicity removed by the transition. -/
theorem
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_factorization_eq_killed_of_prime_dvd_birth
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n) :
    (factorialGapComponentwiseAccumulatedPrivatePowerModulus n).factorization q =
      (factorialGapKilledPrivatePowerModulus n).factorization q := by
  have hfactor :=
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_eq_surviving_mul_killed
      n
  have hsurvivingNe :
      factorialGapSurvivingPrivatePowerModulus n ≠ 0 :=
    (factorialGapSurvivingPrivatePowerModulus_pos n).ne'
  have hkilledNe :
      factorialGapKilledPrivatePowerModulus n ≠ 0 :=
    (factorialGapKilledPrivatePowerModulus_pos n).ne'
  have hqNotSurviving :
      ¬q ∣ factorialGapSurvivingPrivatePowerModulus n :=
    hq.coprime_iff_not_dvd.mp
      (factorialGapSurvivingPrivatePowerModulus_coprime_of_prime_dvd_birth
        hn hq hqBirth)
  rw [
    hfactor,
    Nat.factorization_mul hsurvivingNe hkilledNe,
    Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hqNotSurviving,
    zero_add
  ]

/-- The product of the source-pair powers born at `n` is exactly the
canonical multiplicity-sensitive modulus `P_n`. -/
theorem factorialGapBornPrivatePrimeSourcePowers_prod
    (n : ℕ) :
    (∏ a ∈ factorialGapBornPrivatePrimeSources n,
      factorialGapPrivatePrimeSourcePower a) =
      factorialGapLargePrefixPrivatePowerModulus n := by
  unfold factorialGapBornPrivatePrimeSources
  rw [Finset.prod_sigma]
  simp [
    factorialGapPrivatePrimeSourcePower,
    factorialGapLargePrefixPrivatePowerModulus
  ]

/-- The next accumulator is exactly the product of surviving old
components and the new source-gap modulus. -/
theorem
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_succ
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapComponentwiseAccumulatedPrivatePowerModulus (n + 1) =
      factorialGapSurvivingPrivatePowerModulus n *
        factorialGapLargePrefixPrivatePowerModulus n := by
  unfold
    factorialGapComponentwiseAccumulatedPrivatePowerModulus
    factorialGapSurvivingPrivatePowerModulus
  rw [
    factorialGapActivePrivatePrimeSources_succ_eq_surviving_union_born hn,
    Finset.prod_union
      factorialGapSurvivingPrivatePrimeSources_disjoint_born,
    factorialGapBornPrivatePrimeSourcePowers_prod
  ]

/-- Exact balance law for the canonical accumulator: multiplying the next
accumulator by the killed product equals multiplying the old accumulator
by the newly born product. -/
theorem
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_succ_mul_killed
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapComponentwiseAccumulatedPrivatePowerModulus (n + 1) *
        factorialGapKilledPrivatePowerModulus n =
      factorialGapComponentwiseAccumulatedPrivatePowerModulus n *
        factorialGapLargePrefixPrivatePowerModulus n := by
  rw [
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_succ hn,
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_eq_surviving_mul_killed
  ]
  ac_rfl

/-- The componentwise canonical accumulator divides the actual reduced
denominator at its endpoint. -/
theorem
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_dvd_den
    {n : ℕ} :
    factorialGapComponentwiseAccumulatedPrivatePowerModulus n ∣
      (factorialGapPredecessorScaledRat n).den := by
  have hstartLower :
      ∀ a ∈ factorialGapActivePrivatePrimeSources n,
        2 ≤ a.1 + 1 := by
    intro a ha
    exact
      Nat.le_succ_of_le
        (mem_factorialGapActivePrivatePrimeSources_iff.1 ha).1
  have hstartLe :
      ∀ a ∈ factorialGapActivePrivatePrimeSources n,
        a.1 + 1 ≤ n := by
    intro a ha
    have han :=
      (mem_factorialGapActivePrivatePrimeSources_iff.1 ha).2.1
    omega
  have havoid :
      ∀ a ∈ factorialGapActivePrivatePrimeSources n,
        ∀ j : ℕ, a.1 + 1 ≤ j → j < n →
          Nat.Coprime (factorialGapPrivatePrimeSourcePower a) j ∧
            Nat.Coprime
              (factorialGapPrivatePrimeSourcePower a)
              (j.factorial - 1) := by
    intro a ha j haj hjn
    have hprimeAvoid :=
      (mem_factorialGapActivePrivatePrimeSources_iff.1
        ha).2.2.2 j haj hjn
    exact
      ⟨hprimeAvoid.1.pow_left _,
        hprimeAvoid.2.pow_left _⟩
  exact
    pairwiseCoprimeCompositeFinset_prod_dvd_den_of_interval_coprime
      (s := factorialGapActivePrivatePrimeSources n)
      (start := fun a => a.1 + 1)
      (modulus := factorialGapPrivatePrimeSourcePower)
      (n := n)
      factorialGapActivePrivatePrimeSourcePowers_pairwise_coprime
      hstartLower hstartLe
      (fun a ha =>
        factorialGapPrivatePrimeSourcePower_dvd_entry_den ha)
      havoid

/-- Every killed source prime divides the exact transition normalizer. -/
theorem prime_dvd_factorialGapPredecessorTransitionNormalizer_of_mem_killed
    {n : ℕ} (hn : 2 ≤ n)
    {a : FactorialGapPrivatePrimeSource}
    (ha : a ∈ factorialGapKilledPrivatePrimeSources n) :
    a.2 ∣ factorialGapPredecessorTransitionNormalizer n := by
  have haKilled :=
    mem_factorialGapKilledPrivatePrimeSources.1 ha
  have haData :=
    mem_factorialGapActivePrivatePrimeSources_iff.1 haKilled.1
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff
      haData.1).1 haData.2.2.1
  have hgapNe : a.1.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt
        (Nat.one_lt_factorial.mpr haData.1)).ne'
  have hexpPos :
      0 < (a.1.factorial - 1).factorization a.2 :=
    hqData.1.factorization_pos_of_dvd hgapNe hqData.2.1
  have hqComponent :
      a.2 ∣ factorialGapPrivatePrimeSourcePower a := by
    unfold factorialGapPrivatePrimeSourcePower
    exact dvd_pow_self a.2 hexpPos.ne'
  have hcomponentAccumulator :
      factorialGapPrivatePrimeSourcePower a ∣
        factorialGapComponentwiseAccumulatedPrivatePowerModulus n := by
    exact
      Finset.dvd_prod_of_mem
        factorialGapPrivatePrimeSourcePower haKilled.1
  have hqDen :
      a.2 ∣ (factorialGapPredecessorScaledRat n).den :=
    hqComponent.trans
      (hcomponentAccumulator.trans
        factorialGapComponentwiseAccumulatedPrivatePowerModulus_dvd_den)
  have hcollision :
      a.2 ∣ n ∨ a.2 ∣ n.factorial - 1 := by
    by_cases hqn : a.2 ∣ n
    · exact Or.inl hqn
    · right
      by_contra hqA
      exact
        haKilled.2
          ⟨hqData.1.coprime_iff_not_dvd.mpr hqn,
            hqData.1.coprime_iff_not_dvd.mpr hqA⟩
  exact
    prime_dvd_factorialGapPredecessorTransitionNormalizer_of_collision
      hn hqData.1 hqDen hcollision

/-- The product of all distinct killed prime labels divides the exact
transition normalizer.  Prime-power multiplicity may be only partly
absorbed, but every killed support prime is witnessed in the reduction
factor. -/
theorem factorialGapKilledPrivatePrimeModulus_dvd_transitionNormalizer
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapKilledPrivatePrimeModulus n ∣
      factorialGapPredecessorTransitionNormalizer n := by
  unfold factorialGapKilledPrivatePrimeModulus
  apply Finset.prod_dvd_of_isRelPrime
  · intro a ha b hb hab
    have haActive :=
      (mem_factorialGapKilledPrivatePrimeSources.1 ha).1
    have hbActive :=
      (mem_factorialGapKilledPrivatePrimeSources.1 hb).1
    have haData :=
      mem_factorialGapActivePrivatePrimeSources_iff.1 haActive
    have hbData :=
      mem_factorialGapActivePrivatePrimeSources_iff.1 hbActive
    have hqa :=
      ((mem_factorialGapLargePrefixPrivatePrimes_iff
        haData.1).1 haData.2.2.1).1
    have hqb :=
      ((mem_factorialGapLargePrefixPrivatePrimes_iff
        hbData.1).1 hbData.2.2.1).1
    exact
      Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes hqa hqb).2
          (factorialGapActivePrivatePrimeSources_prime_ne
            haActive hbActive hab))
  · intro a ha
    exact
      prime_dvd_factorialGapPredecessorTransitionNormalizer_of_mem_killed
        hn ha

/-- All distinct killed prime labels lie in the common killed/transition
factor.  Any nontrivial defect therefore records excess multiplicity, not
an entirely missed killed support prime. -/
theorem factorialGapKilledPrivatePrimeModulus_dvd_killedTransitionGcd
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapKilledPrivatePrimeModulus n ∣
      factorialGapKilledTransitionGcd n := by
  unfold factorialGapKilledTransitionGcd
  exact
    Nat.dvd_gcd
      (factorialGapKilledPrivatePrimeModulus_dvd_killedPrivatePowerModulus
        n)
      (factorialGapKilledPrivatePrimeModulus_dvd_transitionNormalizer hn)

/-- The part of the reduced denominator not accounted for by the
canonical componentwise accumulator.  The successor recurrence above
turns this quotient into the exact collision/re-entry remainder. -/
def factorialGapComponentwiseResidualCofactor (n : ℕ) : ℕ :=
  (factorialGapPredecessorScaledRat n).den /
    factorialGapComponentwiseAccumulatedPrivatePowerModulus n

/-- The reduced denominator factors exactly into the componentwise
accumulator and its residual cofactor. -/
theorem
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
    (n : ℕ) :
    factorialGapComponentwiseAccumulatedPrivatePowerModulus n *
        factorialGapComponentwiseResidualCofactor n =
      (factorialGapPredecessorScaledRat n).den := by
  unfold factorialGapComponentwiseResidualCofactor
  exact
    Nat.mul_div_cancel'
      factorialGapComponentwiseAccumulatedPrivatePowerModulus_dvd_den

/-- The residual cofactor is always positive. -/
theorem factorialGapComponentwiseResidualCofactor_pos (n : ℕ) :
    0 < factorialGapComponentwiseResidualCofactor n := by
  have hproductPos :
      0 <
        factorialGapComponentwiseAccumulatedPrivatePowerModulus n *
          factorialGapComponentwiseResidualCofactor n := by
    rw [
      factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
    ]
    exact (factorialGapPredecessorScaledRat n).den_pos
  exact
    pos_of_mul_pos_right hproductPos
      (Nat.zero_le _)

/-- Exact recurrence for the residual cofactor.  The next residual,
transition cancellation, and newly born product balance the old residual,
new factorial gap, and killed product. -/
theorem factorialGapComponentwiseResidualCofactor_succ_recurrence
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapComponentwiseResidualCofactor (n + 1) *
          factorialGapPredecessorTransitionNormalizer n *
          factorialGapLargePrefixPrivatePowerModulus n =
      factorialGapComponentwiseResidualCofactor n *
          (n.factorial - 1) *
          factorialGapKilledPrivatePowerModulus n := by
  have hnextFactor :=
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
      (n + 1)
  have holdFactor :=
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
      n
  have hden :=
    factorialGapPredecessorScaledRat_succ_den_mul_transitionNormalizer
      hn
  have hbalance :=
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_succ_mul_killed
      hn
  have hEPos :
      0 <
        factorialGapComponentwiseAccumulatedPrivatePowerModulus
          (n + 1) := by
    exact
      Nat.pos_of_dvd_of_pos
        factorialGapComponentwiseAccumulatedPrivatePowerModulus_dvd_den
        (factorialGapPredecessorScaledRat (n + 1)).den_pos
  apply Nat.mul_left_cancel hEPos
  calc
    factorialGapComponentwiseAccumulatedPrivatePowerModulus (n + 1) *
          (factorialGapComponentwiseResidualCofactor (n + 1) *
            factorialGapPredecessorTransitionNormalizer n *
            factorialGapLargePrefixPrivatePowerModulus n) =
        (factorialGapComponentwiseAccumulatedPrivatePowerModulus (n + 1) *
            factorialGapComponentwiseResidualCofactor (n + 1)) *
          factorialGapPredecessorTransitionNormalizer n *
          factorialGapLargePrefixPrivatePowerModulus n := by
            ac_rfl
    _ =
        (factorialGapPredecessorScaledRat (n + 1)).den *
          factorialGapPredecessorTransitionNormalizer n *
          factorialGapLargePrefixPrivatePowerModulus n := by
            rw [hnextFactor]
    _ =
        (factorialGapPredecessorScaledRat n).den *
          (n.factorial - 1) *
          factorialGapLargePrefixPrivatePowerModulus n := by
            rw [hden]
    _ =
        (factorialGapComponentwiseAccumulatedPrivatePowerModulus n *
            factorialGapComponentwiseResidualCofactor n) *
          (n.factorial - 1) *
          factorialGapLargePrefixPrivatePowerModulus n := by
            rw [holdFactor]
    _ =
        (factorialGapComponentwiseAccumulatedPrivatePowerModulus n *
            factorialGapLargePrefixPrivatePowerModulus n) *
          (factorialGapComponentwiseResidualCofactor n *
            (n.factorial - 1)) := by
            ac_rfl
    _ =
        (factorialGapComponentwiseAccumulatedPrivatePowerModulus (n + 1) *
            factorialGapKilledPrivatePowerModulus n) *
          (factorialGapComponentwiseResidualCofactor n *
            (n.factorial - 1)) := by
            rw [hbalance]
    _ =
        factorialGapComponentwiseAccumulatedPrivatePowerModulus (n + 1) *
          (factorialGapComponentwiseResidualCofactor n *
            (n.factorial - 1) *
            factorialGapKilledPrivatePowerModulus n) := by
            ac_rfl

/-- Cancelling the full gcd between the killed prime-power mass and the
transition normalizer leaves an exact recurrence whose right-hand
collision factor is only the genuinely unabsorbed multiplicity defect. -/
theorem
    factorialGapComponentwiseResidualCofactor_succ_reduced_recurrence
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapComponentwiseResidualCofactor (n + 1) *
          factorialGapReducedTransitionNormalizer n *
          factorialGapLargePrefixPrivatePowerModulus n =
      factorialGapComponentwiseResidualCofactor n *
          (n.factorial - 1) *
          factorialGapKilledMultiplicityDefect n := by
  have hHPos :
      0 < factorialGapKilledTransitionGcd n := by
    unfold factorialGapKilledTransitionGcd
    exact
      Nat.gcd_pos_of_pos_right _
        (factorialGapPredecessorTransitionNormalizer_pos hn)
  apply Nat.mul_left_cancel hHPos
  calc
    factorialGapKilledTransitionGcd n *
          (factorialGapComponentwiseResidualCofactor (n + 1) *
            factorialGapReducedTransitionNormalizer n *
            factorialGapLargePrefixPrivatePowerModulus n) =
        factorialGapComponentwiseResidualCofactor (n + 1) *
          (factorialGapKilledTransitionGcd n *
            factorialGapReducedTransitionNormalizer n) *
          factorialGapLargePrefixPrivatePowerModulus n := by
            ac_rfl
    _ =
        factorialGapComponentwiseResidualCofactor (n + 1) *
          factorialGapPredecessorTransitionNormalizer n *
          factorialGapLargePrefixPrivatePowerModulus n := by
            rw [
              factorialGapKilledTransitionGcd_mul_reducedTransitionNormalizer
            ]
    _ =
        factorialGapComponentwiseResidualCofactor n *
          (n.factorial - 1) *
          factorialGapKilledPrivatePowerModulus n :=
      factorialGapComponentwiseResidualCofactor_succ_recurrence hn
    _ =
        factorialGapComponentwiseResidualCofactor n *
          (n.factorial - 1) *
          (factorialGapKilledTransitionGcd n *
            factorialGapKilledMultiplicityDefect n) := by
            rw [
              factorialGapKilledTransitionGcd_mul_killedMultiplicityDefect
            ]
    _ =
        factorialGapKilledTransitionGcd n *
          (factorialGapComponentwiseResidualCofactor n *
            (n.factorial - 1) *
            factorialGapKilledMultiplicityDefect n) := by
            ac_rfl

/-- Cancelling the complete selected birth modulus leaves the intrinsic
residual-cofactor dynamics.  New residual mass can enter only through the
unselected part of the new factorial gap or through excess killed
prime-power multiplicity; the reduced transition normalizer is the exact
outflow factor. -/
theorem factorialGapComponentwiseResidualCofactor_succ_intrinsic_recurrence
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapComponentwiseResidualCofactor (n + 1) *
        factorialGapReducedTransitionNormalizer n =
      factorialGapComponentwiseResidualCofactor n *
        factorialGapUnselectedBirthCofactor n *
        factorialGapKilledMultiplicityDefect n := by
  have hPPos :
      0 < factorialGapLargePrefixPrivatePowerModulus n :=
    factorialGapLargePrefixPrivatePowerModulus_pos hn
  apply Nat.mul_right_cancel hPPos
  calc
    (factorialGapComponentwiseResidualCofactor (n + 1) *
          factorialGapReducedTransitionNormalizer n) *
        factorialGapLargePrefixPrivatePowerModulus n =
      factorialGapComponentwiseResidualCofactor n *
          (n.factorial - 1) *
          factorialGapKilledMultiplicityDefect n :=
      factorialGapComponentwiseResidualCofactor_succ_reduced_recurrence
        hn
    _ =
      factorialGapComponentwiseResidualCofactor n *
          (factorialGapLargePrefixPrivatePowerModulus n *
            factorialGapUnselectedBirthCofactor n) *
          factorialGapKilledMultiplicityDefect n := by
            rw [
              factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
                hn
            ]
    _ =
      (factorialGapComponentwiseResidualCofactor n *
          factorialGapUnselectedBirthCofactor n *
          factorialGapKilledMultiplicityDefect n) *
        factorialGapLargePrefixPrivatePowerModulus n := by
            ac_rfl

/-- Primewise form of the intrinsic residual-cofactor recurrence.  For every
prime candidate `q`, its next residual valuation plus its reduced outflow
valuation is exactly its old residual valuation plus its repeated-birth and
excess-kill inflow valuations. -/
theorem
    factorialGapComponentwiseResidualCofactor_succ_factorization_recurrence
    {n q : ℕ} (hn : 2 ≤ n) :
    (factorialGapComponentwiseResidualCofactor
        (n + 1)).factorization q +
        (factorialGapReducedTransitionNormalizer n).factorization q =
      (factorialGapComponentwiseResidualCofactor n).factorization q +
        (factorialGapUnselectedBirthCofactor n).factorization q +
        (factorialGapKilledMultiplicityDefect n).factorization q := by
  have hnextNe :
      factorialGapComponentwiseResidualCofactor (n + 1) ≠ 0 :=
    (factorialGapComponentwiseResidualCofactor_pos (n + 1)).ne'
  have hreducedNe :
      factorialGapReducedTransitionNormalizer n ≠ 0 :=
    (factorialGapReducedTransitionNormalizer_pos hn).ne'
  have holdNe :
      factorialGapComponentwiseResidualCofactor n ≠ 0 :=
    (factorialGapComponentwiseResidualCofactor_pos n).ne'
  have hbirthNe :
      factorialGapUnselectedBirthCofactor n ≠ 0 :=
    (factorialGapUnselectedBirthCofactor_pos hn).ne'
  have hdefectNe :
      factorialGapKilledMultiplicityDefect n ≠ 0 :=
    (factorialGapKilledMultiplicityDefect_pos n).ne'
  have hrec :=
    factorialGapComponentwiseResidualCofactor_succ_intrinsic_recurrence
      hn
  have hfac :=
    congrArg (fun x : ℕ => x.factorization q) hrec
  change
    (factorialGapComponentwiseResidualCofactor (n + 1) *
      factorialGapReducedTransitionNormalizer n).factorization q =
    (factorialGapComponentwiseResidualCofactor n *
      factorialGapUnselectedBirthCofactor n *
      factorialGapKilledMultiplicityDefect n).factorization q at hfac
  rw [
    Nat.factorization_mul hnextNe hreducedNe,
    Nat.factorization_mul (mul_ne_zero holdNe hbirthNe) hdefectNe,
    Nat.factorization_mul holdNe hbirthNe
  ] at hfac
  simpa only [Finsupp.add_apply] using hfac

/-- A prime carried by the excess-kill defect cannot simultaneously occur
in the reduced transition outflow.  This is the primewise content of the
gcd cancellation defining `D_n` and `R_n`. -/
theorem
    factorialGapReducedTransitionNormalizer_factorization_eq_zero_of_prime_dvd_defect
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqDefect : q ∣ factorialGapKilledMultiplicityDefect n) :
    (factorialGapReducedTransitionNormalizer n).factorization q = 0 := by
  have hqCoprime :
      Nat.Coprime q (factorialGapReducedTransitionNormalizer n) :=
    (factorialGapKilledMultiplicityDefect_coprime_reducedTransitionNormalizer
      hn).of_dvd_left hqDefect
  exact
    Nat.factorization_eq_zero_of_not_dvd
      (hq.coprime_iff_not_dvd.mp hqCoprime)

/-- At every prime in the excess-kill defect, the intrinsic recurrence has
no outflow term: its next residual valuation is exactly its old valuation
plus both inflow valuations. -/
theorem
    factorialGapComponentwiseResidualCofactor_succ_factorization_eq_of_prime_dvd_defect
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqDefect : q ∣ factorialGapKilledMultiplicityDefect n) :
    (factorialGapComponentwiseResidualCofactor
        (n + 1)).factorization q =
      (factorialGapComponentwiseResidualCofactor n).factorization q +
        (factorialGapUnselectedBirthCofactor n).factorization q +
        (factorialGapKilledMultiplicityDefect n).factorization q := by
  have hrec :=
    factorialGapComponentwiseResidualCofactor_succ_factorization_recurrence
      (q := q) hn
  rw [
    factorialGapReducedTransitionNormalizer_factorization_eq_zero_of_prime_dvd_defect
      hn hq hqDefect,
    add_zero
  ] at hrec
  exact hrec

/-- Every prime in the excess-kill defect gains strictly more residual
valuation at the next endpoint.  Excess killed multiplicity is therefore
a genuine one-step growth event, never hidden by simultaneous outflow. -/
theorem
    factorialGapComponentwiseResidualCofactor_factorization_lt_succ_of_prime_dvd_defect
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqDefect : q ∣ factorialGapKilledMultiplicityDefect n) :
    (factorialGapComponentwiseResidualCofactor n).factorization q <
      (factorialGapComponentwiseResidualCofactor
        (n + 1)).factorization q := by
  rw [
    factorialGapComponentwiseResidualCofactor_succ_factorization_eq_of_prime_dvd_defect
      hn hq hqDefect
  ]
  have hdefectNe :
      factorialGapKilledMultiplicityDefect n ≠ 0 :=
    (factorialGapKilledMultiplicityDefect_pos n).ne'
  have hdefectPos :
      0 <
        (factorialGapKilledMultiplicityDefect n).factorization q :=
    hq.factorization_pos_of_dvd hdefectNe hqDefect
  omega

/-- The complete excess-kill defect, with all of its prime multiplicities,
is absorbed into the next residual cofactor.  Coprimality with the reduced
outflow prevents any part of `D_n` from being cancelled on the left. -/
theorem factorialGapKilledMultiplicityDefect_dvd_residualCofactor_succ
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapKilledMultiplicityDefect n ∣
      factorialGapComponentwiseResidualCofactor (n + 1) := by
  apply
    (factorialGapKilledMultiplicityDefect_coprime_reducedTransitionNormalizer
      hn).dvd_of_dvd_mul_right
  rw [
    factorialGapComponentwiseResidualCofactor_succ_intrinsic_recurrence
      hn
  ]
  exact dvd_mul_left _ _

/-- At a prime absent from the reduced transition outflow, the next
residual valuation is exactly the sum of the old residual and both inflow
valuations. -/
theorem
    factorialGapComponentwiseResidualCofactor_succ_factorization_eq_of_not_dvd_outflow
    {n q : ℕ} (hn : 2 ≤ n)
    (hqNotOutflow :
      ¬q ∣ factorialGapReducedTransitionNormalizer n) :
    (factorialGapComponentwiseResidualCofactor
        (n + 1)).factorization q =
      (factorialGapComponentwiseResidualCofactor n).factorization q +
        (factorialGapUnselectedBirthCofactor n).factorization q +
        (factorialGapKilledMultiplicityDefect n).factorization q := by
  have hrec :=
    factorialGapComponentwiseResidualCofactor_succ_factorization_recurrence
      (q := q) hn
  rw [
    Nat.factorization_eq_zero_of_not_dvd hqNotOutflow,
    add_zero
  ] at hrec
  exact hrec

/-- A repeated-birth prime absent from the reduced outflow forces strict
growth of its residual valuation. -/
theorem
    factorialGapComponentwiseResidualCofactor_factorization_lt_succ_of_prime_dvd_birth_not_outflow
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n)
    (hqNotOutflow :
      ¬q ∣ factorialGapReducedTransitionNormalizer n) :
    (factorialGapComponentwiseResidualCofactor n).factorization q <
      (factorialGapComponentwiseResidualCofactor
        (n + 1)).factorization q := by
  rw [
    factorialGapComponentwiseResidualCofactor_succ_factorization_eq_of_not_dvd_outflow
      hn hqNotOutflow
  ]
  have hbirthNe :
      factorialGapUnselectedBirthCofactor n ≠ 0 :=
    (factorialGapUnselectedBirthCofactor_pos hn).ne'
  have hbirthPos :
      0 <
        (factorialGapUnselectedBirthCofactor n).factorization q :=
    hq.factorization_pos_of_dvd hbirthNe hqBirth
  omega

/-- Every repeated-birth prime either grows in the residual cofactor or is
present in the reduced outflow.  Hence failure of residual growth forces
divisibility of the reduced transition normalizer. -/
theorem
    prime_dvd_reducedTransitionNormalizer_of_prime_dvd_birth_of_not_residual_growth
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n)
    (hnotGrowth :
      ¬(factorialGapComponentwiseResidualCofactor n).factorization q <
        (factorialGapComponentwiseResidualCofactor
          (n + 1)).factorization q) :
    q ∣ factorialGapReducedTransitionNormalizer n := by
  by_contra hqNotOutflow
  exact
    hnotGrowth
      (factorialGapComponentwiseResidualCofactor_factorization_lt_succ_of_prime_dvd_birth_not_outflow
        hn hq hqBirth hqNotOutflow)

/-- Remove from the repeated-birth cofactor exactly its gcd with the
reduced outflow.  Every remaining prime power divides the next residual
cofactor in full.  This is the multiplicity-sensitive global form of the
birth-versus-outflow dichotomy. -/
theorem
    factorialGapUnselectedBirthCofactor_div_gcd_reducedTransitionNormalizer_dvd_residualCofactor_succ
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapUnselectedBirthCofactor n /
        Nat.gcd
          (factorialGapUnselectedBirthCofactor n)
          (factorialGapReducedTransitionNormalizer n) ∣
      factorialGapComponentwiseResidualCofactor (n + 1) := by
  have hgPos :
      0 <
        Nat.gcd
          (factorialGapUnselectedBirthCofactor n)
          (factorialGapReducedTransitionNormalizer n) :=
    Nat.gcd_pos_of_pos_right _
      (factorialGapReducedTransitionNormalizer_pos hn)
  have hcop :
      Nat.Coprime
        (factorialGapUnselectedBirthCofactor n /
          Nat.gcd
            (factorialGapUnselectedBirthCofactor n)
            (factorialGapReducedTransitionNormalizer n))
        (factorialGapReducedTransitionNormalizer n /
          Nat.gcd
            (factorialGapUnselectedBirthCofactor n)
            (factorialGapReducedTransitionNormalizer n)) :=
    Nat.coprime_div_gcd_div_gcd hgPos
  have hreduced :
      factorialGapComponentwiseResidualCofactor (n + 1) *
          (factorialGapReducedTransitionNormalizer n /
            Nat.gcd
              (factorialGapUnselectedBirthCofactor n)
              (factorialGapReducedTransitionNormalizer n)) =
        factorialGapComponentwiseResidualCofactor n *
          (factorialGapUnselectedBirthCofactor n /
            Nat.gcd
              (factorialGapUnselectedBirthCofactor n)
              (factorialGapReducedTransitionNormalizer n)) *
          factorialGapKilledMultiplicityDefect n := by
    apply Nat.mul_left_cancel hgPos
    calc
      Nat.gcd
            (factorialGapUnselectedBirthCofactor n)
            (factorialGapReducedTransitionNormalizer n) *
          (factorialGapComponentwiseResidualCofactor (n + 1) *
            (factorialGapReducedTransitionNormalizer n /
              Nat.gcd
                (factorialGapUnselectedBirthCofactor n)
                (factorialGapReducedTransitionNormalizer n))) =
        factorialGapComponentwiseResidualCofactor (n + 1) *
          (Nat.gcd
              (factorialGapUnselectedBirthCofactor n)
              (factorialGapReducedTransitionNormalizer n) *
            (factorialGapReducedTransitionNormalizer n /
              Nat.gcd
                (factorialGapUnselectedBirthCofactor n)
                (factorialGapReducedTransitionNormalizer n))) := by
          ac_rfl
      _ =
        factorialGapComponentwiseResidualCofactor (n + 1) *
          factorialGapReducedTransitionNormalizer n := by
            rw [
              Nat.mul_div_cancel'
                (Nat.gcd_dvd_right
                  (factorialGapUnselectedBirthCofactor n)
                  (factorialGapReducedTransitionNormalizer n))
            ]
      _ =
        factorialGapComponentwiseResidualCofactor n *
          factorialGapUnselectedBirthCofactor n *
          factorialGapKilledMultiplicityDefect n :=
            factorialGapComponentwiseResidualCofactor_succ_intrinsic_recurrence
              hn
      _ =
        factorialGapComponentwiseResidualCofactor n *
          (Nat.gcd
              (factorialGapUnselectedBirthCofactor n)
              (factorialGapReducedTransitionNormalizer n) *
            (factorialGapUnselectedBirthCofactor n /
              Nat.gcd
                (factorialGapUnselectedBirthCofactor n)
                (factorialGapReducedTransitionNormalizer n))) *
          factorialGapKilledMultiplicityDefect n := by
            rw [
              Nat.mul_div_cancel'
                (Nat.gcd_dvd_left
                  (factorialGapUnselectedBirthCofactor n)
                  (factorialGapReducedTransitionNormalizer n))
            ]
      _ =
        Nat.gcd
            (factorialGapUnselectedBirthCofactor n)
            (factorialGapReducedTransitionNormalizer n) *
          (factorialGapComponentwiseResidualCofactor n *
            (factorialGapUnselectedBirthCofactor n /
              Nat.gcd
                (factorialGapUnselectedBirthCofactor n)
                (factorialGapReducedTransitionNormalizer n)) *
            factorialGapKilledMultiplicityDefect n) := by
          ac_rfl
  apply hcop.dvd_of_dvd_mul_right
  rw [hreduced]
  exact
    ⟨factorialGapComponentwiseResidualCofactor n *
        factorialGapKilledMultiplicityDefect n,
      by ac_rfl⟩

/-- A repeated-birth prime can occur in the reduced outflow only if it was
already present in the old reduced denominator.  Purely new denominator
mass from the current gap cannot be cancelled by normalization. -/
theorem
    prime_dvd_factorialGapPredecessorScaledRat_den_of_prime_dvd_birth_and_reduced_outflow
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n)
    (hqOutflow : q ∣ factorialGapReducedTransitionNormalizer n) :
    q ∣ (factorialGapPredecessorScaledRat n).den := by
  have hbirthFactor :=
    factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
      hn
  have hqGap : q ∣ n.factorial - 1 := by
    rw [← hbirthFactor]
    exact dvd_mul_of_dvd_right hqBirth _
  have houtflowFactor :=
    factorialGapKilledTransitionGcd_mul_reducedTransitionNormalizer n
  have hqTransition :
      q ∣ factorialGapPredecessorTransitionNormalizer n := by
    rw [← houtflowFactor]
    exact dvd_mul_of_dvd_right hqOutflow _
  by_contra hqNotDen
  exact
    (hq.coprime_iff_not_dvd.mp
      (prime_coprime_factorialGapPredecessorTransitionNormalizer_of_dvd_gap
        hn hq hqGap hqNotDen))
      hqTransition

/-- The complete common factor of the current factorial gap and transition
normalizer already divides the old reduced denominator.  This retains full
prime-power multiplicity, not merely prime support. -/
theorem
    gcd_factorialGap_transitionNormalizer_dvd_predecessorScaledRat_den
    {n : ℕ} (hn : 2 ≤ n) :
    Nat.gcd
        (n.factorial - 1)
        (factorialGapPredecessorTransitionNormalizer n) ∣
      (factorialGapPredecessorScaledRat n).den := by
  have hmod :=
    transitionNormalizer_mul_predecessorGapNumerator_modEq_neg_den
      hn
      (Nat.gcd_dvd_left
        (n.factorial - 1)
        (factorialGapPredecessorTransitionNormalizer n))
  have hdTransitionZ :
      (Nat.gcd
          (n.factorial - 1)
          (factorialGapPredecessorTransitionNormalizer n) : ℤ) ∣
        (factorialGapPredecessorTransitionNormalizer n : ℤ) := by
    exact_mod_cast
      (Nat.gcd_dvd_right
        (n.factorial - 1)
        (factorialGapPredecessorTransitionNormalizer n))
  have hdProductZ :
      (Nat.gcd
          (n.factorial - 1)
          (factorialGapPredecessorTransitionNormalizer n) : ℤ) ∣
        (factorialGapPredecessorTransitionNormalizer n : ℤ) *
          factorialGapPredecessorGapNumerator (n + 1) :=
    dvd_mul_of_dvd_left hdTransitionZ _
  have hdNegDenZ :
      (Nat.gcd
          (n.factorial - 1)
          (factorialGapPredecessorTransitionNormalizer n) : ℤ) ∣
        (-(factorialGapPredecessorScaledRat n).den : ℤ) := by
    convert Int.dvd_add hmod.dvd hdProductZ using 1 <;> ring
  have hdDenZ :
      (Nat.gcd
          (n.factorial - 1)
          (factorialGapPredecessorTransitionNormalizer n) : ℤ) ∣
        ((factorialGapPredecessorScaledRat n).den : ℤ) :=
    dvd_neg.mp hdNegDenZ
  exact_mod_cast hdDenZ

/-- Hence the full multiplicity-sensitive overlap between repeated birth
mass and reduced outflow already divides the old denominator. -/
theorem
    gcd_unselectedBirthCofactor_reducedTransitionNormalizer_dvd_predecessorScaledRat_den
    {n : ℕ} (hn : 2 ≤ n) :
    Nat.gcd
        (factorialGapUnselectedBirthCofactor n)
        (factorialGapReducedTransitionNormalizer n) ∣
      (factorialGapPredecessorScaledRat n).den := by
  have hbirthFactor :=
    factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
      hn
  have hbirthDvdGap :
      factorialGapUnselectedBirthCofactor n ∣ n.factorial - 1 := by
    rw [← hbirthFactor]
    exact dvd_mul_left _ _
  have houtflowFactor :=
    factorialGapKilledTransitionGcd_mul_reducedTransitionNormalizer n
  have houtflowDvdTransition :
      factorialGapReducedTransitionNormalizer n ∣
        factorialGapPredecessorTransitionNormalizer n := by
    rw [← houtflowFactor]
    exact dvd_mul_left _ _
  have hoverlapDvd :
      Nat.gcd
          (factorialGapUnselectedBirthCofactor n)
          (factorialGapReducedTransitionNormalizer n) ∣
        Nat.gcd
          (n.factorial - 1)
          (factorialGapPredecessorTransitionNormalizer n) :=
    Nat.dvd_gcd
      ((Nat.gcd_dvd_left
        (factorialGapUnselectedBirthCofactor n)
        (factorialGapReducedTransitionNormalizer n)).trans
          hbirthDvdGap)
      ((Nat.gcd_dvd_right
        (factorialGapUnselectedBirthCofactor n)
        (factorialGapReducedTransitionNormalizer n)).trans
          houtflowDvdTransition)
  exact
    hoverlapDvd.trans
      (gcd_factorialGap_transitionNormalizer_dvd_predecessorScaledRat_den
        hn)

/-- At every prime in the unselected cofactor, that cofactor retains
exactly the complete current factorial-gap valuation. -/
theorem
    factorialGapUnselectedBirthCofactor_factorization_eq_gap_of_prime_dvd
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n) :
    (factorialGapUnselectedBirthCofactor n).factorization q =
      (n.factorial - 1).factorization q := by
  have hbirthNe :
      factorialGapUnselectedBirthCofactor n ≠ 0 :=
    (factorialGapUnselectedBirthCofactor_pos hn).ne'
  have hgapNe : n.factorial - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hn)).ne'
  have hbirthFactor :=
    factorialGapLargePrefixPrivatePowerModulus_mul_unselectedBirthCofactor
      hn
  have hbirthDvdGap :
      factorialGapUnselectedBirthCofactor n ∣ n.factorial - 1 := by
    rw [← hbirthFactor]
    exact dvd_mul_left _ _
  apply le_antisymm
  · exact
      ((Nat.factorization_le_iff_dvd hbirthNe hgapNe).2
        hbirthDvdGap) q
  · exact
      (hq.pow_dvd_iff_le_factorization hbirthNe).1
        (primePower_dvd_unselectedBirthCofactor_of_prime_dvd
          hn hq hqBirth)

/-- If reduced outflow at a repeated-birth prime exceeds all old residual
mass at that prime, then the current factorial-gap valuation was no larger
than the complete old denominator valuation.  Thus cancellation beyond the
old residual is possible only without a genuine multiplicity amplification
at the current gap. -/
theorem
    factorialGap_factorization_le_den_of_reducedOutflow_exceeds_residual
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n)
    (hexcess :
      (factorialGapComponentwiseResidualCofactor n).factorization q <
        (factorialGapReducedTransitionNormalizer n).factorization q) :
    (n.factorial - 1).factorization q ≤
      (factorialGapPredecessorScaledRat n).den.factorization q := by
  have haccKilled :=
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_factorization_eq_killed_of_prime_dvd_birth
      hn hq hqBirth
  have hdenFactor :=
    factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
      n
  have haccNe :
      factorialGapComponentwiseAccumulatedPrivatePowerModulus n ≠ 0 := by
    exact
      (Nat.pos_of_dvd_of_pos
        factorialGapComponentwiseAccumulatedPrivatePowerModulus_dvd_den
        (factorialGapPredecessorScaledRat n).den_pos).ne'
  have hresidualNe :
      factorialGapComponentwiseResidualCofactor n ≠ 0 :=
    (factorialGapComponentwiseResidualCofactor_pos n).ne'
  have hdenFac :
      (factorialGapPredecessorScaledRat n).den.factorization q =
        (factorialGapComponentwiseAccumulatedPrivatePowerModulus n).factorization q +
          (factorialGapComponentwiseResidualCofactor n).factorization q := by
    have h :=
      congrArg (fun x : ℕ => x.factorization q) hdenFactor
    change
      (factorialGapComponentwiseAccumulatedPrivatePowerModulus n *
          factorialGapComponentwiseResidualCofactor n).factorization q =
        (factorialGapPredecessorScaledRat n).den.factorization q at h
    rw [
      Nat.factorization_mul haccNe hresidualNe,
      Finsupp.add_apply
    ] at h
    exact h.symm
  have hkilledNe :
      factorialGapKilledPrivatePowerModulus n ≠ 0 :=
    (factorialGapKilledPrivatePowerModulus_pos n).ne'
  have htransitionNe :
      factorialGapPredecessorTransitionNormalizer n ≠ 0 :=
    (factorialGapPredecessorTransitionNormalizer_pos hn).ne'
  have hreducedNe :
      factorialGapReducedTransitionNormalizer n ≠ 0 :=
    (factorialGapReducedTransitionNormalizer_pos hn).ne'
  have hgcdNe :
      factorialGapKilledTransitionGcd n ≠ 0 :=
    (Nat.gcd_pos_of_pos_right _
      (factorialGapPredecessorTransitionNormalizer_pos hn)).ne'
  have htransitionFactor :=
    factorialGapKilledTransitionGcd_mul_reducedTransitionNormalizer n
  have htransitionFac :
      (factorialGapPredecessorTransitionNormalizer n).factorization q =
        (factorialGapKilledTransitionGcd n).factorization q +
          (factorialGapReducedTransitionNormalizer n).factorization q := by
    have h :=
      congrArg (fun x : ℕ => x.factorization q) htransitionFactor
    change
      (factorialGapKilledTransitionGcd n *
          factorialGapReducedTransitionNormalizer n).factorization q =
        (factorialGapPredecessorTransitionNormalizer n).factorization q at h
    rw [Nat.factorization_mul hgcdNe hreducedNe, Finsupp.add_apply] at h
    exact h.symm
  have hgcdFac :
      (factorialGapKilledTransitionGcd n).factorization q =
        min
          ((factorialGapKilledPrivatePowerModulus n).factorization q)
          ((factorialGapPredecessorTransitionNormalizer n).factorization q) := by
    unfold factorialGapKilledTransitionGcd
    have h :=
      congrArg (fun f : ℕ →₀ ℕ => f q)
        (Nat.factorization_gcd hkilledNe htransitionNe)
    simpa only [Finsupp.inf_apply] using h
  have hkilledLtTransition :
      (factorialGapKilledPrivatePowerModulus n).factorization q <
        (factorialGapPredecessorTransitionNormalizer n).factorization q := by
    by_contra hnot
    have htransitionLeKilled :
        (factorialGapPredecessorTransitionNormalizer n).factorization q ≤
          (factorialGapKilledPrivatePowerModulus n).factorization q :=
      le_of_not_gt hnot
    have hgcdEqTransition :
        (factorialGapKilledTransitionGcd n).factorization q =
          (factorialGapPredecessorTransitionNormalizer n).factorization q := by
      rw [hgcdFac, min_eq_right htransitionLeKilled]
    omega
  have hgcdEqKilled :
      (factorialGapKilledTransitionGcd n).factorization q =
        (factorialGapKilledPrivatePowerModulus n).factorization q := by
    rw [hgcdFac, min_eq_left hkilledLtTransition.le]
  have hdenLtTransition :
      (factorialGapPredecessorScaledRat n).den.factorization q <
        (factorialGapPredecessorTransitionNormalizer n).factorization q := by
    omega
  have hgapNe : n.factorial - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hn)).ne'
  have hcommonNe :
      Nat.gcd
          (n.factorial - 1)
          (factorialGapPredecessorTransitionNormalizer n) ≠ 0 :=
    (Nat.gcd_pos_of_pos_right _
      (factorialGapPredecessorTransitionNormalizer_pos hn)).ne'
  have hcommonFacLe :=
    (Nat.factorization_le_iff_dvd
      hcommonNe
      (factorialGapPredecessorScaledRat n).den_nz).2
        (gcd_factorialGap_transitionNormalizer_dvd_predecessorScaledRat_den
          hn)
  have hminLe :
      min
          ((n.factorial - 1).factorization q)
          ((factorialGapPredecessorTransitionNormalizer n).factorization q) ≤
        (factorialGapPredecessorScaledRat n).den.factorization q := by
    have hqLe := hcommonFacLe q
    have hfactor :=
      congrArg (fun f : ℕ →₀ ℕ => f q)
        (Nat.factorization_gcd hgapNe htransitionNe)
    have hfactorQ :
        (Nat.gcd
            (n.factorial - 1)
            (factorialGapPredecessorTransitionNormalizer n)).factorization q =
          min
            ((n.factorial - 1).factorization q)
            ((factorialGapPredecessorTransitionNormalizer n).factorization q) := by
      simpa only [Finsupp.inf_apply] using hfactor
    rwa [hfactorQ] at hqLe
  by_cases hgapLeTransition :
      (n.factorial - 1).factorization q ≤
        (factorialGapPredecessorTransitionNormalizer n).factorization q
  · rwa [min_eq_left hgapLeTransition] at hminLe
  · have htransitionLeGap :
        (factorialGapPredecessorTransitionNormalizer n).factorization q ≤
          (n.factorial - 1).factorization q :=
      le_of_not_ge hgapLeTransition
    rw [min_eq_right htransitionLeGap] at hminLe
    omega

/-- Genuine repeated-prime multiplicity amplification cannot disappear
into transition normalization.  If the current factorial gap contains
strictly more `q`-adic mass than the whole old reduced denominator, then
that complete current prime power divides the next residual cofactor. -/
theorem
    factorialGap_primePower_dvd_residualCofactor_succ_of_den_factorization_lt_gap
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n)
    (hamplifies :
      (factorialGapPredecessorScaledRat n).den.factorization q <
        (n.factorial - 1).factorization q) :
    q ^ (n.factorial - 1).factorization q ∣
      factorialGapComponentwiseResidualCofactor (n + 1) := by
  have houtflowLe :
      (factorialGapReducedTransitionNormalizer n).factorization q ≤
        (factorialGapComponentwiseResidualCofactor n).factorization q := by
    by_contra hnot
    have hexcess :
        (factorialGapComponentwiseResidualCofactor n).factorization q <
          (factorialGapReducedTransitionNormalizer n).factorization q :=
      lt_of_not_ge hnot
    have hgapLeDen :=
      factorialGap_factorization_le_den_of_reducedOutflow_exceeds_residual
        hn hq hqBirth hexcess
    omega
  have hrec :=
    factorialGapComponentwiseResidualCofactor_succ_factorization_recurrence
      (q := q) hn
  have hbirthFac :=
    factorialGapUnselectedBirthCofactor_factorization_eq_gap_of_prime_dvd
      hn hq hqBirth
  have hnextNe :
      factorialGapComponentwiseResidualCofactor (n + 1) ≠ 0 :=
    (factorialGapComponentwiseResidualCofactor_pos (n + 1)).ne'
  apply (hq.pow_dvd_iff_le_factorization hnextNe).2
  omega

/-- A strict `q`-adic record for the current factorial gap is already
larger than the actual old reduced-denominator valuation.  This replaces
the opaque denominator comparison by a pure factorial-gap history
condition. -/
theorem
    factorialGapPredecessorScaledRat_den_factorization_lt_gap_of_record
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqGap : q ∣ n.factorial - 1)
    (hrecord :
      ∀ k : ℕ, 2 ≤ k → k < n →
        (k.factorial - 1).factorization q <
          (n.factorial - 1).factorization q) :
    (factorialGapPredecessorScaledRat n).den.factorization q <
      (n.factorial - 1).factorization q := by
  have hgapNe :
      n.factorial - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hn)).ne'
  have hcurrentPos :
      0 < (n.factorial - 1).factorization q :=
    hq.factorization_pos_of_dvd hgapNe hqGap
  have hlcmPos :
      0 < factorialGapPrefixLCM (n - 1) := by
    unfold factorialGapPrefixLCM
    exact
      Nat.pos_of_ne_zero
        ((Finset.lcm_ne_zero_iff).2 fun k hk =>
          (Nat.sub_pos_of_lt
            (Nat.one_lt_factorial.mpr
              (Finset.mem_Icc.1 hk).1)).ne')
  have hlcmLt :
      (factorialGapPrefixLCM (n - 1)).factorization q <
        (n.factorial - 1).factorization q := by
    unfold factorialGapPrefixLCM
    apply finset_lcm_factorization_lt_of_all_lt
    · exact hcurrentPos
    · intro k hk
      exact
        Nat.sub_pos_of_lt
          (Nat.one_lt_factorial.mpr
            (Finset.mem_Icc.1 hk).1)
    · intro k hk
      have hkBounds :=
        Finset.mem_Icc.1 hk
      exact hrecord k hkBounds.1 (by omega)
  have hdenFacLe :
      (factorialGapPredecessorScaledRat n).den.factorization ≤
        (factorialGapPrefixLCM (n - 1)).factorization :=
    (Nat.factorization_le_iff_dvd
      (factorialGapPredecessorScaledRat n).den_nz
      hlcmPos.ne').2
        (factorialGapPredecessorScaledRat_den_dvd_prefixLCM n)
  exact (hdenFacLe q).trans_lt hlcmLt

/-- Every repeated strict valuation record enters the next residual
cofactor with its complete current factorial-gap multiplicity. -/
theorem
    factorialGap_repeatedRecordPrimePower_dvd_residualCofactor_succ
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqGap : q ∣ n.factorial - 1)
    (hrepeat :
      ∃ k : ℕ, 2 ≤ k ∧ k < n ∧ q ∣ k.factorial - 1)
    (hrecord :
      ∀ k : ℕ, 2 ≤ k → k < n →
        (k.factorial - 1).factorization q <
          (n.factorial - 1).factorization q) :
    q ^ (n.factorial - 1).factorization q ∣
      factorialGapComponentwiseResidualCofactor (n + 1) := by
  exact
    factorialGap_primePower_dvd_residualCofactor_succ_of_den_factorization_lt_gap
      hn hq
      (prime_dvd_unselectedBirthCofactor_of_repeat
        hn hq hqGap hrepeat)
      (factorialGapPredecessorScaledRat_den_factorization_lt_gap_of_record
        hn hq hqGap hrecord)

/-- The same record power divides the complete next reduced denominator. -/
theorem factorialGap_repeatedRecordPrimePower_dvd_succ_den
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqGap : q ∣ n.factorial - 1)
    (hrepeat :
      ∃ k : ℕ, 2 ≤ k ∧ k < n ∧ q ∣ k.factorial - 1)
    (hrecord :
      ∀ k : ℕ, 2 ≤ k → k < n →
        (k.factorial - 1).factorization q <
          (n.factorial - 1).factorization q) :
    q ^ (n.factorial - 1).factorization q ∣
      (factorialGapPredecessorScaledRat (n + 1)).den := by
  refine
    (factorialGap_repeatedRecordPrimePower_dvd_residualCofactor_succ
      hn hq hqGap hrepeat hrecord).trans ?_
  refine
    ⟨factorialGapComponentwiseAccumulatedPrivatePowerModulus (n + 1), ?_⟩
  simpa [Nat.mul_comm] using
    (factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
      (n + 1)).symm

/-- Reduced coprimality turns every repeated strict valuation record into a
nonzero next-numerator projection modulo its complete prime power. -/
theorem
    predecessorGapNumeratorNat_mod_repeatedRecordPrimePower_ne_zero
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqGap : q ∣ n.factorial - 1)
    (hrepeat :
      ∃ k : ℕ, 2 ≤ k ∧ k < n ∧ q ∣ k.factorial - 1)
    (hrecord :
      ∀ k : ℕ, 2 ≤ k → k < n →
        (k.factorial - 1).factorization q <
          (n.factorial - 1).factorization q) :
    factorialGapPredecessorGapNumeratorNat (n + 1) %
        q ^ (n.factorial - 1).factorization q ≠ 0 := by
  have hgapNe :
      n.factorial - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hn)).ne'
  have hexpPos :
      0 < (n.factorial - 1).factorization q :=
    hq.factorization_pos_of_dvd hgapNe hqGap
  exact
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
      (one_lt_pow₀ hq.one_lt hexpPos.ne')
      (factorialGap_repeatedRecordPrimePower_dvd_succ_den
        hn hq hqGap hrepeat hrecord)

/-- A square criterion with no reduced-denominator
hypothesis.  If `p²` first appears in a factorial gap at `n`, while `p`
already appeared at one earlier gap, then `p²` enters the next residual
cofactor and actual denominator and has a nonzero reduced-numerator
projection. -/
theorem factorialGap_firstRepeatedPrimeSquare_entry
    {n k p : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (hk2 : 2 ≤ k) (hkn : k < n)
    (hpEarlier : p ∣ k.factorial - 1)
    (hpSq : p ^ 2 ∣ n.factorial - 1)
    (hfirstSq :
      ∀ j : ℕ, 2 ≤ j → j < n →
        ¬p ^ 2 ∣ j.factorial - 1) :
    p ^ 2 ∣ factorialGapComponentwiseResidualCofactor (n + 1) ∧
      p ^ 2 ∣ (factorialGapPredecessorScaledRat (n + 1)).den ∧
      factorialGapPredecessorGapNumeratorNat (n + 1) % (p ^ 2) ≠ 0 := by
  have hgapNe :
      n.factorial - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hn)).ne'
  have hpGap :
      p ∣ n.factorial - 1 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hpSq
  have hcurrentGe :
      2 ≤ (n.factorial - 1).factorization p :=
    (hp.pow_dvd_iff_le_factorization hgapNe).1 hpSq
  have hrecord :
      ∀ j : ℕ, 2 ≤ j → j < n →
        (j.factorial - 1).factorization p <
          (n.factorial - 1).factorization p := by
    intro j hj2 hjn
    have hjGapNe :
        j.factorial - 1 ≠ 0 :=
      (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hj2)).ne'
    have hjFacLtTwo :
        (j.factorial - 1).factorization p < 2 := by
      apply Nat.lt_of_not_ge
      intro hge
      exact
        hfirstSq j hj2 hjn
          ((hp.pow_dvd_iff_le_factorization hjGapNe).2 hge)
    omega
  have hfullResidual :=
    factorialGap_repeatedRecordPrimePower_dvd_residualCofactor_succ
      hn hp hpGap ⟨k, hk2, hkn, hpEarlier⟩ hrecord
  have hsqResidual :
      p ^ 2 ∣ factorialGapComponentwiseResidualCofactor (n + 1) :=
    (pow_dvd_pow p hcurrentGe).trans hfullResidual
  have hresidualDen :
      factorialGapComponentwiseResidualCofactor (n + 1) ∣
        (factorialGapPredecessorScaledRat (n + 1)).den := by
    refine
      ⟨factorialGapComponentwiseAccumulatedPrivatePowerModulus (n + 1), ?_⟩
    simpa [Nat.mul_comm] using
      (factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
        (n + 1)).symm
  have hsqDen :
      p ^ 2 ∣ (factorialGapPredecessorScaledRat (n + 1)).den :=
    hsqResidual.trans hresidualDen
  exact
    ⟨hsqResidual, hsqDen,
      factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
        (by nlinarith [hp.two_le])
        hsqDen⟩

/-! ## Wilson quotients and finite repeated-prime records -/

/-- The natural Wilson quotient.  Wilson's theorem makes the displayed
division exact whenever `p` is prime. -/
def factorialWilsonQuotient (p : ℕ) : ℕ :=
  ((p - 1).factorial + 1) / p

/-- Wilson's theorem in the divisibility form used below. -/
theorem prime_dvd_factorial_pred_factorial_add_one
    {p : ℕ} (hp : p.Prime) :
    p ∣ (p - 1).factorial + 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hwilson :
      ((p - 1).factorial : ZMod p) = -1 :=
    ZMod.wilsons_lemma p
  have hzero :
      (((p - 1).factorial + 1 : ℕ) : ZMod p) = 0 := by
    simpa using congrArg (fun x : ZMod p => x + 1) hwilson
  exact (ZMod.natCast_eq_zero_iff _ _).1 hzero

/-- Exact reconstruction of the numerator from the natural Wilson
quotient. -/
theorem factorialWilsonQuotient_mul_prime
    {p : ℕ} (hp : p.Prime) :
    factorialWilsonQuotient p * p =
      (p - 1).factorial + 1 := by
  exact Nat.div_mul_cancel
    (prime_dvd_factorial_pred_factorial_add_one hp)

/-- For a prime, the Wilson quotient is positive. -/
theorem one_le_factorialWilsonQuotient
    {p : ℕ} (hp : p.Prime) :
    1 ≤ factorialWilsonQuotient p := by
  have hreconstruct :=
    factorialWilsonQuotient_mul_prime hp
  have hnumPos :
      0 < (p - 1).factorial + 1 := by
    positivity
  have hpPos : 0 < p := hp.pos
  by_contra hnot
  have hzero : factorialWilsonQuotient p = 0 := by omega
  rw [hzero, zero_mul] at hreconstruct
  omega

/-- The exact balance behind the Wilson-quotient square criterion. -/
theorem factorialWilsonQuotient_balance
    {p : ℕ} (hp : p.Prime) :
    p * (factorialWilsonQuotient p - 1) =
      (p - 1) * ((p - 2).factorial - 1) := by
  have hpTwo : 2 ≤ p := hp.two_le
  have hfac :
      (p - 1).factorial =
        (p - 1) * (p - 2).factorial := by
    calc
      (p - 1).factorial =
          ((p - 2) + 1).factorial := by congr 1 <;> omega
      _ = ((p - 2) + 1) * (p - 2).factorial :=
        Nat.factorial_succ (p - 2)
      _ = (p - 1) * (p - 2).factorial := by congr 1 <;> omega
  have hreconstruct :=
    factorialWilsonQuotient_mul_prime hp
  have hquotOne :=
    one_le_factorialWilsonQuotient hp
  have hfacOne :
      1 ≤ (p - 2).factorial := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.factorial_ne_zero (p - 2))
  rw [hfac] at hreconstruct
  calc
    p * (factorialWilsonQuotient p - 1) =
        p * factorialWilsonQuotient p - p := by
      rw [Nat.mul_sub_left_distrib]
      simp
    _ = factorialWilsonQuotient p * p - p := by
      rw [Nat.mul_comm p]
    _ = ((p - 1) * (p - 2).factorial + 1) - p := by
      rw [hreconstruct]
    _ = (p - 1) * (p - 2).factorial - (p - 1) := by
      omega
    _ = (p - 1) * ((p - 2).factorial - 1) := by
      rw [Nat.mul_sub_left_distrib]
      simp

/-- Wilson criterion.  For every prime `p`, the congruence
`W_p ≡ 1 (mod p)` is equivalent to a square hit in the factorial gap at
`p - 2`.  Thus the higher-order Wilson condition is exactly the
valuation-amplification trigger used below, rather than merely a numerical
coincidence at `p = 107`. -/
theorem factorialWilsonQuotient_modEq_one_iff_square_dvd_gap
    {p : ℕ} (hp : p.Prime) :
    factorialWilsonQuotient p ≡ 1 [MOD p] ↔
      p ^ 2 ∣ (p - 2).factorial - 1 := by
  have hpTwo := hp.two_le
  have hquotOne :=
    one_le_factorialWilsonQuotient hp
  have hbalance :=
    factorialWilsonQuotient_balance hp
  have hnotDvdPred : ¬p ∣ p - 1 := by
    intro hdiv
    have hle : p ≤ p - 1 :=
      Nat.le_of_dvd (by omega) hdiv
    omega
  have hcoprime :
      Nat.Coprime (p ^ 2) (p - 1) :=
    (hp.coprime_iff_not_dvd.mpr hnotDvdPred).pow_left 2
  constructor
  · intro hmod
    have hpDvdQuotSub :
        p ∣ factorialWilsonQuotient p - 1 :=
      (Nat.modEq_iff_dvd' hquotOne).1 hmod.symm
    have hpSqDvdProduct :
        p ^ 2 ∣ (p - 1) * ((p - 2).factorial - 1) := by
      rw [← hbalance]
      obtain ⟨t, ht⟩ := hpDvdQuotSub
      refine ⟨t, ?_⟩
      rw [ht]
      ring
    exact hcoprime.dvd_of_dvd_mul_left hpSqDvdProduct
  · intro hpSq
    have hpSqDvdProduct :
        p ^ 2 ∣ (p - 1) * ((p - 2).factorial - 1) :=
      dvd_mul_of_dvd_right hpSq (p - 1)
    rw [← hbalance, pow_two] at hpSqDvdProduct
    have hpDvdQuotSub :
        p ∣ factorialWilsonQuotient p - 1 :=
      Nat.dvd_of_mul_dvd_mul_left hp.pos hpSqDvdProduct
    exact ((Nat.modEq_iff_dvd' hquotOne).2 hpDvdQuotSub).symm

/-- The joint source pattern now has a direct denominator-growth
conclusion.  A half-factorial `+1` hit supplies the earlier occurrence;
`W_p ≡ 1 (mod p)` supplies the square occurrence at `p - 2`; and the
first-square condition promotes their conjunction to a strict valuation
record.  The full square then survives in the next residual cofactor and
actual reduced denominator. -/
theorem factorialGap_halfFactorial_Wilson_record_entry
    {p : ℕ} (hp : p.Prime) (hpFive : 5 ≤ p)
    (hhalf :
      p ∣ ((p - 1) / 2).factorial - 1)
    (hWilson :
      factorialWilsonQuotient p ≡ 1 [MOD p])
    (hfirstSq :
      ∀ j : ℕ, 2 ≤ j → j < p - 2 →
        ¬p ^ 2 ∣ j.factorial - 1) :
    p ^ 2 ∣ factorialGapComponentwiseResidualCofactor (p - 1) ∧
      p ^ 2 ∣ (factorialGapPredecessorScaledRat (p - 1)).den ∧
      factorialGapPredecessorGapNumeratorNat (p - 1) % (p ^ 2) ≠ 0 := by
  have hn : 2 ≤ p - 2 := by omega
  have hk2 : 2 ≤ (p - 1) / 2 := by omega
  have hkn : (p - 1) / 2 < p - 2 := by omega
  have hpSq :
      p ^ 2 ∣ (p - 2).factorial - 1 :=
    (factorialWilsonQuotient_modEq_one_iff_square_dvd_gap hp).1
      hWilson
  have hentry :=
    factorialGap_firstRepeatedPrimeSquare_entry
      (n := p - 2) (k := (p - 1) / 2) (p := p)
      hn hp hk2 hkn hhalf hpSq hfirstSq
  have hindex : p - 2 + 1 = p - 1 := by omega
  simpa only [hindex] using hentry

/-- Before endpoint `105`, no factorial gap carries two factors of `107`.
This is a finite residue calculation, not a cofinal claim. -/
theorem oneHundredSeven_sq_not_dvd_factorialGap_before_105
    {k : ℕ} (hk2 : 2 ≤ k) (hk105 : k < 105) :
    ¬107 ^ 2 ∣ k.factorial - 1 := by
  interval_cases k <;> norm_num [Nat.factorial]

/-- An exact repeated-valuation record: `107` occurs at exponent one in
`53! - 1` and
at exponent at least two in `105! - 1`, exceeding every prior valuation. -/
theorem oneHundredSeven_repeatedRecord_at_105 :
    (107 : ℕ).Prime ∧
      107 ∣ (105 : ℕ).factorial - 1 ∧
      (∃ k : ℕ,
        2 ≤ k ∧ k < 105 ∧ 107 ∣ k.factorial - 1) ∧
      (∀ k : ℕ, 2 ≤ k → k < 105 →
        (k.factorial - 1).factorization 107 <
          ((105 : ℕ).factorial - 1).factorization 107) := by
  have hq : (107 : ℕ).Prime := by norm_num
  have hsq :
      107 ^ 2 ∣ (105 : ℕ).factorial - 1 := by
    norm_num [Nat.factorial]
  have hgapNe :
      (105 : ℕ).factorial - 1 ≠ 0 := by
    norm_num [Nat.factorial]
  have hcurrentGe :
      2 ≤ ((105 : ℕ).factorial - 1).factorization 107 :=
    (hq.pow_dvd_iff_le_factorization hgapNe).1 hsq
  have hqGap :
      107 ∣ (105 : ℕ).factorial - 1 :=
    (dvd_pow_self 107 (by norm_num : 2 ≠ 0)).trans hsq
  refine ⟨hq, hqGap, ?_, ?_⟩
  · refine ⟨53, by norm_num, by norm_num, ?_⟩
    norm_num [Nat.factorial]
  · intro k hk2 hk105
    have hnotSq :=
      oneHundredSeven_sq_not_dvd_factorialGap_before_105 hk2 hk105
    have hkGapNe :
        k.factorial - 1 ≠ 0 :=
      (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hk2)).ne'
    have hkFacLt :
        (k.factorial - 1).factorization 107 < 2 := by
      apply Nat.lt_of_not_ge
      intro hge
      exact
        hnotSq
          ((hq.pow_dvd_iff_le_factorization hkGapNe).2 hge)
    omega

/-- The concrete square hit is equivalently the Wilson-quotient
congruence `W_107 ≡ 1 (mod 107)`. -/
theorem oneHundredSeven_factorialWilsonQuotient_modEq_one :
    factorialWilsonQuotient 107 ≡ 1 [MOD 107] := by
  apply
    (factorialWilsonQuotient_modEq_one_iff_square_dvd_gap
      (by norm_num : (107 : ℕ).Prime)).2
  norm_num [Nat.factorial]

/-- At `p = 107`, the half-factorial hit, Wilson-quotient congruence, and
finite first-square record force a square in the reduced denominator at
`106`. -/
theorem oneHundredSeven_halfFactorial_Wilson_record_entry :
    107 ^ 2 ∣ factorialGapComponentwiseResidualCofactor 106 ∧
      107 ^ 2 ∣ (factorialGapPredecessorScaledRat 106).den ∧
      factorialGapPredecessorGapNumeratorNat 106 % (107 ^ 2) ≠ 0 := by
  apply
    factorialGap_halfFactorial_Wilson_record_entry
      (p := 107) (by norm_num) (by norm_num)
  · norm_num [Nat.factorial]
  · exact oneHundredSeven_factorialWilsonQuotient_modEq_one
  · intro j hj2 hj105
    exact
      oneHundredSeven_sq_not_dvd_factorialGap_before_105
        hj2 (by omega)

/-- The concrete record at `105` forces the full square `107^2` into the
next residual cofactor. -/
theorem oneHundredSeven_sq_dvd_residualCofactor_106 :
    107 ^ 2 ∣ factorialGapComponentwiseResidualCofactor 106 := by
  rcases oneHundredSeven_repeatedRecord_at_105 with
    ⟨hq, hqGap, hrepeat, hrecord⟩
  have hfull :=
    factorialGap_repeatedRecordPrimePower_dvd_residualCofactor_succ
      (n := 105) (q := 107) (by norm_num)
      hq hqGap hrepeat hrecord
  have hgapNe :
      (105 : ℕ).factorial - 1 ≠ 0 := by
    norm_num [Nat.factorial]
  have hsq :
      107 ^ 2 ∣ (105 : ℕ).factorial - 1 := by
    norm_num [Nat.factorial]
  have htwoLe :
      2 ≤ ((105 : ℕ).factorial - 1).factorization 107 :=
    (hq.pow_dvd_iff_le_factorization hgapNe).1 hsq
  exact (pow_dvd_pow 107 htwoLe).trans hfull

/-- The same concrete square is an actual next-denominator divisor and
therefore sees a nonzero reduced-numerator projection. -/
theorem predecessorGapNumeratorNat_mod_oneHundredSeven_sq_at_106_ne_zero :
    factorialGapPredecessorGapNumeratorNat 106 % (107 ^ 2) ≠ 0 := by
  have hdivDen :
      107 ^ 2 ∣ (factorialGapPredecessorScaledRat 106).den := by
    refine oneHundredSeven_sq_dvd_residualCofactor_106.trans ?_
    refine
      ⟨factorialGapComponentwiseAccumulatedPrivatePowerModulus 106, ?_⟩
    simpa [Nat.mul_comm] using
      (factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
        106).symm
  exact
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
      (by norm_num)
      hdivDen

/-- Before the nonterminal record index `609`, no factorial gap carries
two factors of `971`.  This is a finite residue calculation, not a cofinal
claim. -/
theorem nineHundredSeventyOne_sq_not_dvd_factorialGap_before_609
    {k : ℕ} (hk2 : 2 ≤ k) (hk609 : k < 609) :
    ¬971 ^ 2 ∣ k.factorial - 1 := by
  interval_cases k <;> norm_num [Nat.factorial]

/-- The exact scan's first genuinely non-Wilson record: `971` occurs in
`361! - 1`, its square first occurs in `609! - 1`, and `609 < 971 - 2`.
The complete square therefore enters the actual denominator at endpoint
`610` and has a nonzero reduced-numerator projection. -/
theorem nineHundredSeventyOne_firstRepeatedPrimeSquare_entry :
    971 ^ 2 ∣ factorialGapComponentwiseResidualCofactor 610 ∧
      971 ^ 2 ∣ (factorialGapPredecessorScaledRat 610).den ∧
      factorialGapPredecessorGapNumeratorNat 610 % (971 ^ 2) ≠ 0 := by
  apply
    factorialGap_firstRepeatedPrimeSquare_entry
      (n := 609) (k := 361) (p := 971)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num [Nat.factorial]
  · norm_num [Nat.factorial]
  · intro j hj2 hj609
    exact
      nineHundredSeventyOne_sq_not_dvd_factorialGap_before_609
        hj2 hj609

/-! ## Repeated-birth amplification and interval persistence -/

/-- Repeated-birth primes whose current factorial-gap multiplicity strictly
exceeds their complete multiplicity in the old reduced denominator. -/
def factorialGapRepeatedBirthAmplificationPrimes (n : ℕ) : Finset ℕ :=
  (factorialGapUnselectedBirthCofactor n).primeFactors.filter fun q =>
    (factorialGapPredecessorScaledRat n).den.factorization q <
      (n.factorial - 1).factorization q

/-- Membership in the canonical repeated-birth amplification set. -/
theorem mem_factorialGapRepeatedBirthAmplificationPrimes_iff
    {n q : ℕ} (hn : 2 ≤ n) :
    q ∈ factorialGapRepeatedBirthAmplificationPrimes n ↔
      q.Prime ∧
      q ∣ factorialGapUnselectedBirthCofactor n ∧
      (factorialGapPredecessorScaledRat n).den.factorization q <
        (n.factorial - 1).factorization q := by
  have hbirthNe :
      factorialGapUnselectedBirthCofactor n ≠ 0 :=
    (factorialGapUnselectedBirthCofactor_pos hn).ne'
  simp only [
    factorialGapRepeatedBirthAmplificationPrimes,
    Finset.mem_filter,
    Nat.mem_primeFactors
  ]
  constructor
  · rintro ⟨⟨hq, hqBirth, _⟩, hamplifies⟩
    exact ⟨hq, hqBirth, hamplifies⟩
  · rintro ⟨hq, hqBirth, hamplifies⟩
    exact ⟨⟨hq, hqBirth, hbirthNe⟩, hamplifies⟩

/-- The complete current-gap prime powers at every amplified repeated
prime, assembled into one canonical pairwise-coprime product. -/
def factorialGapRepeatedBirthAmplificationModulus (n : ℕ) : ℕ :=
  ∏ q ∈ factorialGapRepeatedBirthAmplificationPrimes n,
    q ^ (n.factorial - 1).factorization q

/-- The amplification modulus is genuinely a subproduct of the unselected
birth cofactor, with every selected prime retained to full multiplicity. -/
theorem factorialGapRepeatedBirthAmplificationModulus_dvd_birth
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapRepeatedBirthAmplificationModulus n ∣
      factorialGapUnselectedBirthCofactor n := by
  unfold factorialGapRepeatedBirthAmplificationModulus
  apply Finset.prod_dvd_of_isRelPrime
  · intro q hqMem r hrMem hqr
    have hqData :=
      (mem_factorialGapRepeatedBirthAmplificationPrimes_iff hn).1 hqMem
    have hrData :=
      (mem_factorialGapRepeatedBirthAmplificationPrimes_iff hn).1 hrMem
    exact
      Nat.coprime_iff_isRelPrime.mp
        (Nat.Coprime.pow_left _
          (Nat.Coprime.pow_right _
            ((Nat.coprime_primes hqData.1 hrData.1).2 hqr)))
  · intro q hqMem
    have hqData :=
      (mem_factorialGapRepeatedBirthAmplificationPrimes_iff hn).1 hqMem
    exact
      primePower_dvd_unselectedBirthCofactor_of_prime_dvd
        hn hqData.1 hqData.2.1

/-- Every amplified repeated-birth component survives normalization in
full, so their complete canonical product divides the next residual
cofactor. -/
theorem factorialGapRepeatedBirthAmplificationModulus_dvd_residualCofactor_succ
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapRepeatedBirthAmplificationModulus n ∣
      factorialGapComponentwiseResidualCofactor (n + 1) := by
  unfold factorialGapRepeatedBirthAmplificationModulus
  apply Finset.prod_dvd_of_isRelPrime
  · intro q hqMem r hrMem hqr
    have hqData :=
      (mem_factorialGapRepeatedBirthAmplificationPrimes_iff hn).1 hqMem
    have hrData :=
      (mem_factorialGapRepeatedBirthAmplificationPrimes_iff hn).1 hrMem
    exact
      Nat.coprime_iff_isRelPrime.mp
        (Nat.Coprime.pow_left _
          (Nat.Coprime.pow_right _
            ((Nat.coprime_primes hqData.1 hrData.1).2 hqr)))
  · intro q hqMem
    have hqData :=
      (mem_factorialGapRepeatedBirthAmplificationPrimes_iff hn).1 hqMem
    exact
      factorialGap_primePower_dvd_residualCofactor_succ_of_den_factorization_lt_gap
        hn hqData.1 hqData.2.1 hqData.2.2

/-- The amplified repeated-birth mass is therefore a common divisor of
the current birth cofactor and the next residual cofactor, not merely a
support-level witness. -/
theorem factorialGapRepeatedBirthAmplificationModulus_dvd_birth_gcd_residual_succ
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapRepeatedBirthAmplificationModulus n ∣
      Nat.gcd
        (factorialGapUnselectedBirthCofactor n)
        (factorialGapComponentwiseResidualCofactor (n + 1)) :=
  Nat.dvd_gcd
    (factorialGapRepeatedBirthAmplificationModulus_dvd_birth hn)
    (factorialGapRepeatedBirthAmplificationModulus_dvd_residualCofactor_succ
      hn)

/-- The canonical amplification product is always positive. -/
theorem factorialGapRepeatedBirthAmplificationModulus_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < factorialGapRepeatedBirthAmplificationModulus n := by
  exact
    Nat.pos_of_dvd_of_pos
      (factorialGapRepeatedBirthAmplificationModulus_dvd_birth hn)
      (factorialGapUnselectedBirthCofactor_pos hn)

/-- A nonempty amplification-prime set gives a genuinely nontrivial
full-multiplicity modulus. -/
theorem one_lt_factorialGapRepeatedBirthAmplificationModulus
    {n : ℕ} (hn : 2 ≤ n)
    (hnonempty :
      (factorialGapRepeatedBirthAmplificationPrimes n).Nonempty) :
    1 < factorialGapRepeatedBirthAmplificationModulus n := by
  obtain ⟨q, hqMem⟩ := hnonempty
  have hqData :=
    (mem_factorialGapRepeatedBirthAmplificationPrimes_iff hn).1 hqMem
  have hexpPos :
      0 < (n.factorial - 1).factorization q := by
    omega
  have hpowerOne :
      1 < q ^ (n.factorial - 1).factorization q :=
    one_lt_pow₀ hqData.1.one_lt hexpPos.ne'
  have hpowerDvd :
      q ^ (n.factorial - 1).factorization q ∣
        factorialGapRepeatedBirthAmplificationModulus n := by
    unfold factorialGapRepeatedBirthAmplificationModulus
    exact
      Finset.dvd_prod_of_mem
        (fun r : ℕ => r ^ (n.factorial - 1).factorization r)
        hqMem
  exact
    hpowerOne.trans_le
      (Nat.le_of_dvd
        (factorialGapRepeatedBirthAmplificationModulus_pos hn)
        hpowerDvd)

/-- Amplified repeated-birth mass is not merely present in the residual
quotient: it divides the complete next reduced denominator. -/
theorem factorialGapRepeatedBirthAmplificationModulus_dvd_succ_den
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapRepeatedBirthAmplificationModulus n ∣
      (factorialGapPredecessorScaledRat (n + 1)).den := by
  refine
    (factorialGapRepeatedBirthAmplificationModulus_dvd_residualCofactor_succ
      hn).trans ?_
  refine
    ⟨factorialGapComponentwiseAccumulatedPrivatePowerModulus (n + 1), ?_⟩
  simpa [Nat.mul_comm] using
    (factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
      (n + 1)).symm

/-- Whenever amplification occurs, reduced coprimality turns the whole
full-multiplicity product into a nonzero next-numerator CRT projection. -/
theorem
    predecessorGapNumeratorNat_mod_repeatedBirthAmplificationModulus_ne_zero
    {n : ℕ} (hn : 2 ≤ n)
    (hnonempty :
      (factorialGapRepeatedBirthAmplificationPrimes n).Nonempty) :
    factorialGapPredecessorGapNumeratorNat (n + 1) %
        factorialGapRepeatedBirthAmplificationModulus n ≠ 0 := by
  exact
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
      (one_lt_factorialGapRepeatedBirthAmplificationModulus hn hnonempty)
      (factorialGapRepeatedBirthAmplificationModulus_dvd_succ_den hn)

/-- The repeated-birth cofactor splits across two adjacent times: its
birth/outflow overlap was already present in the old denominator, while
the complementary prime-power mass divides the next residual cofactor.
Consequently the entire `B_n` divides their product. -/
theorem
    factorialGapUnselectedBirthCofactor_dvd_predecessorScaledRat_den_mul_residualCofactor_succ
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapUnselectedBirthCofactor n ∣
      (factorialGapPredecessorScaledRat n).den *
        factorialGapComponentwiseResidualCofactor (n + 1) := by
  rw [
    ← Nat.mul_div_cancel'
      (Nat.gcd_dvd_left
        (factorialGapUnselectedBirthCofactor n)
        (factorialGapReducedTransitionNormalizer n))
  ]
  exact
    mul_dvd_mul
      (gcd_unselectedBirthCofactor_reducedTransitionNormalizer_dvd_predecessorScaledRat_den
        hn)
      (factorialGapUnselectedBirthCofactor_div_gcd_reducedTransitionNormalizer_dvd_residualCofactor_succ
        hn)

/-- Numerical form of the two-time conservation law: repeated birth mass
cannot exceed the old denominator times the next residual cofactor. -/
theorem
    factorialGapUnselectedBirthCofactor_le_predecessorScaledRat_den_mul_residualCofactor_succ
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapUnselectedBirthCofactor n ≤
      (factorialGapPredecessorScaledRat n).den *
        factorialGapComponentwiseResidualCofactor (n + 1) := by
  exact
    Nat.le_of_dvd
      (Nat.mul_pos
        (factorialGapPredecessorScaledRat n).den_pos
        (factorialGapComponentwiseResidualCofactor_pos (n + 1)))
      (factorialGapUnselectedBirthCofactor_dvd_predecessorScaledRat_den_mul_residualCofactor_succ
        hn)

/-- The old denominator mass required by a birth/outflow collision is
already visible either in the canonical active accumulator or in the old
residual cofactor. -/
theorem
    prime_dvd_accumulator_or_residualCofactor_of_prime_dvd_birth_and_reduced_outflow
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n)
    (hqOutflow : q ∣ factorialGapReducedTransitionNormalizer n) :
    q ∣ factorialGapComponentwiseAccumulatedPrivatePowerModulus n ∨
      q ∣ factorialGapComponentwiseResidualCofactor n := by
  have hqDen :=
    prime_dvd_factorialGapPredecessorScaledRat_den_of_prime_dvd_birth_and_reduced_outflow
      hn hq hqBirth hqOutflow
  rw [
    ← factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
  ] at hqDen
  exact hq.dvd_mul.mp hqDen

/-- A repeated-birth prime absent from the old reduced denominator cannot
enter the reduced outflow, and therefore forces strict residual valuation
growth at the next endpoint. -/
theorem
    factorialGapComponentwiseResidualCofactor_factorization_lt_succ_of_prime_dvd_birth_not_old_den
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqBirth : q ∣ factorialGapUnselectedBirthCofactor n)
    (hqNotDen : ¬q ∣ (factorialGapPredecessorScaledRat n).den) :
    (factorialGapComponentwiseResidualCofactor n).factorization q <
      (factorialGapComponentwiseResidualCofactor
        (n + 1)).factorization q := by
  apply
    factorialGapComponentwiseResidualCofactor_factorization_lt_succ_of_prime_dvd_birth_not_outflow
      hn hq hqBirth
  intro hqOutflow
  exact
    hqNotDen
      (prime_dvd_factorialGapPredecessorScaledRat_den_of_prime_dvd_birth_and_reduced_outflow
        hn hq hqBirth hqOutflow)

/-- If a prime enters the next residual cofactor from neither the old
residual nor the excess-kill defect, it must enter through repeated
factorial-gap support.  The witness is consequently nonadjacent and visible
in an explicit descending-factorial collision. -/
theorem prime_dvd_new_residualCofactor_interval_collision
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqNext :
      q ∣ factorialGapComponentwiseResidualCofactor (n + 1))
    (hqNotOld :
      ¬q ∣ factorialGapComponentwiseResidualCofactor n)
    (hqNotDefect :
      ¬q ∣ factorialGapKilledMultiplicityDefect n) :
    ∃ k : ℕ, 2 ≤ k ∧ k + 1 < n ∧
      q ∣ n.descFactorial (n - k) - 1 ∧
      q ≤ n ^ (n - k) := by
  have hnextNe :
      factorialGapComponentwiseResidualCofactor (n + 1) ≠ 0 :=
    (factorialGapComponentwiseResidualCofactor_pos (n + 1)).ne'
  have hbirthNe :
      factorialGapUnselectedBirthCofactor n ≠ 0 :=
    (factorialGapUnselectedBirthCofactor_pos hn).ne'
  have hnextPos :
      0 <
        (factorialGapComponentwiseResidualCofactor
          (n + 1)).factorization q :=
    hq.factorization_pos_of_dvd hnextNe hqNext
  have holdZero :
      (factorialGapComponentwiseResidualCofactor n).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqNotOld
  have hdefectZero :
      (factorialGapKilledMultiplicityDefect n).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqNotDefect
  have hval :=
    factorialGapComponentwiseResidualCofactor_succ_factorization_recurrence
      (q := q) hn
  rw [holdZero, hdefectZero, zero_add, add_zero] at hval
  have hbirthPos :
      0 < (factorialGapUnselectedBirthCofactor n).factorization q := by
    omega
  have hqBirth :
      q ∣ factorialGapUnselectedBirthCofactor n :=
    (hq.dvd_iff_one_le_factorization hbirthNe).2
      (by omega)
  exact
    prime_dvd_unselectedBirthCofactor_interval_collision
      hn hq hqBirth

/-- Every genuinely new prime in the next residual cofactor has one of two
possible origins.  Either it comes from repeated factorial-gap
support, with a nonadjacent descending-factorial collision and power bound,
or it is the label of a killed old source component colliding with the
current radix or gap. -/
theorem prime_dvd_new_residualCofactor_inflow_classification
    {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hqNext :
      q ∣ factorialGapComponentwiseResidualCofactor (n + 1))
    (hqNotOld :
      ¬q ∣ factorialGapComponentwiseResidualCofactor n) :
    (∃ k : ℕ, 2 ≤ k ∧ k + 1 < n ∧
        q ∣ n.descFactorial (n - k) - 1 ∧
        q ≤ n ^ (n - k)) ∨
      ∃ a : FactorialGapPrivatePrimeSource,
        a ∈ factorialGapKilledPrivatePrimeSources n ∧
        a.2 = q ∧
        (q ∣ n ∨ q ∣ n.factorial - 1) := by
  by_cases hqDefect :
      q ∣ factorialGapKilledMultiplicityDefect n
  · exact
      Or.inr
        (prime_dvd_killedMultiplicityDefect_source_collision
          hq hqDefect)
  · exact
      Or.inl
        (prime_dvd_new_residualCofactor_interval_collision
          hn hq hqNext hqNotOld hqDefect)

/-- The next residual cofactor divides the complete intrinsic inflow. -/
theorem
    factorialGapComponentwiseResidualCofactor_succ_dvd_intrinsicInflow
    {n : ℕ} (hn : 2 ≤ n) :
    factorialGapComponentwiseResidualCofactor (n + 1) ∣
      factorialGapComponentwiseResidualCofactor n *
        factorialGapUnselectedBirthCofactor n *
        factorialGapKilledMultiplicityDefect n := by
  refine
    ⟨factorialGapReducedTransitionNormalizer n, ?_⟩
  exact
    (factorialGapComponentwiseResidualCofactor_succ_intrinsic_recurrence
      hn).symm

/-- With neither unselected birth mass nor excess killed multiplicity,
the residual cofactor cannot grow. -/
theorem
    factorialGapComponentwiseResidualCofactor_succ_dvd_of_no_inflow
    {n : ℕ} (hn : 2 ≤ n)
    (hbirth : factorialGapUnselectedBirthCofactor n = 1)
    (hdefect : factorialGapKilledMultiplicityDefect n = 1) :
    factorialGapComponentwiseResidualCofactor (n + 1) ∣
      factorialGapComponentwiseResidualCofactor n := by
  simpa [hbirth, hdefect] using
    factorialGapComponentwiseResidualCofactor_succ_dvd_intrinsicInflow
      hn

/-- If there is no intrinsic inflow but the reduced transition
normalizer is nontrivial, the residual cofactor strictly decreases. -/
theorem
    factorialGapComponentwiseResidualCofactor_succ_lt_of_no_inflow
    {n : ℕ} (hn : 2 ≤ n)
    (hbirth : factorialGapUnselectedBirthCofactor n = 1)
    (hdefect : factorialGapKilledMultiplicityDefect n = 1)
    (hreduced : 1 < factorialGapReducedTransitionNormalizer n) :
    factorialGapComponentwiseResidualCofactor (n + 1) <
      factorialGapComponentwiseResidualCofactor n := by
  have hrec :=
    factorialGapComponentwiseResidualCofactor_succ_intrinsic_recurrence
      hn
  rw [hbirth, hdefect, mul_one, mul_one] at hrec
  have hstrict :
      factorialGapComponentwiseResidualCofactor (n + 1) * 1 <
        factorialGapComponentwiseResidualCofactor (n + 1) *
          factorialGapReducedTransitionNormalizer n :=
    (Nat.mul_lt_mul_left
      (factorialGapComponentwiseResidualCofactor_pos (n + 1))).2
        hreduced
  simpa [hrec] using hstrict

/-- A nonempty active component set makes the componentwise accumulated
modulus nontrivial. -/
theorem
    one_lt_factorialGapComponentwiseAccumulatedPrivatePowerModulus
    {n : ℕ}
    (hnonempty :
      (factorialGapActivePrivatePrimeSources n).Nonempty) :
    1 < factorialGapComponentwiseAccumulatedPrivatePowerModulus n := by
  obtain ⟨a, ha⟩ := hnonempty
  have haData :=
    mem_factorialGapActivePrivatePrimeSources_iff.1 ha
  have hqData :=
    (mem_factorialGapLargePrefixPrivatePrimes_iff
      haData.1).1 haData.2.2.1
  have hgapNe : a.1.factorial - 1 ≠ 0 := by
    exact
      (Nat.sub_pos_of_lt
        (Nat.one_lt_factorial.mpr haData.1)).ne'
  have hexpPos :
      0 < (a.1.factorial - 1).factorization a.2 :=
    hqData.1.factorization_pos_of_dvd hgapNe hqData.2.1
  have hcomponentOne :
      1 < factorialGapPrivatePrimeSourcePower a := by
    unfold factorialGapPrivatePrimeSourcePower
    exact one_lt_pow₀ hqData.1.one_lt hexpPos.ne'
  have hcomponentDvd :
      factorialGapPrivatePrimeSourcePower a ∣
        factorialGapComponentwiseAccumulatedPrivatePowerModulus n := by
    exact
      Finset.dvd_prod_of_mem
        factorialGapPrivatePrimeSourcePower ha
  have haccPos :
      0 <
        factorialGapComponentwiseAccumulatedPrivatePowerModulus n := by
    exact
      Nat.pos_of_dvd_of_pos
        factorialGapComponentwiseAccumulatedPrivatePowerModulus_dvd_den
        (factorialGapPredecessorScaledRat n).den_pos
  exact
    hcomponentOne.trans_le
      (Nat.le_of_dvd haccPos hcomponentDvd)

/-- The reduced numerator is nonzero modulo every nontrivial
componentwise canonical accumulator. -/
theorem
    predecessorGapNumeratorNat_mod_componentwiseAccumulatedPrivatePowerModulus_ne_zero
    {n : ℕ}
    (hnonempty :
      (factorialGapActivePrivatePrimeSources n).Nonempty) :
    factorialGapPredecessorGapNumeratorNat n %
        factorialGapComponentwiseAccumulatedPrivatePowerModulus n ≠ 0 := by
  exact
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
      (one_lt_factorialGapComponentwiseAccumulatedPrivatePowerModulus
        hnonempty)
      factorialGapComponentwiseAccumulatedPrivatePowerModulus_dvd_den

/-- The one-step persistence law iterates across any finite interval that
avoids the prime in both the intervening radices and factorial gaps. -/
theorem prime_dvd_factorialGapPredecessorScaledRat_den_of_interval_avoidance
    {m n q : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hq : q.Prime)
    (hqV : q ∣ (factorialGapPredecessorScaledRat m).den)
    (havoid :
      ∀ j : ℕ, m ≤ j → j < n →
        ¬q ∣ j ∧ ¬q ∣ j.factorial - 1) :
    q ∣ (factorialGapPredecessorScaledRat n).den := by
  induction n, hmn using Nat.le_induction with
  | base =>
      exact hqV
  | succ n hmn ih =>
      have ihDen :
          q ∣ (factorialGapPredecessorScaledRat n).den :=
        ih (fun j hmj hjn =>
          havoid j hmj (hjn.trans (Nat.lt_succ_self n)))
      have hj := havoid n hmn (Nat.lt_succ_self n)
      exact
        prime_dvd_factorialGapPredecessorScaledRat_succ_den
          (hm.trans hmn) hq ihDen hj.1 hj.2

/-- A finite set of denominator primes that all avoid the intervening
radices and factorial gaps persists synchronously as one CRT divisor at the
common endpoint. -/
theorem primeFinset_prod_dvd_den_of_interval_avoidance
    {m n : ℕ} {s : Finset ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hprime : ∀ q ∈ s, q.Prime)
    (hstart :
      ∀ q ∈ s, q ∣ (factorialGapPredecessorScaledRat m).den)
    (havoid :
      ∀ q ∈ s, ∀ j : ℕ, m ≤ j → j < n →
        ¬q ∣ j ∧ ¬q ∣ j.factorial - 1) :
    (∏ q ∈ s, q) ∣
      (factorialGapPredecessorScaledRat n).den := by
  apply primeFinset_prod_dvd_factorialGapPredecessorScaledRat_den
    hprime
  intro q hq
  exact
    prime_dvd_factorialGapPredecessorScaledRat_den_of_interval_avoidance
      hm hmn (hprime q hq) (hstart q hq) (havoid q hq)

/-- Under the same synchronous avoidance hypotheses, the combined
surviving-prime projection of the endpoint numerator is nonzero. -/
theorem predecessorGapNumeratorNat_mod_primeFinset_prod_ne_zero_of_interval_avoidance
    {m n : ℕ} {s : Finset ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hs : s.Nonempty)
    (hprime : ∀ q ∈ s, q.Prime)
    (hstart :
      ∀ q ∈ s, q ∣ (factorialGapPredecessorScaledRat m).den)
    (havoid :
      ∀ q ∈ s, ∀ j : ℕ, m ≤ j → j < n →
        ¬q ∣ j ∧ ¬q ∣ j.factorial - 1) :
    factorialGapPredecessorGapNumeratorNat n % (∏ q ∈ s, q) ≠ 0 := by
  apply
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
      (one_lt_primeFinset_prod hs hprime)
  exact
    primeFinset_prod_dvd_den_of_interval_avoidance
      hm hmn hprime hstart havoid

/-! ## Endpoint cylinders and the exact carry dichotomy -/

/-- The endpoint gap is the reduced predecessor residue after normalization
by `(p-1)!` and subtraction of the displayed block `p, ..., 2p-1`. -/
theorem factorialBlockEndpointGap_eq_predecessorGapRat_sub_block
    (p : ℕ) :
    factorialBlockEndpointGap p =
      factorialGapPredecessorGapRat p / ((p - 1).factorial : ℚ) -
        (factorialGapPrefix (2 * p - 1) -
          factorialGapPrefix (p - 1)) := by
  unfold factorialBlockEndpointGap factorialBlockBase
    factorialGapPredecessorGapRat
  rw [factorialBlockCoefficient_cast_eq_strictFacTopRat]
  have hfac : ((p - 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- The same endpoint identity entirely in terms of the coprime integer pair
`(u_p,v_p)` attached to the reduced predecessor prefix. -/
theorem factorialBlockEndpointGap_eq_predecessorNumerator_sub_block
    (p : ℕ) :
    factorialBlockEndpointGap p =
      (factorialGapPredecessorGapNumerator p : ℚ) /
          ((factorialGapPredecessorScaledRat p).den *
            (p - 1).factorial) -
        (factorialGapPrefix (2 * p - 1) -
          factorialGapPrefix (p - 1)) := by
  rw [
    factorialBlockEndpointGap_eq_predecessorGapRat_sub_block,
    factorialGapPredecessorGapRat_eq_numerator_div_den
  ]
  ring

/-- Consequently the full endpoint window is exactly a thin rational
cylinder for the reduced predecessor residue `u_p/v_p`. -/
theorem factorialBlockEndpointWindow_iff_predecessorNumerator_cylinder
    (p : ℕ) :
    factorialBlockEndpointWindow p ↔
      factorialGapPrefix (2 * p - 1) -
            factorialGapPrefix (p - 1) <
        (factorialGapPredecessorGapNumerator p : ℚ) /
          ((factorialGapPredecessorScaledRat p).den *
            (p - 1).factorial) ∧
      (factorialGapPredecessorGapNumerator p : ℚ) /
            ((factorialGapPredecessorScaledRat p).den *
              (p - 1).factorial) ≤
        factorialGapPrefix (2 * p - 1) -
            factorialGapPrefix (p - 1) +
          factorialBlockEndpointUpperBound p := by
  rw [factorialBlockEndpointWindow,
    factorialBlockEndpointGap_eq_predecessorNumerator_sub_block]
  constructor <;> rintro ⟨hlower, hupper⟩ <;>
    constructor <;> linarith

/-- Exact floor decomposition of the literal prefix.  The strict successor
is the canonical factorial floor of the full series, plus one precisely
when the canonical remainder lies above the scaled tail. -/
theorem strictFacTop_factorialGapPrefix_eq_facFloor_add_endpointFlag
    {m : ℕ} (hm : 2 ≤ m) :
    strictFacTop ((factorialGapPrefix m : ℚ) : ℝ) m =
      facFloor _root_.Erdos68.factorialGapSeries m +
        factorialGapEndpointFlag m := by
  let S : ℝ := _root_.Erdos68.factorialGapSeries
  let A : ℤ := facFloor S m
  let θ : ℝ := canonicalRemainder S m
  let R : ℝ := factorialGapScaledTail m
  have hdecomp :=
    _root_.Erdos68.factorialGapSeries_eq_sum_add_tail hm
  have hprefix := factorialGapPrefix_cast m
  rw [← hprefix] at hdecomp
  change S =
    ((factorialGapPrefix m : ℚ) : ℝ) +
      _root_.Erdos68.factorialGapTail m at hdecomp
  have hAθ :
      (A : ℝ) + θ = (m.factorial : ℝ) * S := by
    dsimp [A, θ, canonicalRemainder]
    ring
  have hscaled :
      (m.factorial : ℝ) *
          ((factorialGapPrefix m : ℚ) : ℝ) =
        (A : ℝ) + θ - R := by
    calc
      (m.factorial : ℝ) *
          ((factorialGapPrefix m : ℚ) : ℝ) =
        (m.factorial : ℝ) *
          (S - _root_.Erdos68.factorialGapTail m) := by
            congr 1
            linarith
      _ = (A : ℝ) + θ - R := by
        rw [hAθ]
        unfold R factorialGapScaledTail
        ring
  have hθNonneg : 0 ≤ θ := by
    exact canonicalRemainder_nonneg S m
  have hθLt : θ < 1 := by
    exact canonicalRemainder_lt_one S m
  have hRPos : 0 < R := by
    exact factorialGapScaledTail_pos hm
  have hRLt : R < 1 := by
    exact factorialGapScaledTail_lt_one hm
  by_cases hRθ : R ≤ θ
  · have hfloor :
        ⌊(m.factorial : ℝ) *
            ((factorialGapPrefix m : ℚ) : ℝ)⌋ = A := by
      apply Int.floor_eq_iff.mpr
      rw [hscaled]
      constructor <;> push_cast
      · linarith
      · linarith
    have hflag : factorialGapEndpointFlag m = 1 := by
      apply (factorialGapEndpointFlag_eq_one_iff m).mpr
      simpa [S, θ, R] using hRθ
    unfold strictFacTop
    rw [hfloor, hflag]
  · have hθR : θ < R := lt_of_not_ge hRθ
    have hfloor :
        ⌊(m.factorial : ℝ) *
            ((factorialGapPrefix m : ℚ) : ℝ)⌋ = A - 1 := by
      apply Int.floor_eq_iff.mpr
      rw [hscaled]
      constructor <;> push_cast
      · linarith
      · linarith
    have hflag : factorialGapEndpointFlag m = 0 := by
      apply (factorialGapEndpointFlag_eq_zero_iff m).mpr
      simpa [S, θ, R] using hθR
    unfold strictFacTop
    rw [hfloor, hflag]
    simp [A, S]

/-- The strict-successor carry is exactly the canonical digit corrected by
the two adjacent endpoint flags. -/
theorem factorialGapStepCarry_eq_digit_flag_expression
    {m : ℕ} (hm : 3 ≤ m) :
    factorialGapStepCarry m =
      1 -
        canonicalDigit _root_.Erdos68.factorialGapSeries m +
        (m : ℤ) * factorialGapEndpointFlag (m - 1) -
        factorialGapEndpointFlag m := by
  have hcurr :=
    strictFacTop_factorialGapPrefix_eq_facFloor_add_endpointFlag
      (m := m) (by omega)
  have hprev :=
    strictFacTop_factorialGapPrefix_eq_facFloor_add_endpointFlag
      (m := m - 1) (by omega)
  have hstep :=
    strictFacTop_factorialGapPrefix_step
      (m := m) (by omega)
  unfold canonicalDigit
  rw [hcurr, hprev] at hstep
  rw [mul_add] at hstep
  omega

/-- Exact branch dichotomy for a unit carry.  The zero branch has canonical
digit zero and both endpoint flags zero; the other branch has the maximal
radix digit and both flags one. -/
theorem factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch
    {m : ℕ} (hm : 3 ≤ m) :
    factorialGapStepCarry m = 1 ↔
      (canonicalDigit _root_.Erdos68.factorialGapSeries m = 0 ∧
        factorialGapEndpointFlag (m - 1) = 0 ∧
        factorialGapEndpointFlag m = 0) ∨
      (canonicalDigit _root_.Erdos68.factorialGapSeries m =
          (m : ℤ) - 1 ∧
        factorialGapEndpointFlag (m - 1) = 1 ∧
        factorialGapEndpointFlag m = 1) := by
  have hdNonneg :=
    canonicalDigit_nonneg
      _root_.Erdos68.factorialGapSeries m (by omega)
  have hdLt :=
    canonicalDigit_lt_radix
      _root_.Erdos68.factorialGapSeries m (by omega)
  obtain hprev | hprev :=
    factorialGapEndpointFlag_eq_zero_or_one (m - 1)
  · obtain hcurr | hcurr :=
      factorialGapEndpointFlag_eq_zero_or_one m
    · rw [factorialGapStepCarry_eq_digit_flag_expression hm,
        hprev, hcurr]
      omega
    · rw [factorialGapStepCarry_eq_digit_flag_expression hm,
        hprev, hcurr]
      omega
  · obtain hcurr | hcurr :=
      factorialGapEndpointFlag_eq_zero_or_one m
    · rw [factorialGapStepCarry_eq_digit_flag_expression hm,
        hprev, hcurr]
      omega
    · rw [factorialGapStepCarry_eq_digit_flag_expression hm,
        hprev, hcurr]
      omega

/-- The zero canonical branch is exactly the tiny lower endpoint cylinder.
This division-free form says `θ_(m-1) < R_m / m`. -/
theorem factorialGap_zero_branch_iff_lower_endpoint_cylinder
    {m : ℕ} (hm : 3 ≤ m) :
    (canonicalDigit _root_.Erdos68.factorialGapSeries m = 0 ∧
        factorialGapEndpointFlag (m - 1) = 0 ∧
        factorialGapEndpointFlag m = 0) ↔
      (m : ℝ) *
          canonicalRemainder
            _root_.Erdos68.factorialGapSeries (m - 1) <
        factorialGapScaledTail m := by
  let S : ℝ := _root_.Erdos68.factorialGapSeries
  change
    (canonicalDigit S m = 0 ∧
        factorialGapEndpointFlag (m - 1) = 0 ∧
        factorialGapEndpointFlag m = 0) ↔
      (m : ℝ) * canonicalRemainder S (m - 1) <
        factorialGapScaledTail m
  have hsucc : m - 1 + 1 = m := by omega
  have hcastSucc :
      ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast hsucc
  have hrec := canonicalRemainder_recurrence S (m - 1)
  rw [hsucc, hcastSucc] at hrec
  have htailRec :=
    factorialGapScaledTail_pred_recurrence (m := m) hm
  have hRPos :=
    factorialGapScaledTail_pos (m := m) (by omega)
  have hRLt :=
    factorialGapScaledTail_lt_one (m := m) (by omega)
  constructor
  · rintro ⟨hdigit, _hprev, hcurr⟩
    have hcurrLt :=
      (factorialGapEndpointFlag_eq_zero_iff m).mp hcurr
    rw [hdigit] at hrec
    norm_num at hrec
    rw [hrec] at hcurrLt
    exact hcurrLt
  · intro hsmall
    have hdigit : canonicalDigit S m = 0 := by
      rw [canonicalDigit_eq_floor_mul_remainder S m (by omega)]
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        exact mul_nonneg (by positivity)
          (canonicalRemainder_nonneg S (m - 1))
      · norm_num
        exact hsmall.trans hRLt
    have hcurrRem :
        canonicalRemainder S m =
          (m : ℝ) * canonicalRemainder S (m - 1) := by
      rw [hdigit] at hrec
      norm_num at hrec
      exact hrec
    have hcurr : factorialGapEndpointFlag m = 0 := by
      apply (factorialGapEndpointFlag_eq_zero_iff m).mpr
      rw [hcurrRem]
      exact hsmall
    have hdenPos :
        0 < 1 / ((m.factorial : ℝ) - 1) := by
      apply one_div_pos.mpr
      have hfacGt : (1 : ℝ) < m.factorial := by
        exact_mod_cast Nat.one_lt_factorial.mpr (by omega : 2 ≤ m)
      linarith
    have hRltPred :
        factorialGapScaledTail m <
          (m : ℝ) * factorialGapScaledTail (m - 1) := by
      linarith
    have hmPos : (0 : ℝ) < m := by positivity
    have hprevLt :
        canonicalRemainder S (m - 1) <
          factorialGapScaledTail (m - 1) := by
      nlinarith
    have hprev :
        factorialGapEndpointFlag (m - 1) = 0 :=
      (factorialGapEndpointFlag_eq_zero_iff (m - 1)).mpr
        hprevLt
    exact ⟨hdigit, hprev, hcurr⟩

/-- The maximal canonical branch is exactly the upper endpoint cylinder. -/
theorem factorialGap_maximal_branch_iff_upper_endpoint_cylinder
    {m : ℕ} (hm : 3 ≤ m) :
    (canonicalDigit _root_.Erdos68.factorialGapSeries m =
          (m : ℤ) - 1 ∧
        factorialGapEndpointFlag (m - 1) = 1 ∧
        factorialGapEndpointFlag m = 1) ↔
      ((m : ℝ) - 1) + factorialGapScaledTail m ≤
        (m : ℝ) *
          canonicalRemainder
            _root_.Erdos68.factorialGapSeries (m - 1) := by
  let S : ℝ := _root_.Erdos68.factorialGapSeries
  change
    (canonicalDigit S m = (m : ℤ) - 1 ∧
        factorialGapEndpointFlag (m - 1) = 1 ∧
        factorialGapEndpointFlag m = 1) ↔
      ((m : ℝ) - 1) + factorialGapScaledTail m ≤
        (m : ℝ) * canonicalRemainder S (m - 1)
  have hsucc : m - 1 + 1 = m := by omega
  have hcastSucc :
      ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast hsucc
  have hrec := canonicalRemainder_recurrence S (m - 1)
  rw [hsucc, hcastSucc] at hrec
  have htailRec :=
    factorialGapScaledTail_pred_recurrence (m := m) hm
  have hRPos :=
    factorialGapScaledTail_pos (m := m) (by omega)
  have hθLt :=
    canonicalRemainder_lt_one S (m - 1)
  constructor
  · rintro ⟨hdigit, _hprev, hcurr⟩
    have hcurrGe :=
      (factorialGapEndpointFlag_eq_one_iff m).mp hcurr
    rw [hdigit] at hrec
    push_cast at hrec
    rw [hrec] at hcurrGe
    linarith
  · intro hlarge
    have hdigit :
        canonicalDigit S m = (m : ℤ) - 1 := by
      rw [canonicalDigit_eq_floor_mul_remainder S m (by omega)]
      apply Int.floor_eq_iff.mpr
      constructor
      · push_cast
        linarith
      · push_cast
        have hmPos : (0 : ℝ) < m := by positivity
        nlinarith
    have hcurrRem :
        canonicalRemainder S m =
          (m : ℝ) * canonicalRemainder S (m - 1) -
            ((m : ℝ) - 1) := by
      rw [hdigit] at hrec
      push_cast at hrec
      exact hrec
    have hcurr : factorialGapEndpointFlag m = 1 := by
      apply (factorialGapEndpointFlag_eq_one_iff m).mpr
      rw [hcurrRem]
      linarith
    have hfacGtTwo : (2 : ℝ) < m.factorial := by
      have hfacSix : 6 ≤ m.factorial :=
        Nat.factorial_le (show 3 ≤ m by omega)
      exact_mod_cast (show 2 < m.factorial by omega)
    have hdenGtOne :
        (1 : ℝ) < (m.factorial : ℝ) - 1 := by
      linarith
    have hepsLtOne :
        1 / ((m.factorial : ℝ) - 1) < 1 := by
      simpa using
        (one_div_lt_one_div_of_lt
          (show (0 : ℝ) < 1 by norm_num) hdenGtOne)
    have hpredScaledLtThreshold :
        (m : ℝ) * factorialGapScaledTail (m - 1) <
          ((m : ℝ) - 1) + factorialGapScaledTail m := by
      have hmReal : (3 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hmPos : (0 : ℝ) < m := by positivity
    have hprevGe :
        factorialGapScaledTail (m - 1) ≤
          canonicalRemainder S (m - 1) := by
      nlinarith
    have hprev :
        factorialGapEndpointFlag (m - 1) = 1 :=
      (factorialGapEndpointFlag_eq_one_iff (m - 1)).mpr
        hprevGe
    exact ⟨hdigit, hprev, hcurr⟩

/-- Exact endpoint-cylinder dichotomy for a unit carry.  The theorem is
pointwise and leaves both the lower and upper cylinders possible.  In the
later conditional contradiction, rationality separately forces sufficiently
late canonical remainders and digits to vanish. -/
theorem factorialGapStepCarry_eq_one_iff_endpoint_cylinders
    {m : ℕ} (hm : 3 ≤ m) :
    factorialGapStepCarry m = 1 ↔
      (m : ℝ) *
          canonicalRemainder
            _root_.Erdos68.factorialGapSeries (m - 1) <
          factorialGapScaledTail m ∨
        ((m : ℝ) - 1) + factorialGapScaledTail m ≤
          (m : ℝ) *
            canonicalRemainder
              _root_.Erdos68.factorialGapSeries (m - 1) := by
  rw [factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch hm,
    factorialGap_zero_branch_iff_lower_endpoint_cylinder hm,
    factorialGap_maximal_branch_iff_upper_endpoint_cylinder hm]

/-- Escaping the lower cylinder forces either a non-unit carry or the
maximal canonical digit.  Thus an upper-cylinder hit is already useful. -/
theorem lower_endpoint_escape_forces_nonunit_or_maximal_digit
    {m : ℕ} (hm : 3 ≤ m)
    (hescape :
      factorialGapScaledTail m ≤
        (m : ℝ) *
          canonicalRemainder
            _root_.Erdos68.factorialGapSeries (m - 1)) :
    factorialGapStepCarry m ≠ 1 ∨
      canonicalDigit _root_.Erdos68.factorialGapSeries m =
        (m : ℤ) - 1 := by
  by_cases hcarry : factorialGapStepCarry m = 1
  · right
    rcases
        (factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch hm).mp
          hcarry with hzero | hmax
    · have hlower :=
        (factorialGap_zero_branch_iff_lower_endpoint_cylinder hm).mp
          hzero
      linarith
    · exact hmax.1
  · exact Or.inl hcarry

/-- The predecessor strict-successor gap is the scaled full-series tail
minus the canonical remainder, with the endpoint flag restoring the
wraparound.  In particular, this exposes the endpoint cylinders through a
quantity computed from the finite rational prefix alone. -/
theorem factorialGapPredecessorGap_eq_scaledTail_sub_remainder_add_flag
    {m : ℕ} (hm : 3 ≤ m) :
    factorialGapPredecessorGap m =
      factorialGapScaledTail (m - 1) -
        canonicalRemainder
          _root_.Erdos68.factorialGapSeries (m - 1) +
        (factorialGapEndpointFlag (m - 1) : ℝ) := by
  let S : ℝ := _root_.Erdos68.factorialGapSeries
  let P : ℝ := ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
  let A : ℤ := facFloor S (m - 1)
  let θ : ℝ := canonicalRemainder S (m - 1)
  let R : ℝ := factorialGapScaledTail (m - 1)
  have hdecomp :=
    _root_.Erdos68.factorialGapSeries_eq_sum_add_tail
      (D := m - 1) (by omega)
  have hprefix := factorialGapPrefix_cast (m - 1)
  rw [← hprefix] at hdecomp
  change S = P + _root_.Erdos68.factorialGapTail (m - 1) at hdecomp
  have hAθ :
      (A : ℝ) + θ = (((m - 1).factorial : ℝ) * S) := by
    dsimp [A, θ, canonicalRemainder]
    ring
  have hscaled :
      ((m - 1).factorial : ℝ) * P =
        (A : ℝ) + θ - R := by
    calc
      ((m - 1).factorial : ℝ) * P =
          ((m - 1).factorial : ℝ) *
            (S - _root_.Erdos68.factorialGapTail (m - 1)) := by
              congr 1
              linarith
      _ = (A : ℝ) + θ - R := by
        rw [hAθ]
        unfold R factorialGapScaledTail
        ring
  have htop :=
    strictFacTop_factorialGapPrefix_eq_facFloor_add_endpointFlag
      (m := m - 1) (by omega)
  unfold factorialGapPredecessorGap
  change
    (strictFacTop P (m - 1) : ℝ) -
        ((m - 1).factorial : ℝ) * P =
      R - θ + (factorialGapEndpointFlag (m - 1) : ℝ)
  rw [htop, hscaled]
  push_cast
  dsimp [A, S, θ, R]
  ring

/-- The zero branch is exactly the lower subwindow of the computable
predecessor-gap carry interval.  Its width is the scaled future tail
`factorialGapScaledTail m`, whereas the full unit-carry interval has width
one. -/
theorem factorialGap_zero_branch_iff_predecessorGap_lower_window
    {m : ℕ} (hm : 3 ≤ m) :
    (canonicalDigit _root_.Erdos68.factorialGapSeries m = 0 ∧
        factorialGapEndpointFlag (m - 1) = 0 ∧
        factorialGapEndpointFlag m = 0) ↔
      1 + 1 / ((m.factorial : ℝ) - 1) <
          (m : ℝ) * factorialGapPredecessorGap m ∧
        (m : ℝ) * factorialGapPredecessorGap m ≤
          1 + 1 / ((m.factorial : ℝ) - 1) +
            factorialGapScaledTail m := by
  let S : ℝ := _root_.Erdos68.factorialGapSeries
  let θ : ℝ := canonicalRemainder S (m - 1)
  let Rprev : ℝ := factorialGapScaledTail (m - 1)
  let R : ℝ := factorialGapScaledTail m
  have hgap :=
    factorialGapPredecessorGap_eq_scaledTail_sub_remainder_add_flag hm
  have htailRec :=
    factorialGapScaledTail_pred_recurrence (m := m) hm
  have hθNonneg := canonicalRemainder_nonneg S (m - 1)
  constructor
  · rintro ⟨hdigit, hprev, hcurr⟩
    have hlower :=
      (factorialGap_zero_branch_iff_lower_endpoint_cylinder hm).mp
        ⟨hdigit, hprev, hcurr⟩
    change
      factorialGapPredecessorGap m =
        Rprev - θ + (factorialGapEndpointFlag (m - 1) : ℝ) at hgap
    rw [hprev] at hgap
    push_cast at hgap
    norm_num at hgap
    change (m : ℝ) * θ < R at hlower
    change
      (m : ℝ) * Rprev =
        1 + 1 / ((m.factorial : ℝ) - 1) + R at htailRec
    constructor
    · have hRPos := factorialGapScaledTail_pos (m := m) (by omega)
      rw [hgap]
      linarith
    · rw [hgap]
      nlinarith
  · rintro ⟨hlower, hupper⟩
    have hcarry : factorialGapStepCarry m = 1 := by
      have hRLt := factorialGapScaledTail_lt_one (m := m) (by omega)
      unfold factorialGapStepCarry
      have hfloor :
          ⌊1 + 1 / ((m.factorial : ℝ) - 1) -
              (m : ℝ) * factorialGapPredecessorGap m⌋ =
            (-1 : ℤ) := by
        apply Int.floor_eq_iff.mpr
        constructor
        · push_cast
          linarith
        · push_cast
          linarith
      rw [hfloor]
      norm_num
    rcases
        (factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch hm).mp
          hcarry with hzero | hmax
    · exact hzero
    · exfalso
      have hlarge :=
        (factorialGap_maximal_branch_iff_upper_endpoint_cylinder hm).mp
          hmax
      obtain ⟨_hdigit, hprev, _hcurr⟩ := hmax
      change
        factorialGapPredecessorGap m =
          Rprev - θ + (factorialGapEndpointFlag (m - 1) : ℝ) at hgap
      rw [hprev] at hgap
      push_cast at hgap
      change ((m : ℝ) - 1) + R ≤ (m : ℝ) * θ at hlarge
      change
        (m : ℝ) * Rprev =
          1 + 1 / ((m.factorial : ℝ) - 1) + R at htailRec
      have hθLt := canonicalRemainder_lt_one S (m - 1)
      change θ < 1 at hθLt
      have hmPos : (0 : ℝ) < m := by positivity
      have hmθLt : (m : ℝ) * θ < (m : ℝ) := by
        simpa using mul_lt_mul_of_pos_left hθLt hmPos
      rw [hgap] at hupper
      linarith

/-- Crossing the explicit rational threshold `2 / m` past the start of the
unit-carry window rules out the zero branch without mentioning the infinite
tail or the full-series remainder. -/
theorem predecessorGap_tailfree_threshold_forces_nonunit_or_maximal_digit
    {m : ℕ} (hm : 3 ≤ m)
    (hthreshold :
      1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
        (m : ℝ) * factorialGapPredecessorGap m) :
    factorialGapStepCarry m ≠ 1 ∨
      canonicalDigit _root_.Erdos68.factorialGapSeries m =
        (m : ℤ) - 1 := by
  by_cases hcarry : factorialGapStepCarry m = 1
  · right
    rcases
        (factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch hm).mp
          hcarry with hzero | hmax
    · have hwindow :=
        (factorialGap_zero_branch_iff_predecessorGap_lower_window hm).mp
          hzero
      have htail :=
        factorialGapScaledTail_lt_two_div (m := m) (by omega)
      linarith
    · exact hmax.1
  · exact Or.inl hcarry

/-- Executable rational form of the tail-free threshold. -/
theorem predecessorGapRat_threshold_forces_nonunit_or_maximal_digit
    {m : ℕ} (hm : 3 ≤ m)
    (hthreshold :
      (1 : ℚ) + 1 / ((m.factorial : ℚ) - 1) + 2 / (m : ℚ) ≤
        (m : ℚ) * factorialGapPredecessorGapRat m) :
    factorialGapStepCarry m ≠ 1 ∨
      canonicalDigit _root_.Erdos68.factorialGapSeries m =
        (m : ℤ) - 1 := by
  apply predecessorGap_tailfree_threshold_forces_nonunit_or_maximal_digit hm
  rw [← factorialGapPredecessorGapRat_cast m]
  have hcast :
      (((1 : ℚ) + 1 / ((m.factorial : ℚ) - 1) + 2 / (m : ℚ) : ℚ) :
          ℝ) ≤
        (((m : ℚ) * factorialGapPredecessorGapRat m : ℚ) : ℝ) :=
    Rat.cast_le.mpr hthreshold
  simpa using hcast

/-- Fully integral-residue form of the tail-free threshold.  The only
division is by the reduced denominator of an explicitly computed rational
prefix. -/
theorem predecessorGapNumerator_threshold_forces_nonunit_or_maximal_digit
    {m : ℕ} (hm : 3 ≤ m)
    (hthreshold :
      (1 : ℚ) + 1 / ((m.factorial : ℚ) - 1) + 2 / (m : ℚ) ≤
        (m : ℚ) *
          ((factorialGapPredecessorGapNumerator m : ℚ) /
            (factorialGapPredecessorScaledRat m).den)) :
    factorialGapStepCarry m ≠ 1 ∨
      canonicalDigit _root_.Erdos68.factorialGapSeries m =
        (m : ℤ) - 1 := by
  apply predecessorGapRat_threshold_forces_nonunit_or_maximal_digit hm
  rwa [factorialGapPredecessorGapRat_eq_numerator_div_den]

/-- Clearing the three positive denominators turns the finite-prefix
threshold into one integer inequality. -/
theorem predecessorGapNumerator_threshold_iff_cleared
    {m : ℕ} (hm : 3 ≤ m) :
    ((1 : ℚ) + 1 / ((m.factorial : ℚ) - 1) + 2 / (m : ℚ) ≤
        (m : ℚ) *
          ((factorialGapPredecessorGapNumerator m : ℚ) /
            (factorialGapPredecessorScaledRat m).den)) ↔
      (((m : ℤ) + 2) * (m.factorial : ℤ) - 2) *
          ((factorialGapPredecessorScaledRat m).den : ℤ) ≤
        (m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1) *
          factorialGapPredecessorGapNumerator m := by
  let M : ℚ := m
  let F : ℚ := m.factorial
  let U : ℚ := factorialGapPredecessorGapNumerator m
  let V : ℚ := (factorialGapPredecessorScaledRat m).den
  have hM : 0 < M := by positivity
  have hF : 1 < F := by
    dsimp [F]
    exact_mod_cast Nat.one_lt_factorial.mpr (by omega : 2 ≤ m)
  have hA : 0 < F - 1 := sub_pos.mpr hF
  have hD : 0 < M * (F - 1) := mul_pos hM hA
  have hV : 0 < V := by positivity
  have hleft :
      (1 : ℚ) + 1 / (F - 1) + 2 / M =
        ((M + 2) * F - 2) / (M * (F - 1)) := by
    field_simp
    ring
  have hright :
      M * (U / V) = (M * U) / V := by ring
  change
    ((1 : ℚ) + 1 / (F - 1) + 2 / M ≤ M * (U / V)) ↔ _
  rw [hleft, hright, div_le_div_iff₀ hD hV]
  constructor <;> intro h
  · have h' :
        (((m : ℚ) + 2) * (m.factorial : ℚ) - 2) *
              ((factorialGapPredecessorScaledRat m).den : ℚ) ≤
            (m : ℚ) ^ 2 * ((m.factorial : ℚ) - 1) *
              (factorialGapPredecessorGapNumerator m : ℚ) := by
      dsimp [M, F, U, V] at h
      convert h using 1 <;> ring
    exact_mod_cast h'
  · have h' :
        (((m : ℚ) + 2) * (m.factorial : ℚ) - 2) *
              ((factorialGapPredecessorScaledRat m).den : ℚ) ≤
            (m : ℚ) ^ 2 * ((m.factorial : ℚ) - 1) *
              (factorialGapPredecessorGapNumerator m : ℚ) := by
      exact_mod_cast h
    dsimp [M, F, U, V]
    convert h' using 1 <;> ring

/-- A modular projection of the positive numerator can imply the full
cleared threshold: its least nonnegative residue is never larger than the
numerator itself. -/
theorem predecessorGapNumerator_mod_threshold_forces_nonunit_or_maximal_digit
    {m q : ℕ} (hm : 3 ≤ m)
    (hthreshold :
      (((m : ℤ) + 2) * (m.factorial : ℤ) - 2) *
          ((factorialGapPredecessorScaledRat m).den : ℤ) ≤
        ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) *
          ((factorialGapPredecessorGapNumeratorNat m % q : ℕ) : ℤ)) :
    factorialGapStepCarry m ≠ 1 ∨
      canonicalDigit _root_.Erdos68.factorialGapSeries m =
        (m : ℤ) - 1 := by
  have hmodNat :
      factorialGapPredecessorGapNumeratorNat m % q ≤
        factorialGapPredecessorGapNumeratorNat m :=
    Nat.mod_le _ _
  have hmod :
      ((factorialGapPredecessorGapNumeratorNat m % q : ℕ) : ℤ) ≤
        (factorialGapPredecessorGapNumeratorNat m : ℤ) := by
    exact_mod_cast hmodNat
  have hcoefficient :
      0 ≤ (m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1) := by
    have hfac : (1 : ℤ) ≤ m.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.factorial_ne_zero m)
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hfac)
  apply predecessorGapNumerator_threshold_forces_nonunit_or_maximal_digit hm
  apply (predecessorGapNumerator_threshold_iff_cleared hm).mpr
  calc
    (((m : ℤ) + 2) * (m.factorial : ℤ) - 2) *
          ((factorialGapPredecessorScaledRat m).den : ℤ) ≤
        ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) *
          ((factorialGapPredecessorGapNumeratorNat m % q : ℕ) : ℤ) :=
      hthreshold
    _ ≤
        ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) *
          (factorialGapPredecessorGapNumeratorNat m : ℤ) :=
      mul_le_mul_of_nonneg_left hmod hcoefficient
    _ =
        (m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1) *
          factorialGapPredecessorGapNumerator m := by
      rw [factorialGapPredecessorGapNumeratorNat_cast]

/-- Any modulus whose projected residue meets the cleared threshold must
capture a correspondingly large part of the reduced denominator.  This
rules out treating a small isolated denominator prime as sufficient: the
useful object is a large CRT divisor. -/
theorem predecessorGapNumerator_modulus_large_of_mod_threshold
    {m d : ℕ} (hm : 3 ≤ m) (hd : 0 < d)
    (hthreshold :
      (((m : ℤ) + 2) * (m.factorial : ℤ) - 2) *
          ((factorialGapPredecessorScaledRat m).den : ℤ) ≤
        ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) *
          ((factorialGapPredecessorGapNumeratorNat m % d : ℕ) : ℤ)) :
    (((m : ℤ) + 2) * (m.factorial : ℤ) - 2) *
          ((factorialGapPredecessorScaledRat m).den : ℤ) <
        ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) * (d : ℤ) := by
  have hmodNat :
      factorialGapPredecessorGapNumeratorNat m % d < d :=
    Nat.mod_lt _ hd
  have hmod :
      ((factorialGapPredecessorGapNumeratorNat m % d : ℕ) : ℤ) <
        (d : ℤ) := by
    exact_mod_cast hmodNat
  have hmPos : (0 : ℤ) < m := by
    exact_mod_cast (by omega : 0 < m)
  have hfac : (1 : ℤ) < m.factorial := by
    exact_mod_cast Nat.one_lt_factorial.mpr (by omega : 2 ≤ m)
  have hcoefficient :
      0 < (m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1) :=
    mul_pos (pow_pos hmPos 2) (sub_pos.mpr hfac)
  exact
    hthreshold.trans_lt
      (mul_lt_mul_of_pos_left hmod hcoefficient)

/-- Once `n!` clears a displayed rational denominator, its canonical
factorial remainder is zero. -/
theorem canonicalRemainder_eq_zero_of_eq_rat
    {x : ℝ} {n q : ℕ} {a : ℤ}
    (hq : 0 < q)
    (hqn : q ≤ n)
    (hx : x = (a : ℝ) / (q : ℝ)) :
    canonicalRemainder x n = 0 := by
  have hqfac : q ∣ n.factorial :=
    Nat.dvd_factorial hq hqn
  have hfac :
      q * (n.factorial / q) = n.factorial :=
    Nat.mul_div_cancel' hqfac
  have hfacR :
      (q : ℝ) * ((n.factorial / q : ℕ) : ℝ) =
        (n.factorial : ℝ) := by
    exact_mod_cast hfac
  have hgrid :
      (n.factorial : ℝ) * x =
        (((n.factorial / q : ℕ) : ℤ) * a : ℤ) := by
    rw [hx, ← hfacR]
    have hqR : (q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hq)
    calc
      ((q : ℝ) * ((n.factorial / q : ℕ) : ℝ)) *
          ((a : ℝ) / (q : ℝ)) =
          ((n.factorial / q : ℕ) : ℝ) *
            ((q : ℝ) * ((a : ℝ) / (q : ℝ))) := by ring
      _ = ((n.factorial / q : ℕ) : ℝ) * (a : ℝ) := by
        rw [mul_div_cancel₀ _ hqR]
      _ = (((n.factorial / q : ℕ) : ℤ) * a : ℤ) := by
        rw [Int.cast_mul, Int.cast_natCast]
  rw [canonicalRemainder_eq_fract, hgrid]
  exact Int.fract_intCast _

/-! ## Conditional cofinal criteria for irrationality -/

/-- If the explicit rational predecessor-gap threshold holds cofinally,
then the factorial-gap series is irrational.  Every quantity in the
hypothesis is computed from a finite prefix. -/
theorem irrational_factorialGapSeries_of_cofinal_predecessorGap_threshold
    (hthreshold :
      ∀ B : ℕ, ∃ m : ℕ,
        3 ≤ m ∧ B < m ∧
          1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
            (m : ℝ) * factorialGapPredecessorGap m) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  by_contra hrat
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  obtain ⟨m, hm, hlarge, hmThreshold⟩ :=
    hthreshold (r.den + 1)
  have hdenPrev : r.den ≤ m - 1 := by omega
  have hcarry :
      factorialGapStepCarry m = 1 := by
    apply factorialGapStepCarry_eq_one_of_series_eq_rat
      (q := r.den) (a := r.num)
    · exact hm
    · exact r.den_pos
    · exact hdenPrev
    · rw [hr, Rat.cast_def]
  rcases
      predecessorGap_tailfree_threshold_forces_nonunit_or_maximal_digit
        hm hmThreshold with hmiss | hmax
  · exact hmiss hcarry
  · have hremPrev :
        canonicalRemainder
            _root_.Erdos68.factorialGapSeries (m - 1) = 0 := by
      apply canonicalRemainder_eq_zero_of_eq_rat
        (q := r.den) (a := r.num)
      · exact r.den_pos
      · exact hdenPrev
      · rw [hr, Rat.cast_def]
    have hdigit :
        canonicalDigit _root_.Erdos68.factorialGapSeries m = 0 := by
      rw [
        canonicalDigit_eq_floor_mul_remainder
          _root_.Erdos68.factorialGapSeries m (by omega),
        hremPrev
      ]
      norm_num
    rw [hdigit] at hmax
    omega

/-- If the exact reduced-numerator threshold holds cofinally, then the
factorial-gap series is irrational.  The hypothesis mentions neither the
infinite series nor a real-valued floor or tail. -/
theorem
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_threshold
    (hthreshold :
      ∀ B : ℕ, ∃ m : ℕ,
        3 ≤ m ∧ B < m ∧
          (1 : ℚ) + 1 / ((m.factorial : ℚ) - 1) + 2 / (m : ℚ) ≤
            (m : ℚ) *
              ((factorialGapPredecessorGapNumerator m : ℚ) /
                (factorialGapPredecessorScaledRat m).den)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply irrational_factorialGapSeries_of_cofinal_predecessorGap_threshold
  intro B
  obtain ⟨m, hm, hlarge, hmThreshold⟩ := hthreshold B
  refine ⟨m, hm, hlarge, ?_⟩
  rw [← factorialGapPredecessorGapRat_cast m,
    factorialGapPredecessorGapRat_eq_numerator_div_den]
  have hcast :
      (((1 : ℚ) + 1 / ((m.factorial : ℚ) - 1) + 2 / (m : ℚ) : ℚ) :
          ℝ) ≤
        (((m : ℚ) *
            ((factorialGapPredecessorGapNumerator m : ℚ) /
              (factorialGapPredecessorScaledRat m).den) : ℚ) : ℝ) :=
    Rat.cast_le.mpr hmThreshold
  simpa using hcast

/-- If the displayed modular lower bound holds cofinally for divisors of
the reduced denominator, then the factorial-gap series is irrational.  The
modular bound promotes to the full numerator threshold. -/
theorem
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_modulus_threshold
    (hthreshold :
      ∀ B : ℕ, ∃ m d : ℕ,
        3 ≤ m ∧
        B < m ∧
        1 < d ∧
        d ∣ (factorialGapPredecessorScaledRat m).den ∧
        (((m : ℤ) + 2) * (m.factorial : ℤ) - 2) *
            ((factorialGapPredecessorScaledRat m).den : ℤ) ≤
          ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) *
            ((factorialGapPredecessorGapNumeratorNat m % d : ℕ) : ℤ)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_threshold
  intro B
  obtain ⟨m, d, hm, hlarge, _hd, _hdDen, hmodThreshold⟩ :=
    hthreshold B
  refine ⟨m, hm, hlarge, ?_⟩
  apply (predecessorGapNumerator_threshold_iff_cleared hm).mpr
  have hmodNat :
      factorialGapPredecessorGapNumeratorNat m % d ≤
        factorialGapPredecessorGapNumeratorNat m :=
    Nat.mod_le _ _
  have hmod :
      ((factorialGapPredecessorGapNumeratorNat m % d : ℕ) : ℤ) ≤
        (factorialGapPredecessorGapNumeratorNat m : ℤ) := by
    exact_mod_cast hmodNat
  have hcoefficient :
      0 ≤ (m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1) := by
    have hfac : (1 : ℤ) ≤ m.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.factorial_ne_zero m)
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hfac)
  calc
    (((m : ℤ) + 2) * (m.factorial : ℤ) - 2) *
          ((factorialGapPredecessorScaledRat m).den : ℤ) ≤
        ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) *
          ((factorialGapPredecessorGapNumeratorNat m % d : ℕ) : ℤ) :=
      hmodThreshold
    _ ≤
        ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) *
          (factorialGapPredecessorGapNumeratorNat m : ℤ) :=
      mul_le_mul_of_nonneg_left hmod hcoefficient
    _ =
        (m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1) *
          factorialGapPredecessorGapNumerator m := by
      rw [factorialGapPredecessorGapNumeratorNat_cast]

/-- Finite-prime-set form of the modular criterion.  Pointwise prime
divisibility assembles the distinct primes into a divisor of the reduced
denominator before the residue bound is applied. -/
theorem
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_primeFinset_threshold
    (hthreshold :
      ∀ B : ℕ, ∃ m : ℕ, ∃ s : Finset ℕ,
        3 ≤ m ∧
        B < m ∧
        s.Nonempty ∧
        (∀ q ∈ s,
          q.Prime ∧
          q ∣ (factorialGapPredecessorScaledRat m).den) ∧
        (((m : ℤ) + 2) * (m.factorial : ℤ) - 2) *
            ((factorialGapPredecessorScaledRat m).den : ℤ) ≤
          ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) *
            ((factorialGapPredecessorGapNumeratorNat m %
              (∏ q ∈ s, q) : ℕ) : ℤ)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_modulus_threshold
  intro B
  obtain ⟨m, s, hm, hlarge, hs, hanchors, hmodThreshold⟩ :=
    hthreshold B
  have hprime : ∀ q ∈ s, q.Prime := by
    intro q hq
    exact (hanchors q hq).1
  have hdiv :
      ∀ q ∈ s, q ∣ (factorialGapPredecessorScaledRat m).den := by
    intro q hq
    exact (hanchors q hq).2
  exact
    ⟨m, ∏ q ∈ s, q, hm, hlarge,
      one_lt_primeFinset_prod hs hprime,
      primeFinset_prod_dvd_factorialGapPredecessorScaledRat_den
        hprime hdiv,
      hmodThreshold⟩

/-- Same-gap squarefree-modulus criterion.  The required hypothesis is the
quantitative projected-residue threshold for the product of all large
prefix-private prime factors of `m! - 1` at their first endpoint. -/
theorem
    irrational_factorialGapSeries_of_cofinal_largePrefixPrivateModulus_threshold
    (hthreshold :
      ∀ B : ℕ, ∃ m : ℕ,
        2 ≤ m ∧
        B < m ∧
        (factorialGapLargePrefixPrivatePrimes m).Nonempty ∧
        ((((m + 1 : ℕ) : ℤ) + 2) *
              ((m + 1).factorial : ℤ) - 2) *
            ((factorialGapPredecessorScaledRat (m + 1)).den : ℤ) ≤
          (((m + 1 : ℕ) : ℤ) ^ 2 *
              (((m + 1).factorial : ℤ) - 1)) *
            ((factorialGapPredecessorGapNumeratorNat (m + 1) %
              factorialGapLargePrefixPrivateModulus m : ℕ) : ℤ)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_modulus_threshold
  intro B
  obtain ⟨m, hm, hlarge, hs, hmodThreshold⟩ :=
    hthreshold B
  have hmem :
      ∀ q ∈ factorialGapLargePrefixPrivatePrimes m, q.Prime := by
    intro q hqMem
    exact
      ((mem_factorialGapLargePrefixPrivatePrimes_iff hm).1 hqMem).1
  have hmodOne :
      1 < factorialGapLargePrefixPrivateModulus m := by
    simpa [factorialGapLargePrefixPrivateModulus] using
      one_lt_primeFinset_prod hs hmem
  have hmodDen :=
    (factorialGapLargePrefixPrivateModulus_two_step_crt_anchors hm hs).1
  exact
    ⟨m + 1, factorialGapLargePrefixPrivateModulus m,
      by omega, by omega, hmodOne, hmodDen, hmodThreshold⟩

/-- Multiplicity-sensitive same-gap criterion.  Its hypothesis retains each
prefix-private prime to its complete valuation in `m! - 1`, avoiding the
squarefree-radical loss. -/
theorem
    irrational_factorialGapSeries_of_cofinal_largePrefixPrivatePowerModulus_threshold
    (hthreshold :
      ∀ B : ℕ, ∃ m : ℕ,
        2 ≤ m ∧
        B < m ∧
        (factorialGapLargePrefixPrivatePrimes m).Nonempty ∧
        ((((m + 1 : ℕ) : ℤ) + 2) *
              ((m + 1).factorial : ℤ) - 2) *
            ((factorialGapPredecessorScaledRat (m + 1)).den : ℤ) ≤
          (((m + 1 : ℕ) : ℤ) ^ 2 *
              (((m + 1).factorial : ℤ) - 1)) *
            ((factorialGapPredecessorGapNumeratorNat (m + 1) %
              factorialGapLargePrefixPrivatePowerModulus m : ℕ) : ℤ)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_modulus_threshold
  intro B
  obtain ⟨m, hm, hlarge, hs, hmodThreshold⟩ :=
    hthreshold B
  exact
    ⟨m + 1, factorialGapLargePrefixPrivatePowerModulus m,
      by omega, by omega,
      one_lt_factorialGapLargePrefixPrivatePowerModulus hm hs,
      factorialGapLargePrefixPrivatePowerModulus_dvd_succ_den hm,
      hmodThreshold⟩

/-- Accumulated-modulus criterion.  The active-source construction supplies
the algebraic entry, coprimality, and transport facts; the displayed
cofinal quantitative residue inequality remains an assumption. -/
theorem
    irrational_factorialGapSeries_of_cofinal_accumulatedPrivatePowerModulus_threshold
    (hthreshold :
      ∀ B : ℕ, ∃ n : ℕ,
        3 ≤ n ∧
        B < n ∧
        (∃ m ∈ factorialGapActivePrefixPrivatePowerSources n,
          (factorialGapLargePrefixPrivatePrimes m).Nonempty) ∧
        (((n : ℤ) + 2) * (n.factorial : ℤ) - 2) *
            ((factorialGapPredecessorScaledRat n).den : ℤ) ≤
          ((n : ℤ) ^ 2 * ((n.factorial : ℤ) - 1)) *
            ((factorialGapPredecessorGapNumeratorNat n %
              factorialGapAccumulatedPrivatePowerModulus n : ℕ) : ℤ)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_modulus_threshold
  intro B
  obtain ⟨n, hn, hlarge, hnonempty, hmodThreshold⟩ :=
    hthreshold B
  exact
    ⟨n, factorialGapAccumulatedPrivatePowerModulus n,
      hn, hlarge,
      one_lt_factorialGapAccumulatedPrivatePowerModulus hnonempty,
      factorialGapAccumulatedPrivatePowerModulus_dvd_den,
      hmodThreshold⟩

/-- Componentwise accumulated-modulus criterion.  This retains
each private prime power independently, so a later collision at one prime
does not erase the surviving contributions born at the same source gap. -/
theorem
    irrational_factorialGapSeries_of_cofinal_componentwiseAccumulatedPrivatePowerModulus_threshold
    (hthreshold :
      ∀ B : ℕ, ∃ n : ℕ,
        3 ≤ n ∧
        B < n ∧
        (factorialGapActivePrivatePrimeSources n).Nonempty ∧
        (((n : ℤ) + 2) * (n.factorial : ℤ) - 2) *
            ((factorialGapPredecessorScaledRat n).den : ℤ) ≤
          ((n : ℤ) ^ 2 * ((n.factorial : ℤ) - 1)) *
            ((factorialGapPredecessorGapNumeratorNat n %
              factorialGapComponentwiseAccumulatedPrivatePowerModulus n :
                ℕ) : ℤ)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_modulus_threshold
  intro B
  obtain ⟨n, hn, hlarge, hnonempty, hmodThreshold⟩ :=
    hthreshold B
  exact
    ⟨n, factorialGapComponentwiseAccumulatedPrivatePowerModulus n,
      hn, hlarge,
      one_lt_factorialGapComponentwiseAccumulatedPrivatePowerModulus
        hnonempty,
      factorialGapComponentwiseAccumulatedPrivatePowerModulus_dvd_den,
      hmodThreshold⟩

/-- Prime-modulus form of the same criterion.  It is useful only when a
single prime captures enough of the reduced denominator; in general a
larger composite divisor is needed. -/
theorem
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_mod_threshold
    (hthreshold :
      ∀ B : ℕ, ∃ m q : ℕ,
        3 ≤ m ∧
        B < m ∧
        q.Prime ∧
        q ∣ (factorialGapPredecessorScaledRat m).den ∧
        (((m : ℤ) + 2) * (m.factorial : ℤ) - 2) *
            ((factorialGapPredecessorScaledRat m).den : ℤ) ≤
          ((m : ℤ) ^ 2 * ((m.factorial : ℤ) - 1)) *
            ((factorialGapPredecessorGapNumeratorNat m % q : ℕ) : ℤ)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_modulus_threshold
  intro B
  obtain ⟨m, q, hm, hlarge, hq, hqDen, hmodThreshold⟩ :=
    hthreshold B
  exact ⟨m, q, hm, hlarge, hq.one_lt, hqDen, hmodThreshold⟩

/-- Cofinal escape from the tiny lower cylinder at prime indices proves
Erdős #68.  A prime need not miss the full unit-carry target: landing in
the maximal-digit upper cylinder also suffices. -/
theorem irrational_factorialGapSeries_of_cofinal_prime_lower_endpoint_escape
    (hescape :
      ∀ B : ℕ, ∃ p : ℕ,
        p.Prime ∧ B < p ∧
        factorialGapScaledTail p ≤
          (p : ℝ) *
            canonicalRemainder
              _root_.Erdos68.factorialGapSeries (p - 1)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  by_contra hrat
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  obtain ⟨p, hp, hlarge, hpEscape⟩ :=
    hescape (max 3 (r.den + 1))
  have hpPred : r.den ≤ p - 1 := by
    have : r.den + 1 < p := (le_max_right 3 (r.den + 1)).trans_lt hlarge
    omega
  have hzero :
      canonicalRemainder
          _root_.Erdos68.factorialGapSeries (p - 1) = 0 := by
    apply canonicalRemainder_eq_zero_of_eq_rat
      (q := r.den) (a := r.num)
    · exact r.den_pos
    · exact hpPred
    · rw [hr, Rat.cast_def]
  have htailPos :
      0 < factorialGapScaledTail p :=
    factorialGapScaledTail_pos hp.two_le
  rw [hzero] at hpEscape
  norm_num at hpEscape
  linarith

#print axioms
  not_dvd_factorialGapPredecessorScaledRat_den_of_prefixPrivate
#print axioms
  factorialGapPredecessorScaledRat_succ_den_dvd_den_mul_gap
#print axioms
  factorialGapPredecessorScaledRat_succ_den_mul_transitionNormalizer
#print axioms
  factorialGapPredecessorGapNumerator_succ_recurrence_cleared
#print axioms
  factorialGapPredecessorGapNumerator_mul_transitionNormalizer
#print axioms
  transitionNormalizer_mul_predecessorGapNumerator_modEq_neg_den
#print axioms
  prime_coprime_factorialGapPredecessorTransitionNormalizer_of_dvd_gap
#print axioms
  prime_dvd_factorialGapPredecessorTransitionNormalizer_of_collision
#print axioms
  factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_one_lt_dvd_den
#print axioms
  factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_prime_dvd_den
#print axioms
  primeFinset_prod_dvd_factorialGapPredecessorScaledRat_den
#print axioms
  factorialGapPredecessorGapNumeratorNat_mod_primeFinset_prod_ne_zero
#print axioms
  factorialGapPredecessorScaledRat_den_dvd_radix_gap_succ_den
#print axioms
  dvd_factorialGapPredecessorScaledRat_succ_den_of_coprime
#print axioms
  prime_dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap
#print axioms
  dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap_coprime
#print axioms
  prime_pow_dvd_factorialGapPredecessorScaledRat_succ_den_of_dvd_gap
#print axioms
  prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_den
#print axioms
  prefixPrivate_prime_dvd_factorialGapPredecessorScaledRat_succ_succ_den
#print axioms
  prefixPrivate_prime_pow_dvd_factorialGapPredecessorScaledRat_two_step_den
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_dvd_gap
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_dvd_tailoredBlockPrivateQuotient
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_dvd_tailoredBlockPrivateModulus
#print axioms
  mem_factorialGapLargePrefixPrivatePrimes_dvd_tailoredBlockPrivateModulus
#print axioms
  factorialGapLargePrefixPrivatePrimes_distinct_factor_pair_tailoredBlock
#print axioms
  factorialGapLargePrefixPrivatePrimes_unit_factor_pair_tailoredBlock
#print axioms
  irrational_factorialGapSeries_of_cofinal_largePrefixPrivate_unitFactorPairFloor
#print axioms
  irrational_factorialGapSeries_of_cofinal_largePrefixPrivate_unitScaleSplit
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_coprime_of_lt
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_pairwise_coprime
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_coprime_old_den
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_dvd_succ_den
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_coprime_succ
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_coprime_succ_gap
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_two_step_den_anchors
#print axioms
  one_lt_factorialGapLargePrefixPrivatePowerModulus
#print axioms
  factorialGapLargePrefixPrivateModulus_two_step_crt_anchors
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_two_step_crt_anchors
#print axioms
  cofinal_large_prime_factorialGap_denominator_anchors
#print axioms
  cofinal_large_prime_factorialGap_two_step_denominator_anchors
#print axioms
  cofinal_largePrefixPrivateModulus_two_step_crt_anchors
#print axioms
  cofinal_large_prime_factorialGap_nonzero_numerator_projections
#print axioms
  dvd_factorialGapPredecessorScaledRat_den_of_interval_coprime
#print axioms
  predecessorGapNumeratorNat_mod_ne_zero_of_interval_coprime
#print axioms
  pairwiseCoprimeCompositeFinset_prod_dvd_den_of_interval_coprime
#print axioms
  predecessorGapNumeratorNat_mod_pairwiseCoprimeCompositeFinset_prod_ne_zero
#print axioms
  factorialGapLargePrefixPrivatePowerModulus_finset_prod_dvd_den
#print axioms
  predecessorGapNumeratorNat_mod_largePrefixPrivatePowerModulus_finset_prod_ne_zero
#print axioms
  mem_factorialGapActivePrefixPrivatePowerSources_iff
#print axioms
  factorialGapAccumulatedPrivatePowerModulus_dvd_den
#print axioms
  one_lt_factorialGapAccumulatedPrivatePowerModulus
#print axioms
  predecessorGapNumeratorNat_mod_accumulatedPrivatePowerModulus_ne_zero
#print axioms
  mem_factorialGapActivePrivatePrimeSources_iff
#print axioms
  factorialGapPrivatePrimeSourcePower_entry_projection
#print axioms
  mem_factorialGapActivePrivatePrimeSources_succ_iff_of_source_lt
#print axioms
  mk_mem_factorialGapActivePrivatePrimeSources_succ_iff
#print axioms
  factorialGapActivePrivatePrimeSources_succ_eq_surviving_union_born
#print axioms
  factorialGapActivePrivatePrimeSources_prime_ne
#print axioms
  factorialGapActivePrivatePrimeSourcePowers_pairwise_coprime
#print axioms
  factorialGapPrivatePrimeSourcePower_dvd_entry_den
#print axioms
  factorialGapComponentwiseAccumulatedPrivatePowerModulus_dvd_den
#print axioms
  factorialGapKilledPrivatePrimeModulus_dvd_transitionNormalizer
#print axioms
  prime_dvd_unselectedBirthCofactor_boundary_or_repeat
#print axioms
  prime_dvd_unselectedBirthCofactor_repeat
#print axioms
  prime_dvd_unselectedBirthCofactor_of_repeat
#print axioms
  prime_dvd_unselectedBirthCofactor_interval_collision
#print axioms
  factorialGap_square_dvd_later_iff_blockQuotient_balance
#print axioms
  primePower_dvd_unselectedBirthCofactor_of_prime_dvd
#print axioms
  factorialGapKilledPrivatePrimeModulus_dvd_killedTransitionGcd
#print axioms
  factorialGapKilledTransitionGcd_mul_reducedTransitionNormalizer
#print axioms
  factorialGapKilledTransitionGcd_mul_killedMultiplicityDefect
#print axioms
  prime_dvd_killedMultiplicityDefect_source_collision
#print axioms
  factorialGapKilledMultiplicityDefect_coprime_reducedTransitionNormalizer
#print axioms
  factorialGapComponentwiseAccumulatedPrivatePowerModulus_mul_residualCofactor
#print axioms
  factorialGapComponentwiseAccumulatedPrivatePowerModulus_succ_mul_killed
#print axioms
  factorialGapComponentwiseResidualCofactor_succ_recurrence
#print axioms
  factorialGapComponentwiseResidualCofactor_succ_reduced_recurrence
#print axioms
  factorialGapComponentwiseResidualCofactor_succ_intrinsic_recurrence
#print axioms
  factorialGapComponentwiseResidualCofactor_succ_factorization_recurrence
#print axioms
  factorialGapReducedTransitionNormalizer_factorization_eq_zero_of_prime_dvd_defect
#print axioms
  factorialGapComponentwiseResidualCofactor_succ_factorization_eq_of_prime_dvd_defect
#print axioms
  factorialGapComponentwiseResidualCofactor_factorization_lt_succ_of_prime_dvd_defect
#print axioms
  factorialGapKilledMultiplicityDefect_dvd_residualCofactor_succ
#print axioms
  factorialGapComponentwiseResidualCofactor_succ_factorization_eq_of_not_dvd_outflow
#print axioms
  factorialGapComponentwiseResidualCofactor_factorization_lt_succ_of_prime_dvd_birth_not_outflow
#print axioms
  exists_late_prefixPrivate_factorialGap_hit_of_primeProduct_lt
#print axioms
  prime_dvd_factorialBlockCollisionCore_of_odd_reflection
#print axioms
  prime_dvd_factorialBlockNormalizedCollisionCore_of_odd_reflection
#print axioms
  one_lt_factorialBlockPrimeHitCount_of_odd_reflection
#print axioms
  prime_dvd_reducedTransitionNormalizer_of_prime_dvd_birth_of_not_residual_growth
#print axioms
  factorialGapUnselectedBirthCofactor_div_gcd_reducedTransitionNormalizer_dvd_residualCofactor_succ
#print axioms
  prime_dvd_factorialGapPredecessorScaledRat_den_of_prime_dvd_birth_and_reduced_outflow
#print axioms
  gcd_factorialGap_transitionNormalizer_dvd_predecessorScaledRat_den
#print axioms
  gcd_unselectedBirthCofactor_reducedTransitionNormalizer_dvd_predecessorScaledRat_den
#print axioms
  factorialGapUnselectedBirthCofactor_factorization_eq_gap_of_prime_dvd
#print axioms
  factorialGap_factorization_le_den_of_reducedOutflow_exceeds_residual
#print axioms
  factorialGap_primePower_dvd_residualCofactor_succ_of_den_factorization_lt_gap
#print axioms
  factorialGapPredecessorScaledRat_den_factorization_lt_gap_of_record
#print axioms
  factorialGap_repeatedRecordPrimePower_dvd_residualCofactor_succ
#print axioms
  factorialGap_repeatedRecordPrimePower_dvd_succ_den
#print axioms
  predecessorGapNumeratorNat_mod_repeatedRecordPrimePower_ne_zero
#print axioms
  factorialWilsonQuotient_modEq_one_iff_square_dvd_gap
#print axioms
  factorialGap_halfFactorial_Wilson_record_entry
#print axioms
  oneHundredSeven_sq_not_dvd_factorialGap_before_105
#print axioms
  predecessorGapNumeratorNat_mod_oneHundredSeven_sq_at_106_ne_zero
#print axioms
  nineHundredSeventyOne_sq_not_dvd_factorialGap_before_609
#print axioms
  nineHundredSeventyOne_firstRepeatedPrimeSquare_entry
#print axioms
  factorialGapRepeatedBirthAmplificationModulus_dvd_birth_gcd_residual_succ
#print axioms
  factorialGapRepeatedBirthAmplificationModulus_dvd_succ_den
#print axioms
  predecessorGapNumeratorNat_mod_repeatedBirthAmplificationModulus_ne_zero
#print axioms
  factorialGapUnselectedBirthCofactor_dvd_predecessorScaledRat_den_mul_residualCofactor_succ
#print axioms
  factorialGapUnselectedBirthCofactor_le_predecessorScaledRat_den_mul_residualCofactor_succ
#print axioms
  prime_dvd_accumulator_or_residualCofactor_of_prime_dvd_birth_and_reduced_outflow
#print axioms
  factorialGapComponentwiseResidualCofactor_factorization_lt_succ_of_prime_dvd_birth_not_old_den
#print axioms
  prime_dvd_new_residualCofactor_interval_collision
#print axioms
  prime_dvd_new_residualCofactor_inflow_classification
#print axioms
  factorialGapComponentwiseResidualCofactor_succ_dvd_intrinsicInflow
#print axioms
  factorialGapComponentwiseResidualCofactor_succ_lt_of_no_inflow
#print axioms
  one_lt_factorialGapComponentwiseAccumulatedPrivatePowerModulus
#print axioms
  predecessorGapNumeratorNat_mod_componentwiseAccumulatedPrivatePowerModulus_ne_zero
#print axioms
  prime_dvd_factorialGapPredecessorScaledRat_den_of_interval_avoidance
#print axioms
  predecessorGapNumeratorNat_mod_primeFinset_prod_ne_zero_of_interval_avoidance
#print axioms
  factorialBlockEndpointWindow_iff_predecessorNumerator_cylinder
#print axioms
  strictFacTop_factorialGapPrefix_eq_facFloor_add_endpointFlag
#print axioms
  factorialGapPredecessorGap_eq_scaledTail_sub_remainder_add_flag
#print axioms
  predecessorGap_tailfree_threshold_forces_nonunit_or_maximal_digit
#print axioms
  predecessorGapNumerator_threshold_forces_nonunit_or_maximal_digit
#print axioms
  predecessorGapNumerator_mod_threshold_forces_nonunit_or_maximal_digit
#print axioms
  irrational_factorialGapSeries_of_cofinal_predecessorGap_threshold
#print axioms
  irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_threshold
#print axioms
  irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_modulus_threshold
#print axioms
  irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_primeFinset_threshold
#print axioms
  irrational_factorialGapSeries_of_cofinal_largePrefixPrivateModulus_threshold
#print axioms
  irrational_factorialGapSeries_of_cofinal_largePrefixPrivatePowerModulus_threshold
#print axioms
  irrational_factorialGapSeries_of_cofinal_accumulatedPrivatePowerModulus_threshold
#print axioms
  irrational_factorialGapSeries_of_cofinal_componentwiseAccumulatedPrivatePowerModulus_threshold
#print axioms
  irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_mod_threshold
#print axioms
  irrational_factorialGapSeries_of_cofinal_prime_lower_endpoint_escape

end ErdosProblems.Erdos68
