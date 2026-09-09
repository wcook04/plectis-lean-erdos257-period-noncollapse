import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the three-prime running-LCM coordinate

This module starts the problem-owned formalization of the first unresolved
three-prime case. It records the exact computational height used by the
running-LCM representation, its cubic majorant, the smallest non-separation
fixture for `{2,3,5}`, the variable-base tail-state update, and the uniform
quadratic bound for actual filtered smooth-number shells.

No declaration here asserts irrationality or transcendence of a three-prime
value. The missing producer is still an infinite residue-escape or genuinely
higher-dimensional analytic theorem.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- The `{p,q,r}`-smooth lattice point with exponent vector `(i,j,k)`. -/
def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

/-- The product of the largest pure `p`-, `q`-, and `r`-powers not exceeding
`x`. For a `{p,q,r}`-smooth `x`, this is the running LCM of the smooth prefix. -/
def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

/-- The exact rational lattice kernel attached to the running-LCM height. -/
def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

/-- Exponent vectors of the actual `{p,q,r}`-smooth prefix up to `x`.  The
logarithmic box makes the prefix finite; the final filter keeps only products
which really lie below `x`. -/
def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x

/-- The literal running LCM of the finite smooth prefix. -/
def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2

/-- Every actual smooth prefix value divides the coordinatewise maximal
pure-power product. -/
theorem smooth3Val_dvd_threePrimeHeight_of_mem
    {p q r x : ℕ} {e : ℕ × ℕ × ℕ}
    (he : e ∈ smoothPrefixExponents p q r x) :
    smooth3Val p q r e.1 e.2.1 e.2.2 ∣ threePrimeHeight p q r x := by
  have hbox := (Finset.mem_filter.mp he).1
  have hpBox := Finset.mem_product.mp hbox
  have hqrBox := Finset.mem_product.mp hpBox.2
  have hpExp : e.1 ≤ Nat.log p x := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hpBox.1)
  have hqExp : e.2.1 ≤ Nat.log q x := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hqrBox.1)
  have hrExp : e.2.2 ≤ Nat.log r x := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hqrBox.2)
  exact mul_dvd_mul
    (mul_dvd_mul (pow_dvd_pow p hpExp) (pow_dvd_pow q hqExp))
    (pow_dvd_pow r hrExp)

/-- The literal smooth-prefix LCM divides the computational height. -/
theorem smoothPrefixLcm_dvd_threePrimeHeight (p q r x : ℕ) :
    smoothPrefixLcm p q r x ∣ threePrimeHeight p q r x := by
  apply Finset.lcm_dvd
  intro e he
  exact smooth3Val_dvd_threePrimeHeight_of_mem he

/-- The pure `p` height component occurs in the actual prefix. -/
theorem pureFirst_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (Nat.log p x, 0, 0) ∈ smoothPrefixExponents p q r x := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
        Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  · simpa [smooth3Val] using Nat.pow_log_le_self p hx

/-- The pure `q` height component occurs in the actual prefix. -/
theorem pureSecond_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (0, Nat.log q x, 0) ∈ smoothPrefixExponents p q r x := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_self _),
        Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  · simpa [smooth3Val] using Nat.pow_log_le_self q hx

/-- The pure `r` height component occurs in the actual prefix. -/
theorem pureThird_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (0, 0, Nat.log r x) ∈ smoothPrefixExponents p q r x := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
        Finset.mem_range.mpr (Nat.lt_succ_self _)⟩
  · simpa [smooth3Val] using Nat.pow_log_le_self r hx

/-- Exact running-LCM identity for three pairwise-distinct primes. -/
theorem smoothPrefixLcm_eq_threePrimeHeight
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x := by
  apply Nat.dvd_antisymm (smoothPrefixLcm_dvd_threePrimeHeight p q r x)
  have hpDvd : p ^ Nat.log p x ∣ smoothPrefixLcm p q r x := by
    simpa [smoothPrefixLcm, smooth3Val] using
      (Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureFirst_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx))
  have hqDvd : q ^ Nat.log q x ∣ smoothPrefixLcm p q r x := by
    simpa [smoothPrefixLcm, smooth3Val] using
      (Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureSecond_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx))
  have hrDvd : r ^ Nat.log r x ∣ smoothPrefixLcm p q r x := by
    simpa [smoothPrefixLcm, smooth3Val] using
      (Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureThird_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx))
  have hpqCoprime :
      (p ^ Nat.log p x).Coprime (q ^ Nat.log q x) :=
    Nat.coprime_pow_primes _ _ hp hq hpq
  have hprCoprime :
      (p ^ Nat.log p x).Coprime (r ^ Nat.log r x) :=
    Nat.coprime_pow_primes _ _ hp hr hpr
  have hqrCoprime :
      (q ^ Nat.log q x).Coprime (r ^ Nat.log r x) :=
    Nat.coprime_pow_primes _ _ hq hr hqr
  have hpqDvd :
      p ^ Nat.log p x * q ^ Nat.log q x ∣ smoothPrefixLcm p q r x :=
    hpqCoprime.mul_dvd_of_dvd_of_dvd hpDvd hqDvd
  have hpqrCoprime :
      (p ^ Nat.log p x * q ^ Nat.log q x).Coprime
        (r ^ Nat.log r x) :=
    Nat.coprime_mul_iff_left.mpr ⟨hprCoprime, hqrCoprime⟩
  exact hpqrCoprime.mul_dvd_of_dvd_of_dvd hpqDvd hrDvd

/-- Two cutoffs lie in the same three-prime logarithmic cell when none of the
three maximal pure-power coordinates changes between them. -/
def SameThreePrimeLogCell (p q r x y : ℕ) : Prop :=
  Nat.log p x = Nat.log p y ∧
    Nat.log q x = Nat.log q y ∧
      Nat.log r x = Nat.log r y

/-- The computational height is exactly constant on every logarithmic cell. -/
theorem threePrimeHeight_eq_of_sameLogCell
    {p q r x y : ℕ} (hcell : SameThreePrimeLogCell p q r x y) :
    threePrimeHeight p q r x = threePrimeHeight p q r y := by
  rcases hcell with ⟨hp, hq, hr⟩
  simp [threePrimeHeight, hp, hq, hr]

/-- For pairwise-distinct primes, the literal smooth-prefix LCM is constant on
every three-prime logarithmic cell.  This is the finite formal interface behind
the prime-power jump expansion: the LCM can change only when one logarithmic
coordinate changes. -/
theorem smoothPrefixLcm_eq_of_sameLogCell
    {p q r x y : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hcell : SameThreePrimeLogCell p q r x y) :
    smoothPrefixLcm p q r x = smoothPrefixLcm p q r y := by
  rw [smoothPrefixLcm_eq_threePrimeHeight hp hq hr hpq hpr hqr hx,
    smoothPrefixLcm_eq_threePrimeHeight hp hq hr hpq hpr hqr hy]
  exact threePrimeHeight_eq_of_sameLogCell hcell

/-- The rational lattice kernel is likewise constant whenever its two smooth
arguments occupy the same logarithmic cell. -/
theorem threePrimeKernelQ_eq_of_sameLogCell
    {p q r i j k i' j' k' : ℕ}
    (hcell : SameThreePrimeLogCell p q r
      (smooth3Val p q r i j k) (smooth3Val p q r i' j' k')) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  simp only [threePrimeKernelQ]
  rw [threePrimeHeight_eq_of_sameLogCell hcell]

/-! ## Finite pure-power jump enumeration -/

/-- The first `count` positive powers of one prime base.  Exponent zero is
omitted because it is the common initial value `1` in every channel. -/
def positivePrimePowers (p count : ℕ) : Finset ℕ :=
  (Finset.range count).image fun e => p ^ (e + 1)

/-- A prime base has no repeated positive powers. -/
theorem positivePrimePowers_card
    {p count : ℕ} (hp : p.Prime) :
    (positivePrimePowers p count).card = count := by
  calc
    (positivePrimePowers p count).card = (Finset.range count).card := by
      rw [positivePrimePowers, Finset.card_image_iff]
      intro a _ha b _hb hab
      exact Nat.add_right_cancel (Nat.pow_right_injective hp.two_le hab)
    _ = count := Finset.card_range count

/-- The common origin `1` is absent from every positive prime-power channel. -/
theorem one_not_mem_positivePrimePowers
    {p count : ℕ} (hp : p.Prime) :
    1 ∉ positivePrimePowers p count := by
  intro hone
  change 1 ∈ (Finset.range count).image (fun e => p ^ (e + 1)) at hone
  rcases Finset.mem_image.mp hone with ⟨e, _he, hpow⟩
  have hlt : 1 < p ^ (e + 1) := one_lt_pow₀ hp.one_lt (by omega)
  exact (Nat.ne_of_gt hlt) hpow

/-- Positive power channels of two distinct primes are disjoint. -/
theorem positivePrimePowers_disjoint
    {p q pcount qcount : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Disjoint (positivePrimePowers p pcount) (positivePrimePowers q qcount) := by
  rw [Finset.disjoint_left]
  intro x hpx hqx
  change x ∈ (Finset.range pcount).image (fun e => p ^ (e + 1)) at hpx
  change x ∈ (Finset.range qcount).image (fun e => q ^ (e + 1)) at hqx
  rcases Finset.mem_image.mp hpx with ⟨a, _ha, hpa⟩
  rcases Finset.mem_image.mp hqx with ⟨b, _hb, hqb⟩
  have hpow : p ^ (a + 1) = q ^ (b + 1) := hpa.trans hqb.symm
  exact hpq (hp.pow_inj hq hpow).1

/-- The finite union of the first `count` positive powers in each of the three
prime channels. -/
def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ :=
  (positivePrimePowers p count ∪ positivePrimePowers q count) ∪
    positivePrimePowers r count

/-- For three pairwise-distinct primes, the finite positive jump channels have
exactly `3 * count` elements: there are no cross-channel duplicate powers. -/
theorem threePrimePositiveJumpSet_card
    {p q r count : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (threePrimePositiveJumpSet p q r count).card = 3 * count := by
  have hpqDisjoint :=
    positivePrimePowers_disjoint (pcount := count) (qcount := count) hp hq hpq
  have hprDisjoint :=
    positivePrimePowers_disjoint (pcount := count) (qcount := count) hp hr hpr
  have hqrDisjoint :=
    positivePrimePowers_disjoint (pcount := count) (qcount := count) hq hr hqr
  have hpqrDisjoint :
      Disjoint
        (positivePrimePowers p count ∪ positivePrimePowers q count)
        (positivePrimePowers r count) :=
    Finset.disjoint_union_left.mpr ⟨hprDisjoint, hqrDisjoint⟩
  rw [threePrimePositiveJumpSet,
    Finset.card_union_of_disjoint hpqrDisjoint,
    Finset.card_union_of_disjoint hpqDisjoint,
    positivePrimePowers_card hp,
    positivePrimePowers_card hq,
    positivePrimePowers_card hr]
  omega

/-- The finite jump set including the unique common origin `1`. -/
def threePrimeJumpSetWithOrigin (p q r count : ℕ) : Finset ℕ :=
  insert 1 (threePrimePositiveJumpSet p q r count)

/-- Including the common origin turns the `3 * count` positive candidates into
exactly `3 * count + 1` distinct finite jump values. -/
theorem threePrimeJumpSetWithOrigin_card
    {p q r count : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (threePrimeJumpSetWithOrigin p q r count).card = 3 * count + 1 := by
  have hone : 1 ∉ threePrimePositiveJumpSet p q r count := by
    simp [threePrimePositiveJumpSet,
      one_not_mem_positivePrimePowers hp,
      one_not_mem_positivePrimePowers hq,
      one_not_mem_positivePrimePowers hr]
  rw [threePrimeJumpSetWithOrigin, Finset.card_insert_of_notMem hone,
    threePrimePositiveJumpSet_card hp hq hr hpq hpr hqr]

/-! ## Single-coordinate jump ratios -/

/-- If only the first logarithmic coordinate advances by one, the height is
multiplied by the first base. -/
theorem threePrimeHeight_firstLogStep
    {p q r x y : ℕ}
    (hp : Nat.log p y = Nat.log p x + 1)
    (hq : Nat.log q y = Nat.log q x)
    (hr : Nat.log r y = Nat.log r x) :
    threePrimeHeight p q r y = p * threePrimeHeight p q r x := by
  simp only [threePrimeHeight, hp, hq, hr, pow_succ]
  ring

/-- If only the second logarithmic coordinate advances by one, the height is
multiplied by the second base. -/
theorem threePrimeHeight_secondLogStep
    {p q r x y : ℕ}
    (hp : Nat.log p y = Nat.log p x)
    (hq : Nat.log q y = Nat.log q x + 1)
    (hr : Nat.log r y = Nat.log r x) :
    threePrimeHeight p q r y = q * threePrimeHeight p q r x := by
  simp only [threePrimeHeight, hp, hq, hr, pow_succ]
  ring

/-- If only the third logarithmic coordinate advances by one, the height is
multiplied by the third base. -/
theorem threePrimeHeight_thirdLogStep
    {p q r x y : ℕ}
    (hp : Nat.log p y = Nat.log p x)
    (hq : Nat.log q y = Nat.log q x)
    (hr : Nat.log r y = Nat.log r x + 1) :
    threePrimeHeight p q r y = r * threePrimeHeight p q r x := by
  simp only [threePrimeHeight, hp, hq, hr, pow_succ]
  ring

/-- A first-coordinate jump multiplies the literal running LCM by `p`. -/
theorem smoothPrefixLcm_firstLogStep
    {p q r x y : ℕ} (pprime : p.Prime) (qprime : q.Prime) (rprime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hp : Nat.log p y = Nat.log p x + 1)
    (hq : Nat.log q y = Nat.log q x)
    (hr : Nat.log r y = Nat.log r x) :
    smoothPrefixLcm p q r y = p * smoothPrefixLcm p q r x := by
  rw [smoothPrefixLcm_eq_threePrimeHeight pprime qprime rprime hpq hpr hqr hy,
    smoothPrefixLcm_eq_threePrimeHeight pprime qprime rprime hpq hpr hqr hx]
  exact threePrimeHeight_firstLogStep hp hq hr

/-- A second-coordinate jump multiplies the literal running LCM by `q`. -/
theorem smoothPrefixLcm_secondLogStep
    {p q r x y : ℕ} (pprime : p.Prime) (qprime : q.Prime) (rprime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hp : Nat.log p y = Nat.log p x)
    (hq : Nat.log q y = Nat.log q x + 1)
    (hr : Nat.log r y = Nat.log r x) :
    smoothPrefixLcm p q r y = q * smoothPrefixLcm p q r x := by
  rw [smoothPrefixLcm_eq_threePrimeHeight pprime qprime rprime hpq hpr hqr hy,
    smoothPrefixLcm_eq_threePrimeHeight pprime qprime rprime hpq hpr hqr hx]
  exact threePrimeHeight_secondLogStep hp hq hr

/-- A third-coordinate jump multiplies the literal running LCM by `r`. -/
theorem smoothPrefixLcm_thirdLogStep
    {p q r x y : ℕ} (pprime : p.Prime) (qprime : q.Prime) (rprime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hp : Nat.log p y = Nat.log p x)
    (hq : Nat.log q y = Nat.log q x)
    (hr : Nat.log r y = Nat.log r x + 1) :
    smoothPrefixLcm p q r y = r * smoothPrefixLcm p q r x := by
  rw [smoothPrefixLcm_eq_threePrimeHeight pprime qprime rprime hpq hpr hqr hy,
    smoothPrefixLcm_eq_threePrimeHeight pprime qprime rprime hpq hpr hqr hx]
  exact threePrimeHeight_thirdLogStep hp hq hr

/-! ## Finite jump grouping -/

/-- A finite rectangular exponent box.  This is the exact finite domain used
before passing to the infinite three-prime smooth series. -/
def smoothExponentBox (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (hp + 1)).product
    ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))

/-- The running-LCM height attached to one smooth exponent triple. -/
def smoothPointHeight (p q r : ℕ) (e : ℕ × ℕ × ℕ) : ℕ :=
  threePrimeHeight p q r (smooth3Val p q r e.1 e.2.1 e.2.2)

/-- The points of a finite exponent box with one fixed running-LCM height. -/
def smoothHeightFiber
    (p q r hp hq hr H : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (smoothExponentBox hp hq hr).filter fun e => smoothPointHeight p q r e = H

/-- On a fixed height fiber, every lattice-kernel summand is the reciprocal of
that common height, so the fiber sum is exactly its multiplicity times that
reciprocal. -/
theorem smoothHeightFiber_kernel_sum
    (p q r hp hq hr H : ℕ) :
    (∑ e ∈ smoothHeightFiber p q r hp hq hr H,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by
  classical
  calc
    (∑ e ∈ smoothHeightFiber p q r hp hq hr H,
        threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
        ∑ _e ∈ smoothHeightFiber p q r hp hq hr H, ((H : ℚ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro e he
      have hheight : smoothPointHeight p q r e = H :=
        (Finset.mem_filter.mp he).2
      simpa [threePrimeKernelQ, smoothPointHeight, hheight]
    _ = (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by
      simp

/-- Exact finite normal form obtained by grouping the smooth lattice kernel by
its genuine running-LCM heights.  The coefficient of each height is the
cardinality of its fiber.  Together with logarithmic-cell constancy, this is
the checked finite core of the prime-power jump expansion. -/
theorem finiteSmoothKernelSum_groupedByHeight
    (p q r hp hq hr : ℕ) :
    (∑ e ∈ smoothExponentBox hp hq hr,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by
  classical
  calc
    (∑ e ∈ smoothExponentBox hp hq hr,
        threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
        ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
          ∑ e ∈ smoothExponentBox hp hq hr with smoothPointHeight p q r e = H,
            threePrimeKernelQ p q r e.1 e.2.1 e.2.2 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun _e he => Finset.mem_image_of_mem (smoothPointHeight p q r) he) _
    _ = ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro H _hH
      exact smoothHeightFiber_kernel_sum p q r hp hq hr H

/-- Each pure-power component of the height is at most `x`, so the three-prime
height is bounded by `x³`. -/
theorem threePrimeHeight_le_cube
    (p q r x : ℕ) (hx : x ≠ 0) :
    threePrimeHeight p q r x ≤ x ^ 3 := by
  have hp := Nat.pow_log_le_self p hx
  have hq := Nat.pow_log_le_self q hx
  have hr := Nat.pow_log_le_self r hx
  calc
    threePrimeHeight p q r x
        ≤ (x * x) * x := Nat.mul_le_mul (Nat.mul_le_mul hp hq) hr
    _ = x ^ 3 := by ring

/-! The first exact `{2,3,5}` kernel values. -/

@[simp] theorem kernel_235_origin :
    threePrimeKernelQ 2 3 5 0 0 0 = 1 := by
  have h2 : Nat.log 2 1 = 0 := Nat.log_of_lt (by norm_num)
  have h3 : Nat.log 3 1 = 0 := Nat.log_of_lt (by norm_num)
  have h5 : Nat.log 5 1 = 0 := Nat.log_of_lt (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

@[simp] theorem kernel_235_two :
    threePrimeKernelQ 2 3 5 1 0 0 = 1 / 2 := by
  have h2 : Nat.log 2 2 = 1 := by
    simpa using Nat.log_pow (b := 2) (by norm_num : 1 < 2) 1
  have h3 : Nat.log 3 2 = 0 := Nat.log_of_lt (by norm_num)
  have h5 : Nat.log 5 2 = 0 := Nat.log_of_lt (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

@[simp] theorem kernel_235_three :
    threePrimeKernelQ 2 3 5 0 1 0 = 1 / 6 := by
  have h2 : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h3 : Nat.log 3 3 = 1 := by
    simpa using Nat.log_pow (b := 3) (by norm_num : 1 < 3) 1
  have h5 : Nat.log 5 3 = 0 := Nat.log_of_lt (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

@[simp] theorem kernel_235_six :
    threePrimeKernelQ 2 3 5 1 1 0 = 1 / 60 := by
  have h2 : Nat.log 2 6 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h3 : Nat.log 3 6 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h5 : Nat.log 5 6 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

/-- The smallest exact witness that the three-prime kernel is not rank one.
The two sides are `1/60` and `1/12`. -/
theorem kernel_235_not_rankOne :
    threePrimeKernelQ 2 3 5 0 0 0 *
        threePrimeKernelQ 2 3 5 1 1 0 ≠
      threePrimeKernelQ 2 3 5 1 0 0 *
        threePrimeKernelQ 2 3 5 0 1 0 := by
  norm_num

/-- One step of the exact variable-base tail orbit from the jump expansion. -/
def tailStateStep (base digit state : ℤ) : ℤ :=
  base * (state - digit)

theorem tailStateStep_eq (base digit state next : ℤ) :
    next = tailStateStep base digit state ↔
      next = base * state - base * digit := by
  simp [tailStateStep, mul_sub]

/-! ## Exact short-shell multiplicity bounds -/

/-- Exponent triples in a half-open multiplicative shell, with explicit
coordinate bounds.  The coordinate bounds are the interface to the pure-power
jump heights; the interval filter is the actual smooth-number shell. -/
def smoothExponentShell
    (p q r lo hi hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (hp + 1)).product
      ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))).filter
    fun e => lo ≤ smooth3Val p q r e.1 e.2.1 e.2.2 ∧
      smooth3Val p q r e.1 e.2.1 e.2.2 < hi

/-- In an interval of multiplicative width at most `base`, fixing the other
factors leaves at most one exponent of `base`. -/
theorem exponent_unique_in_short_interval
    {base lo hi weight a b : ℕ}
    (hbase : 0 < base) (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hpow : base ^ (a + 1) ≤ base ^ b :=
      Nat.pow_le_pow_right hbase (by omega)
    have hcontra : hi < hi := calc
      hi ≤ base * lo := hwidth
      _ ≤ base * (base ^ a * weight) := Nat.mul_le_mul_left base haLo
      _ = base ^ (a + 1) * weight := by
        rw [pow_succ]
        ac_rfl
      _ ≤ base ^ b * weight := Nat.mul_le_mul_right weight hpow
      _ < hi := hbHi
    exact (Nat.lt_irrefl hi hcontra).elim
  · exact hab
  · have hpow : base ^ (b + 1) ≤ base ^ a :=
      Nat.pow_le_pow_right hbase (by omega)
    have hcontra : hi < hi := calc
      hi ≤ base * lo := hwidth
      _ ≤ base * (base ^ b * weight) := Nat.mul_le_mul_left base hbLo
      _ = base ^ (b + 1) * weight := by
        rw [pow_succ]
        ac_rfl
      _ ≤ base ^ a * weight := Nat.mul_le_mul_right weight hpow
      _ < hi := haHi
    exact (Nat.lt_irrefl hi hcontra).elim

/-- Projecting away the first exponent is injective on a shell whose width is
at most the first base.  Consequently the shell has at most the size of the
other two exponent ranges. -/
theorem smoothExponentShell_card_le_dropFirst
    {p q r lo hi hp hq hr : ℕ}
    (hpPos : 0 < p) (hwidth : hi ≤ p * lo) :
    (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (hq + 1) * (hr + 1) := by
  classical
  let target := (Finset.range (hq + 1)).product (Finset.range (hr + 1))
  have hcard :
      (smoothExponentShell p q r lo hi hp hq hr).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn (fun e : ℕ × ℕ × ℕ => e.2) ?_ ?_
    · intro e he
      change e ∈ smoothExponentShell p q r lo hi hp hq hr at he
      change e.2 ∈ target
      rcases e with ⟨a, b, c⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he
      have houter := Finset.mem_product.mp he.1
      have hinner := Finset.mem_product.mp houter.2
      exact Finset.mem_product.mpr
        ⟨hinner.1, hinner.2⟩
    · intro e₁ he₁ e₂ he₂ hproj
      change e₁ ∈ smoothExponentShell p q r lo hi hp hq hr at he₁
      change e₂ ∈ smoothExponentShell p q r lo hi hp hq hr at he₂
      rcases e₁ with ⟨a₁, b₁, c₁⟩
      rcases e₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he₁ he₂
      have ha₁Lo : lo ≤ p ^ a₁ * (q ^ b₁ * r ^ c₁) := by
        simpa [smooth3Val, mul_assoc] using he₁.2.1
      have ha₁Hi : p ^ a₁ * (q ^ b₁ * r ^ c₁) < hi := by
        simpa [smooth3Val, mul_assoc] using he₁.2.2
      have ha₂Lo : lo ≤ p ^ a₂ * (q ^ b₁ * r ^ c₁) := by
        simpa [smooth3Val, mul_assoc] using he₂.2.1
      have ha₂Hi : p ^ a₂ * (q ^ b₁ * r ^ c₁) < hi := by
        simpa [smooth3Val, mul_assoc] using he₂.2.2
      have ha : a₁ = a₂ := exponent_unique_in_short_interval hpPos hwidth
        ha₁Lo ha₁Hi ha₂Lo ha₂Hi
      simp [ha]
  simpa [target] using hcard

/-- The symmetric projection needed when the third height is the largest:
fixing the first two exponents leaves at most one exponent of the third base. -/
theorem smoothExponentShell_card_le_dropThird
    {p q r lo hi hp hq hr : ℕ}
    (hrPos : 0 < r) (hwidth : hi ≤ r * lo) :
    (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (hp + 1) * (hq + 1) := by
  classical
  let target := (Finset.range (hp + 1)).product (Finset.range (hq + 1))
  have hcard :
      (smoothExponentShell p q r lo hi hp hq hr).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn
      (fun e : ℕ × ℕ × ℕ => (e.1, e.2.1)) ?_ ?_
    · intro e he
      change e ∈ smoothExponentShell p q r lo hi hp hq hr at he
      change (e.1, e.2.1) ∈ target
      rcases e with ⟨a, b, c⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he
      have houter := Finset.mem_product.mp he.1
      have hinner := Finset.mem_product.mp houter.2
      exact Finset.mem_product.mpr ⟨houter.1, hinner.1⟩
    · intro e₁ he₁ e₂ he₂ hproj
      change e₁ ∈ smoothExponentShell p q r lo hi hp hq hr at he₁
      change e₂ ∈ smoothExponentShell p q r lo hi hp hq hr at he₂
      rcases e₁ with ⟨a₁, b₁, c₁⟩
      rcases e₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he₁ he₂
      have hc₁Lo : lo ≤ r ^ c₁ * (p ^ a₁ * q ^ b₁) := by
        simpa [smooth3Val, mul_assoc, mul_comm, mul_left_comm] using he₁.2.1
      have hc₁Hi : r ^ c₁ * (p ^ a₁ * q ^ b₁) < hi := by
        simpa [smooth3Val, mul_assoc, mul_comm, mul_left_comm] using he₁.2.2
      have hc₂Lo : lo ≤ r ^ c₂ * (p ^ a₁ * q ^ b₁) := by
        simpa [smooth3Val, mul_assoc, mul_comm, mul_left_comm] using he₂.2.1
      have hc₂Hi : r ^ c₂ * (p ^ a₁ * q ^ b₁) < hi := by
        simpa [smooth3Val, mul_assoc, mul_comm, mul_left_comm] using he₂.2.2
      have hc : c₁ = c₂ := exponent_unique_in_short_interval hrPos hwidth
        hc₁Lo hc₁Hi hc₂Lo hc₂Hi
      simp [hc]
  simpa [target] using hcard

/-- If `a ≤ b ≤ c` and the three heights sum to `j`, then the product of
the two smaller shifted heights satisfies the clean quadratic estimate used
in the scaled-tail analysis.  This is the denominator-free form of
`(a+1)(b+1) ≤ (j+3)²/9`. -/
theorem sorted_pair_quadratic
    {a b c j : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hsum : a + b + c = j) :
    9 * ((a + 1) * (b + 1)) ≤ (j + 3) ^ 2 := by
  have hj : a + 2 * b ≤ j := by omega
  let d := b - a
  have hd : d + a = b := by
    dsimp [d]
    omega
  have hnon : 0 ≤ d * (3 * a + 4 * d + 3) := Nat.zero_le _
  have hlocal :
      9 * ((a + 1) * (b + 1)) ≤ (a + 2 * b + 3) ^ 2 := by
    nlinarith
  exact hlocal.trans (Nat.pow_le_pow_left (Nat.add_le_add_right hj 3) 2)

/-- The exact smooth shell inherits the uniform quadratic multiplicity bound
once its height coordinates are sorted and sum to the jump index. -/
theorem smoothExponentShell_card_quadratic
    {p q r lo hi hp hq hr j : ℕ}
    (hrPos : 0 < r) (hwidth : hi ≤ r * lo)
    (hpq : hp ≤ hq) (hqr : hq ≤ hr)
    (hsum : hp + hq + hr = j) :
    9 * (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (j + 3) ^ 2 := by
  exact (Nat.mul_le_mul_left 9
    (smoothExponentShell_card_le_dropThird hrPos hwidth)).trans
      (sorted_pair_quadratic hpq hqr hsum)

/-! ## Exact dyadic block geometry for `{2,3,5}` -/

/-- A positive `p`-power lies strictly inside the dyadic block
`(2^a, 2^(a+1))`.  Endpoints are excluded because the dyadic jump itself is
the distinguished terminal factor of the compressed block. -/
def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)

/-- A channel contributes at most one internal pure-power jump to a dyadic
block.  This is the exact reason that a compressed `{2,3,5}` block contains
at most the dyadic jump together with one `3`-jump and one `5`-jump. -/
theorem dyadicInternalPower_exponent_unique
    {p a e f : ℕ} (hp : 2 ≤ p)
    (he : DyadicInternalPower p a e)
    (hf : DyadicInternalPower p a f) :
    e = f := by
  have hpPos : 0 < p := by omega
  have hwidth : 2 ^ (a + 1) ≤ p * 2 ^ a := by
    rw [pow_succ]
    simpa [mul_comm] using Nat.mul_le_mul_right (2 ^ a) hp
  apply exponent_unique_in_short_interval
    (base := p) (lo := 2 ^ a) (hi := 2 ^ (a + 1)) (weight := 1)
    hpPos hwidth
  · simpa using Nat.le_of_lt he.1
  · simpa using he.2
  · simpa using Nat.le_of_lt hf.1
  · simpa using hf.2

/-- Across one dyadic block, a logarithm in any base at least two increases
by at most one. -/
theorem log_dyadic_succ_le
    {p a : ℕ} (hp : 2 ≤ p) :
    Nat.log p (2 ^ (a + 1)) ≤ Nat.log p (2 ^ a) + 1 := by
  calc
    Nat.log p (2 ^ (a + 1)) ≤ Nat.log p (2 ^ a * p) := by
      apply Nat.log_mono_right
      rw [pow_succ]
      exact Nat.mul_le_mul_left (2 ^ a) hp
    _ = Nat.log p (2 ^ a) + 1 := by
      exact Nat.log_mul_base (by omega) (by positivity)

/-- For an odd base larger than two, its logarithm advances across a dyadic
block exactly when one base power lies strictly inside that block. -/
theorem exists_dyadicInternalPower_iff_log_succ
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p) :
    (∃ e, DyadicInternalPower p a e) ↔
      Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a) + 1 := by
  have hpOne : 1 < p := by omega
  constructor
  · rintro ⟨e, heLower, heUpper⟩
    have hLower : Nat.log p (2 ^ a) < e :=
      (Nat.log_lt_iff_lt_pow hpOne (by positivity)).2 heLower
    have hUpper : e ≤ Nat.log p (2 ^ (a + 1)) :=
      Nat.le_log_of_pow_le hpOne heUpper.le
    have hStep := log_dyadic_succ_le (a := a) (Nat.le_of_lt hp)
    omega
  · intro hStep
    let e := Nat.log p (2 ^ (a + 1))
    refine ⟨e, ?_, ?_⟩
    · dsimp [e]
      simpa only [Nat.succ_eq_add_one, hStep] using
        Nat.lt_pow_succ_log_self hpOne (2 ^ a)
    · dsimp [e]
      have hLe :
          p ^ Nat.log p (2 ^ (a + 1)) ≤ 2 ^ (a + 1) :=
        Nat.pow_log_le_self p (by positivity)
      have hOdd : Odd (p ^ Nat.log p (2 ^ (a + 1))) := hpOdd.pow
      have hEven : Even (2 ^ (a + 1)) :=
        even_two.pow_of_ne_zero (by omega)
      have hNe : p ^ Nat.log p (2 ^ (a + 1)) ≠ 2 ^ (a + 1) := by
        intro hEq
        exact (Nat.not_even_iff_odd.mpr hOdd) (by simpa [hEq] using hEven)
      exact lt_of_le_of_ne hLe hNe

/-- If no odd-base power occurs inside a dyadic block, the corresponding
logarithmic coordinate stays fixed. -/
theorem log_dyadic_succ_eq_of_no_internalPower
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p)
    (hNo : ¬ ∃ e, DyadicInternalPower p a e) :
    Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a) := by
  have hMono : Nat.log p (2 ^ a) ≤ Nat.log p (2 ^ (a + 1)) := by
    apply Nat.log_mono_right
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ a)
  have hStep := log_dyadic_succ_le (a := a) (by omega : 2 ≤ p)
  have hNotSucc :
      Nat.log p (2 ^ (a + 1)) ≠ Nat.log p (2 ^ a) + 1 := by
    intro hEq
    exact hNo ((exists_dyadicInternalPower_iff_log_succ hp hpOdd).2 hEq)
  omega

/-- The exact radix of the dyadic block after compressing all internal
`3`- and `5`-power jumps.  Each internal channel contributes its prime once,
and the terminal dyadic jump contributes the factor `2`. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)

/-- Every actual compressed dyadic radix is one of `2, 6, 10, 30`.
This replaces the generic interval `[2,30]` by the exact four-symbol alphabet
consumed by the integer certificate engine. -/
theorem dyadicBlockBase235_cases (a : ℕ) :
    dyadicBlockBase235 a = 2 ∨
      dyadicBlockBase235 a = 6 ∨
      dyadicBlockBase235 a = 10 ∨
      dyadicBlockBase235 a = 30 := by
  classical
  by_cases h3 : ∃ e, DyadicInternalPower 3 a e <;>
    by_cases h5 : ∃ e, DyadicInternalPower 5 a e <;>
      simp [dyadicBlockBase235, h3, h5]

/-- In particular, the actual dyadic block radix satisfies the hypotheses of
the checked bounded-radix escape theorem, with no hidden larger base. -/
theorem dyadicBlockBase235_mem_interval (a : ℕ) :
    2 ≤ dyadicBlockBase235 a ∧ dyadicBlockBase235 a ≤ 30 := by
  rcases dyadicBlockBase235_cases a with h | h | h | h <;>
    simp [h]

/-- The synthetic four-symbol radix is the exact successive-height ratio on
the actual dyadic `{2,3,5}` orbit. -/
theorem threePrimeHeight_dyadicBlock_succ (a : ℕ) :
    threePrimeHeight 2 3 5 (2 ^ (a + 1)) =
      dyadicBlockBase235 a * threePrimeHeight 2 3 5 (2 ^ a) := by
  classical
  have h2 : Nat.log 2 (2 ^ (a + 1)) = Nat.log 2 (2 ^ a) + 1 := by
    simp
  by_cases h3 : ∃ e, DyadicInternalPower 3 a e
  · have h3Log :=
      (exists_dyadicInternalPower_iff_log_succ
        (p := 3) (a := a) (by norm_num) (by exact ⟨1, by norm_num⟩)).1 h3
    by_cases h5 : ∃ e, DyadicInternalPower 5 a e
    · have h5Log :=
        (exists_dyadicInternalPower_iff_log_succ
          (p := 5) (a := a) (by norm_num) (by exact ⟨2, by norm_num⟩)).1 h5
      simp only [threePrimeHeight]
      rw [h2, h3Log, h5Log]
      simp [dyadicBlockBase235, h3, h5]
      ring
    · have h5Log := log_dyadic_succ_eq_of_no_internalPower
        (p := 5) (a := a) (by norm_num) (by exact ⟨2, by norm_num⟩) h5
      simp only [threePrimeHeight]
      rw [h2, h3Log, h5Log]
      simp [dyadicBlockBase235, h3, h5]
      ring
  · have h3Log := log_dyadic_succ_eq_of_no_internalPower
      (p := 3) (a := a) (by norm_num) (by exact ⟨1, by norm_num⟩) h3
    by_cases h5 : ∃ e, DyadicInternalPower 5 a e
    · have h5Log :=
        (exists_dyadicInternalPower_iff_log_succ
          (p := 5) (a := a) (by norm_num) (by exact ⟨2, by norm_num⟩)).1 h5
      simp only [threePrimeHeight]
      rw [h2, h3Log, h5Log]
      simp [dyadicBlockBase235, h3, h5]
      ring
    · have h5Log := log_dyadic_succ_eq_of_no_internalPower
        (p := 5) (a := a) (by norm_num) (by exact ⟨2, by norm_num⟩) h5
      simp only [threePrimeHeight]
      rw [h2, h3Log, h5Log]
      simp [dyadicBlockBase235, h3, h5]
      ring

/-! ## Exact rank-two certificate -/

/-- The determinant of the smallest `{2,3,5}` kernel rectangle is exactly
`-1/15`.  In particular, the corresponding `2 × 2` matrix has rank two over
the rationals; this is stronger than merely recording that it is not rank one. -/
theorem kernel_235_minor_eq_neg_one_fifteen :
    threePrimeKernelQ 2 3 5 0 0 0 *
          threePrimeKernelQ 2 3 5 1 1 0 -
        threePrimeKernelQ 2 3 5 1 0 0 *
          threePrimeKernelQ 2 3 5 0 1 0 =
      -(1 / 15 : ℚ) := by
  norm_num

end ErdosProblems.Erdos269
