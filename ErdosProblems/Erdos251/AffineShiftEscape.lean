import ErdosProblems.Erdos251.PrimeGapDyadicTail

/-!
# Erdős #251: the ±2 wall, and the affine 2-adic escape that removes it

`PrimeGapDyadicTail` ends at `not_eventuallyIntegralTailShift_of_cofinal_small_mismatch`:
to rule out eventual integrality of a fixed shift it asks for cofinally many
**adjacent pairs** of shifts of modulus `< 1` whose digits differ.  That
producer is far more rigid than its wording suggests.

## The ±2 wall

From `tailShift_succ` the digit is `δ = 2·T_h(N) - T_h(N+1)`.  Two unit
windows force `|δ| < 3`, and for actual prime gaps every digit is even, so a
nonzero digit under the requested hypotheses is **exactly `±2`**
(`digit_eq_two_or_neg_two_of_small_pair`), with the sign pinned to a half-unit
window (`shift_gt_half_of_digit_eq_two` and
`shift_lt_neg_half_of_digit_eq_neg_two`).  For `h = 1` the requested supply is
therefore: cofinally many adjacent prime gaps differing by exactly `2`.  Sign
changes alone — the standard input — do not deliver a prescribed magnitude.

## The replacement

Every step of the recurrence buys one exact 2-adic bit instead.  If the shift
is integral then one further step makes it *even* (`evenIntegral_succ`), and
`r` further steps confine it to a single affine class modulo `2^{r+1}`
determined by the observed digit block:

`T_h(N+r) ∈ -B_{h,N,r} + 2^{r+1}·ℤ`   (`affinePowTwo_of_evenIntegral`).

Escaping *that* lattice cofinally already rules out eventual integrality
(`not_eventuallyIntegralTailShift_of_cofinal_affinePowTwo_escape`).  This is a
strictly weaker demand than the adjacent-small-pair certificate:

* only **one** complete tail shift is tested, not two adjacent ones;
* no archimedean unit window is required;
* the finite block `B_{h,N,r}` determines an exponentially sparse target;
* `r` may be chosen to suit the arithmetic block.

The original certificate is the `r = 1` corner (`affinePowTwo_one`).

## Claim ceiling

**Erdős #251 remains open.**  Nothing here supplies a cofinal producer.  What
is settled is that the previously requested producer parity-collapses to an
exact `±2` gap-difference event, and that it can be replaced by a one-tail
affine anti-concentration hierarchy.
-/

namespace ErdosProblems.Erdos251

/-! ## The parity collapse -/

/-- **The ±2 wall.**  Under exactly the hypotheses of the existing
adjacent-small-mismatch consumer, an even nonzero digit is forced to be `±2`.
The requested producer is therefore a prescribed-magnitude gap event, not a
mere inequality of digits. -/
theorem digit_eq_two_or_neg_two_of_small_pair {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k)
    (hlow : -1 < tailShift T h N) (hhigh : tailShift T h N < 1)
    (hlow' : -1 < tailShift T h (N + 1)) (hhigh' : tailShift T h (N + 1) < 1)
    (hne : g (N + h + 1) ≠ g (N + 1)) :
    g (N + h + 1) - g (N + 1) = 2 ∨ g (N + h + 1) - g (N + 1) = -2 := by
  obtain ⟨k, hk⟩ := heven
  have hstep := tailShift_succ hrec h N
  have hdelta : ((g (N + h + 1) - g (N + 1) : ℤ) : ℚ)
      = 2 * tailShift T h N - tailShift T h (N + 1) := by
    push_cast
    linarith [hstep]
  have habs : ((g (N + h + 1) - g (N + 1) : ℤ) : ℚ) < 3 ∧
      (-3 : ℚ) < ((g (N + h + 1) - g (N + 1) : ℤ) : ℚ) := by
    constructor <;> · rw [hdelta]; linarith
  have hq : (g (N + h + 1) - g (N + 1) : ℤ) < 3 ∧ (-3 : ℤ) < g (N + h + 1) - g (N + 1) := by
    constructor
    · exact_mod_cast habs.1
    · exact_mod_cast habs.2
  have hnz : g (N + h + 1) - g (N + 1) ≠ 0 := sub_ne_zero.mpr hne
  omega

/-- **Sign alignment.**  A `+2` digit pins the shift into the *upper half* of
its window: the digit magnitude and the shift sign are not independent. -/
theorem shift_gt_half_of_digit_eq_two {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (hdigit : g (N + h + 1) - g (N + 1) = 2)
    (hlow' : -1 < tailShift T h (N + 1)) :
    1 / 2 < tailShift T h N := by
  have hstep := tailShift_succ hrec h N
  have hd : ((g (N + h + 1) : ℤ) : ℚ) - ((g (N + 1) : ℤ) : ℚ) = 2 := by
    have hcast : ((g (N + h + 1) - g (N + 1) : ℤ) : ℚ) = ((2 : ℤ) : ℚ) := by rw [hdigit]
    push_cast at hcast
    linarith
  linarith [hstep, hd]

/-- The mirror statement for a `-2` digit. -/
theorem shift_lt_neg_half_of_digit_eq_neg_two {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (hdigit : g (N + h + 1) - g (N + 1) = -2)
    (hhigh' : tailShift T h (N + 1) < 1) :
    tailShift T h N < -(1 / 2) := by
  have hstep := tailShift_succ hrec h N
  have hd : ((g (N + h + 1) : ℤ) : ℚ) - ((g (N + 1) : ℤ) : ℚ) = -2 := by
    have hcast : ((g (N + h + 1) - g (N + 1) : ℤ) : ℚ) = ((-2 : ℤ) : ℚ) := by rw [hdigit]
    push_cast at hcast
    linarith
  linarith [hstep, hd]

/-- **Signed-window normal form.**  Under the hypotheses of the adjacent-small-
mismatch producer, its two unit-window conditions are equivalent to the exact
`±2` digit event with the corresponding half-window condition.  This packages
the reduction used by the computational and analytic consumers without
claiming that the event is cofinal for the actual primes. -/
theorem adjacent_small_mismatch_iff_signed_two_window {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < tailShift T h N ∧ tailShift T h N < 1 ∧
        -1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1 ∧
        g (N + h + 1) ≠ g (N + 1)) ↔
      ((g (N + h + 1) - g (N + 1) = 2 ∧
          1 / 2 < tailShift T h N ∧ tailShift T h N < 1) ∨
        (g (N + h + 1) - g (N + 1) = -2 ∧
          -1 < tailShift T h N ∧ tailShift T h N < -(1 / 2))) := by
  constructor
  · rintro ⟨hlow, hhigh, hlow', hhigh', hne⟩
    rcases digit_eq_two_or_neg_two_of_small_pair hrec h N heven
        hlow hhigh hlow' hhigh' hne with htwo | hneg
    · exact Or.inl ⟨htwo, shift_gt_half_of_digit_eq_two hrec h N htwo hlow', hhigh⟩
    · exact Or.inr ⟨hneg, hlow, shift_lt_neg_half_of_digit_eq_neg_two hrec h N hneg hhigh'⟩
  · rintro (⟨htwo, hhalf, hhigh⟩ | ⟨hneg, hlow, hhalf⟩)
    · have hstep := tailShift_succ hrec h N
      have htwoQ :
          ((g (N + h + 1) : ℚ) - (g (N + 1) : ℚ)) = 2 := by
        exact_mod_cast htwo
      have hne : g (N + h + 1) ≠ g (N + 1) := by
        intro heq
        rw [heq] at htwo
        omega
      refine ⟨by linarith, hhigh, ?_, ?_, hne⟩
      · linarith [hstep, htwoQ]
      · linarith [hstep, htwoQ]
    · have hstep := tailShift_succ hrec h N
      have hnegQ :
          ((g (N + h + 1) : ℚ) - (g (N + 1) : ℚ)) = -2 := by
        exact_mod_cast hneg
      have hne : g (N + h + 1) ≠ g (N + 1) := by
        intro heq
        rw [heq] at hneg
        omega
      refine ⟨hlow, by linarith, ?_, ?_, hne⟩
      · linarith [hstep, hnegQ]
      · linarith [hstep, hnegQ]

/-! ## The affine 2-adic ladder -/

/-- A rational that is the cast of an even integer. -/
def RatEvenIntegral (x : ℚ) : Prop := ∃ k : ℤ, x = ((2 * k : ℤ) : ℚ)

/-- `x` lies in the affine class `-c` modulo `2^(r+1)`. -/
def RatAffinePowTwo (x : ℚ) (c : ℤ) (r : ℕ) : Prop :=
  ∃ z : ℤ, x = ((((2 : ℤ) ^ (r + 1)) * z - c : ℤ) : ℚ)

/-- The digit sequence governing the fixed `h`-shift cocycle. -/
def shiftDigit (g : ℕ → ℤ) (h n : ℕ) : ℤ := g (n + h) - g n

/-- A fixed tail shift is itself a dyadic recurrence, with difference digits. -/
theorem tailShift_recurrence {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ) :
    DyadicTailRecurrence (shiftDigit g h) (tailShift T h) := by
  intro N
  have := tailShift_succ hrec h N
  simpa [shiftDigit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- **One step lifts integrality to evenness.**  Because every digit difference
is even, an integral shift becomes an *even* integral shift after one step. -/
theorem evenIntegral_succ {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (hInt : RatIntegral (tailShift T h N))
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    RatEvenIntegral (tailShift T h (N + 1)) := by
  obtain ⟨z, hz⟩ := hInt
  obtain ⟨k, hk⟩ := heven
  refine ⟨z - k, ?_⟩
  have hstep := tailShift_succ hrec h N
  have hd : ((g (N + h + 1) : ℤ) : ℚ) - ((g (N + 1) : ℤ) : ℚ) = ((2 * k : ℤ) : ℚ) := by
    have : ((g (N + h + 1) - g (N + 1) : ℤ) : ℚ) = ((2 * k : ℤ) : ℚ) := by rw [hk]
    push_cast at this ⊢
    linarith
  rw [hstep, hz]
  push_cast
  push_cast at hd
  linarith

/-- **The affine ladder.**  Each additional step fixes one further binary digit:
an even-integral shift lands, `r` steps later, in one affine class modulo
`2^(r+1)` determined by the observed finite digit block. -/
theorem affinePowTwo_of_evenIntegral {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N r : ℕ)
    (hEven : RatEvenIntegral (tailShift T h N)) :
    RatAffinePowTwo (tailShift T h (N + r)) (dyadicTailBlock (shiftDigit g h) N r) r := by
  obtain ⟨z, hz⟩ := hEven
  refine ⟨z, ?_⟩
  rw [tail_iterate_eq_pow_mul_sub_block (tailShift_recurrence hrec h) N r, hz]
  push_cast
  rw [pow_succ]
  ring

/-- The original small-pair certificate is the `r = 1` corner of the ladder. -/
theorem affinePowTwo_one {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (hEven : RatEvenIntegral (tailShift T h N)) :
    RatAffinePowTwo (tailShift T h (N + 1)) (g (N + 1 + h) - g (N + 1)) 1 := by
  have := affinePowTwo_of_evenIntegral hrec h N 1 hEven
  simpa [dyadicTailBlock, shiftDigit] using this

/-- **The replacement producer.**  Cofinal escape from the data-dependent affine
cylinders rules out eventual integrality of the fixed shift.  Only one tail is
tested at each witness, and no unit window is required. -/
theorem not_eventuallyIntegralTailShift_of_cofinal_affinePowTwo_escape
    {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hdiffEven : ∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k)
    (hsupply : ∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
      ¬ RatAffinePowTwo (tailShift T h (N + r))
        (dyadicTailBlock (shiftDigit g h) N r) r) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  rintro ⟨N₀, hInt⟩
  obtain ⟨N, r, hN, hescape⟩ := hsupply N₀
  obtain ⟨M, hM⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
  have hEvenN : RatEvenIntegral (tailShift T h N) := by
    rw [hM]
    exact evenIntegral_succ hrec h M (hInt M (by omega)) (hdiffEven M)
  exact hescape (affinePowTwo_of_evenIntegral hrec h N r hEvenN)

end ErdosProblems.Erdos251
