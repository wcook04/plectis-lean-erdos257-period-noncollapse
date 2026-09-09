import ErdosProblems.Erdos251.PrimeGapDyadicTail
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Erdős #251: the integral shifts form an order lattice, and one schedule decides

Two structural refinements of the dyadic tail criterion.

**The invariant is the multiplicative order, not a totient.**
`tailShift_integral_iff_orderOf_dvd` : at any basepoint `N`,

`tailShift T h N ∈ ℤ  ↔  orderOf (2 : ZMod (T N).den) ∣ h`.

So the integral shift lengths form a single principal lattice.  Euler's
totient is only a (possibly very non-minimal) witness.  When the denominator
is even the order is `0`, and the statement correctly says that *no positive*
shift is integral.

**One predetermined schedule decides irrationality.**
`irrational_initial_iff_nonintegral_on_schedule` : any schedule `s` that
tends to infinity, is eventually divisible by every positive integer, and is
positive, already decides the problem on the *diagonal* pairs
`(N, h) = (s j, s j)`.  The corpus criterion quantifies over all shift
lengths and all basepoints; this replaces both quantifiers by one
predetermined sequence.  The factorial schedule is the corollary
`irrational_initial_iff_all_factorialDiagonal_nonintegral`; `lcm (1..j)` works
identically and is much smaller.

Erdős #251 remains open: producing the cofinal misses is still the missing
prime-theoretic input.
-/

namespace ErdosProblems.Erdos251

/-! ## The order lattice -/

/-- **The integral shift lengths are exactly the multiples of the order of
`2` modulo the current reduced denominator.** -/
theorem tailShift_integral_iff_orderOf_dvd {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔ orderOf (2 : ZMod (T N).den) ∣ h := by
  rw [tailShift_integral_iff_two_pow_modEq_one hrec, orderOf_dvd_iff_pow_eq_one,
    ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rfl

/-! ## Shift cocycle and multiple closure -/

theorem realIntegral_add {x y : ℝ} (hx : RealIntegral x) (hy : RealIntegral y) :
    RealIntegral (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; ring⟩

/-- Shifts compose as a cocycle over the basepoint. -/
theorem realTailShift_add (T : ℕ → ℝ) (h k N : ℕ) :
    realTailShift T (h + k) N = realTailShift T h N + realTailShift T k (N + h) := by
  unfold realTailShift
  rw [show N + (h + k) = N + h + k by omega]
  ring

/-- If one fixed shift length is integral at every basepoint beyond `N`, so
is every positive multiple of it. -/
theorem realTailShift_mul_integral_of_eventually (T : ℕ → ℝ) {h N : ℕ}
    (hInt : ∀ k : ℕ, RealIntegral (realTailShift T h (N + k))) :
    ∀ m k : ℕ, RealIntegral (realTailShift T (m * h) (N + k)) := by
  intro m
  induction m with
  | zero =>
      intro k
      exact ⟨0, by simp [realTailShift]⟩
  | succ m ih =>
      intro k
      rw [show (m + 1) * h = m * h + h by ring, realTailShift_add]
      refine realIntegral_add (ih k) ?_
      rw [show N + k + m * h = N + (k + m * h) by omega]
      exact hInt (k + m * h)

/-! ## One schedule decides -/

/-- The least common multiple of the positive integers seen so far. -/
def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)

theorem lcmDiagonalSchedule_pos (j : ℕ) : 0 < lcmDiagonalSchedule j := by
  induction j with
  | zero => simp [lcmDiagonalSchedule]
  | succ j ih =>
      simpa [lcmDiagonalSchedule] using Nat.lcm_pos ih (Nat.succ_pos j)

theorem lcmDiagonalSchedule_dvd_of_le {h j : ℕ}
    (hh : 0 < h) (hle : h ≤ j) : h ∣ lcmDiagonalSchedule j := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases h_eq : h = j + 1
      · subst h
        simpa [lcmDiagonalSchedule] using
          (Nat.dvd_lcm_right (lcmDiagonalSchedule j) (j + 1))
      · have hle' : h ≤ j := by omega
        exact dvd_trans (ih hle') (by
          simpa [lcmDiagonalSchedule] using
            (Nat.dvd_lcm_left (lcmDiagonalSchedule j) (j + 1)))

/-- **Schedule criterion.**  Any positive schedule that tends to infinity and
is eventually divisible by every positive integer decides irrationality on
its own diagonal. -/
theorem irrational_initial_iff_nonintegral_on_schedule {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (s : ℕ → ℕ)
    (hpos : ∀ j, 0 < s j)
    (hdvd : ∀ h : ℕ, 0 < h → ∃ J : ℕ, ∀ j : ℕ, J ≤ j → h ∣ s j)
    (hgrow : ∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → N ≤ s j) :
    Irrational (T 0) ↔ ∀ j : ℕ, ¬ RealIntegral (realTailShift T (s j) (s j)) := by
  constructor
  · intro hirr j
    exact (irrational_initial_iff_all_positive_tailShifts_nonintegral hrec).1 hirr
      (s j) (hpos j) (s j)
  · intro hmiss
    by_contra hrat
    obtain ⟨h, N, hh, hInt⟩ :=
      (not_irrational_initial_iff_exists_eventually_integral_positive_tailShift hrec).1 hrat
    obtain ⟨J₁, hJ₁⟩ := hdvd h hh
    obtain ⟨J₂, hJ₂⟩ := hgrow N
    set j : ℕ := max J₁ J₂ with hj
    obtain ⟨m, hm⟩ := hJ₁ j (le_max_left J₁ J₂)
    have hNle : N ≤ s j := hJ₂ j (le_max_right J₁ J₂)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hNle
    have hmul := realTailShift_mul_integral_of_eventually T hInt m k
    have hmh : m * h = s j := by rw [hm]; ring
    rw [hmh, ← hk] at hmul
    exact hmiss j hmul

/-- **The factorial diagonal decides Erdős #251's dyadic criterion.**  A
single predetermined sequence of pairs `(N, h) = (j!, j!)` replaces the
double quantifier over all shift lengths and all basepoints. -/
theorem irrational_initial_iff_all_factorialDiagonal_nonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ, ¬ RealIntegral (realTailShift T j.factorial j.factorial) := by
  apply irrational_initial_iff_nonintegral_on_schedule hrec (fun j => j.factorial)
  · intro j; exact Nat.factorial_pos j
  · intro h hh
    exact ⟨h, fun j hj => Nat.dvd_factorial hh hj⟩
  · intro N
    exact ⟨N, fun j hj => le_trans hj (Nat.self_le_factorial j)⟩

/-- **The lcm diagonal is a smaller deciding schedule.**  The schedule
`lcmDiagonalSchedule j = lcm(1, ..., j)` has the same cofinal divisibility
and growth properties as the factorial schedule, while remaining pointwise
no larger. -/
theorem irrational_initial_iff_all_lcmDiagonal_nonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) := by
  apply irrational_initial_iff_nonintegral_on_schedule hrec lcmDiagonalSchedule
  · exact lcmDiagonalSchedule_pos
  · intro h hh
    refine ⟨h, ?_⟩
    intro j hj
    exact lcmDiagonalSchedule_dvd_of_le hh hj
  · intro N
    by_cases hN : N = 0
    · exact ⟨0, by simp [hN]⟩
    · refine ⟨N, ?_⟩
      intro j hj
      exact Nat.le_of_dvd (lcmDiagonalSchedule_pos j)
        (lcmDiagonalSchedule_dvd_of_le (by omega) hj)

/-- Rationality is likewise decided by a single integral point of the
factorial diagonal. -/
theorem not_irrational_initial_iff_exists_integral_factorialDiagonal {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ j : ℕ, RealIntegral (realTailShift T j.factorial j.factorial) := by
  rw [irrational_initial_iff_all_factorialDiagonal_nonintegral hrec]
  push_neg
  rfl

end ErdosProblems.Erdos251
