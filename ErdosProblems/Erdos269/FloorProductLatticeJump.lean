import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Erdős #269 companion: lattice jumps, adjacent exchange, floor-product witness

Ordinary Type B r4 (file 05) proposed a shrinking-jump irrationality argument
for floor-product series and a complete rational-linear classification of the
`{2,3,5}` prime-power channels.  This module formalises only the local
algebraic and lattice core:

* tails on `D⁻¹ℤ` cannot realise a nonzero shrinking jump;
* the adjacent-channel swap identity used in the three-channel argument;
* the three-prime reversal contribution and the four-prime cancellation
  witness;
* the complementary-floor identity and the exact `b₁=b₂=2`, `α₂=1-α`
  cancellation (`∑ 1/A_n = 3`);
* the one-slope jump `(1-b)/(b A)` as a compiling special case of the
  floor-product jump.

The r3 coordinate-fibre leftover is not restated here: lattice-finiteness
without radix intervals is already `eq_of_memInvInt_of_abs_lt`.  Nothing
here proves irrationality of the repeated three-prime running-LCM series.
The parent residual remains nonintegrality of `B X_a`.  The torus
orbit-closure half of R1/R3 is not formalised.
-/

namespace ErdosProblems.Erdos269

/-! ### Lattice of denominator-`D` rationals -/

/-- Membership in the lattice `D⁻¹ℤ`. -/
def MemInvInt (D : ℕ) (z : ℝ) : Prop :=
  ∃ a : ℤ, z = (a : ℝ) / (D : ℝ)

theorem memInvInt_zero (D : ℕ) : MemInvInt D 0 :=
  ⟨0, by simp⟩

/-- Distinct lattice points are at least `1/D` apart. -/
theorem abs_sub_ge_inv_of_memInvInt
    {D : ℕ} (hD : 0 < D) {z w : ℝ}
    (hz : MemInvInt D z) (hw : MemInvInt D w) (hne : z ≠ w) :
    (1 : ℝ) / D ≤ |z - w| := by
  obtain ⟨a, ha⟩ := hz
  obtain ⟨b, hb⟩ := hw
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hab : a ≠ b := by
    intro h
    exact hne (by rw [ha, hb, h])
  have hge : (1 : ℝ) ≤ |(a - b : ℝ)| := by
    have : (1 : ℤ) ≤ |a - b| := Int.one_le_abs (sub_ne_zero.mpr hab)
    exact_mod_cast this
  have hdiff : z - w = (a - b : ℝ) / D := by
    rw [ha, hb, div_sub_div_same]
  have hDabs : |(D : ℝ)| = D := abs_of_nonneg (Nat.cast_nonneg D)
  rw [hdiff, abs_div, hDabs]
  exact (div_le_div_iff_of_pos_right hDpos).mpr hge

/-- Lattice points closer than `1/D` coincide. -/
theorem eq_of_memInvInt_of_abs_lt
    {D : ℕ} (hD : 0 < D) {z w : ℝ}
    (hz : MemInvInt D z) (hw : MemInvInt D w)
    (hlt : |z - w| < 1 / D) : z = w := by
  by_contra hne
  exact (not_le_of_gt hlt) (abs_sub_ge_inv_of_memInvInt hD hz hw hne)

/-- **Lattice-jump lemma.**  A sequence of nonzero `D⁻¹ℤ` gaps cannot
become smaller than `1/D`. -/
theorem shrinking_jumps_contradict_memInvInt
    {D : ℕ} (hD : 0 < D) {δ : ℕ → ℝ}
    (hδ : ∀ n, MemInvInt D (δ n))
    (hne : ∀ n, δ n ≠ 0)
    (hsmall : ∃ N, ∀ n, N ≤ n → |δ n| < 1 / D) :
    False := by
  obtain ⟨N, hN⟩ := hsmall
  have hge := abs_sub_ge_inv_of_memInvInt hD (hδ N) (memInvInt_zero D) (hne N)
  have hge' : (1 : ℝ) / D ≤ |δ N| := by simpa using hge
  exact (not_le_of_gt (hN N le_rfl)) hge'

/-- Small pairwise lattice gaps force an eventually constant tail. -/
theorem eventually_const_of_small_lattice_gaps
    {D : ℕ} (hD : 0 < D) {z : ℕ → ℝ}
    (hz : ∀ n, MemInvInt D (z n))
    {N : ℕ}
    (hsmall : ∀ n m, N ≤ n → N ≤ m → |z n - z m| < 1 / D) :
    ∃ c, MemInvInt D c ∧ ∀ n, N ≤ n → z n = c := by
  refine ⟨z N, hz N, ?_⟩
  intro n hn
  exact eq_of_memInvInt_of_abs_lt hD (hz n) (hz N) (hsmall n N hn le_rfl)

/-! ### One-slope floor-product jump -/

/-- One-slope jump `(3.3)` in a single coordinate: the two sides of a floor
boundary differ by `(1-b)/(b A)`. -/
noncomputable def oneSlopeJump (b A : ℕ) : ℝ :=
  ((1 : ℝ) - b) / (b * A)

theorem oneSlopeJump_ne_zero {b A : ℕ} (hb : 2 ≤ b) (hA : 1 ≤ A) :
    oneSlopeJump b A ≠ 0 := by
  unfold oneSlopeJump
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hnum : (1 : ℝ) - b ≠ 0 := by linarith
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hb2
  have hApos : (0 : ℝ) < A := by exact_mod_cast (Nat.succ_le_iff.mp hA)
  exact div_ne_zero hnum (mul_ne_zero hbpos.ne' hApos.ne')

theorem abs_oneSlopeJump {b A : ℕ} (hb : 2 ≤ b) (hA : 1 ≤ A) :
    |oneSlopeJump b A| = ((b : ℝ) - 1) / (b * A) := by
  unfold oneSlopeJump
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hApos : (0 : ℝ) < A := by exact_mod_cast (Nat.succ_le_iff.mp hA)
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hb2
  rw [abs_div, abs_mul, abs_of_pos hbpos, abs_of_pos hApos, abs_sub_comm,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - 1)]

/-- **One-slope special case.**  If two `D⁻¹ℤ` tails differ by the one-slope
floor jump and `A` is larger than `D(b-1)/b`, the lattice gap is violated. -/
theorem not_both_memInvInt_of_oneSlopeJump
    {D b A : ℕ} (hD : 0 < D) (hb : 2 ≤ b) (hA : 1 ≤ A)
    (hbig : D * (b - 1) < b * A)
    {z w : ℝ} (hz : MemInvInt D z) (hw : MemInvInt D w)
    (hdiff : z - w = oneSlopeJump b A) :
    False := by
  have hne : z ≠ w := by
    intro h
    apply oneSlopeJump_ne_zero hb hA
    rw [← hdiff, h, sub_self]
  have hge := abs_sub_ge_inv_of_memInvInt hD hz hw hne
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hb2
  have hApos : (0 : ℝ) < A := by exact_mod_cast (Nat.succ_le_iff.mp hA)
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hb1 : 1 ≤ b := le_trans (by norm_num : 1 ≤ 2) hb
  have hlt : |z - w| < 1 / D := by
    rw [hdiff, abs_oneSlopeJump hb hA]
    have hcast : (D : ℝ) * ((b : ℝ) - 1) < (b : ℝ) * A := by
      have hnat : ((D * (b - 1) : ℕ) : ℝ) < ((b * A : ℕ) : ℝ) := by
        exact_mod_cast hbig
      have hsub : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
        rw [Nat.cast_sub hb1, Nat.cast_one]
      calc
        (D : ℝ) * ((b : ℝ) - 1)
            = (D : ℝ) * ((b - 1 : ℕ) : ℝ) := by rw [hsub]
        _ = ((D * (b - 1) : ℕ) : ℝ) := by rw [Nat.cast_mul]
        _ < ((b * A : ℕ) : ℝ) := hnat
        _ = (b : ℝ) * A := by rw [Nat.cast_mul]
    rw [div_lt_div_iff₀ (mul_pos hbpos hApos) hDpos]
    simpa [mul_comm, one_mul] using hcast
  exact (not_le_of_gt hlt) hge

/-! ### Adjacent-channel exchange and three-prime reversal -/

/-- Weighted adjacent swap: exchanging the order of primes `p` then `q`
changes the unit-weight (or signed-weight) contribution by
`(c_p(q-1) - c_q(p-1))/(p q)`. -/
theorem adjacent_channel_exchange (p q cp cq : ℚ)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    cp / p + cq / (p * q) - (cq / q + cp / (p * q))
      = (cp * (q - 1) - cq * (p - 1)) / (p * q) := by
  field_simp
  ring

/-- Three-stream reversal identity `(6.1)`. -/
theorem triple_reversal_identity (a b c : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (1 / a + 1 / (a * b) + 1 / (a * b * c))
      - (1 / c + 1 / (c * b) + 1 / (c * b * a))
      = (c - a) * (b + 1) / (a * b * c) := by
  field_simp
  ring

/-- Witness W2: a four-prime reversal need not change the unit-weight sum. -/
theorem four_prime_reversal_cancellation :
    (1 / 43 + 1 / (43 * 5) + 1 / (43 * 5 * 7)
      + 1 / (43 * 5 * 7 * 41) : ℚ)
      =
    (1 / 41 + 1 / (41 * 7) + 1 / (41 * 7 * 5)
      + 1 / (41 * 7 * 5 * 43) : ℚ) := by
  norm_num

/-! ### Complementary-floor cancellation (W1) -/

theorem floor_neg_of_not_int {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    Int.floor (-x) = -Int.floor x - 1 := by
  have hx' : x ∉ Set.range Int.cast := by
    rintro ⟨n, hn⟩
    exact hx n hn.symm
  have hceil : Int.ceil x = Int.floor x + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem x).mpr hx'
  rw [Int.floor_neg, hceil]
  ring

/-- For `0 < α < 1` and `n ≥ 1` with `nα` non-integral,
`⌊nα⌋ + ⌊n(1-α)⌋ = n-1`. -/
theorem complementary_floor {α : ℝ} {n : ℕ}
    (_hα0 : 0 < α) (_hα1 : α < 1) (_hn : 1 ≤ n)
    (hni : ∀ k : ℤ, (n : ℝ) * α ≠ k) :
    Int.floor ((n : ℝ) * α) + Int.floor ((n : ℝ) * (1 - α))
      = (n : ℤ) - 1 := by
  have hrew : (n : ℝ) * (1 - α) = -((n : ℝ) * α) + (n : ℤ) := by
    push_cast
    ring
  rw [hrew, Int.floor_add_intCast, floor_neg_of_not_int hni]
  ring

/-- Termwise W1: complementary slopes with a shared base `2` give
`A_n = 2^{n-1}`. -/
theorem complementary_floor_product_pow {α : ℝ} {n : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1) (hn : 1 ≤ n)
    (hni : ∀ k : ℤ, (n : ℝ) * α ≠ k) :
    (2 : ℚ) ^ Int.floor ((n : ℝ) * α)
      * (2 : ℚ) ^ Int.floor ((n : ℝ) * (1 - α))
      = (2 : ℚ) ^ ((n : ℤ) - 1) := by
  rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
    complementary_floor hα0 hα1 hn hni]

/-- Denominators of the cancelled two-slope series: `A_0 = 1` and
`A_{n+1} = 2^n`. -/
def cancellationWitnessDenom : ℕ → ℚ
  | 0 => 1
  | n + 1 => (2 : ℚ) ^ n

/-- Partial sums of the W1 series equal `3 - 2^{1-N}`. -/
theorem cancellation_witness_partial (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), 1 / cancellationWitnessDenom n
      = 3 - (2 : ℚ) * (1 / 2 : ℚ) ^ N := by
  rw [Finset.sum_range_succ']
  have h0 : 1 / cancellationWitnessDenom 0 = 1 := by simp [cancellationWitnessDenom]
  have hsucc : ∀ i ∈ Finset.range N,
      1 / cancellationWitnessDenom (i + 1) = (1 / 2 : ℚ) ^ i := by
    intro i _
    simp [cancellationWitnessDenom]
  rw [h0, Finset.sum_congr rfl hsucc]
  have hr : (1 / 2 : ℚ) ≠ 1 := by norm_num
  rw [geom_sum_eq hr N]
  field_simp
  ring

end ErdosProblems.Erdos269
