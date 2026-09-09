import ErdosProblems.Erdos68.PrimeZeroBranch

/-!
# Erdős #68: the shrinking-target normal form

The corpus already carries two exact normal forms for the irrationality of
`S = ∑ 1/(n! - 1)`: cofinal non-unit carries, and cofinal misses of the
strict-successor divisibility.  Both treat *every* unit carry as a failure.

A unit carry has two radically different causes: the canonical orbit sits in
the tiny lower endpoint cylinder, or the canonical digit is maximal.  The
second is harmless.  This module isolates that distinction and produces a
**third** exact normal form:

`S ∉ ℚ  ↔  ∀ B, ∃ m > B, factorialGapScaledTail m ≤ m · r_{m-1}`

(`irrational_factorialGapSeries_iff_cofinal_lower_endpoint_escape`), i.e.
irrationality is exactly *cofinal escape from the lower endpoint cylinder*.
Since `0 < factorialGapScaledTail m < 2/m`, the trapping radius is
`O(m⁻²)`: Erdős #68 is an explicit deterministic shrinking-target problem
for the factorial orbit, with a quadratically small target.

The escape target is strictly more permissive than the carry target
(`factorialGap_lower_endpoint_escape_iff_nonunit_or_maximal_digit`), and it
admits a completely **tail-free two-sided** consumer over the finite
predecessor gap (`irrational_factorialGapSeries_of_cofinal_predecessorGap_outside_window`).
The corpus previously exposed only the upper half of that window.

Erdős #68 remains open: no theorem here produces the cofinal escape events.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- **The escape criterion is exactly the harmless-carry criterion.**  The
forward implication is the existing consumer; the converse is new and is what
turns the one-way test into a normal form. -/
theorem factorialGap_lower_endpoint_escape_iff_nonunit_or_maximal_digit
    {m : ℕ} (hm : 3 ≤ m) :
    factorialGapScaledTail m ≤
        (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1) ↔
      factorialGapStepCarry m ≠ 1 ∨
        canonicalDigit _root_.Erdos68.factorialGapSeries m = (m : ℤ) - 1 := by
  constructor
  · exact lower_endpoint_escape_forces_nonunit_or_maximal_digit hm
  · intro hor
    by_contra hnot
    have htrap :
        (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1) <
          factorialGapScaledTail m := lt_of_not_ge hnot
    have hzero := (factorialGap_zero_branch_iff_lower_endpoint_cylinder hm).2 htrap
    rcases hor with hcarry | hmax
    · exact hcarry
        ((factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch hm).2 (Or.inl hzero))
    · have hz : (0 : ℤ) = (m : ℤ) - 1 := hzero.1.symm.trans hmax
      have hmR : (3 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      omega

/-- One escape at index `m` excludes every displayed rational denominator
below `m`.  Unlike the existing prime-indexed consumer, no primality
assumption is needed. -/
theorem factorialGap_rational_denominator_ge_of_lower_endpoint_escape
    {m q : ℕ} {a : ℤ} (hm : 2 ≤ m) (hq : 0 < q)
    (hseries : _root_.Erdos68.factorialGapSeries = (a : ℝ) / (q : ℝ))
    (hescape :
      factorialGapScaledTail m ≤
        (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1)) :
    m ≤ q := by
  by_contra hmq
  have hqpred : q ≤ m - 1 := by omega
  have hzero : canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1) = 0 :=
    canonicalRemainder_eq_zero_of_eq_rat (q := q) (a := a) hq hqpred hseries
  have htail : 0 < factorialGapScaledTail m := factorialGapScaledTail_pos hm
  rw [hzero, mul_zero] at hescape
  linarith

/-- **Third exact normal form for Erdős #68.**  The series is irrational
exactly when its canonical factorial orbit escapes the lower endpoint
cylinder cofinally.  Because `0 < factorialGapScaledTail m < 2/m`, this is a
shrinking-target statement with target radius `O(m⁻²)`. -/
theorem irrational_factorialGapSeries_iff_cofinal_lower_endpoint_escape :
    Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        factorialGapScaledTail m ≤
          (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1) := by
  constructor
  · intro hirr B
    by_contra hcofinal
    push_neg at hcofinal
    have htrap : ∀ m : ℕ, B < m →
        (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1) <
          factorialGapScaledTail m := by
      intro m hmB
      exact lt_of_not_ge fun hge => absurd (hcofinal m hmB) (not_lt.2 hge)
    have hunit : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1 := by
      refine ⟨max 3 (B + 1), fun m hm => ?_⟩
      have hm3 : 3 ≤ m := le_trans (le_max_left 3 (B + 1)) hm
      have hmB : B < m := by
        have := le_trans (le_max_right 3 (B + 1)) hm
        omega
      exact (factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch hm3).2
        (Or.inl ((factorialGap_zero_branch_iff_lower_endpoint_cylinder hm3).2 (htrap m hmB)))
    exact (not_irrational_factorialGapSeries_of_eventually_unit_carries hunit) hirr
  · intro hescape
    by_contra hrat
    obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
    obtain ⟨m, hmLarge, hmEscape⟩ := hescape (max 2 (r.den + 1))
    have hm2 : 2 ≤ m := by
      have := le_max_left 2 (r.den + 1)
      omega
    have hmq : m ≤ r.den :=
      factorialGap_rational_denominator_ge_of_lower_endpoint_escape
        (m := m) (q := r.den) (a := r.num) hm2 r.den_pos (by rw [hr, Rat.cast_def]) hmEscape
    have := le_max_right 2 (r.den + 1)
    omega

/-- **Tail-free two-sided window.**  Escaping the lower endpoint cylinder is
implied by the finite predecessor gap avoiding a rational window of width
`2/m` — on *either* side.  The corpus previously exposed only the upper
half. -/
theorem lower_endpoint_escape_of_predecessorGap_outside_window
    {m : ℕ} (hm : 3 ≤ m)
    (hout :
      (m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m) :
    factorialGapScaledTail m ≤
      (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1) := by
  by_contra hnot
  have htrap :
      (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1) <
        factorialGapScaledTail m := lt_of_not_ge hnot
  have hzero := (factorialGap_zero_branch_iff_lower_endpoint_cylinder hm).2 htrap
  have hwindow := (factorialGap_zero_branch_iff_predecessorGap_lower_window hm).1 hzero
  rcases hout with hlow | hhigh
  · exact absurd hwindow.1 (not_lt.2 hlow)
  · have htail : factorialGapScaledTail m < 2 / (m : ℝ) :=
      factorialGapScaledTail_lt_two_div (by omega)
    linarith [hwindow.2]

/-- **Two-sided finite consumer.**  Cofinal avoidance of the explicit
rational window of width `2/m` proves irrationality.  No infinite sum, real
floor, or tail occurs in the hypothesis. -/
theorem irrational_factorialGapSeries_of_cofinal_predecessorGap_outside_window
    (hout : ∀ B : ℕ, ∃ m : ℕ, 3 ≤ m ∧ B < m ∧
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  rw [irrational_factorialGapSeries_iff_cofinal_lower_endpoint_escape]
  intro B
  obtain ⟨m, hm3, hmB, hmWindow⟩ := hout B
  exact ⟨m, hmB, lower_endpoint_escape_of_predecessorGap_outside_window hm3 hmWindow⟩

/-- The trapping radius is quadratically small: the exact target has width
`factorialGapScaledTail m / m ∈ (0, 2/m²)`. -/
theorem lower_endpoint_target_radius_lt_two_div_sq {m : ℕ} (hm : 2 ≤ m) :
    0 < factorialGapScaledTail m / (m : ℝ) ∧
      factorialGapScaledTail m / (m : ℝ) < 2 / (m : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hpos := factorialGapScaledTail_pos hm
  have hlt := factorialGapScaledTail_lt_two_div hm
  constructor
  · positivity
  · rw [div_lt_div_iff₀ hmR (by positivity)]
    have h2 : factorialGapScaledTail m * (m : ℝ) < 2 := by
      rw [lt_div_iff₀ hmR] at hlt
      linarith
    nlinarith

end ErdosProblems.Erdos68
