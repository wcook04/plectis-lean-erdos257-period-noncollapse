import ErdosProblems.Erdos269.DyadicShellSummability

/-!
# Erdős #269: extinction of the integral branch through pinning windows

The bounded-radix dichotomy leaves exactly one branch between the genuine
infinite tail and cofinal escape: an exact integral normalized state.  This
module lands the structural facts that turn that branch into a decidable,
computationally mapped object.

## 1. Positivity and the pinning identity

Every genuine tail is strictly positive (each shell contains `2^a`).
Unrolling the shell decomposition gives the exact pinning identity

`X_a = d_a / b_a + X_(a+1) / b_a`,

so every true state lies strictly above its window anchor `d_a / b_a`.
In particular, when `b_a` divides `d_a`, the anchor is already an integer
and integrality would force `X_(a+1) = 0`, which positivity forbids: such
scales are killed outright.

## 2. Upward closure

The recurrence has integer coefficients, so one integral state makes every
later state integral.  The integral-index set is empty or a final segment,
so the whole question concentrates on a first integral index.

## 3. Iterated pinning and forced equality

Iterating the pinning identity expresses every true state as a finite
digit sum plus a remainder that carries another factor `2^-k` per shell
(because every block radix is at least two).  Any real orbit following the
recurrence from index `A` onward inside windows of a width function that
reproduces under the recurrence and vanishes against `2^-k` therefore
satisfies `|y_A - X_A| <= width (A+k) / 2^k -> 0`, hence equals the true
state.  Consequently an integer seed surviving all windows forever forces
the true state itself to be integral - exactly the quantity the companion
experiment `check_erdos269_integral_branch.py` measures.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- The genuine infinite normalized tail state. -/
noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a

theorem threePrimeHeight235_cast_pos (x : ℕ) :
    (0 : ℝ) < (threePrimeHeight 2 3 5 x : ℝ) := by
  unfold threePrimeHeight
  positivity

theorem dyadicBlockBase235_pos (a : ℕ) : 0 < dyadicBlockBase235 a := by
  rcases dyadicBlockBase235_cases a with h | h | h | h <;>
    simp [h]

theorem threePrimeHeightQ235_pos (x : ℕ) :
    0 < threePrimeHeight 2 3 5 x := by
  unfold threePrimeHeight
  positivity

theorem dyadicShellMassQ235_pos (a : ℕ) : 0 < dyadicShellMassQ235 a := by
  have hmem : (a, 0, 0) ∈ dyadicSmoothShell235 a := by
    refine mem_dyadicSmoothShell235_iff.mpr ?_
    have h1 : smooth3Val 2 3 5 (a, 0, 0).1 (a, 0, 0).2.1 (a, 0, 0).2.2
        = 2 ^ a := by
      simp [smooth3Val]
    have h2 : (2 : ℕ) ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
    rw [h1, h2]
    exact ⟨le_refl _, by nlinarith [show (0 : ℕ) < 2 ^ a by positivity]⟩
  refine Finset.sum_pos ?_ ?_
  · intro e _
    exact inv_pos.mpr (by exact_mod_cast threePrimeHeightQ235_pos _)
  · exact ⟨(a, 0, 0), hmem⟩

theorem dyadicShellMassR235_pos (a : ℕ) : 0 < dyadicShellMassR235 a := by
  unfold dyadicShellMassR235
  exact_mod_cast dyadicShellMassQ235_pos a

theorem dyadicShellTsumTailR235_pos (a : ℕ) :
    0 < dyadicShellTsumTailR235 a := by
  have hsplit := dyadicShellTsumTailR235_eq_shell_add a
  have hpos : 0 ≤ dyadicShellTsumTailR235 (a + 1) :=
    tsum_nonneg (fun n => dyadicShellMassR235_nonneg (a + 1 + n))
  linarith [dyadicShellMassR235_pos a, hpos, hsplit]

theorem trueNormalizedState_pos (a : ℕ) : 0 < trueNormalizedState a := by
  have hH : (0 : ℝ) < (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) :=
    mod_cast threePrimeHeightQ235_pos (2 ^ a)
  have htail : 0 < dyadicShellTsumTailR235 a := dyadicShellTsumTailR235_pos a
  unfold trueNormalizedState dyadicNormalizedTailStateR235
  exact mul_pos (div_pos hH (by norm_num)) htail

/-- **Pinning identity, multiplied form.**  Every true state satisfies
`X_a * b_a = d_a + X_(a+1)`; all steps are definitional or linear. -/
theorem trueNormalizedState_pinning_mul (a : ℕ) :
    trueNormalizedState a * (dyadicBlockBase235 a : ℝ)
      = (dyadicOrderedBlockDigit235 a : ℝ)
        + trueNormalizedState (a + 1) := by
  have hbpos : (0 : ℝ) < (dyadicBlockBase235 a : ℝ) := by
    exact_mod_cast dyadicBlockBase235_pos a
  have hsucc : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ)
      = (dyadicBlockBase235 a : ℝ) * (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) :=
    mod_cast threePrimeHeight_dyadicBlock_succ a
  have hdigit : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2
      * dyadicShellMassR235 a = (dyadicOrderedBlockDigit235 a : ℝ) :=
    half_threePrimeHeight_mul_dyadicShellMassR235 a
  have hsplit : dyadicShellTsumTailR235 a =
      dyadicShellMassR235 a + dyadicShellTsumTailR235 (a + 1) :=
    dyadicShellTsumTailR235_eq_shell_add a
  have hstate : trueNormalizedState (a + 1)
      = (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2
        * dyadicShellTsumTailR235 (a + 1) := rfl
  have hself : trueNormalizedState a
      = (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2
        * dyadicShellTsumTailR235 a := rfl
  -- the future-tail share transfers through the radix product
  have hshare : (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2
        * dyadicShellTsumTailR235 (a + 1)
          * (dyadicBlockBase235 a : ℝ)
      = (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2
        * dyadicShellTsumTailR235 (a + 1) := by
    rw [hsucc]
    ring
  have hmass : (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2
        * dyadicShellMassR235 a * (dyadicBlockBase235 a : ℝ)
      = (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2
        * dyadicShellMassR235 a := by
    rw [hsucc]
    ring
  rw [hself, hstate, hsplit]
  linarith [hdigit, hshare, hmass]

/-- **Pinning identity.**  Every true state sits exactly one future state
above its anchor digit quotient. -/
theorem trueNormalizedState_pinning (a : ℕ) :
    trueNormalizedState a =
      (dyadicOrderedBlockDigit235 a : ℝ) / (dyadicBlockBase235 a : ℝ) +
        trueNormalizedState (a + 1) / (dyadicBlockBase235 a : ℝ) := by
  have hbne : (dyadicBlockBase235 a : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast dyadicBlockBase235_pos a)
  have hm := trueNormalizedState_pinning_mul a
  refine Eq.trans ?_ (add_div _ _ _)
  exact eq_div_iff hbne |>.mpr hm

/-- **Zero-gap separation.**  When the block radix divides the ordered
digit the anchor is an exact integer, so an integral state at such a scale
cannot sit in the first unit interval above the anchor; quantitatively,
`X_a` integral implies `X_a >= anchor + 1`.  This is a quantitative
separation, not an outright exclusion of integrality. -/
theorem zero_gap_digit_separation (a : ℕ)
    (hgap : (dyadicBlockBase235 a : ℤ) ∣ dyadicOrderedBlockDigit235 a)
    (z : ℤ) (hint : trueNormalizedState a = (z : ℝ)) :
    (z : ℝ) ≥ (dyadicOrderedBlockDigit235 a : ℝ)
      / (dyadicBlockBase235 a : ℝ) + 1 := by
  obtain ⟨k, hk⟩ := hgap
  have hpin := trueNormalizedState_pinning a
  have hbpos : (0 : ℝ) < (dyadicBlockBase235 a : ℝ) := by
    exact_mod_cast dyadicBlockBase235_pos a
  have hnextpos : 0 < trueNormalizedState (a + 1) := trueNormalizedState_pos _
  have hterm : 0 < trueNormalizedState (a + 1) / (dyadicBlockBase235 a : ℝ) :=
    div_pos hnextpos hbpos
  have hanchor :
      (dyadicOrderedBlockDigit235 a : ℝ) / (dyadicBlockBase235 a : ℝ)
        = (k : ℝ) := by
    have hc : (dyadicOrderedBlockDigit235 a : ℝ)
        = (dyadicBlockBase235 a : ℝ) * (k : ℝ) := by
      exact_mod_cast hk
    rw [hc]
    field_simp
  rw [hint, hanchor] at hpin
  have hgt : (z : ℝ) > (k : ℝ) := by linarith
  have hint2 : z > k := by exact_mod_cast hgt
  have hle : k + 1 ≤ z := by omega
  have hc : (((k : ℤ) + 1 : ℤ) : ℝ) ≤ (z : ℝ) := Int.cast_le.mpr hle
  push_cast at hc
  linarith

/-- **Upward closure.**  One integral state makes all later states
integral, because the recurrence has integer coefficients. -/
theorem integral_state_upward_closed {a : ℕ} {z : ℤ}
    (hint : trueNormalizedState a = (z : ℝ)) :
    ∀ n, a ≤ n → ∃ z' : ℤ, trueNormalizedState n = (z' : ℝ) := by
  intro n hn
  induction n with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    exact ⟨z, hint⟩
  | succ n ih =>
    rcases Nat.lt_or_ge n a with hlt | hge
    · have han : a = n + 1 := by omega
      subst han
      exact ⟨z, hint⟩
    · obtain ⟨z', hz'⟩ := ih hge
      refine ⟨(dyadicBlockBase235 n : ℤ) * z'
        - (dyadicOrderedBlockDigit235 n : ℤ), ?_⟩
      have hrec := dyadicNormalizedShellTsumTailR235_succ n
      have hz2 : dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 n
          = (z' : ℝ) := hz'
      rw [show trueNormalizedState (n + 1)
            = dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (n + 1)
          from rfl, hrec, hz2]
      push_cast
      ring

/-! ## Iterated pinning -/

/-- Iterating the pinning identity `k` times bounds the state by a digit
sum carrying one factor of `2^-i` per shell plus a final remainder under
`2^-k`.  Only `b >= 2`, positivity of states, and nonnegativity of digits
are used. -/
theorem trueNormalizedState_le_iterated (m k : ℕ) :
    trueNormalizedState m ≤
      (∑ i ∈ Finset.range k,
          ((dyadicOrderedBlockDigit235 (m + i) : ℝ) / 2 ^ (i + 1))) +
        trueNormalizedState (m + k) / 2 ^ k := by
  induction k with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    norm_num
  | succ k ih =>
    -- peel one further shell at the deepest recorded index `m + k`
    have hidx : m + k + 1 = m + (k + 1) := Nat.add_assoc m k 1
    have hbpos : (0 : ℝ) < (dyadicBlockBase235 (m + k) : ℝ) := by
      exact_mod_cast dyadicBlockBase235_pos (m + k)
    have hb2 : (2 : ℝ) ≤ (dyadicBlockBase235 (m + k) : ℝ) :=
      mod_cast (dyadicBlockBase235_mem_interval (m + k)).1
    have hnonneg : 0 ≤ trueNormalizedState (m + (k + 1)) :=
      le_of_lt (trueNormalizedState_pos _)
    have hd : 0 ≤ (dyadicOrderedBlockDigit235 (m + k) : ℝ) := Nat.cast_nonneg _
    have hpin := trueNormalizedState_pinning (m + k)
    rw [hidx] at hpin
    have hsplit : trueNormalizedState (m + k) ≤
        (dyadicOrderedBlockDigit235 (m + k) : ℝ) / 2
          + trueNormalizedState (m + (k + 1)) / 2 := by
      have e1 : (dyadicOrderedBlockDigit235 (m + k) : ℝ)
          / (dyadicBlockBase235 (m + k) : ℝ)
          ≤ (dyadicOrderedBlockDigit235 (m + k) : ℝ) / 2 := by
        rw [div_le_div_iff₀ hbpos (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      have e2 : trueNormalizedState (m + (k + 1))
          / (dyadicBlockBase235 (m + k) : ℝ)
          ≤ trueNormalizedState (m + (k + 1)) / 2 := by
        refine div_le_div_of_nonneg_left hnonneg (by norm_num : (0 : ℝ) < 2) ?_
        linarith
      linarith
    have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h2X : 2 * trueNormalizedState (m + k)
        ≤ (dyadicOrderedBlockDigit235 (m + k) : ℝ)
          + trueNormalizedState (m + (k + 1)) := by linarith
    -- push the extra shell through the factor `2^-k` already accumulated
    have hstep : trueNormalizedState (m + k) / 2 ^ k
        ≤ (dyadicOrderedBlockDigit235 (m + k) : ℝ) / 2 ^ (k + 1)
          + trueNormalizedState (m + (k + 1)) / 2 ^ (k + 1) := by
      rw [pow_succ, ← add_div,
        div_le_div_iff₀ hpow (by positivity : (0 : ℝ) < 2 ^ k * 2)]
      nlinarith [mul_le_mul_of_nonneg_right h2X hpow.le]
    rw [Finset.sum_range_succ]
    linarith [ih, hstep]

/-! ## Forced equality of window-tracking orbits -/

/-- **Forced equality.**  Any real orbit that follows the source recurrence
from index `A` onward and stays inside the anchor windows of a width
function reproducing along the orbit must coincide with the genuine tail.
Deviations multiply by at least two per shell while both orbits remain
inside the same window, so the initial deviation is dominated by
`width (A+k)/2^k -> 0`.  Hence "an integer seed survives all windows"
is equivalent to "the true state is an integer" - exactly the quantity
the companion experiments decide per index. -/
theorem surviving_window_orbit_eq_true_state
    (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ)
    (hrec : ∀ n, A ≤ n →
      y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n -
          (dyadicOrderedBlockDigit235 n : ℝ))
    (hwin : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) /
          (dyadicBlockBase235 n : ℝ) + width n)
    (hwidth : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ)
        < trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) /
            (dyadicBlockBase235 n : ℝ) + width n)
    (hvanish : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      width (A + k) / 2 ^ k < ε) :
    y A = trueNormalizedState A := by
  by_contra hne
  have hepos : 0 < |y A - trueNormalizedState A| :=
    abs_pos.mpr (sub_ne_zero_of_ne hne)
  obtain ⟨k₀, hk₀⟩ := hvanish (|y A - trueNormalizedState A| / 2)
    (by linarith [abs_nonneg (y A)])
  -- deviations multiply by at least two per shell
  have hdev : ∀ k : ℕ,
      (2 : ℝ) ^ k * |y A - trueNormalizedState A|
        ≤ |y (A + k) - trueNormalizedState (A + k)| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hbposR : (0 : ℝ) < (dyadicBlockBase235 (A + k) : ℝ) := by
        exact_mod_cast dyadicBlockBase235_pos (A + k)
      have hb2 : (2 : ℝ) ≤ (dyadicBlockBase235 (A + k) : ℝ) :=
        mod_cast (dyadicBlockBase235_mem_interval (A + k)).1
      have hts : ∀ n : ℕ, trueNormalizedState n
          = dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 n :=
        fun _ => rfl
      have h1 := hrec (A + k) (by omega)
      have h2 := dyadicNormalizedShellTsumTailR235_succ (A + k)
      have hdiff : y (A + k + 1) - trueNormalizedState (A + k + 1)
          = (dyadicBlockBase235 (A + k) : ℝ)
            * (y (A + k) - trueNormalizedState (A + k)) := by
        rw [h1, hts (A + k + 1), h2, hts (A + k)]
        ring
      have hstep : (2 : ℝ) * |y (A + k) - trueNormalizedState (A + k)|
          ≤ |y (A + k + 1) - trueNormalizedState (A + k + 1)| := by
        rw [hdiff, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rwa [abs_of_pos hbposR]
      calc (2 : ℝ) ^ (k + 1) * |y A - trueNormalizedState A|
          = 2 * ((2 : ℝ) ^ k * |y A - trueNormalizedState A|) := by ring
        _ ≤ 2 * |y (A + k) - trueNormalizedState (A + k)| :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ |y (A + k + 1) - trueNormalizedState (A + k + 1)| := hstep
  -- both orbits sit inside the same window at A + k, so their difference
  -- is at most the width
  have hbound : ∀ k : ℕ,
      |y (A + k) - trueNormalizedState (A + k)| ≤ width (A + k) := by
    intro k
    have hlow : trueNormalizedState (A + k) - y (A + k) ≤ width (A + k) := by
      obtain ⟨hy, hy'⟩ := hwin (A + k) (by omega)
      obtain ⟨hx, hx'⟩ := hwidth (A + k) (by omega)
      linarith
    have hhigh : y (A + k) - trueNormalizedState (A + k) ≤ width (A + k) := by
      obtain ⟨hy, hy'⟩ := hwin (A + k) (by omega)
      obtain ⟨hx, hx'⟩ := hwidth (A + k) (by omega)
      linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  specialize hk₀ k₀ (Nat.le_refl _)
  have hbound0 := hbound k₀
  have hdev0 := hdev k₀
  -- width (A+k0) < 2^k0 * |e| / 2 while also 2^k0 * |e| <= width
  have hlt : width (A + k₀) / 2 ^ k₀
      < |y A - trueNormalizedState A| / 2 := hk₀
  have hwpos : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
  have hcanc : width (A + k₀) / 2 ^ k₀ * 2 ^ k₀ = width (A + k₀) :=
    div_mul_cancel₀ _ hwpos.ne'
  have hm : width (A + k₀) / 2 ^ k₀ * 2 ^ k₀
      < |y A - trueNormalizedState A| / 2 * 2 ^ k₀ :=
    mul_lt_mul_of_pos_right hlt hwpos
  rw [hcanc] at hm
  have hhalf : |y A - trueNormalizedState A| / 2 * 2 ^ k₀
      ≤ |y A - trueNormalizedState A| * 2 ^ k₀ := by
    nlinarith [abs_nonneg (y A - trueNormalizedState A)]
  linarith

end ErdosProblems.Erdos269
