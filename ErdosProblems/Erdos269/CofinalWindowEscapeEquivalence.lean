import ErdosProblems.Erdos269.RationalityCarryBridge

/-!
# Erdős #269: the cofinal local-window escape producer is *equivalent* to the target

`RationalityCarryBridge` closes the rationality-to-carry bridge and derives

  `ActualCofinalLocalWindowEscape → Irrational (Σ_{h ∈ ⟨2,3,5⟩} 1/H(h))`.

The producer was therefore recorded as a *strictly stronger, target-deciding*
open route.  This module proves the **converse**, unconditionally:

  `Irrational (Σ_{h ∈ ⟨2,3,5⟩} 1/H(h)) → ActualCofinalLocalWindowEscape`,

so the two are exactly equivalent (`actualCofinalLocalWindowEscape_iff`,
`actualCofinalLocalWindowEscape_iff_irrational_value`).

## What this proves and what it does not

It **proves** an exact equivalence of two propositions.  It does **not** prove
either of them.  **Erdős #269 remains open.**  The mathematical content is a
*no-go for the producer as a reduction*: `ActualCofinalLocalWindowEscape` is
not a weaker, more tractable statement one could hope to attack by
window/anti-concentration arguments and thereby obtain irrationality; proving
it is literally proving Erdős #269.  Any future effort spent on the producer
must be justified as an attack on the target itself.

## The mechanism

Let `X_a = trueNormalizedState a` be the genuine half-height normalized tail,
`b` the actual radix word and `m` the actual ordered digit, so
`X_{a+1} = b_a X_a - m_a`, `0 < X_a ≤ 90 (a+1)^2`.  Unrolling across a window
`[lo, lo+len)` gives, over the reals,

  `X_{lo+len} = W X_lo - F`,   `W = windowBase b lo len`,  `F = windowForcing b m lo len`.

If the least positive residue `r` of `-(B F)` modulo `W` satisfies `r ≤ K` with
`K = B · 90 (lo+len+1)^2`, then writing `r + B F = W k'` and substituting
`F = W X_lo - X_{lo+len}` yields the *exact* identity

  `W · (B X_lo - k) = B X_{lo+len} - r`,  `k = -k'`,

and since `0 < B X_{lo+len} ≤ K` and `0 < r ≤ K`, we get
`dist(B X_lo, ℤ) ≤ K / W ≤ K / 2^len` (`near_integer_of_residue_le`).

That is the whole story: the residue can only stay short if `B X_lo` is
exponentially well approximated by an integer at *every* window length.  As
`K` grows quadratically in `len` and `W ≥ 2^len` grows exponentially, an
irrational `B X_lo` forces the residue to escape at some finite `len`
(`cofinalLocalWindowEscape_of_irrational`), and conversely a short residue at
every window is exactly the rational/integral-carry branch the bridge already
consumes.

The exponential-beats-quadratic step is kept elementary and
`Nat`-only (`exists_pow_gt_quadratic`, via `n < 2^n` at window length `3n`),
so nothing here depends on limit machinery.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-! ## The real window identity for the genuine normalized state -/

/-- Unrolling the genuine real recurrence `X_{a+1} = b_a X_a - m_a` across a
window: `X_{lo+len} = W X_lo - F` with `W`, `F` the *integer* window base and
window forcing of the actual radix word and actual ordered digit. -/
theorem trueNormalizedState_window (lo len : ℕ) :
    trueNormalizedState (lo + len)
      = ((windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len : ℤ) : ℝ)
          * trueNormalizedState lo
        - ((windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
              (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len : ℤ) : ℝ) := by
  induction len with
  | zero => simp [windowBase, windowForcing]
  | succ len ih =>
      have hstep : trueNormalizedState (lo + len + 1)
          = (dyadicBlockBase235 (lo + len) : ℝ) * trueNormalizedState (lo + len)
            - (dyadicOrderedBlockDigit235 (lo + len) : ℝ) :=
        dyadicNormalizedShellTsumTailR235_succ (lo + len)
      rw [show lo + (len + 1) = lo + len + 1 from rfl, hstep, ih]
      simp only [windowBase, windowForcing]
      push_cast
      ring

/-- Every window base of the actual radix word is at least `2^len`. -/
theorem two_pow_le_windowBase235 (lo len : ℕ) :
    (2 : ℤ) ^ len ≤ windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len := by
  induction len with
  | zero => simp [windowBase]
  | succ len ih =>
      have hb : (2 : ℤ) ≤ (dyadicBlockBase235 (lo + len) : ℤ) := by
        exact_mod_cast (dyadicBlockBase235_mem_interval (lo + len)).1
      have hpos : (0 : ℤ) < (2 : ℤ) ^ len := by positivity
      simp only [windowBase]
      calc (2 : ℤ) ^ (len + 1) = 2 * 2 ^ len := by ring
        _ ≤ (dyadicBlockBase235 (lo + len) : ℤ)
              * windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len :=
            mul_le_mul hb ih hpos.le (by linarith)

theorem windowBase235_pos (lo len : ℕ) :
    0 < windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len :=
  lt_of_lt_of_le (by positivity) (two_pow_le_windowBase235 lo len)

/-! ## Irrationality transfers from the value to every normalized state -/

theorem irrational_dyadicShellTsumTailR235_of_one
    (h : Irrational (dyadicShellTsumTailR235 1)) (a : ℕ) (ha : 1 ≤ a) :
    Irrational (dyadicShellTsumTailR235 a) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = 1 + m := ⟨a - 1, by omega⟩
  have hsplit := dyadicShellTsumTailR235_eq_range_add 1 m
  have hprefR : (∑ i ∈ Finset.range m, dyadicShellMassR235 (1 + i))
      = ((dyadicSmoothWindowMassQ235 1 m : ℚ) : ℝ) := by
    simp only [dyadicSmoothWindowMassQ235, dyadicShellMassR235, Rat.cast_sum]
  rw [hprefR] at hsplit
  have hrw : dyadicShellTsumTailR235 (1 + m)
      = dyadicShellTsumTailR235 1 - ((dyadicSmoothWindowMassQ235 1 m : ℚ) : ℝ) := by
    linarith
  rw [hrw]
  exact h.sub_ratCast _

theorem irrational_trueNormalizedState
    (h : Irrational (dyadicShellTsumTailR235 1)) (a : ℕ) (ha : 1 ≤ a) :
    Irrational (trueNormalizedState a) := by
  set q : ℚ := (threePrimeHeight 2 3 5 (2 ^ a) : ℚ) / 2 with hq
  have hqne : q ≠ 0 := by
    rw [hq]
    have hpos : (0 : ℝ) < (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) :=
      threePrimeHeight235_cast_pos _
    have hne : (threePrimeHeight 2 3 5 (2 ^ a) : ℚ) ≠ 0 := by
      have : threePrimeHeight 2 3 5 (2 ^ a) ≠ 0 := by
        intro hz
        rw [hz] at hpos
        simp at hpos
      exact_mod_cast this
    simpa using hne
  have hstate : trueNormalizedState a = (q : ℝ) * dyadicShellTsumTailR235 a := by
    unfold trueNormalizedState dyadicNormalizedTailStateR235
    rw [hq]
    push_cast
    ring
  rw [hstate]
  exact (irrational_dyadicShellTsumTailR235_of_one h a ha).ratCast_mul hqne

/-! ## Exponential beats quadratic, elementarily -/

/-- For every `c` and `lo` there is a positive window length `len` with
`c (lo+len+1)^2 < 2^len`.  Take `n = 16 c (lo+1)^2 + 1` and `len = 3n`, and use
`n < 2^n`. -/
theorem exists_pow_gt_quadratic (c lo : ℕ) :
    ∃ len : ℕ, 0 < len ∧ c * (lo + len + 1) ^ 2 < 2 ^ len := by
  set n : ℕ := 16 * c * (lo + 1) ^ 2 + 1 with hn
  have hn1 : 1 ≤ n := by omega
  refine ⟨3 * n, by omega, ?_⟩
  have h2n : n < 2 ^ n := Nat.lt_two_pow_self
  have hcube : n ^ 3 < (2 ^ n) ^ 3 := Nat.pow_lt_pow_left h2n (by norm_num)
  have hpow : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by
    rw [← pow_mul]
    ring_nf
  have hstep1 : lo + 3 * n + 1 ≤ (lo + 1) * (4 * n) := by nlinarith
  have hstep2 : c * (lo + 3 * n + 1) ^ 2 ≤ c * ((lo + 1) * (4 * n)) ^ 2 := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep1 2)
  have hstep3 : c * ((lo + 1) * (4 * n)) ^ 2 = 16 * c * (lo + 1) ^ 2 * n ^ 2 := by ring
  have hstep4 : 16 * c * (lo + 1) ^ 2 * n ^ 2 ≤ n * n ^ 2 :=
    Nat.mul_le_mul_right _ (by omega)
  have hstep5 : n * n ^ 2 = n ^ 3 := by ring
  calc c * (lo + 3 * n + 1) ^ 2 ≤ c * ((lo + 1) * (4 * n)) ^ 2 := hstep2
    _ = 16 * c * (lo + 1) ^ 2 * n ^ 2 := hstep3
    _ ≤ n * n ^ 2 := hstep4
    _ = n ^ 3 := hstep5
    _ < (2 ^ n) ^ 3 := hcube
    _ = 2 ^ (3 * n) := hpow

/-! ## The core inequality: a short residue pins `B X_lo` near an integer -/

/-- **Exact pinning, for an arbitrary short bound.**  If the local-window
residue at `(lo, len)` does not exceed `K`, and `K` is at least the state width
`B · 90 (lo+len+1)^2`, then `B X_lo` lies within `K / 2^len` of an integer.

The width hypothesis is the only thing `K` must satisfy: nothing about its
growth rate is used here, which is why no reshaping of the short bound can
escape the equivalence below. -/
theorem near_integer_of_residue_le_general
    (B lo len K : ℕ) (hB : 0 < B)
    (hKle : B * bridgeWidth (lo + len) ≤ K)
    (hres : leastPositiveResidue
        (Int.natAbs (windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len))
        (-((B : ℤ) * windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
             (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len))
      ≤ K) :
    ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)|
      ≤ ((K : ℕ) : ℝ) / 2 ^ len := by
  classical
  set W : ℤ := windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len with hW
  set F : ℤ := windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
      (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len with hF
  have hWpos : 0 < W := windowBase235_pos lo len
  have hWnat : ((Int.natAbs W : ℕ) : ℤ) = W := Int.natAbs_of_nonneg hWpos.le
  have hWnatpos : 0 < Int.natAbs W := Int.natAbs_pos.mpr hWpos.ne'
  set r : ℕ := leastPositiveResidue (Int.natAbs W) (-((B : ℤ) * F)) with hr
  obtain ⟨hrpos, hrle⟩ := leastPositiveResidue_pos_le hWnatpos (-((B : ℤ) * F))
  have hmod : Int.ModEq (Int.natAbs W) (r : ℤ) (-((B : ℤ) * F)) :=
    leastPositiveResidue_modEq hWnatpos _
  obtain ⟨t, ht⟩ : (W : ℤ) ∣ (-((B : ℤ) * F) - (r : ℤ)) := by
    have := Int.ModEq.dvd hmod
    rwa [hWnat] at this
  -- the real window identity
  have hwin := trueNormalizedState_window lo len
  rw [← hW, ← hF] at hwin
  set X : ℝ := trueNormalizedState lo with hX
  set Y : ℝ := trueNormalizedState (lo + len) with hY
  have htR : -((B : ℝ) * (F : ℝ)) - (r : ℝ) = (W : ℝ) * (t : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ht
  have hFR : (F : ℝ) = (W : ℝ) * X - Y := by rw [hwin]; ring
  refine ⟨-t, ?_⟩
  have hkey : (W : ℝ) * ((B : ℝ) * X - ((-t : ℤ) : ℝ)) = (B : ℝ) * Y - (r : ℝ) := by
    rw [hFR] at htR
    push_cast
    push_cast at htR
    linarith
  -- bound the right-hand side by `K`
  have hYpos : 0 < Y := trueNormalizedState_pos _
  have hYle : Y ≤ 90 * ((lo + len + 1 : ℕ) : ℝ) ^ 2 :=
    trueNormalizedState_le_quadratic (lo + len)
  have hKR : ((B * bridgeWidth (lo + len) : ℕ) : ℝ)
      = (B : ℝ) * (90 * ((lo + len + 1 : ℕ) : ℝ) ^ 2) := by
    unfold bridgeWidth
    push_cast
    ring
  have hKcast : ((B * bridgeWidth (lo + len) : ℕ) : ℝ) ≤ ((K : ℕ) : ℝ) := by
    exact_mod_cast hKle
  have hBY : (B : ℝ) * Y ≤ ((K : ℕ) : ℝ) := by
    refine le_trans ?_ hKcast
    rw [hKR]
    exact mul_le_mul_of_nonneg_left hYle (by positivity)
  have hBYpos : 0 < (B : ℝ) * Y := by
    have : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    positivity
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
  have hrK : (r : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hres
  have habs : |(B : ℝ) * Y - (r : ℝ)| ≤ ((K : ℕ) : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  -- divide by `W ≥ 2^len`
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
  have h2len : ((2 : ℝ) ^ len) ≤ (W : ℝ) := by
    have := two_pow_le_windowBase235 lo len
    rw [← hW] at this
    exact_mod_cast this
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ len := by positivity
  have habs2 : (W : ℝ) * |(B : ℝ) * X - ((-t : ℤ) : ℝ)| ≤ ((K : ℕ) : ℝ) := by
    calc (W : ℝ) * |(B : ℝ) * X - ((-t : ℤ) : ℝ)|
        = |(W : ℝ) * ((B : ℝ) * X - ((-t : ℤ) : ℝ))| := by
          rw [abs_mul, abs_of_pos hWR]
      _ = |(B : ℝ) * Y - (r : ℝ)| := by rw [hkey]
      _ ≤ ((K : ℕ) : ℝ) := habs
  have hnn : 0 ≤ |(B : ℝ) * X - ((-t : ℤ) : ℝ)| := abs_nonneg _
  rw [le_div_iff₀ h2pos]
  calc |(B : ℝ) * X - ((-t : ℤ) : ℝ)| * (2 : ℝ) ^ len
      ≤ |(B : ℝ) * X - ((-t : ℤ) : ℝ)| * (W : ℝ) :=
        mul_le_mul_of_nonneg_left h2len hnn
    _ = (W : ℝ) * |(B : ℝ) * X - ((-t : ℤ) : ℝ)| := by ring
    _ ≤ ((K : ℕ) : ℝ) := habs2

/-! ## The converse of the bridge -/

/-- An irrational real is uniformly bounded away from every integer. -/
theorem exists_dist_lower_bound_of_irrational {y : ℝ} (hy : Irrational y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, δ ≤ |y - (k : ℝ)| := by
  have hfr0 : Int.fract y ≠ 0 := by
    intro h0
    have hyz : y = ((⌊y⌋ : ℤ) : ℝ) := by
      have hfa := Int.floor_add_fract y
      rw [h0] at hfa
      linarith
    exact hy.ne_int ⌊y⌋ hyz
  have hfrpos : 0 < Int.fract y := lt_of_le_of_ne (Int.fract_nonneg y) (Ne.symm hfr0)
  have hfrlt : Int.fract y < 1 := Int.fract_lt_one y
  refine ⟨min (Int.fract y) (1 - Int.fract y), lt_min hfrpos (by linarith), ?_⟩
  intro k
  have hfa := Int.floor_add_fract y
  rcases le_or_gt k ⌊y⌋ with hk | hk
  · have hkc : ((k : ℤ) : ℝ) ≤ ((⌊y⌋ : ℤ) : ℝ) := by exact_mod_cast hk
    have h1 : Int.fract y ≤ y - (k : ℝ) := by linarith
    exact le_trans (le_trans (min_le_left _ _) h1) (le_abs_self _)
  · have hk' : ⌊y⌋ + 1 ≤ k := by omega
    have hkc : ((⌊y⌋ : ℤ) : ℝ) + 1 ≤ ((k : ℤ) : ℝ) := by exact_mod_cast hk'
    have h1 : 1 - Int.fract y ≤ (k : ℝ) - y := by linarith
    have h3 : min (Int.fract y) (1 - Int.fract y) ≤ |(k : ℝ) - y| :=
      le_trans (le_trans (min_le_right (Int.fract y) (1 - Int.fract y)) h1)
        (le_abs_self ((k : ℝ) - y))
    rwa [abs_sub_comm] at h3

/-- The quantitative input: a positive window length at which a quadratic
short bound is already beaten by the exponentially growing window base. -/
theorem exists_len_quadratic_div_lt (c lo : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ len : ℕ, 0 < len ∧ ((c * (lo + len + 1) ^ 2 : ℕ) : ℝ) / 2 ^ len < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  obtain ⟨len, hlenpos, hlen⟩ := exists_pow_gt_quadratic (N * c) lo
  refine ⟨len, hlenpos, ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hN
  have h5 : (1 : ℝ) < (N : ℝ) * ε := by rwa [div_lt_iff₀ hε] at hN
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ len := by positivity
  have hKlt : ((c * (lo + len + 1) ^ 2 : ℕ) : ℝ) * (N : ℝ) < (2 : ℝ) ^ len := by
    have hnat : N * (c * (lo + len + 1) ^ 2) < 2 ^ len := by
      have heq : N * (c * (lo + len + 1) ^ 2) = N * c * (lo + len + 1) ^ 2 := by ring
      rw [heq]
      exact hlen
    have hcast := (Nat.cast_lt (α := ℝ)).2 hnat
    push_cast at hcast ⊢
    nlinarith [hcast]
  rw [div_lt_iff₀ h2pos]
  by_contra hbc
  rw [not_lt] at hbc
  have h1 : ε * 2 ^ len * (N : ℝ) ≤ ((c * (lo + len + 1) ^ 2 : ℕ) : ℝ) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hbc hNpos.le
  have h2 : ε * 2 ^ len * (N : ℝ) < 2 ^ len := lt_of_le_of_lt h1 hKlt
  have h3 : (ε * (N : ℝ)) * 2 ^ len < 1 * 2 ^ len := by nlinarith [h2]
  have h4 : ε * (N : ℝ) < 1 := lt_of_mul_lt_mul_right h3 h2pos.le
  nlinarith [h4, h5]

/-- **General escape.**  Irrationality of the value implies the cofinal
local-window escape for *any* short bound `sb` that the exponentially growing
window base eventually beats.  Nothing about `sb` other than that is used, so
no reshaping or sharpening of the short bound yields a genuinely weaker
producer. -/
theorem cofinalLocalWindowEscape_of_irrational_of_beaten
    (h : Irrational (dyadicShellTsumTailR235 1)) (sb : ℕ → ℕ → ℕ)
    (hbeat : ∀ B lo : ℕ, 0 < B → ∀ ε : ℝ, 0 < ε →
        ∃ len : ℕ, 0 < len ∧
          ((max (sb B (lo + len)) (B * bridgeWidth (lo + len)) : ℕ) : ℝ)
            / 2 ^ len < ε) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 sb := by
  intro B hBpos _hBcop lo₀
  classical
  set lo : ℕ := lo₀ + 1 with hlo
  obtain ⟨δ, hδpos, hfar⟩ := exists_dist_lower_bound_of_irrational
    ((irrational_trueNormalizedState h lo (by omega)).natCast_mul
      (m := B) (by omega))
  obtain ⟨len, hlenpos, hlt⟩ := hbeat B lo hBpos δ hδpos
  refine ⟨lo, len, by omega, hlenpos, ?_, ?_⟩
  · exact Int.natAbs_pos.mpr (windowBase235_pos lo len).ne'
  · by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨k, hk⟩ := near_integer_of_residue_le_general B lo len
      (max (sb B (lo + len)) (B * bridgeWidth (lo + len))) hBpos
      (le_max_right _ _) (le_trans hcon (le_max_left _ _))
    exact absurd (le_trans (hfar k) hk) (not_le.mpr hlt)

/-- **The whole quadratic family is equivalent to the target.**  For every
short bound dominated by `c B · (n+1)^2` — in particular every sharpening of
the Lean width `90 (n+1)^2`, and every rescaling of it — irrationality implies
the escape.  The same argument works verbatim for any fixed polynomial degree;
only `exists_pow_gt_quadratic` would change. -/
theorem cofinalLocalWindowEscape_of_irrational_of_quadratic
    (h : Irrational (dyadicShellTsumTailR235 1)) (sb : ℕ → ℕ → ℕ) (c : ℕ → ℕ)
    (hsb : ∀ B n, sb B n ≤ c B * (n + 1) ^ 2) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 sb := by
  refine cofinalLocalWindowEscape_of_irrational_of_beaten h sb ?_
  intro B lo hBpos ε hε
  obtain ⟨len, hlenpos, hlen⟩ :=
    exists_len_quadratic_div_lt (max (c B) (B * 90)) lo hε
  refine ⟨len, hlenpos, lt_of_le_of_lt ?_ hlen⟩
  have hdom : max (sb B (lo + len)) (B * bridgeWidth (lo + len))
      ≤ max (c B) (B * 90) * (lo + len + 1) ^ 2 := by
    refine max_le ?_ ?_
    · exact le_trans (hsb B (lo + len)) (Nat.mul_le_mul_right _ (le_max_left _ _))
    · unfold bridgeWidth
      calc B * (90 * (lo + len + 1) ^ 2)
          = B * 90 * (lo + len + 1) ^ 2 := by ring
        _ ≤ max (c B) (B * 90) * (lo + len + 1) ^ 2 :=
            Nat.mul_le_mul_right _ (le_max_right _ _)
  have hcast := (Nat.cast_le (α := ℝ)).2 hdom
  gcongr

/-- **Main theorem.**  Irrationality of the value *implies* the actual cofinal
local-window escape.  Together with `irrational_of_cofinalLocalWindowEscape`
this makes the producer exactly equivalent to the target. -/
theorem cofinalLocalWindowEscape_of_irrational
    (h : Irrational (dyadicShellTsumTailR235 1)) :
    ActualCofinalLocalWindowEscape :=
  cofinalLocalWindowEscape_of_irrational_of_quadratic h
    (fun B n => B * bridgeWidth n) (fun B => B * 90)
    (fun B n => Nat.le_of_eq (by unfold bridgeWidth; ring))

/-! ## The equivalence -/

/-- **The producer is exactly the target.**  `ActualCofinalLocalWindowEscape`
is equivalent to irrationality of `Σ_{h ≥ 2} 1/H(h)`; it is therefore not a
weaker sufficient condition, and no attack on it can be easier than Erdős
#269 itself. -/
theorem actualCofinalLocalWindowEscape_iff :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 1) :=
  ⟨irrational_of_cofinalLocalWindowEscape, cofinalLocalWindowEscape_of_irrational⟩

/-- Headline form: the producer is equivalent to irrationality of the Erdős
#269 value `Σ_{h ∈ ⟨2,3,5⟩} 1/H(h)`. -/
theorem actualCofinalLocalWindowEscape_iff_irrational_value :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 0) := by
  rw [actualCofinalLocalWindowEscape_iff]
  constructor
  · intro h
    rw [dyadicShellTsumTailR235_zero_eq, add_comm]
    simpa using h.add_natCast 1
  · intro h
    rw [dyadicShellTsumTailR235_zero_eq, add_comm] at h
    have h' := h.sub_natCast 1
    simpa using h'

/-! ## Axiom receipts -/

section AxiomReceipts

#print axioms trueNormalizedState_window
#print axioms near_integer_of_residue_le_general
#print axioms exists_pow_gt_quadratic
#print axioms cofinalLocalWindowEscape_of_irrational_of_beaten
#print axioms cofinalLocalWindowEscape_of_irrational_of_quadratic
#print axioms cofinalLocalWindowEscape_of_irrational
#print axioms actualCofinalLocalWindowEscape_iff
#print axioms actualCofinalLocalWindowEscape_iff_irrational_value

end AxiomReceipts

end ErdosProblems.Erdos269
