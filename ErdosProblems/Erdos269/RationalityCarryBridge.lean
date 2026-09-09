import ErdosProblems.Erdos269.NormalizedStateWidth
import ErdosProblems.Erdos269.RationalLatticeReduction

/-!
# Erdős #269: the rationality-to-carry bridge, closed

The paper's Problem `prob:bridge269` ("actual rationality-to-carry
identification") asks: starting from the `{2,3,5}` running-LCM series and a
reduced denominator `D = D_sm · B` with `D_sm` `30`-smooth and `gcd(B,30) = 1`,
prove with a stated onset `a ≥ a_D` that the literal radix word
`β_a = dyadicBlockBase235 a`, the literal digit `m_a = dyadicOrderedBlockDigit235 a`
and the literal normalized tail `T_a = trueNormalizedState a` give positive
integral carries `c_a = D T_a` with `c_(a+1) = β_a c_a - D m_a`, an explicit
bound, and `D_sm ∣ c_a`; and that the reduced carry `d_a = c_a / D_sm` obeys
`d_(a+1) = β_a d_a - B m_a` with `0 < d_a ≤ K(B, a)`.

This module proves exactly that, with `K(B, a) = B · 90 (a+1)^2` (the width of
`NormalizedStateWidth`) and onset `a_D = α + 1 + 2β + 3γ` for
`D_sm = 2^α 3^β 5^γ`.  The pieces:

* `exists_smooth_coprime_split` — every positive integer is `2^α 3^β 5^γ · B`
  with `gcd(B, 30) = 1`;
* `smooth_dvd_heightNormalizer235` — the half height `H(2^a)/2` absorbs
  `2^α 3^β 5^γ` once `a ≥ α + 1 + 2β + 3γ`;
* `qsmul_trueNormalizedState_eq_height_mul_sub` — the all-scale lattice with
  its explicit witness `q X_a = (H(2^a)/2) p - q z_a`, so the carry is
  congruent to `(H(2^a)/2) p` modulo `q` and the smooth part divides it;
* `latticeCarry` and its recurrence, positivity and width, all inherited from
  the true state through the integer cast;
* `reducedLatticeCarry` — the quotient by the smooth part, with the reduced
  recurrence and the bound `0 < d_a ≤ B · 90 (a+1)^2` from the onset on.

The consumer `no_positive_reducedCarry_of_cofinalLocalWindowEscape` of
`RestrictedFloorSum` was stated for carries defined at every index; the
onset-aware form `no_positive_reducedCarry_of_cofinalLocalWindowEscape_onset`
proved here uses the producer's own `∀ lo₀ ∃ lo ≥ lo₀` clause to start the
window past the onset.

## Consequence

`irrational_of_cofinalLocalWindowEscape`: the paper's Problem `prob:producer`
(9.5), i.e. `CofinalLocalWindowEscape` for the actual radix word, the actual
ordered digit and the short bound `B · 90 (n+1)^2`, implies that
`Σ_{h ≥ 2} 1/H(h)` is irrational, hence (`irrational_value_of_cofinalLocalWindowEscape`)
that the Erdős #269 value `Σ_{h ≥ 1} 1/H(h)` is irrational.  The generic
extinction theorem is thereby a theorem about the actual series: the only
unproved input is the cofinal local-window escape itself.

## Claim ceiling

`CofinalLocalWindowEscape` is a named `Prop`, not a theorem.  Nothing here
proves it, and **Erdős #269 remains open**.  What is closed is the bridge: a
rational value forces, from an explicit onset, a positive reduced integral
carry of the exact shape the residue consumer refutes, with every object the
literal one from the series.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-! ## Onset-aware window identity and consumer -/

/-- The local-window identity needs the recurrence only from the window start. -/
theorem integralCarry_window_of_ge
    (c b m : ℕ → ℤ) (B : ℤ) (lo len : ℕ)
    (hrec : ∀ n, lo ≤ n → c (n + 1) = b n * c n - B * m n) :
    c (lo + len) =
      windowBase b lo len * c lo - B * windowForcing b m lo len := by
  induction len with
  | zero => simp [windowBase, windowForcing]
  | succ len ih =>
      rw [Nat.add_succ, hrec (lo + len) (Nat.le_add_right lo len), ih]
      simp only [windowBase, windowForcing]
      ring

/-- The residue consumer, for a reduced carry that is only defined, positive
and bounded from an onset `a₀` onward.  The producer's `∀ lo₀ ∃ lo ≥ lo₀`
clause supplies a window starting past the onset. -/
theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape_onset
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (a₀ : ℕ) (d : ℕ → ℤ)
    (hrec : ∀ n, a₀ ≤ n →
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, a₀ ≤ n → 0 < d n)
    (hbound : ∀ n, a₀ ≤ n → Int.natAbs (d n) ≤ shortBound B n) :
    False := by
  rcases hescape B hBpos hBcoprime a₀ with
    ⟨lo, len, hlo, _hlen, hbasePos, hresidueEscape⟩
  let W : ℤ := windowBase (fun n => (b n : ℤ)) lo len
  let F : ℤ := windowForcing
    (fun n => (b n : ℤ)) (fun n => (m n : ℤ)) lo len
  have hwindow :
      d (lo + len) = W * d lo - (B : ℤ) * F := by
    simpa [W, F] using
      integralCarry_window_of_ge d
        (fun n => (b n : ℤ)) (fun n => (m n : ℤ))
        (B : ℤ) lo len (fun n hn => hrec n (le_trans hlo hn))
  have hmodW :
      Int.ModEq W (d (lo + len)) (-((B : ℤ) * F)) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-d lo, ?_⟩
    rw [hwindow]
    ring
  have hmod :
      Int.ModEq (Int.natAbs W)
        (d (lo + len)) (-((B : ℤ) * F)) :=
    (Int.modEq_natAbs).2 hmodW
  exact no_bounded_positive_int_state_of_leastPositiveResidue
    (by simpa [W] using hbasePos)
    (hpos (lo + len) (le_trans hlo (Nat.le_add_right lo len)))
    (hbound (lo + len) (le_trans hlo (Nat.le_add_right lo len)))
    (by simpa [W, F] using hresidueEscape)
    hmod

/-! ## Splitting a denominator into its `30`-smooth and rough parts -/

/-- Every positive integer is `2^α 3^β 5^γ · B` with `B` coprime to `30`. -/
theorem exists_smooth_coprime_split (q : ℕ) (hq : 0 < q) :
    ∃ α β γ B : ℕ,
      q = 2 ^ α * 3 ^ β * 5 ^ γ * B ∧ 0 < B ∧ Nat.Coprime B 30 := by
  obtain ⟨α, q₁, h2, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hq.ne' 2 (by norm_num)
  have hq₁ : q₁ ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨β, q₂, h3, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hq₁ 3 (by norm_num)
  have hq₂ : q₂ ≠ 0 := by
    rintro rfl
    simp at hq₁
  obtain ⟨γ, B, h5, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hq₂ 5 (by norm_num)
  have hB : B ≠ 0 := by
    rintro rfl
    simp at hq₂
  have h2B : ¬ 2 ∣ B := fun h =>
    h2 (Dvd.dvd.mul_left (Dvd.dvd.mul_left h _) _)
  have h3B : ¬ 3 ∣ B := fun h => h3 (Dvd.dvd.mul_left h _)
  have hc2 : Nat.Coprime B 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2B).symm
  have hc3 : Nat.Coprime B 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3B).symm
  have hc5 : Nat.Coprime B 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5).symm
  refine ⟨α, β, γ, B, by ring, Nat.pos_of_ne_zero hB, ?_⟩
  have h30 : (30 : ℕ) = 2 * 3 * 5 := by norm_num
  rw [h30]
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right hc2 hc3) hc5

/-- The half height `H(2^a)/2` absorbs `2^α 3^β 5^γ` once
`a ≥ α + 1 + 2β + 3γ` (using `3 ≤ 4` and `5 ≤ 8`). -/
theorem smooth_dvd_heightNormalizer235 {α β γ a : ℕ}
    (ha : α + 1 + 2 * β + 3 * γ ≤ a) :
    2 ^ α * 3 ^ β * 5 ^ γ ∣ heightNormalizer235 a := by
  have h1 : 1 ≤ a := by omega
  have hle : smooth3Val 2 3 5 (α + 1) β γ ≤ 2 ^ a := by
    unfold smooth3Val
    calc 2 ^ (α + 1) * 3 ^ β * 5 ^ γ
        ≤ 2 ^ (α + 1) * 4 ^ β * 8 ^ γ := by gcongr <;> norm_num
      _ = 2 ^ (α + 1 + 2 * β + 3 * γ) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, show (8 : ℕ) = 2 ^ 3 by norm_num,
            ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hdvd := smooth3Val_dvd_threePrimeHeight_of_le
    (p := 2) (q := 3) (r := 5) (by norm_num) (by norm_num) (by norm_num) hle
  rw [← two_mul_heightNormalizer235 a h1] at hdvd
  have hsv : smooth3Val 2 3 5 (α + 1) β γ = 2 * (2 ^ α * 3 ^ β * 5 ^ γ) := by
    unfold smooth3Val
    ring
  rw [hsv] at hdvd
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hdvd

/-! ## The lattice witness, made explicit -/

/-- The all-scale lattice with its explicit witness: if the value is `p/q`
then `q X_a = (H(2^a)/2) p - q z_a` for an integer `z_a` (the cleared
prefix), at every scale `a ≥ 1`. -/
theorem qsmul_trueNormalizedState_eq_height_mul_sub
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    ∃ z : ℤ,
      (q : ℝ) * trueNormalizedState a
        = ((heightNormalizer235 a : ℕ) : ℝ) * (p : ℝ) - (q : ℝ) * (z : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = 1 + m := ⟨a - 1, by omega⟩
  have hsplit := dyadicShellTsumTailR235_eq_range_add 1 m
  set prefQ : ℚ := dyadicSmoothWindowMassQ235 1 m with hprefQ
  have hprefR : (∑ i ∈ Finset.range m, dyadicShellMassR235 (1 + i)) = (prefQ : ℝ) := by
    simp only [hprefQ, dyadicSmoothWindowMassQ235, dyadicShellMassR235, Rat.cast_sum]
  obtain ⟨z, hz⟩ := heightNormalizer235_mul_windowMass_eq_int 1 m
  have hnorm : trueNormalizedState (1 + m)
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * dyadicShellTsumTailR235 (1 + m) := by
    unfold trueNormalizedState dyadicNormalizedTailStateR235
    have h2 : ((threePrimeHeight 2 3 5 (2 ^ (1 + m)) : ℕ) : ℝ)
        = 2 * ((heightNormalizer235 (1 + m) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
        (two_mul_heightNormalizer235 (1 + m) (by omega)).symm
    rw [h2]
    ring
  have htail : dyadicShellTsumTailR235 (1 + m) = (p : ℝ) / (q : ℝ) - (prefQ : ℝ) := by
    have := hsplit
    rw [hprefR, hval] at this
    linarith
  have hzR : ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (prefQ : ℝ) = ((z : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun r : ℚ => (r : ℝ)) hz
  have hqne : (q : ℝ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hqp : (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by field_simp
  refine ⟨(z : ℤ), ?_⟩
  rw [hnorm, htail]
  push_cast
  calc (q : ℝ) * (((heightNormalizer235 (1 + m) : ℕ) : ℝ)
          * ((p : ℝ) / (q : ℝ) - (prefQ : ℝ)))
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * ((q : ℝ) * ((p : ℝ) / (q : ℝ)))
          - (q : ℝ) * (((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (prefQ : ℝ)) := by ring
    _ = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (p : ℝ) - (q : ℝ) * ((z : ℕ) : ℝ) := by
          rw [hqp, hzR]

/-! ## The integral lattice carry and its reduction -/

/-- The integral lattice carry `c_a = q X_a`, read off through the floor.  For
`a ≥ 1` and a rational value it is exactly `q X_a`. -/
noncomputable def latticeCarry (q : ℤ) (a : ℕ) : ℤ :=
  ⌊(q : ℝ) * trueNormalizedState a⌋

theorem latticeCarry_cast {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    ((latticeCarry q a : ℤ) : ℝ) = (q : ℝ) * trueNormalizedState a := by
  obtain ⟨z, hz⟩ := qsmul_trueNormalizedState_eq_height_mul_sub hq hval ha
  have hint : (q : ℝ) * trueNormalizedState a
      = (((heightNormalizer235 a : ℕ) : ℤ) * p - q * z : ℤ) := by
    rw [hz]
    push_cast
    ring
  unfold latticeCarry
  rw [hint, Int.floor_intCast]

/-- The carry is congruent to `(H(2^a)/2) · p` modulo `q`; in particular any
common divisor of `q` and the half height divides it. -/
theorem smooth_dvd_latticeCarry {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {s : ℤ} (hsq : s ∣ q) {a : ℕ} (ha : 1 ≤ a)
    (hsh : s ∣ ((heightNormalizer235 a : ℕ) : ℤ)) :
    s ∣ latticeCarry q a := by
  obtain ⟨z, hz⟩ := qsmul_trueNormalizedState_eq_height_mul_sub hq hval ha
  have hint : (q : ℝ) * trueNormalizedState a
      = (((heightNormalizer235 a : ℕ) : ℤ) * p - q * z : ℤ) := by
    rw [hz]
    push_cast
    ring
  have hc : latticeCarry q a = ((heightNormalizer235 a : ℕ) : ℤ) * p - q * z := by
    unfold latticeCarry
    rw [hint, Int.floor_intCast]
  rw [hc]
  exact dvd_sub (dvd_mul_of_dvd_left hsh _) (dvd_mul_of_dvd_left hsq _)

/-- The carry obeys the literal affine recurrence
`c_(a+1) = b_a c_a - q d_a` at every scale `a ≥ 1`. -/
theorem latticeCarry_succ {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    latticeCarry q (a + 1)
      = (dyadicBlockBase235 a : ℤ) * latticeCarry q a
        - q * (dyadicOrderedBlockDigit235 a : ℤ) := by
  have h1 := latticeCarry_cast hq hval ha
  have h2 := latticeCarry_cast hq hval (show 1 ≤ a + 1 by omega)
  have hrec : trueNormalizedState (a + 1)
      = (dyadicBlockBase235 a : ℝ) * trueNormalizedState a
        - (dyadicOrderedBlockDigit235 a : ℝ) :=
    dyadicNormalizedShellTsumTailR235_succ a
  have hR : ((latticeCarry q (a + 1) : ℤ) : ℝ)
      = (((dyadicBlockBase235 a : ℤ) * latticeCarry q a
          - q * (dyadicOrderedBlockDigit235 a : ℤ) : ℤ) : ℝ) := by
    rw [h2, hrec]
    push_cast
    rw [h1]
    ring
  exact_mod_cast hR

/-- The carry is positive at every scale `a ≥ 1`. -/
theorem latticeCarry_pos {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) : 0 < latticeCarry q a := by
  have h := latticeCarry_cast hq hval ha
  have hpos : (0 : ℝ) < (q : ℝ) * trueNormalizedState a :=
    mul_pos (by exact_mod_cast hq) (trueNormalizedState_pos a)
  rw [← h] at hpos
  exact_mod_cast hpos

/-- The carry is bounded by `q · 90 (a+1)^2` at every scale `a ≥ 1`. -/
theorem latticeCarry_le {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    latticeCarry q a ≤ q * ((90 * (a + 1) ^ 2 : ℕ) : ℤ) := by
  have h := latticeCarry_cast hq hval ha
  have hle : (q : ℝ) * trueNormalizedState a ≤ (q : ℝ) * (90 * ((a + 1 : ℕ) : ℝ) ^ 2) :=
    trueNormalizedState_mul_le a (by exact_mod_cast hq.le)
  rw [← h] at hle
  have hle' : ((latticeCarry q a : ℤ) : ℝ) ≤ ((q * ((90 * (a + 1) ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) := by
    push_cast
    push_cast at hle
    linarith
  exact_mod_cast hle'

/-- The width used as the short bound of the bridge. -/
def bridgeWidth (n : ℕ) : ℕ := 90 * (n + 1) ^ 2

/-- The reduced carry `d_a = c_a / D_sm`. -/
noncomputable def reducedLatticeCarry (q s : ℤ) (a : ℕ) : ℤ :=
  latticeCarry q a / s

/-- **The bridge.**  A rational value `p/q` with `q = 2^α 3^β 5^γ · B`,
`gcd(B,30) = 1`, yields, from the onset `a₀ = α + 1 + 2β + 3γ` on, a reduced
integral carry `d` with

`d_(a+1) = b_a d_a - B m_a`,   `0 < d_a`,   `|d_a| ≤ B · 90 (a+1)^2`,

for the actual radix word `b = dyadicBlockBase235`, the actual ordered digit
`m = dyadicOrderedBlockDigit235`, at every `a ≥ a₀`. -/
theorem exists_reducedCarry_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ (B a₀ : ℕ) (d : ℕ → ℤ), 0 < B ∧ Nat.Coprime B 30 ∧
      (∀ n, a₀ ≤ n →
        d (n + 1) = (dyadicBlockBase235 n : ℤ) * d n
          - (B : ℤ) * (dyadicOrderedBlockDigit235 n : ℤ)) ∧
      (∀ n, a₀ ≤ n → 0 < d n) ∧
      (∀ n, a₀ ≤ n → Int.natAbs (d n) ≤ B * bridgeWidth n) := by
  obtain ⟨α, β, γ, B, hqeq, hBpos, hBcop⟩ :=
    exists_smooth_coprime_split q.toNat (by omega)
  set s : ℕ := 2 ^ α * 3 ^ β * 5 ^ γ with hs
  have hsPos : 0 < s := by positivity
  have hqs : q = ((s : ℕ) : ℤ) * ((B : ℕ) : ℤ) := by
    have hnat : q.toNat = s * B := by rw [hqeq]
    have := Int.toNat_of_nonneg hq.le
    rw [← this, hnat]
    push_cast
    ring
  set a₀ : ℕ := α + 1 + 2 * β + 3 * γ with ha₀
  have ha₀1 : 1 ≤ a₀ := by omega
  have hsdvd : ∀ n, a₀ ≤ n → ((s : ℕ) : ℤ) ∣ latticeCarry q n := by
    intro n hn
    refine smooth_dvd_latticeCarry hq hval ?_ (by omega) ?_
    · rw [hqs]
      exact dvd_mul_right _ _
    · exact_mod_cast smooth_dvd_heightNormalizer235 (a := n) (by omega)
  have hfac : ∀ k, a₀ ≤ k →
      latticeCarry q k = ((s : ℕ) : ℤ) * reducedLatticeCarry q (s : ℤ) k := by
    intro k hk
    unfold reducedLatticeCarry
    exact (Int.mul_ediv_cancel' (hsdvd k hk)).symm
  have hsne : ((s : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hsPos.ne'
  have hsZ : (0 : ℤ) < ((s : ℕ) : ℤ) := by exact_mod_cast hsPos
  -- `set` hides `q` inside the reduced carry, so rewriting `q = s · B` below
  -- cannot accidentally rewrite the carry's own denominator argument.
  set d : ℕ → ℤ := reducedLatticeCarry q (s : ℤ) with hdset
  refine ⟨B, a₀, d, hBpos, hBcop, ?_, ?_, ?_⟩
  · intro n hn
    have hrec := latticeCarry_succ hq hval (a := n) (by omega)
    rw [hfac n hn, hfac (n + 1) (by omega)] at hrec
    apply mul_left_cancel₀ hsne
    rw [hrec]
    linear_combination (-(dyadicOrderedBlockDigit235 n : ℤ)) * hqs
  · intro n hn
    have hpos := latticeCarry_pos hq hval (a := n) (by omega)
    rw [hfac n hn] at hpos
    exact pos_of_mul_pos_right hpos hsZ.le
  · intro n hn
    have hle := latticeCarry_le hq hval (a := n) (by omega)
    have hpos := latticeCarry_pos hq hval (a := n) (by omega)
    rw [hfac n hn] at hle hpos
    have hdpos : 0 < d n := pos_of_mul_pos_right hpos hsZ.le
    have hdle : d n ≤ ((B : ℕ) : ℤ) * ((90 * (n + 1) ^ 2 : ℕ) : ℤ) := by
      have h' : ((s : ℕ) : ℤ) * d n
          ≤ ((s : ℕ) : ℤ) * (((B : ℕ) : ℤ) * ((90 * (n + 1) ^ 2 : ℕ) : ℤ)) := by
        calc ((s : ℕ) : ℤ) * d n
            ≤ q * ((90 * (n + 1) ^ 2 : ℕ) : ℤ) := hle
          _ = ((s : ℕ) : ℤ) * (((B : ℕ) : ℤ) * ((90 * (n + 1) ^ 2 : ℕ) : ℤ)) := by
              rw [hqs]; ring
      exact le_of_mul_le_mul_left h' hsZ
    have hcast : ((B * bridgeWidth n : ℕ) : ℤ)
        = ((B : ℕ) : ℤ) * ((90 * (n + 1) ^ 2 : ℕ) : ℤ) := by
      unfold bridgeWidth
      push_cast
      ring
    rw [← hcast] at hdle
    omega

/-! ## Consequence: the producer implies irrationality -/

/-- The paper's Problem `prob:producer` (9.5), stated for the actual radix
word, the actual ordered digit and the short bound `B · 90 (n+1)^2`. -/
def ActualCofinalLocalWindowEscape : Prop :=
  CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235
    (fun B n => B * bridgeWidth n)

/-- Under the actual escape producer, the value is not `p/q` for any `q > 0`. -/
theorem value_ne_rat_of_cofinalLocalWindowEscape
    (hescape : ActualCofinalLocalWindowEscape) {p q : ℤ} (hq : 0 < q) :
    dyadicShellTsumTailR235 1 ≠ (p : ℝ) / (q : ℝ) := by
  intro hval
  obtain ⟨B, a₀, d, hBpos, hBcop, hrec, hpos, hbound⟩ :=
    exists_reducedCarry_of_value_eq_rat hq hval
  exact no_positive_reducedCarry_of_cofinalLocalWindowEscape_onset
    dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun B n => B * bridgeWidth n)
    hescape B hBpos hBcop a₀ d hrec hpos hbound

/-- **Bridge consequence.**  The actual cofinal local-window escape implies
that `Σ_{h ≥ 2} 1/H(h) = S - 1` is irrational. -/
theorem irrational_of_cofinalLocalWindowEscape
    (hescape : ActualCofinalLocalWindowEscape) :
    Irrational (dyadicShellTsumTailR235 1) := by
  rw [irrational_iff_ne_rational]
  intro a b hb
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have h := value_ne_rat_of_cofinalLocalWindowEscape hescape (p := -a) (q := -b)
      (by omega)
    intro heq
    apply h
    rw [heq]
    push_cast
    rw [neg_div_neg_eq]
  · exact value_ne_rat_of_cofinalLocalWindowEscape hescape hpos

/-- The zeroth shell is the single point `1`, with height `1`. -/
theorem dyadicSmoothShell235_zero : dyadicSmoothShell235 0 = {(0, 0, 0)} := by
  ext e
  rcases e with ⟨i, j, k⟩
  rw [mem_dyadicSmoothShell235_iff, Finset.mem_singleton]
  simp only [smooth3Val, pow_zero, pow_one]
  constructor
  · rintro ⟨-, hlt⟩
    have h2 : 2 ^ i ≤ 2 ^ i * 3 ^ j * 5 ^ k :=
      (Nat.le_mul_of_pos_right _ (by positivity)).trans
        (Nat.le_mul_of_pos_right _ (by positivity))
    have h3 : 3 ^ j ≤ 2 ^ i * 3 ^ j * 5 ^ k :=
      (Nat.le_mul_of_pos_left _ (by positivity)).trans
        (Nat.le_mul_of_pos_right _ (by positivity))
    have h5 : 5 ^ k ≤ 2 ^ i * 3 ^ j * 5 ^ k :=
      Nat.le_mul_of_pos_left _ (by positivity)
    have hi : i = 0 := by
      by_contra hne
      have : 2 ≤ 2 ^ i := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hne)
      omega
    have hj : j = 0 := by
      by_contra hne
      have : 3 ≤ 3 ^ j := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hne)
      omega
    have hk : k = 0 := by
      by_contra hne
      have : 5 ≤ 5 ^ k := by
        calc 5 = 5 ^ 1 := by norm_num
          _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hne)
      omega
    simp [hi, hj, hk]
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem dyadicShellMassR235_zero : dyadicShellMassR235 0 = 1 := by
  unfold dyadicShellMassR235 dyadicShellMassQ235
  rw [dyadicSmoothShell235_zero, Finset.sum_singleton]
  simp [smooth3Val, threePrimeHeight]

/-- The Erdős #269 value `Σ_{h ≥ 1} 1/H(h)` is `1 + Σ_{h ≥ 2} 1/H(h)`. -/
theorem dyadicShellTsumTailR235_zero_eq :
    dyadicShellTsumTailR235 0 = 1 + dyadicShellTsumTailR235 1 := by
  rw [dyadicShellTsumTailR235_eq_shell_add 0, dyadicShellMassR235_zero]

/-- **Headline form of the bridge.**  The actual cofinal local-window escape
implies that the Erdős #269 value `Σ_{h ∈ ⟨2,3,5⟩} 1/H(h)` is irrational. -/
theorem irrational_value_of_cofinalLocalWindowEscape
    (hescape : ActualCofinalLocalWindowEscape) :
    Irrational (dyadicShellTsumTailR235 0) := by
  rw [dyadicShellTsumTailR235_zero_eq, add_comm]
  simpa using (irrational_of_cofinalLocalWindowEscape hescape).add_natCast 1

end ErdosProblems.Erdos269
