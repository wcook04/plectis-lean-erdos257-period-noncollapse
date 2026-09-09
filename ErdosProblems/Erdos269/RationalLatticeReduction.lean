import ErdosProblems.Erdos269.DyadicShellSummability
import ErdosProblems.Erdos269.ThreePrimeRunningLcm

/-!
# Erdős #269: rationality forces an all-scale lattice, and the collision target

Let `S = ∑_{smooth s ≥ 2} 1/H(s)` with `H` the running `{2,3,5}` LCM height, and
let `X_a = (H(2^a)/2) · T_a` be the normalized dyadic tail state.

Three things are proved here.

1.  **Clearing at every prime-power boundary.**  For `p ∈ {2,3,5}`, `m ≥ 1` and
    every smooth `x < p^m`, one has `p · H(x) ∣ H(p^m)`.  The dyadic case
    `p = 2` is the clearing used by the tail recurrence; the `p = 3` and
    `p = 5` cases are new and give two further families of boundaries at which
    the same rational prefix clears.

2.  **All-scale rationality lattice.**  If `S = p/q` then *every* `X_a` lies on
    the `(1/q)`-lattice simultaneously, with an explicit integer witness.  This
    is the arithmetic reduction, no irrationality claim.

3.  **The collision target.**  Rationality does not merely produce one
    exceptional integral state: by pigeonhole on `(1/q)ℤ / ℤ` it forces two
    distinct scales whose tail states differ by an *integer*.  Contrapositive:
    if the normalized tail states are pairwise incongruent mod `1`, then `S` is
    irrational.  The `q = 1` "integral state" branch is the special case
    `X_a - 0 ∈ ℤ`; the collision statement covers every denominator at once.

Nothing here claims irrationality.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-! ### Monomial clearing -/

/-- Divisibility of `{2,3,5}` monomials is exponentwise. -/
theorem monomial235_dvd {a b c a' b' c' : ℕ}
    (h2 : a ≤ a') (h3 : b ≤ b') (h5 : c ≤ c') :
    2 ^ a * 3 ^ b * 5 ^ c ∣ 2 ^ a' * 3 ^ b' * 5 ^ c' :=
  mul_dvd_mul (mul_dvd_mul (pow_dvd_pow 2 h2) (pow_dvd_pow 3 h3)) (pow_dvd_pow 5 h5)

/-- **Prime-power boundary clearing.**  Every `{2,3,5}`-smooth point strictly
below the boundary `p ^ m` has running height dividing `H(p^m)/p`, stated in the
division-free form `p · H(x) ∣ H(p^m)`.

The point is that only the `p`-exponent has to be pushed down by one: below
`p ^ m` the `p`-exponent is at most `m - 1`, while the two other exponents are
monotone and so are already dominated. -/
theorem smoothHeight_mul_prime_dvd_boundaryHeight
    {p m x : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (hx : 0 < x) (hlt : x < p ^ m) :
    p * threePrimeHeight 2 3 5 x ∣ threePrimeHeight 2 3 5 (p ^ m) := by
  have hxne : x ≠ 0 := hx.ne'
  rcases hp with rfl | rfl | rfl
  · have hlog : Nat.log 2 x < m := Nat.log_lt_of_lt_pow hxne hlt
    have hpow : Nat.log 2 (2 ^ m) = m := Nat.log_pow (by norm_num) m
    have h3 : Nat.log 3 x ≤ Nat.log 3 (2 ^ m) := Nat.log_mono_right hlt.le
    have h5 : Nat.log 5 x ≤ Nat.log 5 (2 ^ m) := Nat.log_mono_right hlt.le
    have hleft : 2 * threePrimeHeight 2 3 5 x
        = 2 ^ (Nat.log 2 x + 1) * 3 ^ Nat.log 3 x * 5 ^ Nat.log 5 x := by
      unfold threePrimeHeight; ring
    have hright : threePrimeHeight 2 3 5 (2 ^ m)
        = 2 ^ m * 3 ^ Nat.log 3 (2 ^ m) * 5 ^ Nat.log 5 (2 ^ m) := by
      unfold threePrimeHeight; rw [hpow]
    rw [hleft, hright]
    exact monomial235_dvd hlog h3 h5
  · have hlog : Nat.log 3 x < m := Nat.log_lt_of_lt_pow hxne hlt
    have hpow : Nat.log 3 (3 ^ m) = m := Nat.log_pow (by norm_num) m
    have h2 : Nat.log 2 x ≤ Nat.log 2 (3 ^ m) := Nat.log_mono_right hlt.le
    have h5 : Nat.log 5 x ≤ Nat.log 5 (3 ^ m) := Nat.log_mono_right hlt.le
    have hleft : 3 * threePrimeHeight 2 3 5 x
        = 2 ^ Nat.log 2 x * 3 ^ (Nat.log 3 x + 1) * 5 ^ Nat.log 5 x := by
      unfold threePrimeHeight; ring
    have hright : threePrimeHeight 2 3 5 (3 ^ m)
        = 2 ^ Nat.log 2 (3 ^ m) * 3 ^ m * 5 ^ Nat.log 5 (3 ^ m) := by
      unfold threePrimeHeight; rw [hpow]
    rw [hleft, hright]
    exact monomial235_dvd h2 hlog h5
  · have hlog : Nat.log 5 x < m := Nat.log_lt_of_lt_pow hxne hlt
    have hpow : Nat.log 5 (5 ^ m) = m := Nat.log_pow (by norm_num) m
    have h2 : Nat.log 2 x ≤ Nat.log 2 (5 ^ m) := Nat.log_mono_right hlt.le
    have h3 : Nat.log 3 x ≤ Nat.log 3 (5 ^ m) := Nat.log_mono_right hlt.le
    have hleft : 5 * threePrimeHeight 2 3 5 x
        = 2 ^ Nat.log 2 x * 3 ^ Nat.log 3 x * 5 ^ (Nat.log 5 x + 1) := by
      unfold threePrimeHeight; ring
    have hright : threePrimeHeight 2 3 5 (5 ^ m)
        = 2 ^ Nat.log 2 (5 ^ m) * 3 ^ Nat.log 3 (5 ^ m) * 5 ^ m := by
      unfold threePrimeHeight; rw [hpow]
    rw [hleft, hright]
    exact monomial235_dvd h2 h3 hlog

/-! ### The dyadic half-height normalizer -/

/-- Half-height normalizer at scale `a`: the coefficient of the normalized tail
state and the clearing denominator of the smooth prefix. -/
def heightNormalizer235 (a : ℕ) : ℕ :=
  threePrimeHeight 2 3 5 (2 ^ a) / 2

/-- The half-height normalizer really is half the endpoint height. -/
theorem two_mul_heightNormalizer235 (a : ℕ) (ha : 1 ≤ a) :
    2 * heightNormalizer235 a = threePrimeHeight 2 3 5 (2 ^ a) := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have hlog : Nat.log 2 (2 ^ (n + 1)) = n + 1 := Nat.log_pow (by norm_num) _
  have hdvd : 2 ∣ threePrimeHeight 2 3 5 (2 ^ (n + 1)) := by
    unfold threePrimeHeight
    rw [hlog]
    exact ⟨2 ^ n * 3 ^ Nat.log 3 (2 ^ (n + 1)) * 5 ^ Nat.log 5 (2 ^ (n + 1)), by ring⟩
  exact Nat.two_mul_div_two_of_even (even_iff_two_dvd.mpr hdvd)

/-- Clearing divisibility at a dyadic boundary: the running height of any smooth
point below `2 ^ a` divides the scale-`a` half-height normalizer. -/
theorem threePrimeHeight_smooth_dvd_heightNormalizer235
    {a i j k : ℕ} (hs : smooth3Val 2 3 5 i j k < 2 ^ a) :
    threePrimeHeight 2 3 5 (smooth3Val 2 3 5 i j k) ∣ heightNormalizer235 a := by
  have hsPos : 0 < smooth3Val 2 3 5 i j k := by
    simp only [smooth3Val]
    positivity
  have haPos : 1 ≤ a := by
    by_contra hcon
    have ha0 : a = 0 := by omega
    subst ha0
    rw [pow_zero] at hs
    omega
  have hmul := smoothHeight_mul_prime_dvd_boundaryHeight
    (p := 2) (m := a) (Or.inl rfl) hsPos hs
  rw [← two_mul_heightNormalizer235 a haPos] at hmul
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hmul

/-! ### Clearing the rational prefix -/

/-- The scale-`A` normalizer clears one whole shell below the scale. -/
theorem heightNormalizer235_mul_shellMass_eq_nat {A a : ℕ} (hlt : a < A) :
    (heightNormalizer235 A : ℚ) * dyadicShellMassQ235 a
      = ((∑ e ∈ dyadicSmoothShell235 a,
            heightNormalizer235 A /
              threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℕ) : ℚ) := by
  classical
  rw [dyadicShellMassQ235, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hbound : smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < 2 ^ A := by
    refine lt_of_lt_of_le (mem_dyadicSmoothShell235_iff.mp he).2 ?_
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdvd := threePrimeHeight_smooth_dvd_heightNormalizer235 hbound
  have hpos : 0 < threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) := by
    unfold threePrimeHeight; positivity
  have hne : ((threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  rw [Nat.cast_div hdvd hne]
  field_simp

/-- Rational mass of the smooth window `[start, start + count)` of shells. -/
def dyadicSmoothWindowMassQ235 (start count : ℕ) : ℚ :=
  ∑ i ∈ Finset.range count, dyadicShellMassQ235 (start + i)

/-- **Prefix clearing.**  The half-height normalizer at the top of a window
clears the entire rational window mass to an integer. -/
theorem heightNormalizer235_mul_windowMass_eq_int (start count : ℕ) :
    ∃ z : ℕ,
      (heightNormalizer235 (start + count) : ℚ) *
        dyadicSmoothWindowMassQ235 start count = (z : ℚ) := by
  classical
  refine ⟨∑ i ∈ Finset.range count,
      ∑ e ∈ dyadicSmoothShell235 (start + i),
        heightNormalizer235 (start + count) /
          threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2), ?_⟩
  rw [dyadicSmoothWindowMassQ235, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hlt : start + i < start + count := by
    have := Finset.mem_range.mp hi
    omega
  exact heightNormalizer235_mul_shellMass_eq_nat hlt

/-- The convergent shell tail splits into a finite prefix window plus the later
tail, at any offset and depth. -/
theorem dyadicShellTsumTailR235_eq_range_add (a k : ℕ) :
    dyadicShellTsumTailR235 a =
      ∑ i ∈ Finset.range k, dyadicShellMassR235 (a + i) +
        dyadicShellTsumTailR235 (a + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : dyadicShellTsumTailR235 (a + k)
          = dyadicShellMassR235 (a + k) + dyadicShellTsumTailR235 (a + k + 1) :=
        dyadicShellTsumTailR235_eq_shell_add (a + k)
      rw [hstep, show a + (k + 1) = a + k + 1 from rfl]
      ring

/-! ### The all-scale lattice -/

/-- **All-scale rationality lattice.**  If the running-LCM series value is
rational with denominator `q`, then every normalized dyadic tail state is
`(1/q)`-integral simultaneously, with the explicit integer witness
`p · H(2^a)/2 - q · (cleared prefix)`. -/
theorem qsmul_normalizedTailState_eq_int_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    ∃ k : ℤ,
      (q : ℝ) * dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a
        = (k : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = 1 + m := ⟨a - 1, by omega⟩
  have hsplit := dyadicShellTsumTailR235_eq_range_add 1 m
  set prefQ : ℚ := dyadicSmoothWindowMassQ235 1 m with hprefQ
  have hprefR : (∑ i ∈ Finset.range m, dyadicShellMassR235 (1 + i)) = (prefQ : ℝ) := by
    simp only [hprefQ, dyadicSmoothWindowMassQ235, dyadicShellMassR235, Rat.cast_sum]
  obtain ⟨z, hz⟩ := heightNormalizer235_mul_windowMass_eq_int 1 m
  have hnorm : dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + m)
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * dyadicShellTsumTailR235 (1 + m) := by
    unfold dyadicNormalizedTailStateR235
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
  have hqtail : (q : ℝ) * dyadicShellTsumTailR235 (1 + m)
      = (p : ℝ) - (q : ℝ) * (prefQ : ℝ) := by
    rw [htail, mul_sub, hqp]
  refine ⟨(heightNormalizer235 (1 + m) : ℤ) * p - q * (z : ℤ), ?_⟩
  have hcast : (((heightNormalizer235 (1 + m) : ℤ) * p - q * (z : ℤ) : ℤ) : ℝ)
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (p : ℝ) - (q : ℝ) * ((z : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, hnorm]
  calc (q : ℝ) *
        (((heightNormalizer235 (1 + m) : ℕ) : ℝ) * dyadicShellTsumTailR235 (1 + m))
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ)
          * ((q : ℝ) * dyadicShellTsumTailR235 (1 + m)) := by ring
    _ = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * ((p : ℝ) - (q : ℝ) * (prefQ : ℝ)) := by
          rw [hqtail]
    _ = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (p : ℝ)
          - (q : ℝ) * (((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (prefQ : ℝ)) := by ring
    _ = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (p : ℝ) - (q : ℝ) * ((z : ℕ) : ℝ) := by
          rw [hzR]

/-! ### The collision target -/

/-- Pigeonhole: a real sequence all of whose `q`-multiples are integers has two
distinct indices whose values differ by an integer.  There are at most `q`
residues available mod `1`. -/
theorem exists_int_sub_of_qsmul_int {q : ℤ} (hq : 0 < q) (x : ℕ → ℝ)
    (h : ∀ n : ℕ, ∃ k : ℤ, (q : ℝ) * x n = (k : ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ z : ℤ, x j - x i = (z : ℝ) := by
  classical
  choose k hk using h
  set Q : ℕ := q.toNat with hQ
  have hQpos : 0 < Q := by omega
  have hQcast : ((Q : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq.le
  haveI : NeZero Q := ⟨hQpos.ne'⟩
  have hcard : (Finset.univ : Finset (ZMod Q)).card < (Finset.range (Q + 1)).card := by
    simpa [Finset.card_univ, ZMod.card] using Nat.lt_succ_self Q
  obtain ⟨i, -, j, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (f := fun n : ℕ => ((k n : ℤ) : ZMod Q)) hcard (fun n _ => Finset.mem_univ _)
  have hdvd : ∀ u v : ℕ,
      ((k u : ℤ) : ZMod Q) = ((k v : ℤ) : ZMod Q) → (q : ℤ) ∣ k v - k u := by
    intro u v huv
    have hzero : (((k v - k u : ℤ)) : ZMod Q) = 0 := by
      push_cast
      rw [huv]
      ring
    have hd : ((Q : ℕ) : ℤ) ∣ (k v - k u) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
    rwa [hQcast] at hd
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have main : ∀ u v : ℕ, (q : ℤ) ∣ k v - k u → ∃ z : ℤ, x v - x u = (z : ℝ) := by
    intro u v hd
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    have hmul : (q : ℝ) * (x v - x u) = (q : ℝ) * (z : ℝ) := by
      rw [mul_sub, hk v, hk u, ← Int.cast_sub, hz]
      push_cast
      ring
    exact mul_left_cancel₀ hqne hmul
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨i, j, hlt, main i j (hdvd i j heq)⟩
  · exact ⟨j, i, hlt, main j i (hdvd j i heq.symm)⟩

/-- **Collision target.**  If `S` is rational then two distinct dyadic scales
carry normalized tail states differing by an integer.  Contrapositive: if the
normalized tail states are pairwise incongruent modulo `1`, `S` is irrational.

The classical "exceptional integral state" branch is the sub-case in which one
state is congruent to `0`; this statement covers every denominator at once. -/
theorem exists_normalizedTailState_collision_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ z : ℤ,
      dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + j) -
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + i) = (z : ℝ) :=
  exists_int_sub_of_qsmul_int hq
    (fun n => dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + n))
    (fun n => qsmul_normalizedTailState_eq_int_of_value_eq_rat hq hval (by omega))

end ErdosProblems.Erdos269
