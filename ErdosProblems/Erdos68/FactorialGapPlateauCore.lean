import ErdosProblems.Erdos68.CanonicalFactorialDigits
import ErdosProblems.Erdos68.PrimeUnitTranslator
import ErdosProblems.Erdos68.StrictSuccessorArithmetic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Erdős #68: factorial-gap plateau core

Lightweight core for the strict-successor recurrence, carry bounds, and the
exact divisibility criterion.  Heavy exact-index certificates live in
`FactorialZeroPlateauCertificates`; the full plateau file re-exports both.
-/
namespace ErdosProblems.Erdos68

/-! ## Factorial grid arithmetic -/

/-- Strict successor of the factorially scaled prefix. -/
noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1

/-- Computable rational form of `strictFacTop`, used for exact finite
certificates while retaining the real-valued statement needed for the
series. -/
def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

/-- The rational and real strict-successor implementations agree exactly. -/
theorem strictFacTop_ratCast (x : ℚ) (n : ℕ) :
    strictFacTop (x : ℝ) n = strictFacTopRat x n := by
  unfold strictFacTop strictFacTopRat
  rw [← Rat.cast_natCast, ← Rat.cast_mul, Rat.floor_cast]

/-- After normalization by `n!`, the strict successor lies in the
one-factorial-cell interval immediately above its input. -/
theorem strictFacTop_div_factorial_bounds (x : ℝ) (n : ℕ) :
    x < (strictFacTop x n : ℝ) / (n.factorial : ℝ) ∧
      (strictFacTop x n : ℝ) / (n.factorial : ℝ) ≤
        x + 1 / (n.factorial : ℝ) := by
  have hfac : (0 : ℝ) < n.factorial := by positivity
  constructor
  · rw [lt_div_iff₀ hfac]
    unfold strictFacTop
    push_cast
    simpa [mul_comm] using
      Int.lt_floor_add_one ((n.factorial : ℝ) * x)
  · rw [div_le_iff₀ hfac]
    have hfloor := Int.floor_le ((n.factorial : ℝ) * x)
    calc
      (strictFacTop x n : ℝ) =
          (⌊(n.factorial : ℝ) * x⌋ : ℝ) + 1 := by
            unfold strictFacTop
            push_cast
            rfl
      _ ≤ (n.factorial : ℝ) * x + 1 := by linarith
      _ = (x + 1 / (n.factorial : ℝ)) *
          (n.factorial : ℝ) := by
            field_simp

/-- Algebraic form of the grid crossing.  If `q*S` is obtained from
`q*H = k+r` by adding the scaled tail `u`, then the next `q⁻¹` grid point
lies below `S` exactly when the fractional pieces cross one. -/
theorem rationalGridPoint_le_iff_crosses
    {q : ℕ} {S H r u : ℚ} {k : ℤ}
    (hq : 0 < q)
    (hH : (q : ℚ) * H = (k : ℚ) + r)
    (htail : (q : ℚ) * (S - H) = u) :
    ((k + 1 : ℤ) : ℚ) / q ≤ S ↔ 1 ≤ r + u := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have htotal : (q : ℚ) * S = (k : ℚ) + r + u := by
    linarith
  have htotalRight : S * (q : ℚ) = (k : ℚ) + r + u := by
    simpa [mul_comm] using htotal
  rw [div_le_iff₀ hqQ]
  push_cast
  rw [htotalRight]
  constructor <;> intro h <;> linarith

/-- A factorial grid point between a prefix value `H` and a target `S`
forces both the strict successor of `n!H` and the canonical floor of `n!S`
to equal the same grid integer, provided the remaining factorial tail is
strictly shorter than one grid unit. -/
theorem factorialGrid_plateau
    {n : ℕ} {H G S : ℝ} {z : ℤ}
    (hHG : H < G)
    (hGS : G ≤ S)
    (htail : (n.factorial : ℝ) * (S - H) < 1)
    (hgrid : (n.factorial : ℝ) * G = (z : ℝ)) :
    strictFacTop H n = z ∧ facFloor S n = z := by
  have hfacPos : (0 : ℝ) < n.factorial := by positivity
  have hscaledHG : (n.factorial : ℝ) * H < (z : ℝ) := by
    rw [← hgrid]
    exact mul_lt_mul_of_pos_left hHG hfacPos
  have hgridGap :
      (n.factorial : ℝ) * (G - H) < 1 := by
    have hGHle : G - H ≤ S - H := by linarith
    have hmul :
        (n.factorial : ℝ) * (G - H) ≤
          (n.factorial : ℝ) * (S - H) :=
      mul_le_mul_of_nonneg_left hGHle hfacPos.le
    linarith
  have hscaledHLower :
      ((z - 1 : ℤ) : ℝ) ≤ (n.factorial : ℝ) * H := by
    push_cast
    rw [← hgrid]
    nlinarith
  have hfloorH :
      ⌊(n.factorial : ℝ) * H⌋ = z - 1 := by
    exact Int.floor_eq_iff.mpr ⟨hscaledHLower, by
      push_cast
      simpa using hscaledHG⟩
  have hscaledSLower :
      (z : ℝ) ≤ (n.factorial : ℝ) * S := by
    rw [← hgrid]
    exact mul_le_mul_of_nonneg_left hGS hfacPos.le
  have hscaledSUpper :
      (n.factorial : ℝ) * S < (z : ℝ) + 1 := by
    rw [← hgrid]
    nlinarith
  constructor
  · simp [strictFacTop, hfloorH]
  · unfold facFloor
    exact Int.floor_eq_iff.mpr ⟨hscaledSLower, hscaledSUpper⟩

/-- If a rational target with denominator `q` lies above a prefix by less
than one factorial grid unit, then at every dilated prime index `k p`
whose factorial clears `q`, the strict factorial successor is divisible by
`p^k`.  Thus a rational value of the series imposes a prime-power
divisibility condition on the strict factorial successor. -/
theorem prime_pow_dvd_strictFacTop_of_rational_target
    {p k q : ℕ} {a : ℤ}
    (hp : p.Prime)
    (hq : 0 < q)
    (hqn : q ≤ k * p)
    (hpq : ¬p ∣ q)
    {H : ℝ}
    (hH : H < (a : ℝ) / (q : ℝ))
    (htail :
      (((k * p).factorial : ℝ) *
        ((a : ℝ) / (q : ℝ) - H)) < 1) :
    (p : ℤ) ^ k ∣ strictFacTop H (k * p) := by
  have hqfac : q ∣ (k * p).factorial :=
    Nat.dvd_factorial hq hqn
  have hfac :
      q * ((k * p).factorial / q) = (k * p).factorial :=
    Nat.mul_div_cancel' hqfac
  have hfacR :
      (q : ℝ) * (((k * p).factorial / q : ℕ) : ℝ) =
        ((k * p).factorial : ℝ) := by
    exact_mod_cast hfac
  have hgridR :
      (((k * p).factorial : ℝ) * ((a : ℝ) / (q : ℝ))) =
        (((((k * p).factorial / q : ℕ) : ℤ) * a : ℤ) : ℝ) := by
    calc
      (((k * p).factorial : ℝ) * ((a : ℝ) / (q : ℝ))) =
          ((q : ℝ) * (((k * p).factorial / q : ℕ) : ℝ)) *
            ((a : ℝ) / (q : ℝ)) := by rw [hfacR]
      _ = (((k * p).factorial / q : ℕ) : ℝ) * (a : ℝ) := by
        field_simp
      _ = (((((k * p).factorial / q : ℕ) : ℤ) * a : ℤ) : ℝ) := by
        simp only [Int.cast_mul, Int.cast_natCast]
  have hplateau :=
    factorialGrid_plateau hH le_rfl htail hgridR
  have hpPow : p ^ k ∣ (k * p).factorial := by
    rw [Nat.mul_comm]
    apply pow_dvd_iff_le_emultiplicity.mpr
    rw [hp.emultiplicity_factorial_mul]
    simp
  have hcop : (p ^ k).Coprime q :=
    (hp.coprime_iff_not_dvd.mpr hpq).pow_left k
  have hpCleared : p ^ k ∣ (k * p).factorial / q := by
    apply hcop.dvd_of_dvd_mul_left
    rw [hfac]
    exact hpPow
  have hpClearedInt :
      (p : ℤ) ^ k ∣ (((k * p).factorial / q : ℕ) : ℤ) := by
    exact_mod_cast hpCleared
  have hpowInt :
      (p : ℤ) ^ k ∣
        (((k * p).factorial / q : ℕ) : ℤ) * a :=
    dvd_mul_of_dvd_left hpClearedInt a
  rw [hplateau.1]
  exact hpowInt

/-- Consecutive plateau floors whose grid integers scale by the next radix
force the corresponding canonical factorial digit to vanish. -/
theorem canonicalDigit_eq_zero_of_plateau
    {x : ℝ} {m : ℕ} {z zPrev : ℤ}
    (hfloor : facFloor x m = z)
    (hfloorPrev : facFloor x (m - 1) = zPrev)
    (hscale : z = (m : ℤ) * zPrev) :
    canonicalDigit x m = 0 := by
  simp [canonicalDigit, hfloor, hfloorPrev, hscale]

/-- If the first-exit offset lies in `[0,2)`, the strict-successor carry
`-floor δ` is rigidly either zero or minus one. -/
theorem firstExit_carry_rigid
    {δ : ℝ} {b : ℤ}
    (hδ0 : 0 ≤ δ)
    (hδ2 : δ < 2)
    (hb : b = -⌊δ⌋) :
    b = 0 ∨ b = -1 := by
  have hfloor0 : 0 ≤ ⌊δ⌋ := Int.floor_nonneg.mpr hδ0
  have hfloor2 : ⌊δ⌋ < 2 := Int.floor_lt.mpr hδ2
  omega

/-! ## Exact prefixes and prime-power divisibility -/

/-- Finite geometric peeling of a factorial-gap denominator.  The first `K`
terms are pure powers of `x`; all non-factorial denominator content is
confined to the final residual. -/
theorem one_div_sub_one_geometric_split
    {x : ℚ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) (K : ℕ) :
    1 / (x - 1) =
      (∑ j ∈ Finset.range K, 1 / x ^ (j + 1)) +
        1 / (x ^ K * (x - 1)) := by
  have hxSub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  induction K with
  | zero =>
      simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have hresidual :
          1 / (x ^ K * (x - 1)) =
            1 / x ^ (K + 1) +
              1 / (x ^ (K + 1) * (x - 1)) := by
        field_simp [hx0, hxSub]
        ring
      calc
        1 / (x - 1) =
            (∑ j ∈ Finset.range K, 1 / x ^ (j + 1)) +
              1 / (x ^ K * (x - 1)) := ih
        _ =
            (∑ j ∈ Finset.range K, 1 / x ^ (j + 1)) +
              (1 / x ^ (K + 1) +
                1 / (x ^ (K + 1) * (x - 1))) := by
          rw [hresidual]
        _ =
            (∑ j ∈ Finset.range K, 1 / x ^ (j + 1)) +
              1 / x ^ (K + 1) +
                1 / (x ^ (K + 1) * (x - 1)) := by
          ring

/-- The exact rational prefix of the Erdős #68 series through index `n`. -/
def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

/-- Casting the exact rational prefix to the reals gives the finite real
prefix used in the analytic tail decomposition. -/
theorem factorialGapPrefix_cast (n : ℕ) :
    ((factorialGapPrefix n : ℚ) : ℝ) =
      ∑ k ∈ Finset.Icc 2 n,
        (1 : ℝ) /
          ((((k.factorial : ℤ) - 1 : ℤ) : ℝ)) := by
  unfold factorialGapPrefix
  push_cast
  rfl

/-- A rational value for the Erdős #68 series forces the expected
`p^k` divisibility of the actual prefix strict successor at every
factorial index `k p` clearing the denominator and coprime to it. -/
theorem prime_pow_dvd_strictFacTop_factorialGapPrefix_of_series_eq_rat
    {p k q : ℕ} {a : ℤ}
    (hp : p.Prime)
    (hq : 0 < q)
    (hqn : q ≤ k * p)
    (hpq : ¬p ∣ q)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    (p : ℤ) ^ k ∣
      strictFacTop
        ((factorialGapPrefix (k * p) : ℚ) : ℝ) (k * p) := by
  have hD : 2 ≤ k * p := by
    have hp2 : 2 ≤ p := hp.two_le
    have hk : 0 < k := by
      by_contra hk0
      have : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      simp at hqn
      omega
    nlinarith
  have hdecomp :=
    _root_.Erdos68.factorialGapSeries_eq_sum_add_tail hD
  have hprefix := factorialGapPrefix_cast (k * p)
  have htailEq :
      (a : ℝ) / (q : ℝ) -
          ((factorialGapPrefix (k * p) : ℚ) : ℝ) =
        _root_.Erdos68.factorialGapTail (k * p) := by
    rw [← hseries, hdecomp, hprefix]
    ring
  have htailPos :=
    _root_.Erdos68.factorialGapTail_pos hD
  have hH :
      ((factorialGapPrefix (k * p) : ℚ) : ℝ) <
        (a : ℝ) / (q : ℝ) := by
    rw [sub_eq_iff_eq_add] at htailEq
    linarith
  have htailLt :=
    _root_.Erdos68.factorialGapTail_lt_one_div_factorial hD
  have hfacPos : (0 : ℝ) < (k * p).factorial := by positivity
  have hscaled :
      (((k * p).factorial : ℝ) *
        ((a : ℝ) / (q : ℝ) -
          ((factorialGapPrefix (k * p) : ℚ) : ℝ))) < 1 := by
    rw [htailEq]
    have hmul := mul_lt_mul_of_pos_left htailLt hfacPos
    simpa [ne_of_gt hfacPos] using hmul
  exact prime_pow_dvd_strictFacTop_of_rational_target
    hp hq hqn hpq hH hscaled

/-- Once `n!` clears a displayed rational denominator, the strict successor
of the Erdős #68 prefix is exactly the corresponding cleared
rational grid integer.

The hypothesis is divisibility `q ∣ n!`, not the cruder size bound `q ≤ n`.
Only the divisibility is used, and it is strictly weaker: every `q ≤ n`
divides `n!`, but so does every `n`-smooth `q` of any magnitude. -/
theorem strictFacTop_factorialGapPrefix_eq_cleared_rational_of_dvd
    {n q : ℕ} {a : ℤ}
    (hn : 2 ≤ n)
    (hq : 0 < q)
    (hqfac : q ∣ n.factorial)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    strictFacTop ((factorialGapPrefix n : ℚ) : ℝ) n =
      (((n.factorial / q : ℕ) : ℤ) * a : ℤ) := by
  have hdecomp :=
    _root_.Erdos68.factorialGapSeries_eq_sum_add_tail hn
  have hprefix := factorialGapPrefix_cast n
  have htailEq :
      (a : ℝ) / (q : ℝ) -
          ((factorialGapPrefix n : ℚ) : ℝ) =
        _root_.Erdos68.factorialGapTail n := by
    rw [← hseries, hdecomp, hprefix]
    ring
  have htailPos :=
    _root_.Erdos68.factorialGapTail_pos hn
  have hH :
      ((factorialGapPrefix n : ℚ) : ℝ) <
        (a : ℝ) / (q : ℝ) := by
    rw [sub_eq_iff_eq_add] at htailEq
    linarith
  have htailLt :=
    _root_.Erdos68.factorialGapTail_lt_one_div_factorial hn
  have hfacPos : (0 : ℝ) < n.factorial := by positivity
  have hscaled :
      (n.factorial : ℝ) *
          ((a : ℝ) / (q : ℝ) -
            ((factorialGapPrefix n : ℚ) : ℝ)) < 1 := by
    rw [htailEq]
    have hmul := mul_lt_mul_of_pos_left htailLt hfacPos
    simpa [ne_of_gt hfacPos] using hmul
  have hfac :
      q * (n.factorial / q) = n.factorial :=
    Nat.mul_div_cancel' hqfac
  have hfacR :
      (q : ℝ) * ((n.factorial / q : ℕ) : ℝ) =
        (n.factorial : ℝ) := by
    exact_mod_cast hfac
  have hgrid :
      (n.factorial : ℝ) * ((a : ℝ) / (q : ℝ)) =
        (((n.factorial / q : ℕ) : ℤ) * a : ℤ) := by
    calc
      (n.factorial : ℝ) * ((a : ℝ) / (q : ℝ)) =
          ((q : ℝ) * ((n.factorial / q : ℕ) : ℝ)) *
            ((a : ℝ) / (q : ℝ)) := by rw [hfacR]
      _ = ((n.factorial / q : ℕ) : ℝ) * (a : ℝ) := by
        field_simp
      _ = (((n.factorial / q : ℕ) : ℤ) * a : ℤ) := by
        simp only [Int.cast_mul, Int.cast_natCast]
  exact (factorialGrid_plateau hH le_rfl hscaled hgrid).1

/-- Size-bound corollary of the divisibility form, kept so the existing
consumers are unchanged. -/
theorem strictFacTop_factorialGapPrefix_eq_cleared_rational
    {n q : ℕ} {a : ℤ}
    (hn : 2 ≤ n)
    (hq : 0 < q)
    (hqn : q ≤ n)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    strictFacTop ((factorialGapPrefix n : ℚ) : ℝ) n =
      (((n.factorial / q : ℕ) : ℤ) * a : ℤ) :=
  strictFacTop_factorialGapPrefix_eq_cleared_rational_of_dvd
    hn hq (Nat.dvd_factorial hq hqn) hseries

/-- One exact missed prime already gives a quantitative obstruction: the
denominator of any displayed rational value of the Erdős #68 series must be
at least that prime. -/
theorem rational_denominator_ge_of_prime_miss
    {p q : ℕ} {a : ℤ}
    (hp : p.Prime)
    (hq : 0 < q)
    (hmiss :
      ¬(p : ℤ) ∣
        strictFacTop ((factorialGapPrefix p : ℚ) : ℝ) p)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    p ≤ q := by
  by_contra hpq
  have hqp : q ≤ p := by omega
  have hcop : ¬p ∣ q := by
    intro hdiv
    have hp_le_q := Nat.le_of_dvd hq hdiv
    omega
  apply hmiss
  simpa using
    (prime_pow_dvd_strictFacTop_factorialGapPrefix_of_series_eq_rat
      (p := p) (k := 1) (q := q) (a := a)
      hp hq (by simpa using hqp) hcop hseries)

/-- Any cofinal family of fixed-exponent prime-power misses for the actual
prefix strict successors proves the irrationality of the Erdős #68
series. -/
theorem irrational_factorialGapSeries_of_cofinal_prime_power_misses
    {k : ℕ}
    (hmiss : ∀ B : ℕ, ∃ p : ℕ,
      p.Prime ∧ B < p ∧
        ¬(p : ℤ) ^ k ∣
          strictFacTop
            ((factorialGapPrefix (k * p) : ℚ) : ℝ) (k * p)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  by_contra hrat
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  obtain ⟨p, hp, hdenp, hpMiss⟩ := hmiss r.den
  have hk : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    simp at hpMiss
  have hpq : ¬p ∣ r.den := by
    intro hpd
    have hle : p ≤ r.den :=
      Nat.le_of_dvd r.den_pos hpd
    omega
  have hqn : r.den ≤ k * p := by
    have hpk : p ≤ k * p := by
      nlinarith
    omega
  apply hpMiss
  apply prime_pow_dvd_strictFacTop_factorialGapPrefix_of_series_eq_rat
    hp r.den_pos hqn hpq
  rw [hr, Rat.cast_def]

/-! ## The carry recurrence and the exact irrationality criterion -/

/-- Adding the endpoint `τ` to the actual factorial-gap prefix contributes
exactly `1 / (τ! - 1)`. -/
theorem factorialGapPrefix_eq_prev_add
    {τ : ℕ} (hτ : 2 ≤ τ) :
    factorialGapPrefix τ =
      factorialGapPrefix (τ - 1) + 1 / ((τ.factorial : ℚ) - 1) := by
  have hset :
      Finset.Icc 2 τ = insert τ (Finset.Icc 2 (τ - 1)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : τ ∉ Finset.Icc 2 (τ - 1) := by
    simp only [Finset.mem_Icc]
    omega
  rw [factorialGapPrefix, hset, Finset.sum_insert hnotmem,
    factorialGapPrefix]
  ring

/-- Distance from the strict factorial successor of the preceding actual
prefix to that scaled prefix.  Unlike an ordinary fractional-part
complement, this takes the value one when the scaled prefix is integral. -/
noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)

/-- The exact rounding carry in the strict-successor recurrence for the
Erdős #68 prefixes. -/
noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋

/-- The strict factorial successors of consecutive prefixes satisfy
an exact radix recurrence with `factorialGapStepCarry` as rounding digit. -/
theorem strictFacTop_factorialGapPrefix_step
    {m : ℕ} (hm : 2 ≤ m) :
    strictFacTop ((factorialGapPrefix m : ℚ) : ℝ) m =
      (m : ℤ) *
          strictFacTop
            ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) +
        1 - factorialGapStepCarry m := by
  have hfac :
      m.factorial = m * (m - 1).factorial := by
    calc
      m.factorial = ((m - 1) + 1).factorial := by congr 1 <;> omega
      _ = ((m - 1) + 1) * (m - 1).factorial := Nat.factorial_succ _
      _ = m * (m - 1).factorial := by congr 1 <;> omega
  have hfacOne : (1 : ℝ) < m.factorial := by
    exact_mod_cast Nat.one_lt_factorial.mpr hm
  have hden : ((m.factorial : ℝ) - 1) ≠ 0 := by linarith
  have hprefix :
      ((factorialGapPrefix m : ℚ) : ℝ) =
        ((factorialGapPrefix (m - 1) : ℚ) : ℝ) +
          1 / ((m.factorial : ℝ) - 1) := by
    exact_mod_cast factorialGapPrefix_eq_prev_add hm
  let H : ℝ := ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
  let Z : ℤ := strictFacTop H (m - 1)
  have hscaled :
      (m.factorial : ℝ) *
          ((factorialGapPrefix m : ℚ) : ℝ) =
        (m : ℝ) * (Z : ℝ) +
          (1 + 1 / ((m.factorial : ℝ) - 1) -
            (m : ℝ) * factorialGapPredecessorGap m) := by
    calc
      (m.factorial : ℝ) *
          ((factorialGapPrefix m : ℚ) : ℝ) =
          (m.factorial : ℝ) *
            (H + 1 / ((m.factorial : ℝ) - 1)) := by
              rw [hprefix]
      _ = (m.factorial : ℝ) * H +
          (1 + 1 / ((m.factorial : ℝ) - 1)) := by
            field_simp [hden]
            ring
      _ = (m : ℝ) * (Z : ℝ) +
          (1 + 1 / ((m.factorial : ℝ) - 1) -
            (m : ℝ) * factorialGapPredecessorGap m) := by
              rw [hfac]
              simp only [Nat.cast_mul]
              unfold factorialGapPredecessorGap Z H strictFacTop
              push_cast
              ring
  unfold strictFacTop factorialGapStepCarry
  rw [hscaled]
  have hmZ :
      (m : ℝ) * (Z : ℝ) = (((m : ℤ) * Z : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hmZ, Int.floor_intCast_add]
  push_cast
  dsimp [Z, H, strictFacTop]
  ring

/-- Dividing the strict-successor recurrence by `m!` turns its carry defect
into one ordinary factorial-series coefficient. -/
theorem strictFacTop_factorialGapPrefix_div_factorial_step
    {m : ℕ} (hm : 3 ≤ m) :
    (strictFacTop
          ((factorialGapPrefix m : ℚ) : ℝ) m : ℝ) /
        (m.factorial : ℝ) =
      (strictFacTop
            ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) /
          ((m - 1).factorial : ℝ) +
        ((1 - factorialGapStepCarry m : ℤ) : ℝ) /
          (m.factorial : ℝ) := by
  have hrec :=
    strictFacTop_factorialGapPrefix_step (m := m) (show 2 ≤ m by omega)
  have hfacNat :
      m.factorial = m * (m - 1).factorial := by
    have hmSucc : m - 1 + 1 = m := by omega
    simpa only [hmSucc] using Nat.factorial_succ (m - 1)
  have hfac :
      (m.factorial : ℝ) =
        (m : ℝ) * ((m - 1).factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [hrec, hfac]
  push_cast
  field_simp
  ring

/-- Exact finite factorial-series expansion of the normalized strict
successor.  The coefficient at index `m` is `1 - factorialGapStepCarry m`;
thus an eventual unit-carry tail is exactly an eventual zero-coefficient
tail in this representation. -/
theorem strictFacTop_factorialGapPrefix_carry_expansion
    (M : ℕ) (hM : 2 ≤ M) :
    (strictFacTop
          ((factorialGapPrefix M : ℚ) : ℝ) M : ℝ) /
        (M.factorial : ℝ) =
      (strictFacTop
            ((factorialGapPrefix 2 : ℚ) : ℝ) 2 : ℝ) /
          ((2 : ℕ).factorial : ℝ) +
        ∑ m ∈ Finset.Icc 3 M,
          ((1 - factorialGapStepCarry m : ℤ) : ℝ) /
            (m.factorial : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
      simp
  | succ M hM ih =>
      have hIcc :
          Finset.Icc 3 (M + 1) =
            insert (M + 1) (Finset.Icc 3 M) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      calc
        (strictFacTop
              ((factorialGapPrefix (M + 1) : ℚ) : ℝ) (M + 1) : ℝ) /
            ((M + 1).factorial : ℝ) =
          (strictFacTop
                ((factorialGapPrefix M : ℚ) : ℝ) M : ℝ) /
              (M.factorial : ℝ) +
            ((1 - factorialGapStepCarry (M + 1) : ℤ) : ℝ) /
              ((M + 1).factorial : ℝ) := by
                simpa only [Nat.add_sub_cancel] using
                  strictFacTop_factorialGapPrefix_div_factorial_step
                    (m := M + 1) (by omega)
        _ =
          ((strictFacTop
                ((factorialGapPrefix 2 : ℚ) : ℝ) 2 : ℝ) /
              ((2 : ℕ).factorial : ℝ) +
            ∑ m ∈ Finset.Icc 3 M,
              ((1 - factorialGapStepCarry m : ℤ) : ℝ) /
                (m.factorial : ℝ)) +
            ((1 - factorialGapStepCarry (M + 1) : ℤ) : ℝ) /
              ((M + 1).factorial : ℝ) := by rw [ih]
        _ =
          (strictFacTop
                ((factorialGapPrefix 2 : ℚ) : ℝ) 2 : ℝ) /
              ((2 : ℕ).factorial : ℝ) +
            (((1 - factorialGapStepCarry (M + 1) : ℤ) : ℝ) /
                ((M + 1).factorial : ℝ) +
              ∑ m ∈ Finset.Icc 3 M,
                ((1 - factorialGapStepCarry m : ℤ) : ℝ) /
                  (m.factorial : ℝ)) := by ring
        _ =
          (strictFacTop
                ((factorialGapPrefix 2 : ℚ) : ℝ) 2 : ℝ) /
              ((2 : ℕ).factorial : ℝ) +
            ∑ m ∈ Finset.Icc 3 (M + 1),
              ((1 - factorialGapStepCarry m : ℤ) : ℝ) /
                (m.factorial : ℝ) := by
                  rw [hIcc, Finset.sum_insert (by simp)]

/-- The normalized strict successor of the prefix converges to the Erdős #68
series.  Hence an eventually stationary normalized carry recurrence has the
series itself as its rational stationary value. -/
theorem tendsto_strictFacTop_factorialGapPrefix_div_factorial :
    Filter.Tendsto
      (fun n : ℕ =>
        (strictFacTop
              ((factorialGapPrefix n : ℚ) : ℝ) n : ℝ) /
          (n.factorial : ℝ))
      Filter.atTop
      (nhds _root_.Erdos68.factorialGapSeries) := by
  have hfacTop :
      Filter.Tendsto (fun n : ℕ => (n.factorial : ℝ))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop
  have hinv :
      Filter.Tendsto (fun n : ℕ => 1 / (n.factorial : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hfacTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n : ℕ =>
      _root_.Erdos68.factorialGapSeries -
        1 / (n.factorial : ℝ))
    (h := fun n : ℕ =>
      _root_.Erdos68.factorialGapSeries +
        1 / (n.factorial : ℝ))
    ?_ ?_ ?_ ?_
  · simpa using tendsto_const_nhds.sub hinv
  · simpa using tendsto_const_nhds.add hinv
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hdecomp :=
      _root_.Erdos68.factorialGapSeries_eq_sum_add_tail hn
    have hprefix := factorialGapPrefix_cast n
    rw [← hprefix] at hdecomp
    obtain ⟨hzLower, hzUpper⟩ :=
      strictFacTop_div_factorial_bounds
        (((factorialGapPrefix n : ℚ) : ℝ)) n
    have htailLt :=
      _root_.Erdos68.factorialGapTail_lt_one_div_factorial hn
    linarith
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hdecomp :=
      _root_.Erdos68.factorialGapSeries_eq_sum_add_tail hn
    have hprefix := factorialGapPrefix_cast n
    rw [← hprefix] at hdecomp
    obtain ⟨hzLower, hzUpper⟩ :=
      strictFacTop_div_factorial_bounds
        (((factorialGapPrefix n : ℚ) : ℝ)) n
    have htailPos :=
      _root_.Erdos68.factorialGapTail_pos hn
    linarith

/-- If the Erdős #68 series has a displayed rational value `a / q`,
then every carry after the denominator threshold is exactly one. -/
theorem factorialGapStepCarry_eq_one_of_dvd_pred_factorial
    {m q : ℕ} {a : ℤ}
    (hm : 3 ≤ m)
    (hq : 0 < q)
    (hqfac : q ∣ (m - 1).factorial)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    factorialGapStepCarry m = 1 := by
  have hpredDvd : (m - 1).factorial ∣ m.factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have hprev :=
    strictFacTop_factorialGapPrefix_eq_cleared_rational_of_dvd
      (n := m - 1) (q := q) (a := a)
      (by omega) hq hqfac hseries
  have hcurr :=
    strictFacTop_factorialGapPrefix_eq_cleared_rational_of_dvd
      (n := m) (q := q) (a := a)
      (by omega) hq (hqfac.trans hpredDvd) hseries
  have hfac :
      m.factorial = m * (m - 1).factorial := by
    have hmSucc : m - 1 + 1 = m := by omega
    simpa only [hmSucc] using Nat.factorial_succ (m - 1)
  have hquot :
      m.factorial / q = m * ((m - 1).factorial / q) := by
    rw [hfac]
    exact Nat.mul_div_assoc m hqfac
  have hscale :
      (((m.factorial / q : ℕ) : ℤ) * a : ℤ) =
        (m : ℤ) * ((((m - 1).factorial / q : ℕ) : ℤ) * a) := by
    rw [hquot]
    push_cast
    ring
  have hrec :=
    strictFacTop_factorialGapPrefix_step (show 2 ≤ m by omega)
  rw [hcurr, hprev, hscale] at hrec
  omega

/-- Size-bound corollary of the divisibility form, kept so the existing
consumers are unchanged. -/
theorem factorialGapStepCarry_eq_one_of_series_eq_rat
    {m q : ℕ} {a : ℤ}
    (hm : 3 ≤ m)
    (hq : 0 < q)
    (hqm : q ≤ m - 1)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    factorialGapStepCarry m = 1 :=
  factorialGapStepCarry_eq_one_of_dvd_pred_factorial
    hm hq (Nat.dvd_factorial hq hqm) hseries

/-- If the carry sequence is eventually one, then the normalized
strict-successor recurrence is eventually constant.  Its independently
proved limit is the original series, so the series is rational. -/
theorem not_irrational_factorialGapSeries_of_eventually_unit_carries
    (hunit : ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      factorialGapStepCarry m = 1) :
    ¬Irrational _root_.Erdos68.factorialGapSeries := by
  obtain ⟨M, hunit⟩ := hunit
  let K : ℕ := max M 2
  let R : ℕ → ℝ := fun n =>
    (strictFacTop
          ((factorialGapPrefix n : ℚ) : ℝ) n : ℝ) /
      (n.factorial : ℝ)
  have hKTwo : 2 ≤ K := by simp [K]
  have hMK : M ≤ K := by simp [K]
  have hstationary : ∀ n : ℕ, K ≤ n → R n = R K := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hKn ih =>
        have hcarry : factorialGapStepCarry (n + 1) = 1 :=
          hunit (n + 1) (by omega)
        have hstep :=
          strictFacTop_factorialGapPrefix_div_factorial_step
            (m := n + 1) (by omega)
        have hnext : R (n + 1) = R n := by
          simpa [R, hcarry] using hstep
        exact hnext.trans ih
  have heventually : R =ᶠ[Filter.atTop] fun _ => R K :=
    (Filter.eventually_ge_atTop K).mono hstationary
  have hlimitK : Filter.Tendsto R Filter.atTop (nhds (R K)) :=
    tendsto_const_nhds.congr' heventually.symm
  have hlimitSeries :
      Filter.Tendsto R Filter.atTop
        (nhds _root_.Erdos68.factorialGapSeries) := by
    simpa [R] using
      tendsto_strictFacTop_factorialGapPrefix_div_factorial
  have hseriesEq :
      _root_.Erdos68.factorialGapSeries = R K :=
    tendsto_nhds_unique hlimitSeries hlimitK
  let r : ℚ :=
    (strictFacTop
          ((factorialGapPrefix K : ℚ) : ℝ) K : ℚ) /
      (K.factorial : ℚ)
  have hr : (r : ℝ) = R K := by
    simp [r, R]
  rw [hseriesEq, ← hr]
  exact Rat.not_irrational r

/-- Exact carry characterization of rationality: the series is
non-irrational exactly when its carry
sequence is eventually one. -/
theorem not_irrational_factorialGapSeries_iff_eventually_unit_carries :
    ¬Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        factorialGapStepCarry m = 1 := by
  constructor
  · intro hrat
    obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
    refine ⟨max 3 (r.den + 1), ?_⟩
    intro m hm
    apply factorialGapStepCarry_eq_one_of_series_eq_rat
      (m := m) (q := r.den) (a := r.num)
    · omega
    · exact r.den_pos
    · omega
    · rw [hr, Rat.cast_def]
  · exact
      not_irrational_factorialGapSeries_of_eventually_unit_carries

/-- A single exact non-unit carry at index `m` forces every displayed
rational denominator of the series to be at least `m`. -/
theorem rational_denominator_ge_of_nonunit_carry
    {m q : ℕ} {a : ℤ}
    (hm : 3 ≤ m)
    (hmiss : factorialGapStepCarry m ≠ 1)
    (hq : 0 < q)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    m ≤ q := by
  by_contra hmq
  apply hmiss
  exact factorialGapStepCarry_eq_one_of_series_eq_rat
    hm hq (by omega) hseries

/-- A single exact non-unit carry at index `m` excludes every displayed
rational denominator dividing `(m-1)!`.

This is strictly stronger than `rational_denominator_ge_of_nonunit_carry`,
which only excludes `q ≤ m - 1`.  The size bound leaves every `q > m - 1`
open, including the `(m-1)`-smooth ones such as `(m-1)!` itself and the
primorial below `m`; the divisibility form excludes all of them at once.
Equivalently, the Smarandache function (also called the Kempner function)
`min {k : q ∣ k!}` of any displayed denominator is at least `m`, so `q` carries a prime power `p ^ e` with
`e` exceeding the multiplicity of `p` in `(m-1)!`. -/
theorem rational_denominator_not_dvd_pred_factorial_of_nonunit_carry
    {m q : ℕ} {a : ℤ}
    (hm : 3 ≤ m)
    (hmiss : factorialGapStepCarry m ≠ 1)
    (hq : 0 < q)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    ¬ (q ∣ (m - 1).factorial) := fun hdvd =>
  hmiss
    (factorialGapStepCarry_eq_one_of_dvd_pred_factorial
      hm hq hdvd hseries)

theorem factorialGapPredecessorGap_pos_le_one (m : ℕ) :
    0 < factorialGapPredecessorGap m ∧
      factorialGapPredecessorGap m ≤ 1 := by
  let A : ℝ :=
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
  have hfloorLe : ((⌊A⌋ : ℤ) : ℝ) ≤ A :=
    Int.floor_le A
  have hltFloor : A < (((⌊A⌋ + 1 : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast Int.lt_floor_add_one A
  unfold factorialGapPredecessorGap strictFacTop
  dsimp [A] at hfloorLe hltFloor
  push_cast at hltFloor ⊢
  constructor <;> linarith

/-- The actual rounding carry lies in the sharp range required by the
strict-successor divisibility criterion. -/
theorem factorialGapStepCarry_bounds
    {m : ℕ} (hm : 3 ≤ m) :
    (-1 : ℤ) ≤ factorialGapStepCarry m ∧
      factorialGapStepCarry m ≤ (m : ℤ) - 1 := by
  have hfacNat : 2 < m.factorial := by
    have hsix : 6 ≤ m.factorial := by
      calc
        6 = (3 : ℕ).factorial := by norm_num
        _ ≤ m.factorial := Nat.factorial_le (by omega)
    omega
  have hfacReal : (2 : ℝ) < m.factorial := by
    exact_mod_cast hfacNat
  have hdenPos : (0 : ℝ) < (m.factorial : ℝ) - 1 := by
    linarith
  have hdenOne : (1 : ℝ) < (m.factorial : ℝ) - 1 := by
    linarith
  have hepsPos :
      (0 : ℝ) < 1 / ((m.factorial : ℝ) - 1) :=
    one_div_pos.mpr hdenPos
  have hepsLt :
      1 / ((m.factorial : ℝ) - 1) < (1 : ℝ) :=
    (div_lt_one hdenPos).2 hdenOne
  obtain ⟨hgapPos, hgapOne⟩ :=
    factorialGapPredecessorGap_pos_le_one m
  have hmPos : (0 : ℝ) < m := by positivity
  have hyUpper :
      1 + 1 / ((m.factorial : ℝ) - 1) -
          (m : ℝ) * factorialGapPredecessorGap m < 2 := by
    nlinarith [mul_pos hmPos hgapPos]
  have hyLower :
      (1 : ℝ) - m <
        1 + 1 / ((m.factorial : ℝ) - 1) -
          (m : ℝ) * factorialGapPredecessorGap m := by
    nlinarith
  unfold factorialGapStepCarry
  constructor
  · have hfloorLt :
        ⌊1 + 1 / ((m.factorial : ℝ) - 1) -
            (m : ℝ) * factorialGapPredecessorGap m⌋ < (2 : ℤ) :=
      Int.floor_lt.mpr hyUpper
    omega
  · have hfloorLower :
        (1 : ℤ) - (m : ℤ) ≤
          ⌊1 + 1 / ((m.factorial : ℝ) - 1) -
            (m : ℝ) * factorialGapPredecessorGap m⌋ := by
      apply Int.le_floor.mpr
      exact_mod_cast hyLower.le
    omega

/-- The unit-carry condition is exactly divisibility of the computable
rational strict successor by its index.  This eliminates the real predecessor
gap and its floor: at every `m ≥ 3`, a unit
carry occurs precisely when the exact integer
`strictFacTopRat (factorialGapPrefix m) m` is a multiple of `m`. -/
theorem factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat
    {m : ℕ} (hm : 3 ≤ m) :
    factorialGapStepCarry m = 1 ↔
      (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m := by
  have hrec :=
    strictFacTop_factorialGapPrefix_step
      (m := m) (show 2 ≤ m by omega)
  obtain ⟨hbLower, hbUpper⟩ :=
    factorialGapStepCarry_bounds hm
  rw [← strictFacTop_ratCast]
  exact
    (dvd_strictSuccessor_iff_roundingDigit_eq_one
      (m := (m : ℤ))
      (N :=
        strictFacTop
          ((factorialGapPrefix m : ℚ) : ℝ) m)
      (Nprev :=
        strictFacTop
          ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1))
      (b := factorialGapStepCarry m)
      (by exact_mod_cast hm)
      hrec hbLower hbUpper).symm

/-- Arbitrarily late failures of the unit-carry condition prove the
irrationality of the Erdős #68 series. -/
theorem irrational_factorialGapSeries_of_cofinal_nonunit_carries
    (hmiss : ∀ B : ℕ, ∃ m : ℕ,
      B < m ∧ factorialGapStepCarry m ≠ 1) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  by_contra hrat
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  obtain ⟨m, hmLarge, hmMiss⟩ := hmiss (max 2 r.den)
  apply hmMiss
  apply factorialGapStepCarry_eq_one_of_series_eq_rat
    (m := m) (q := r.den) (a := r.num)
  · omega
  · exact r.den_pos
  · omega
  · rw [hr, Rat.cast_def]

/-- The original irrationality problem is exactly the assertion that
non-unit carries occur cofinally.  No implication is lost in passing from
the series to this integer recurrence. -/
theorem irrational_factorialGapSeries_iff_cofinal_nonunit_carries :
    Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ factorialGapStepCarry m ≠ 1 := by
  constructor
  · intro hirr B
    by_contra hnone
    push Not at hnone
    have hunit :
        ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
          factorialGapStepCarry m = 1 := by
      refine ⟨B + 1, ?_⟩
      intro m hm
      exact hnone m (by omega)
    exact
      (not_irrational_factorialGapSeries_of_eventually_unit_carries hunit)
        hirr
  · exact irrational_factorialGapSeries_of_cofinal_nonunit_carries

/-- The original irrationality problem is equivalently a cofinal failure of
one purely integral divisibility test on the exact rational prefixes.  No
prime restriction, real approximation, or rounding-carry hypothesis remains
in this formulation. -/
theorem irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses :
    Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧
          ¬(m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m := by
  rw [irrational_factorialGapSeries_iff_cofinal_nonunit_carries]
  constructor
  · intro hmiss B
    obtain ⟨m, hmLarge, hmCarry⟩ := hmiss (max 2 B)
    have hm3 : 3 ≤ m := by omega
    refine ⟨m, by omega, ?_⟩
    intro hmDvd
    exact hmCarry
      ((factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm3).2 hmDvd)
  · intro hmiss B
    obtain ⟨m, hmLarge, hmDvd⟩ := hmiss (max 2 B)
    have hm3 : 3 ≤ m := by omega
    refine ⟨m, by omega, ?_⟩
    intro hmCarry
    exact hmDvd
      ((factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm3).1 hmCarry)

end ErdosProblems.Erdos68
