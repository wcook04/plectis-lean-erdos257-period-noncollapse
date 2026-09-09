import ErdosProblems.Erdos251.PrimeGapDyadicTail

/-!
# Erdős #251: a kernel-decided denominator floor

`S = Σ_{i ≥ 0} p_i / 2^{i+1}` is the prime series (zero-based, `p_0 = 2`).
This module proves inside the Lean kernel, with `decide +kernel` and no
`native_decide`, that every rational `a/b` equal to `S` has `b ≥ 2^589 > 10^177`,
and the same for the prime-gap series `S - 2` of Erdős #251.

The mechanism is elementary and every step is checked:

1. `primeSumLoop c X` runs a trial-division sieve over `m < X` inside the
   kernel and returns `(π(X), Σ_{i < π(X)} p_i 2^{c-1-i})`.  Its semantics
   (`primeSumLoop_fst`, `primeSumLoop_snd`) are proved from `Nat.nth_count`.
2. `prime0_le_polynomial` (`p_i ≤ 1250 (i+1)^4`, already in the development)
   and `pow_four_mul_two_pow_le` (`(c+1+j)^4 2^j ≤ (c+1)^4 3^j` for `c ≥ 9`)
   bound the omitted tail by `5000 (c+1)^4 / 2^{c+1}`.
3. `den_ge_of_between`: if `u/v < x < u'/v'` with `u'v - uv' = 1`, every
   rational `a/b = x` has `b ≥ v + v'`.
4. `certCheck` packages the four integer inequalities; `den_bound_of_certCheck`
   turns `certCheck = true` into the floor; the instance is `decide +kernel`.

The Python receipt in the packet (`q ≥ 2^39997 > 10^12040`, 23369 certified
partial quotients) is far larger: bit length `39998` is not an exponent.
Nothing here bears on irrationality.  The point is the evidence class: this
floor is a theorem of the kernel, not a receipt.
-/

open Finset

namespace ErdosProblems.Erdos251

/-! ## Kernel-evaluable trial division -/

/-- `noSmallDivisor m fuel k = true` iff no `j` with `k ≤ j < k + fuel` and
`j * j ≤ m` divides `m`. -/
def noSmallDivisor (m : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, k =>
      if m < k * k then true
      else if m % k == 0 then false
      else noSmallDivisor m fuel (k + 1)

theorem noSmallDivisor_eq_true_iff (m : ℕ) : ∀ (fuel k : ℕ),
    noSmallDivisor m fuel k = true ↔
      ∀ j, k ≤ j → j < k + fuel → j * j ≤ m → ¬ j ∣ m := by
  intro fuel
  induction fuel with
  | zero =>
    intro k
    simp only [noSmallDivisor, true_iff]
    intro j h1 h2
    omega
  | succ fuel ih =>
    intro k
    by_cases hlt : m < k * k
    · have hb : noSmallDivisor m (fuel + 1) k = true := by
        simp [noSmallDivisor, hlt]
      rw [hb]
      refine ⟨fun _ j h1 _ hjj => ?_, fun _ => rfl⟩
      have hk : k * k ≤ j * j := Nat.mul_le_mul h1 h1
      omega
    · by_cases hmod : m % k = 0
      · have hb : noSmallDivisor m (fuel + 1) k = false := by
          simp [noSmallDivisor, hlt, hmod]
        rw [hb]
        refine ⟨fun hc => Bool.noConfusion hc, fun hP => ?_⟩
        exact absurd (Nat.dvd_of_mod_eq_zero hmod)
          (hP k le_rfl (by omega) (by omega))
      · have hb : noSmallDivisor m (fuel + 1) k = noSmallDivisor m fuel (k + 1) := by
          simp [noSmallDivisor, hlt, hmod]
        rw [hb, ih (k + 1)]
        constructor
        · intro h j h1 h2 hjj
          rcases Nat.eq_or_lt_of_le h1 with rfl | hlt'
          · exact fun hdvd => hmod (Nat.mod_eq_zero_of_dvd hdvd)
          · exact h j hlt' (by omega) hjj
        · intro h j h1 h2 hjj
          exact h j (by omega) (by omega) hjj

/-- Trial-division primality test, kernel-evaluable. -/
def isPrimeTD (m : ℕ) : Bool := decide (2 ≤ m) && noSmallDivisor m m 2

theorem isPrimeTD_eq_true_iff (m : ℕ) : isPrimeTD m = true ↔ Nat.Prime m := by
  rw [Nat.prime_def_le_sqrt, isPrimeTD, Bool.and_eq_true, decide_eq_true_iff,
    noSmallDivisor_eq_true_iff]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun j hj hjs => h j hj ?_ (Nat.le_sqrt.mp hjs)⟩
    have := Nat.le_sqrt.mp hjs
    have hjm : j ≤ m := by nlinarith
    omega
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun j hj _ hjj => h j hj (Nat.le_sqrt.mpr hjj)⟩

/-! ## The kernel sieve and its semantics -/

/-- After processing all `m < X`: `(π(X), Σ_{i < π(X)} p_i 2^{B-i-1})`. -/
def primeSumLoop (B : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 =>
      let s := primeSumLoop B m
      if isPrimeTD m then (s.1 + 1, s.2 + m * 2 ^ (B - s.1 - 1)) else s

theorem primeSumLoop_fst (B : ℕ) : ∀ X : ℕ, (primeSumLoop B X).1 = Nat.count Nat.Prime X
  | 0 => by simp [primeSumLoop]
  | X + 1 => by
      have ih := primeSumLoop_fst B X
      by_cases hp : Nat.Prime X
      · have hb : isPrimeTD X = true := (isPrimeTD_eq_true_iff X).mpr hp
        simp [primeSumLoop, hb, Nat.count_succ, hp, ih]
      · have hb : isPrimeTD X = false := by
          rw [← Bool.not_eq_true, isPrimeTD_eq_true_iff]; exact hp
        simp [primeSumLoop, hb, Nat.count_succ, hp, ih]

theorem primeSumLoop_snd (B : ℕ) : ∀ X : ℕ, Nat.count Nat.Prime X ≤ B →
    (primeSumLoop B X).2 =
      ∑ i ∈ range (Nat.count Nat.Prime X), prime0 i * 2 ^ (B - i - 1)
  | 0, _ => by simp [primeSumLoop]
  | X + 1, hB => by
      have hmono : Nat.count Nat.Prime X ≤ Nat.count Nat.Prime (X + 1) :=
        Nat.count_monotone _ (Nat.le_succ X)
      have ih := primeSumLoop_snd B X (le_trans hmono hB)
      have hfst := primeSumLoop_fst B X
      by_cases hp : Nat.Prime X
      · have hb : isPrimeTD X = true := (isPrimeTD_eq_true_iff X).mpr hp
        have hnth : prime0 (Nat.count Nat.Prime X) = X := Nat.nth_count hp
        simp [primeSumLoop, hb, Nat.count_succ, hp, sum_range_succ, hnth, ih, hfst]
      · have hb : isPrimeTD X = false := by
          rw [← Bool.not_eq_true, isPrimeTD_eq_true_iff]; exact hp
        simp [primeSumLoop, hb, Nat.count_succ, hp, ih]

/-- The finite prefix of the prime series as a dyadic rational. -/
theorem sum_primeDyadicTerm_eq_div (c B : ℕ) (hcB : c ≤ B) :
    ∑ i ∈ range c, primeDyadicTerm i =
      ((∑ i ∈ range c, prime0 i * 2 ^ (B - i - 1) : ℕ) : ℝ) / 2 ^ B := by
  have hB : (2 : ℝ) ^ B ≠ 0 := by positivity
  rw [eq_div_iff hB, Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < c := mem_range.mp hi
  have h2 : (2 : ℝ) ^ (i + 1) ≠ 0 := by positivity
  have h2' : (2 : ℝ) ^ B = 2 ^ (B - i - 1) * 2 ^ (i + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [primeDyadicTerm, div_mul_eq_mul_div, div_eq_iff h2, h2']
  ring

/-! ## The tail bound -/

theorem pow_four_mul_two_pow_le (c : ℕ) (hc : 9 ≤ c) :
    ∀ j : ℕ, (c + 1 + j) ^ 4 * 2 ^ j ≤ (c + 1) ^ 4 * 3 ^ j
  | 0 => by simp
  | j + 1 => by
      have ih := pow_four_mul_two_pow_le c hc j
      have hstep : 2 * (c + 1 + (j + 1)) ^ 4 ≤ 3 * (c + 1 + j) ^ 4 := by
        have h10 : 10 ≤ c + 1 + j := by omega
        set n := c + 1 + j with hn
        have : c + 1 + (j + 1) = n + 1 := by omega
        rw [this]
        nlinarith [Nat.mul_le_mul h10 h10, Nat.mul_le_mul (Nat.mul_le_mul h10 h10) h10,
          Nat.mul_le_mul (Nat.mul_le_mul h10 h10) (Nat.mul_le_mul h10 h10)]
      calc (c + 1 + (j + 1)) ^ 4 * 2 ^ (j + 1)
          = 2 * (c + 1 + (j + 1)) ^ 4 * 2 ^ j := by ring
        _ ≤ 3 * (c + 1 + j) ^ 4 * 2 ^ j := Nat.mul_le_mul_right _ hstep
        _ = 3 * ((c + 1 + j) ^ 4 * 2 ^ j) := by ring
        _ ≤ 3 * ((c + 1) ^ 4 * 3 ^ j) := Nat.mul_le_mul_left _ ih
        _ = (c + 1) ^ 4 * 3 ^ (j + 1) := by ring

theorem primeDyadicTerm_add_le (c : ℕ) (hc : 9 ≤ c) (j : ℕ) :
    primeDyadicTerm (j + c) ≤ 1250 * (c + 1) ^ 4 / 2 ^ (c + 1) * ((3 : ℝ) / 4) ^ j := by
  have h1 : (prime0 (j + c) : ℝ) ≤ 1250 * ((c : ℝ) + 1 + j) ^ 4 := by
    have := prime0_le_polynomial (j + c)
    have e : ((j + c + 1 : ℕ) : ℝ) = (c : ℝ) + 1 + j := by push_cast; ring
    calc (prime0 (j + c) : ℝ) ≤ ((1250 * (j + c + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast this
      _ = 1250 * ((c : ℝ) + 1 + j) ^ 4 := by push_cast; ring
  have h2 : ((c : ℝ) + 1 + j) ^ 4 * 2 ^ j ≤ ((c : ℝ) + 1) ^ 4 * 3 ^ j := by
    have := pow_four_mul_two_pow_le c hc j
    exact_mod_cast this
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have key : ((c : ℝ) + 1 + j) ^ 4 ≤ ((c : ℝ) + 1) ^ 4 * ((3 : ℝ) / 4) ^ j * 2 ^ j := by
    have e : ((3 : ℝ) / 4) ^ j * 2 ^ j * 2 ^ j = 3 ^ j := by
      rw [← mul_pow, ← mul_pow]; norm_num
    refine le_of_mul_le_mul_right ?_ h2j
    calc ((c : ℝ) + 1 + j) ^ 4 * 2 ^ j ≤ ((c : ℝ) + 1) ^ 4 * 3 ^ j := h2
      _ = ((c : ℝ) + 1) ^ 4 * ((3 : ℝ) / 4) ^ j * 2 ^ j * 2 ^ j := by rw [← e]; ring
  rw [primeDyadicTerm, div_le_iff₀ (by positivity)]
  have e2 : (1250 : ℝ) * (c + 1) ^ 4 / 2 ^ (c + 1) * ((3 : ℝ) / 4) ^ j * 2 ^ (j + c + 1)
      = 1250 * (((c : ℝ) + 1) ^ 4 * ((3 : ℝ) / 4) ^ j * 2 ^ j) := by
    rw [show (2 : ℝ) ^ (j + c + 1) = 2 ^ j * 2 ^ (c + 1) by rw [← pow_add]; congr 1]
    field_simp
  rw [e2]
  nlinarith [key, h1]

theorem tsum_primeDyadicTerm_tail_le (c : ℕ) (hc : 9 ≤ c) :
    ∑' j, primeDyadicTerm (j + c) ≤ 5000 * (c + 1) ^ 4 / 2 ^ (c + 1) := by
  have hf : Summable (fun j => primeDyadicTerm (j + c)) :=
    (summable_nat_add_iff c).mpr summable_primeDyadicTerm
  have hg : Summable (fun j : ℕ => 1250 * (c + 1) ^ 4 / 2 ^ (c + 1) * ((3 : ℝ) / 4) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ∑' j, primeDyadicTerm (j + c)
      ≤ ∑' j : ℕ, 1250 * (c + 1) ^ 4 / 2 ^ (c + 1) * ((3 : ℝ) / 4) ^ j :=
        hf.tsum_le_tsum (primeDyadicTerm_add_le c hc) hg
    _ = 1250 * (c + 1) ^ 4 / 2 ^ (c + 1) * ∑' j : ℕ, ((3 : ℝ) / 4) ^ j := tsum_mul_left
    _ = 1250 * (c + 1) ^ 4 / 2 ^ (c + 1) * 4 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    _ = 5000 * (c + 1) ^ 4 / 2 ^ (c + 1) := by ring

/-- The bracket: prefix ≤ `S` ≤ prefix + tail bound. -/
theorem tsum_primeDyadicTerm_bracket (c : ℕ) (hc : 9 ≤ c) :
    (∑ i ∈ range c, primeDyadicTerm i) ≤ ∑' n, primeDyadicTerm n ∧
      ∑' n, primeDyadicTerm n ≤
        (∑ i ∈ range c, primeDyadicTerm i) + 5000 * (c + 1) ^ 4 / 2 ^ (c + 1) := by
  have hsplit := Summable.sum_add_tsum_nat_add c summable_primeDyadicTerm
  have hnn : 0 ≤ ∑' j, primeDyadicTerm (j + c) :=
    tsum_nonneg fun j => by unfold primeDyadicTerm; positivity
  have htail := tsum_primeDyadicTerm_tail_le c hc
  constructor <;> linarith

/-! ## Farey neighbours -/

/-- If `u/v < x < u'/v'` with `u'v - uv' = 1`, every rational `a/b = x` has
`b ≥ v + v'`. -/
theorem den_ge_of_between (u v u' v' : ℕ) (hv : 0 < v) (hv' : 0 < v')
    (hdet : u' * v = u * v' + 1) (a : ℤ) (b : ℕ) (hb : 0 < b)
    (h1 : (u : ℝ) / v < a / b) (h2 : (a : ℝ) / b < u' / v') : v + v' ≤ b := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv'R : (0 : ℝ) < v' := by exact_mod_cast hv'
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_div_iff₀ hvR hbR] at h1
  rw [div_lt_div_iff₀ hbR hv'R] at h2
  have h1z : (u : ℤ) * b < a * v := by exact_mod_cast h1
  have h2z : a * v' < (u' : ℤ) * b := by exact_mod_cast h2
  have hdetz : (u' : ℤ) * v = u * v' + 1 := by exact_mod_cast hdet
  have hx : (1 : ℤ) ≤ a * v - u * b := by omega
  have hy : (1 : ℤ) ≤ u' * b - a * v' := by omega
  have hv0 : (0 : ℤ) ≤ v := by positivity
  have hv'0 : (0 : ℤ) ≤ v' := by positivity
  have key : (b : ℤ) - v - v' = v * ((u' * b - a * v') - 1) + v' * ((a * v - u * b) - 1) := by
    linear_combination (-(b : ℤ)) * hdetz
  have p1 := mul_nonneg hv0 (sub_nonneg.mpr hy)
  have p2 := mul_nonneg hv'0 (sub_nonneg.mpr hx)
  have : (v : ℤ) + v' ≤ b := by linarith
  exact_mod_cast this

/-! ## The certificate -/

/-- The four integer inequalities the kernel decides. -/
def certCheck (c u v u' v' X : ℕ) : Bool :=
  let s := primeSumLoop c X
  (s.1 == c) && decide (0 < v) && decide (0 < v') && (u' * v == u * v' + 1) &&
    decide (u * 2 ^ c < s.2 * v) &&
    decide ((2 * s.2 + 5000 * (c + 1) ^ 4) * v' < u' * 2 ^ (c + 1))

theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b := by
  intro a b hb hS
  simp only [certCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨hcount, hv⟩, hv'⟩, hdet⟩, hlo⟩, hhi⟩ := h
  rw [primeSumLoop_fst] at hcount
  have hsnd := primeSumLoop_snd c X (by rw [hcount])
  rw [hcount] at hsnd
  set lo := (primeSumLoop c X).2 with hlo_def
  have hprefix : ∑ i ∈ range c, primeDyadicTerm i = (lo : ℝ) / 2 ^ c := by
    rw [sum_primeDyadicTerm_eq_div c c le_rfl, hsnd]
  obtain ⟨hb1, hb2⟩ := tsum_primeDyadicTerm_bracket c hc
  rw [hprefix] at hb1 hb2
  have h2c : (0 : ℝ) < 2 ^ c := by positivity
  have h2c1 : (0 : ℝ) < 2 ^ (c + 1) := by positivity
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv'R : (0 : ℝ) < v' := by exact_mod_cast hv'
  have hloR : (u : ℝ) / v < (lo : ℝ) / 2 ^ c := by
    rw [div_lt_div_iff₀ hvR h2c]; exact_mod_cast hlo
  have hhiR : ((2 * lo + 5000 * (c + 1) ^ 4 : ℕ) : ℝ) / 2 ^ (c + 1) < (u' : ℝ) / v' := by
    rw [div_lt_div_iff₀ h2c1 hv'R]; exact_mod_cast hhi
  have hsum : (lo : ℝ) / 2 ^ c + 5000 * (c + 1) ^ 4 / 2 ^ (c + 1)
      = ((2 * lo + 5000 * (c + 1) ^ 4 : ℕ) : ℝ) / 2 ^ (c + 1) := by
    push_cast
    rw [pow_succ]
    field_simp
    ring
  refine den_ge_of_between u v u' v' hv hv' hdet a b hb ?_ ?_
  · rw [← hS]; exact lt_of_lt_of_le hloR hb1
  · rw [← hS]; exact lt_of_le_of_lt hb2 (by rw [hsum]; exact hhiR)

/-! ## The `X = 10^4` instance and the unconditional floor

The literals are generated by
`formal_math/probes/erdos251_kernel_denominator_certificate.py --X 10000`. -/

def certX : ℕ := 10000

def certC : ℕ := 1229

def certU : ℕ :=
  8065641857152652932176019632186898003271162829171466334827308360779441527871744503350940785598890336998852555074615973558897922500842023448210201391609566636587897181681526620217

def certV : ℕ :=
  2194945124413663232143970924541263312422069524635615360518424707735195822181683072018928990483166295508439269024868312162917239885377332351730406072544968385302138677814423351745

def certU' : ℕ :=
  653943710149816262688241189247090522210826000856855544597530261633155217846686899097127598765624846200590981384174695232839888185316374272333277389611483117334000493867584923912

def certV' : ℕ :=
  177961107578986655119842724162170963012013632328159817663784906052492297355019687649040361529707294916566508739385806203025466313389810291243786005499164537499383612081805160767

/-- The kernel re-runs the `10^4` trial-division sieve and decides the four
Farey inequalities on the certificate literals. -/
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true := by
  decide +kernel

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 4096 in
/-- Every rational `a / b` equal to `S` has `b ≥ 2^589 > 10^177`. -/
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by
  have hfloor := den_bound_of_certCheck certC certU certV certU' certV' certX
    (by decide) cert_10000 a b hb hS
  have hbit : (2 ^ 589 : ℕ) ≤ certV + certV' := by decide
  omega

/-- The same floor for the prime-gap series `S - 2` of Erdős #251. -/
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by
  refine kernel_denominator_floor (a + 2 * (b : ℤ)) b hb ?_
  rw [tsum_primeDyadicTerm_eq_two_add_primeGap_unconditional, hS]
  push_cast
  have hbR : (↑b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp
  ring

end ErdosProblems.Erdos251
