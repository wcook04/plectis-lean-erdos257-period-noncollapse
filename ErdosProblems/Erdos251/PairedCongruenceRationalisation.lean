import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Erdős #251: paired congruence-preserving rationalisation (elementary core)

Type B r4 (ordinary, unreviewed) proposed a simultaneous rationalisation: for
any nonnegative summable dyadic series, a cutoff, and an envelope tending to
infinity, one can raise coefficients by a slowly growing correction so that the
perturbed series is rational, a prescribed prefix is unchanged, and *every*
fixed modulus is eventually preserved for both the coefficients and their
cumulative sums.

The mechanism is a pair of corrections with a digit-independent unweighted
total and a free base-four weighted contribution.  This module formalises that
elementary core, independently of Kuperberg's sieve theorem and independently
of the actual prime-gap word.

* `pairEvenCorrection`, `pairOddCorrection`: `e_{2j} = M d`, `e_{2j+1} = M(3-d)`.
* `pairCorrection_sum`: identity (2.7), `e_{2j}+e_{2j+1}=3M`.
* `pairCorrection_weighted`: identity (2.8), the dyadic pair equals
  `M(d+3)/4^{j+1}`.
* `stageCorrection_modEq`: the stage congruence invariant (2.4)–(2.5).
* `intervalDigit_spec`: the one-step Kakeya filling lemma.
* `kakeya_geometric_four`: the geometric overlap for weights `4^{-(j+1)}`.
* `bounded_all_moduli_eventually_trivial`: a bounded perturbation preserving
  every fixed modulus is eventually zero.

The full Theorem 2.2 existence (schedule plus digit selection to a chosen
rational) is not a named declaration here.  Nothing here claims irrationality
of the actual prime-gap series.  The polynomial countermodel remains the
registered first-page object.
-/

open Filter Topology Finset

namespace ErdosProblems.Erdos251

/-! ## Pair identities (2.7) and (2.8) -/

/-- Even-index correction in a pair: `M * d` with digit `d ∈ {0,1,2,3}`. -/
def pairEvenCorrection (M d : ℕ) : ℕ :=
  M * d

/-- Odd-index correction in a pair: `M * (3 - d)`. -/
def pairOddCorrection (M d : ℕ) : ℕ :=
  M * (3 - d)

/-- **Identity (2.7).**  The unweighted pair total is `3M`, independently of the
digit. -/
theorem pairCorrection_sum (M d : ℕ) (hd : d ≤ 3) :
    pairEvenCorrection M d + pairOddCorrection M d = 3 * M := by
  unfold pairEvenCorrection pairOddCorrection
  have h3 : 3 - d + d = 3 := Nat.sub_add_cancel hd
  calc
    M * d + M * (3 - d) = M * (d + (3 - d)) := by ring
    _ = M * (3 - d + d) := by rw [Nat.add_comm]
    _ = M * 3 := by rw [h3]
    _ = 3 * M := by ring

/-- **Identity (2.8).**  The dyadic contribution of one pair is
`M(d+3)/4^{j+1}`. -/
theorem pairCorrection_weighted (M d j : ℕ) (hd : d ≤ 3) :
    (pairEvenCorrection M d : ℚ) / 2 ^ (2 * j + 1) +
        (pairOddCorrection M d : ℚ) / 2 ^ (2 * j + 2) =
      (M : ℚ) * (d + 3) / 4 ^ (j + 1) := by
  unfold pairEvenCorrection pairOddCorrection
  have hd' : ((3 - d : ℕ) : ℚ) = (3 : ℚ) - d := Nat.cast_sub hd
  have h4 : (4 : ℚ) ^ (j + 1) = (2 : ℚ) ^ (2 * (j + 1)) := by
    calc
      (4 : ℚ) ^ (j + 1) = ((2 : ℚ) ^ 2) ^ (j + 1) := by norm_num
      _ = (2 : ℚ) ^ (2 * (j + 1)) := by rw [← pow_mul]
  have hidx : 2 * (j + 1) = 2 * j + 2 := by ring
  rw [h4, hidx]
  push_cast
  rw [hd']
  have hsucc : (2 : ℚ) ^ (2 * j + 2) = (2 : ℚ) ^ (2 * j + 1) * 2 := by
    have : 2 * j + 2 = (2 * j + 1) + 1 := by ring
    rw [this, pow_succ]
  rw [hsucc]
  field_simp
  ring

/-- Finite unweighted series identity: cumulative pair totals ignore the digits. -/
theorem pairCorrection_unweighted_sum (M d : ℕ → ℕ) (hd : ∀ j, d j ≤ 3) (N : ℕ) :
    ∑ j ∈ range N, (pairEvenCorrection (M j) (d j) + pairOddCorrection (M j) (d j)) =
      3 * ∑ j ∈ range N, M j := by
  simp_rw [pairCorrection_sum _ _ (hd _)]
  rw [← Finset.mul_sum]

/-- A constant-`M` block of `ℓ` pairs contributes `3 M ℓ`, independently of the
digits.  This is the schedule quantity `C_{k+1} = C_k + 3 M_k ℓ_k`. -/
theorem pairCorrection_block_sum (M : ℕ) (d : ℕ → ℕ) (hd : ∀ j, d j ≤ 3)
    (J ℓ : ℕ) :
    ∑ j ∈ Ico J (J + ℓ),
        (pairEvenCorrection M (d j) + pairOddCorrection M (d j)) =
      3 * M * ℓ := by
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  simp_rw [pairCorrection_sum M _ (hd _)]
  simp [sum_const, card_range, mul_comm, mul_left_comm]

/-- Finite weighted series identity. -/
theorem pairCorrection_weighted_sum (M d : ℕ → ℕ) (hd : ∀ j, d j ≤ 3) (N : ℕ) :
    ∑ j ∈ range N,
        ((pairEvenCorrection (M j) (d j) : ℚ) / 2 ^ (2 * j + 1) +
          (pairOddCorrection (M j) (d j) : ℚ) / 2 ^ (2 * j + 2)) =
      ∑ j ∈ range N, (M j : ℚ) * (d j + 3) / 4 ^ (j + 1) :=
  sum_congr rfl fun j _ => pairCorrection_weighted (M j) (d j) j (hd j)

/-! ## Stage congruence invariant (2.4)–(2.5) -/

/-- If the running unweighted correction `C` is a multiple of `3M` and the stage
length satisfies `ℓ ≡ -C/(3M) (mod r)`, then the next running correction is a
multiple of `3 M r`.  Here `r` is the ratio `M_{k+1}/M_k` of successive
stage moduli. -/
theorem stageCorrection_modEq {C M ℓ r : ℕ} (hM : 0 < M) (_hr : 0 < r)
    (hdiv : 3 * M ∣ C)
    (hℓ : (ℓ : ℤ) ≡ -((C / (3 * M) : ℕ) : ℤ) [ZMOD r]) :
    (C + 3 * M * ℓ : ℤ) ≡ 0 [ZMOD (3 * M * r)] := by
  obtain ⟨q, hq⟩ := hdiv
  have hpos : 0 < 3 * M := Nat.mul_pos (by decide) hM
  have hq' : C / (3 * M) = q := by
    rw [hq, Nat.mul_div_right q hpos]
  rw [hq'] at hℓ
  have hsum : (q + ℓ : ℤ) ≡ 0 [ZMOD r] := by
    simpa [add_comm] using hℓ.add_right (q : ℤ)
  have hC : (C + 3 * M * ℓ : ℤ) = (3 * M : ℤ) * ((q : ℤ) + ℓ) := by
    rw [hq]
    norm_cast
    ring
  rw [hC]
  rw [Int.modEq_zero_iff_dvd] at hsum ⊢
  obtain ⟨t, ht⟩ := hsum
  refine ⟨t, ?_⟩
  rw [ht]
  ring

/-- Specialisation: a fresh stage starts with `C = 0`, which is a multiple of
every later `3M`. -/
theorem stageCorrection_zero (M r : ℕ) (hM : 0 < M) (hr : 0 < r) (ℓ : ℕ)
    (hℓ : (ℓ : ℤ) ≡ 0 [ZMOD r]) :
    (3 * M * ℓ : ℤ) ≡ 0 [ZMOD (3 * M * r)] := by
  simpa using stageCorrection_modEq (C := 0) hM hr (dvd_zero _) (by simpa using hℓ)

/-! ## Bounded all-moduli perturbations are eventually trivial -/

/-- **Proposition 2.4.**  If `|b_n-a_n| ≤ C` and `b_n ≡ a_n (mod q)` eventually
for every fixed `q`, then `b_n = a_n` eventually. -/
theorem bounded_all_moduli_eventually_trivial {a b : ℕ → ℤ} {C : ℕ}
    (hbd : ∀ n, |b n - a n| ≤ C)
    (hcong : ∀ q : ℕ, 0 < q → ∃ N, ∀ n ≥ N, b n ≡ a n [ZMOD q]) :
    ∃ N, ∀ n ≥ N, b n = a n := by
  obtain ⟨N, hN⟩ := hcong (C + 1) (Nat.succ_pos C)
  refine ⟨N, fun n hn => ?_⟩
  have hdvd : ((C + 1 : ℕ) : ℤ) ∣ b n - a n :=
    Int.modEq_iff_dvd.mp (hN n hn).symm
  have habs : |b n - a n| < (C + 1 : ℤ) := by
    have := hbd n
    linarith
  have hzero : b n - a n = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith

/-- Consequently a bounded all-moduli perturbation cannot change rationality of
a convergent dyadic series: the two series differ by a finite dyadic rational. -/
theorem bounded_all_moduli_partial_stabilises {a b : ℕ → ℕ} {C N M : ℕ}
    (_hbd : ∀ n, |(b n : ℤ) - (a n : ℤ)| ≤ C)
    (heq : ∀ n ≥ N, b n = a n) (hNM : N ≤ M) :
    ∑ n ∈ range M, ((b n : ℚ) - (a n : ℚ)) / 2 ^ (n + 1) =
      ∑ n ∈ range N, ((b n : ℚ) - (a n : ℚ)) / 2 ^ (n + 1) := by
  have hsplit := sum_range_add (fun n : ℕ => ((b n : ℚ) - (a n : ℚ)) / 2 ^ (n + 1)) N (M - N)
  have hN : N + (M - N) = M := Nat.add_sub_of_le hNM
  rw [hN] at hsplit
  rw [hsplit]
  convert add_zero _
  refine sum_eq_zero fun n hn => ?_
  have : N ≤ N + n := Nat.le_add_right _ _
  simp [heq _ this]

/-! ## Interval-filling lemma (one-step Kakeya remainder) -/

/-- Greedy base-`b` digit for remainder `y` against weight `w`. -/
noncomputable def intervalDigit (b : ℕ) (w y : ℝ) : ℕ :=
  min (b - 1) (Int.toNat ⌊y / w⌋)

theorem intervalDigit_le (b : ℕ) (w y : ℝ) : intervalDigit b w y ≤ b - 1 :=
  min_le_left _ _

/-- Consecutive intervals `[d w, d w + (b-1)S]` overlap when `w ≤ (b-1)S`, and
their union is `[0,(b-1)(w+S)]`.  The greedy digit keeps the new remainder in
`[0,(b-1)S]`. -/
theorem intervalDigit_spec {b : ℕ} {w S y : ℝ} (hb : 2 ≤ b) (hw : 0 < w)
    (_hS : 0 ≤ S) (hy0 : 0 ≤ y) (hy1 : y ≤ (b - 1 : ℕ) * (w + S))
    (hk : w ≤ (b - 1 : ℕ) * S) :
    0 ≤ y - (intervalDigit b w y : ℝ) * w ∧
      y - (intervalDigit b w y : ℝ) * w ≤ (b - 1 : ℕ) * S := by
  have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    rw [Nat.cast_sub hb1, Nat.cast_one]
  have hx : 0 ≤ y / w := div_nonneg hy0 hw.le
  have hk0 : 0 ≤ ⌊y / w⌋ := Int.floor_nonneg.mpr hx
  have hfl : (⌊y / w⌋ : ℝ) * w ≤ y := (le_div_iff₀ hw).mp (Int.floor_le _)
  have hfu : y < (⌊y / w⌋ + 1 : ℝ) * w := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one _)
  unfold intervalDigit
  by_cases hcase : Int.toNat ⌊y / w⌋ ≤ b - 1
  · have hd : ((min (b - 1) (Int.toNat ⌊y / w⌋) : ℕ) : ℝ) = (⌊y / w⌋ : ℝ) := by
      rw [min_eq_right hcase]
      have : ((⌊y / w⌋).toNat : ℤ) = ⌊y / w⌋ := Int.toNat_of_nonneg hk0
      exact_mod_cast this
    constructor
    · rw [hd]; linarith
    · rw [hd]
      have : y - (⌊y / w⌋ : ℝ) * w < w := by linarith
      exact le_trans (le_of_lt this) hk
  · have hge : b ≤ Int.toNat ⌊y / w⌋ := by omega
    have hbk : (b : ℤ) ≤ ⌊y / w⌋ := by
      have := Int.ofNat_le.mpr hge
      simpa [Int.toNat_of_nonneg hk0] using this
    have hyb : (b : ℝ) * w ≤ y := by
      have : (b : ℝ) ≤ (⌊y / w⌋ : ℝ) := Int.cast_le.mpr hbk
      nlinarith
    have hd : min (b - 1) (Int.toNat ⌊y / w⌋) = b - 1 :=
      min_eq_left (le_of_lt (Nat.not_le.mp hcase))
    have hdm : ((min (b - 1) (Int.toNat ⌊y / w⌋) : ℕ) : ℝ) = ((b - 1 : ℕ) : ℝ) := by
      simp [hd]
    constructor
    · rw [hdm]
      have : ((b - 1 : ℕ) : ℝ) * w ≤ (b : ℝ) * w := by
        rw [hcast]
        nlinarith
      linarith
    · rw [hdm]
      have : y ≤ ((b - 1 : ℕ) : ℝ) * w + ((b - 1 : ℕ) : ℝ) * S := by
        simpa [mul_add] using hy1
      linarith

/-- Geometric overlap for the constant-weight series `w_j = 4^{-(j+1)}`.
This is the equality `3 ∑_{i>j} w_i = w_j` used in Theorem 2.2. -/
theorem kakeya_geometric_four (j : ℕ) :
    (1 / 4 : ℝ) ^ (j + 1) = 3 * ∑' i : ℕ, (1 / 4 : ℝ) ^ (j + 2 + i) := by
  have hr0 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hr1 : (1 / 4 : ℝ) < 1 := by norm_num
  have hgeo : ∑' n : ℕ, (1 / 4 : ℝ) ^ n = (1 - 1 / 4 : ℝ)⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  have hinv : ((1 : ℝ) - 1 / 4)⁻¹ = 4 / 3 := by norm_num
  have hshift :
      ∑' i : ℕ, (1 / 4 : ℝ) ^ (j + 2 + i) =
        (1 / 4 : ℝ) ^ (j + 2) * ∑' i : ℕ, (1 / 4 : ℝ) ^ i := by
    rw [← tsum_mul_left]
    exact tsum_congr fun i => pow_add (1 / 4 : ℝ) (j + 2) i
  rw [hshift, hgeo, hinv]
  have : (1 / 4 : ℝ) ^ (j + 2) = (1 / 4 : ℝ) ^ (j + 1) * (1 / 4) := by
    rw [pow_succ]
  rw [this]
  ring

theorem kakeya_geometric_four_le (j : ℕ) :
    (1 / 4 : ℝ) ^ (j + 1) ≤ 3 * ∑' i : ℕ, (1 / 4 : ℝ) ^ (j + 2 + i) :=
  (kakeya_geometric_four j).le

#print axioms pairCorrection_sum
#print axioms pairCorrection_weighted
#print axioms pairCorrection_block_sum
#print axioms stageCorrection_modEq
#print axioms bounded_all_moduli_eventually_trivial
#print axioms intervalDigit_spec
#print axioms kakeya_geometric_four

end ErdosProblems.Erdos251
