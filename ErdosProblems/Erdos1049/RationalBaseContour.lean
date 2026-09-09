import ErdosProblems.Erdos1049.ZudilinHeightRegion
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Erdős #1049: the rational-base contour of Zudilin's `(14,12,14;27)` forms

The proof note `RationalBaseIrrationality_31_4_Proof.md` shows that the linear
forms of W. Zudilin, *Heine's basic transform and a permutation group for
q-harmonic series*, Acta Arith. 111 (2004) 153–164, in the direction
`(α₀,α₁,α₂;β) = (14,12,14;27)`, after homogenisation at a reduced rational base
`a/b`, prove that `F(a/b) = ∑_{m≥1} 1/((a/b)^m - 1)` is irrational whenever

`log b / log a < θ* := C₀ / C₁`,   `C₁ = 1091/2`,   `C₀ = 266 - (3/π²)(225 - J)`,

where `J = ∑_{i=1}^{13} (ψ₁(uᵢ) - ψ₁(vᵢ))` is the trigamma integral of Zudilin's
step function `ω` over its thirteen printed intervals `[uᵢ, vᵢ)` and
`ψ₁(x) = ∑_{k≥0} 1/(k+x)²`.

This module formalises the finite part of that theorem: the constants are
defined from the trigamma series, and Lean proves

* `eightyOne_twoHundredths_lt_zudilinContour : 81/200 < θ*` from the single
  `k = 0` term of each trigamma difference and `π > 3.14`;
* `zudilinContour_lt_half : θ* < 1/2` from `J < ψ₁(1/14) < 198`;
* membership of `31/4` and every power `(31/4)^r` in the contour region, and
  the inclusion of the older `81/200` region in it;
* exclusion of `3/2` from the contour region;
* the exact integer bookkeeping of the forms: `2M(a;b) = 2(266n² + 34n + 1)`,
  the degree step `d_{k+1} - d_k = 40n + 1 - k`, and the top degree
  `2 d_{b-1} = 1091n² + 81n + 2`.

No analytic step is formalised.  Zudilin's Lemma 7 (integrality in `ℤ[p]`),
his Lemma 2 (trigamma equidistribution of `φ(l)`), and the Archimedean
estimate stay in the ordinary proof note.  Membership in the contour region is
the exact hypothesis that note consumes; it is not by itself an irrationality
statement.
-/

namespace ErdosProblems.Erdos1049

/-! ## The trigamma series `ψ₁(x) = ∑_{k≥0} 1/(k+x)²` -/

/-- The series representation of the trigamma function.  Only this series is
used; the identification with `d²/dx² log Γ` is classical and not needed. -/
noncomputable def trigammaSeries (x : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2

theorem summable_trigammaTerm {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + x) ^ 2) := by
  have h := (Real.summable_one_div_nat_add_rpow x 2).2 (by norm_num)
  refine h.congr fun k => ?_
  have hpos : 0 < (k : ℝ) + x := by positivity
  rw [abs_of_pos hpos, Real.rpow_two]

theorem trigammaSeries_nonneg (x : ℝ) : 0 ≤ trigammaSeries x :=
  tsum_nonneg fun k => by positivity

/-- The trigamma series is decreasing on the positive axis. -/
theorem trigammaSeries_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    trigammaSeries y ≤ trigammaSeries x := by
  unfold trigammaSeries
  refine Summable.tsum_le_tsum (fun k => ?_)
    (summable_trigammaTerm (hx.trans_le hxy)) (summable_trigammaTerm hx)
  have h1 : 0 < (k : ℝ) + x := by positivity
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ h1.le (by linarith) 2)

/-- Any finite partial sum of the termwise difference bounds `ψ₁(u) - ψ₁(v)`
from below when `0 < u < v`. -/
theorem sum_le_trigammaSeries_sub {u v : ℝ} (hu : 0 < u) (huv : u < v) (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / ((k : ℝ) + u) ^ 2 - 1 / ((k : ℝ) + v) ^ 2) ≤
      trigammaSeries u - trigammaSeries v := by
  have hsu := summable_trigammaTerm hu
  have hsv := summable_trigammaTerm (hu.trans huv)
  unfold trigammaSeries
  rw [← hsu.tsum_sub hsv]
  refine (hsu.sub hsv).sum_le_tsum (Finset.range K) (fun k _ => ?_)
  have h1 : 0 < (k : ℝ) + u := by positivity
  have h2 : 1 / ((k : ℝ) + v) ^ 2 ≤ 1 / ((k : ℝ) + u) ^ 2 :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ h1.le (by linarith) 2)
  linarith

/-- The `k = 0` term alone. -/
theorem firstTerm_le_trigammaSeries_sub {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    1 / u ^ 2 - 1 / v ^ 2 ≤ trigammaSeries u - trigammaSeries v := by
  simpa using sum_le_trigammaSeries_sub hu huv 1

/-- `ψ₁(x) ≤ 1/x² + π²/6` for `0 < x`: split off the `k = 0` term and compare
the rest with `ζ(2)`. -/
theorem trigammaSeries_le (x : ℝ) (hx : 0 < x) :
    trigammaSeries x ≤ 1 / x ^ 2 + Real.pi ^ 2 / 6 := by
  set f : ℕ → ℝ := fun k => 1 / ((k : ℝ) + x) ^ 2 with hf
  set g : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2 with hg
  have hs : Summable f := summable_trigammaTerm hx
  have hs2 : Summable g := hasSum_zeta_two.summable
  have hzeta : ∑' k : ℕ, g (k + 1) = Real.pi ^ 2 / 6 := by
    have h := hasSum_zeta_two.tsum_eq
    rw [hs2.tsum_eq_zero_add] at h
    have h0 : g 0 = 0 := by simp [hg]
    rw [h0, zero_add] at h
    exact h
  have hshift : Summable (fun k : ℕ => f (k + 1)) := (summable_nat_add_iff 1).2 hs
  have hshift2 : Summable (fun k : ℕ => g (k + 1)) := (summable_nat_add_iff 1).2 hs2
  have hcmp : ∑' k : ℕ, f (k + 1) ≤ ∑' k : ℕ, g (k + 1) := by
    refine Summable.tsum_le_tsum (fun k => ?_) hshift hshift2
    simp only [hf, hg]
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ hk.le (by linarith) 2)
  have h0 : f 0 = 1 / x ^ 2 := by simp [hf]
  have hsplit : trigammaSeries x = f 0 + ∑' k : ℕ, f (k + 1) := hs.tsum_eq_zero_add
  rw [hsplit, h0]
  linarith

/-! ## The thirteen intervals and the constant `J` -/

/-- One interval's contribution `ψ₁(u) - ψ₁(v)`. -/
noncomputable def zudilinJTerm (u v : ℝ) : ℝ := trigammaSeries u - trigammaSeries v

/-- `J = ∫₀¹ ω(x) d(-ψ'(x))` over the thirteen intervals on which `ω = 1`
(Zudilin 2004, end of Section 5), written as the trigamma series. -/
noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)

/-- `C₁ = (α₀+α₁+α₂)β - (α₁²+α₂²+β²)/2 = 1091/2`, Zudilin's (25). -/
noncomputable def zudilinC1 : ℝ := 1091 / 2

/-- `C₀ = α₁²/2 + α₀α₁ + (β-α₂)(α₂-α₁) - (3/π²)(m² - J)` with `m = 15`,
Zudilin's (26). -/
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)

/-- The rational-base threshold `θ* = C₀/C₁ = 1/μ`, where `μ = C₁/C₀` is the
irrationality-exponent bound of Zudilin's Theorem 1. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1

/-- The parameter region of the authored rational-base theorem: reduced bases
`a/b` with `log b / log a < θ*`.  Membership is the hypothesis the ordinary
proof consumes; it is not an irrationality statement. -/
def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour

/-! ## Lower bound: `J > 77.6`, hence `θ* > 81/200` -/

theorem zudilinJTerm_ge {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    1 / u ^ 2 - 1 / v ^ 2 ≤ zudilinJTerm u v :=
  firstTerm_le_trigammaSeries_sub hu huv

/-- The `k = 0` terms already give `J ≥ 77.6` (the exact value is
`J = 77.943…`; the thirteen first terms sum to `77.609…`). -/
theorem zudilinJ_ge : (776 : ℝ) / 10 ≤ zudilinJ := by
  have h1 := zudilinJTerm_ge (u := 1 / 14) (v := 1 / 12) (by norm_num) (by norm_num)
  have h2 := zudilinJTerm_ge (u := 1 / 7) (v := 1 / 6) (by norm_num) (by norm_num)
  have h3 := zudilinJTerm_ge (u := 3 / 14) (v := 1 / 4) (by norm_num) (by norm_num)
  have h4 := zudilinJTerm_ge (u := 2 / 7) (v := 1 / 3) (by norm_num) (by norm_num)
  have h5 := zudilinJTerm_ge (u := 5 / 14) (v := 2 / 5) (by norm_num) (by norm_num)
  have h6 := zudilinJTerm_ge (u := 3 / 7) (v := 7 / 15) (by norm_num) (by norm_num)
  have h7 := zudilinJTerm_ge (u := 1 / 2) (v := 8 / 15) (by norm_num) (by norm_num)
  have h8 := zudilinJTerm_ge (u := 4 / 7) (v := 3 / 5) (by norm_num) (by norm_num)
  have h9 := zudilinJTerm_ge (u := 9 / 14) (v := 2 / 3) (by norm_num) (by norm_num)
  have h10 := zudilinJTerm_ge (u := 5 / 7) (v := 11 / 15) (by norm_num) (by norm_num)
  have h11 := zudilinJTerm_ge (u := 11 / 14) (v := 4 / 5) (by norm_num) (by norm_num)
  have h12 := zudilinJTerm_ge (u := 6 / 7) (v := 13 / 15) (by norm_num) (by norm_num)
  have h13 := zudilinJTerm_ge (u := 13 / 14) (v := 14 / 15) (by norm_num) (by norm_num)
  unfold zudilinJ
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 ⊢
  linarith

theorem zudilinC1_pos : 0 < zudilinC1 := by unfold zudilinC1; norm_num

/-- `C₀ > 88371/400 = (81/200) · C₁`, from `J ≥ 77.6` and `π > 3.14`. -/
theorem zudilinC0_gt : (88371 : ℝ) / 400 < zudilinC0 := by
  have hJ := zudilinJ_ge
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : (9.8596 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_pos]
  have hpi2pos : 0 < Real.pi ^ 2 := by positivity
  have hcoef : 3 / Real.pi ^ 2 < 3 / 9.8596 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hpi2
  have hT : 225 - zudilinJ ≤ 225 - 776 / 10 := by linarith
  have hTpos : (0 : ℝ) < 225 - 776 / 10 := by norm_num
  have hprod : 3 / Real.pi ^ 2 * (225 - zudilinJ) < 3 / 9.8596 * (225 - 776 / 10) := by
    calc 3 / Real.pi ^ 2 * (225 - zudilinJ)
        ≤ 3 / Real.pi ^ 2 * (225 - 776 / 10) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ < 3 / 9.8596 * (225 - 776 / 10) :=
          mul_lt_mul_of_pos_right hcoef hTpos
  unfold zudilinC0
  norm_num at hprod ⊢
  linarith

/-- **`81/200 < θ*`.**  The older `81/200` cutoff is a rational sub-boundary of
the contour. -/
theorem eightyOne_twoHundredths_lt_zudilinContour :
    (81 : ℝ) / 200 < zudilinContour := by
  unfold zudilinContour
  rw [lt_div_iff₀ zudilinC1_pos]
  have := zudilinC0_gt
  unfold zudilinC1
  linarith

/-! ## Upper bound: `J < ψ₁(1/14) < 198`, hence `θ* < 1/2` -/

/-- Telescoping through the ordered, disjoint intervals: every right endpoint
`vᵢ` is at most the next left endpoint `uᵢ₊₁`, and `ψ₁` is decreasing, so
`J ≤ ψ₁(1/14) - ψ₁(14/15) ≤ ψ₁(1/14)`. -/
theorem zudilinJ_le : zudilinJ ≤ trigammaSeries (1 / 14) := by
  have a1 := trigammaSeries_antitone (x := 1 / 12) (y := 1 / 7) (by norm_num) (by norm_num)
  have a2 := trigammaSeries_antitone (x := 1 / 6) (y := 3 / 14) (by norm_num) (by norm_num)
  have a3 := trigammaSeries_antitone (x := 1 / 4) (y := 2 / 7) (by norm_num) (by norm_num)
  have a4 := trigammaSeries_antitone (x := 1 / 3) (y := 5 / 14) (by norm_num) (by norm_num)
  have a5 := trigammaSeries_antitone (x := 2 / 5) (y := 3 / 7) (by norm_num) (by norm_num)
  have a6 := trigammaSeries_antitone (x := 7 / 15) (y := 1 / 2) (by norm_num) (by norm_num)
  have a7 := trigammaSeries_antitone (x := 8 / 15) (y := 4 / 7) (by norm_num) (by norm_num)
  have a8 := trigammaSeries_antitone (x := 3 / 5) (y := 9 / 14) (by norm_num) (by norm_num)
  have a9 := trigammaSeries_antitone (x := 2 / 3) (y := 5 / 7) (by norm_num) (by norm_num)
  have a10 := trigammaSeries_antitone (x := 11 / 15) (y := 11 / 14) (by norm_num) (by norm_num)
  have a11 := trigammaSeries_antitone (x := 4 / 5) (y := 6 / 7) (by norm_num) (by norm_num)
  have a12 := trigammaSeries_antitone (x := 13 / 15) (y := 13 / 14) (by norm_num) (by norm_num)
  have hlast := trigammaSeries_nonneg (14 / 15)
  unfold zudilinJ zudilinJTerm
  norm_num at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hlast ⊢
  linarith

theorem trigammaSeries_one_div_fourteen_lt : trigammaSeries (1 / 14) < 198 := by
  have h := trigammaSeries_le (1 / 14) (by norm_num)
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi2 : Real.pi ^ 2 < 9.9225 := by nlinarith [Real.pi_pos]
  norm_num at h
  linarith

theorem zudilinJ_lt : zudilinJ < 225 :=
  lt_of_le_of_lt zudilinJ_le (trigammaSeries_one_div_fourteen_lt.trans (by norm_num))

theorem zudilinC0_lt : zudilinC0 < 266 := by
  unfold zudilinC0
  have hJ := zudilinJ_lt
  have hpos : 0 < 3 / Real.pi ^ 2 := by positivity
  have : 0 < 3 / Real.pi ^ 2 * (225 - zudilinJ) := mul_pos hpos (by linarith)
  linarith

/-- **`θ* < 1/2`.**  With `C₁ = 545.5` and `C₀ < 266`, the contour sits below
`266/545.5 = 0.4876`. -/
theorem zudilinContour_lt_half : zudilinContour < 1 / 2 := by
  unfold zudilinContour
  rw [div_lt_iff₀ zudilinC1_pos]
  have := zudilinC0_lt
  unfold zudilinC1
  linarith

/-! ## Membership and exclusion -/

/-- The older `81/200` region is contained in the contour region. -/
theorem zudilinContourRegion_of_zudilinHeightRegion {a b : ℕ}
    (h : ZudilinHeightRegion a b) : ZudilinContourRegion a b :=
  h.trans eightyOne_twoHundredths_lt_zudilinContour

/-- `31/4` lies in the contour region. -/
theorem thirtyoneFour_mem_zudilinContourRegion : ZudilinContourRegion 31 4 :=
  zudilinContourRegion_of_zudilinHeightRegion thirtyoneFour_mem_zudilinHeightRegion

/-- The logarithmic height ratio is invariant under a common positive power. -/
theorem zudilinContourRegion_pow (a b r : ℕ) (hr : 0 < r)
    (h : ZudilinContourRegion a b) :
    ZudilinContourRegion (a ^ r) (b ^ r) := by
  unfold ZudilinContourRegion at h ⊢
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
  rw [mul_div_mul_left _ _ (by exact_mod_cast hr.ne')]
  exact h

/-- Every positive power of `31/4` lies in the contour region. -/
theorem thirtyoneFour_power_mem_zudilinContourRegion (r : ℕ) (hr : 0 < r) :
    ZudilinContourRegion (31 ^ r) (4 ^ r) :=
  zudilinContourRegion_pow 31 4 r hr thirtyoneFour_mem_zudilinContourRegion

/-- `1/2 < log 2 / log 3`, from `3 < 2²`. -/
theorem half_lt_threeHalves_log_ratio : (1 : ℝ) / 2 < Real.log 2 / Real.log 3 := by
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have h34 : Real.log (3 : ℝ) < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [lt_div_iff₀ hlog3]
  linarith

/-- `3/2` lies outside the full contour region, not only outside its `81/200`
sub-boundary.  This is a method boundary for this family of forms, not a
statement about the arithmetic nature of `F(3/2)`. -/
theorem threeHalves_outside_zudilinContourRegion : ¬ ZudilinContourRegion 3 2 := by
  intro h
  unfold ZudilinContourRegion at h
  have h1 := zudilinContour_lt_half
  have h2 := half_lt_threeHalves_log_ratio
  norm_num at h h2
  linarith

/-! ## Exact integer bookkeeping of the forms at index `n` -/

/-- `a₀ = 14n + 1`. -/
def zudilinA0 (n : ℤ) : ℤ := 14 * n + 1
/-- `a₁ = 12n + 1`. -/
def zudilinA1 (n : ℤ) : ℤ := 12 * n + 1
/-- `a₂ = 14n + 1`. -/
def zudilinA2 (n : ℤ) : ℤ := 14 * n + 1
/-- `b = 27n + 2`. -/
def zudilinB (n : ℤ) : ℤ := 27 * n + 2

/-- Zudilin's (16): `2M(a;b) = a₁(a₁-1) + 2a₀a₁ + 2(b-a₂)(a₂-a₁)` equals
`2(266n² + 34n + 1)`. -/
theorem two_mul_zudilinM (n : ℤ) :
    zudilinA1 n * (zudilinA1 n - 1) + 2 * zudilinA0 n * zudilinA1 n +
        2 * (zudilinB n - zudilinA2 n) * (zudilinA2 n - zudilinA1 n) =
      2 * (266 * n ^ 2 + 34 * n + 1) := by
  unfold zudilinA0 zudilinA1 zudilinA2 zudilinB
  ring

/-- Twice the `p`-degree of the `k`-th summand `A_k p^{a₀k}` of `A(p)`:
`2a₀k` plus twice the exponent of (8), plus twice the degrees
`(a₁-1)(k-a₁)` and `(b-k-1)(k-a₂)` of the two Gaussian binomials. -/
def twoMulZudilinSummandDegree (n k : ℤ) : ℤ :=
  2 * zudilinA0 n * k + zudilinA1 n * (zudilinA1 n - 1) -
      (zudilinB n - zudilinA2 n) * (zudilinB n - zudilinA2 n - 1) +
    (zudilinB n - k) * (zudilinB n - k - 1) +
    2 * (zudilinA1 n - 1) * (k - zudilinA1 n) +
    2 * (zudilinB n - k - 1) * (k - zudilinA2 n)

/-- The degree step `d_{k+1} - d_k = 40n + 1 - k`, positive for
`k ≤ b - 2 = 27n`; hence the top summand `k = b - 1` carries the degree of
`A(p)` alone and no cancellation can occur. -/
theorem twoMulZudilinSummandDegree_succ_sub (n k : ℤ) :
    twoMulZudilinSummandDegree n (k + 1) - twoMulZudilinSummandDegree n k =
      2 * (40 * n + 1 - k) := by
  unfold twoMulZudilinSummandDegree zudilinA0 zudilinA1 zudilinA2 zudilinB
  ring

/-- The top degree: `2 deg A_n = 1091n² + 81n + 2`, so `deg A_n / n² → C₁`. -/
theorem twoMulZudilinSummandDegree_top (n : ℤ) :
    twoMulZudilinSummandDegree n (zudilinB n - 1) = 1091 * n ^ 2 + 81 * n + 2 := by
  unfold twoMulZudilinSummandDegree zudilinA0 zudilinA1 zudilinA2 zudilinB
  ring

/-- The step is positive on the whole summation range `a₂ ≤ k ≤ b - 2`. -/
theorem twoMulZudilinSummandDegree_step_pos (n k : ℤ) (hn : 0 ≤ n)
    (hk : k ≤ zudilinB n - 2) :
    0 < twoMulZudilinSummandDegree n (k + 1) - twoMulZudilinSummandDegree n k := by
  rw [twoMulZudilinSummandDegree_succ_sub]
  unfold zudilinB at hk
  omega

end ErdosProblems.Erdos1049
