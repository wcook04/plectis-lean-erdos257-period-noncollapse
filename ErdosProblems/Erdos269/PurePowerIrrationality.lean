import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Erdős #269 companion: a conditional irrationality criterion for Cantor-state series

Let `H(x) = ∏_p p^⌊log_p x⌋` be the running `{2,3,5}`-smooth LCM height and put

    Σ₂ = ∑_{m ≥ 1} 1/H(2^m)  =  0.5931259677635827115280234…

This is **not** Erdős #269 itself, which asks about `S = ∑_{smooth s ≥ 2} 1/H(s)`.
`Σ₂` is the sub-series carried by one prime channel.

This file proves four theorems:

* `state_mem_Ioo`: interval confinement. A Cantor state obeying the
  recurrence `y' = b·y − 1` with `y' ∈ (0,1)` lies in `(1/b, 2/b)`.
* `stateGap_lower_bound`: separation. States confined by leading radices
  `a` and `p·a` with `p ≥ 3` are separated by at least `1/(3a)`.
* `irrational_of_small_nonzero_forms`: the general criterion that if integer
  linear forms `n·x − k` take arbitrarily small nonzero values, `x` is
  irrational.
* `irrational_of_clearing_and_small_gaps`: the conditional assembly theorem.
  Given a normalizer sequence `Hgt : ℕ → ℤ` and a state sequence `y : ℕ → ℝ`
  with (`clear`) `∀ M, ∃ z, y M = Hgt M * x − z` and (`gaps`) for every `d`
  there exist `M, M'` with `Hgt M ≠ Hgt M'`, `y M ≠ y M'`, and
  `|y M − y M'| < 1/d`, then `x` is irrational.

The `clear` and `gaps` hypotheses of `irrational_of_clearing_and_small_gaps`
range over arbitrary sequences and are not discharged in this file for `Σ₂`
or for any other concrete series. The sketch below states, without
formalizing, how `state_mem_Ioo` and `stateGap_lower_bound` would discharge
`gaps` for `Σ₂` given a Sturmian right-special-factor input supplied outside
this file. No theorem in this file establishes `Irrational Σ₂`.

## The argument sketch (unformalized in this file)

Write `H_M = H(2^{M-1})` and `y_M = H_M · ∑_{m ≥ M} 1/H(2^m)`.  Then

* **clearing**: `H(2^m) ∣ H_M` for `m < M`, so `y_M = H_M·Σ₂ − (integer)`;
* **range**: `0 < y_M < 1`;
* **recurrence**: `y_{M+1} = b_{M-1}·y_M − 1`, where `b ∈ {2,6,10,30}`.

The recurrence plus the range force the interval confinement
`y_M ∈ (1/b, 2/b)`, so two states whose leading radices differ by a factor
`p ≥ 3` are separated by at least `1/(3b)`. The Sturmian input is that for
every `L` the radix word has a right-special factor of length `L` with two
extensions differing by a single non-dyadic channel. Two occurrences
`M ≠ M'` then satisfy `y_M − y_M' = (y_{M+L} − y_{M'+L}) / P` with `P ≥ 2^L`,
so the gap is nonzero and tends to `0`.
-/

namespace ErdosProblems.Erdos269

/-! ### Interval confinement -/

/-- **Interval confinement.**  A Cantor state with all digits `1` obeying
`y' = b·y − 1` with `y'` in `(0,1)` is confined to `(1/b, 2/b)`.  The confining
interval is determined by the *current radix letter alone*. -/
theorem state_mem_Ioo {b : ℕ} (hb : 0 < b) {y y' : ℝ}
    (hrec : y' = (b : ℝ) * y - 1) (h0 : 0 < y') (h1 : y' < 1) :
    1 / (b : ℝ) < y ∧ y < 2 / (b : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  constructor
  · rw [div_lt_iff₀ hbR, mul_comm]
    nlinarith [hrec, h0]
  · rw [lt_div_iff₀ hbR, mul_comm]
    nlinarith [hrec, h1]

/-- **Separation.**  States confined by leading radices `a` and `p·a` with
`p ≥ 3` are separated by at least `1/(3a)`.  A factor of two would give gap
zero, which is why the flipped channel must be a non-dyadic prime. -/
theorem stateGap_lower_bound {a p : ℕ} (ha : 0 < a) (hp : 3 ≤ p) {u v : ℝ}
    (hu : 1 / (a : ℝ) < u) (hv : v < 2 / ((p : ℝ) * (a : ℝ))) :
    1 / (3 * (a : ℝ)) < u - v := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) := by linarith
  have hstep : 2 / ((p : ℝ) * (a : ℝ)) ≤ 2 / (3 * (a : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have : v < 2 / (3 * (a : ℝ)) := lt_of_lt_of_le hv hstep
  have hsplit : 1 / (a : ℝ) - 2 / (3 * (a : ℝ)) = 1 / (3 * (a : ℝ)) := by
    field_simp
    ring
  linarith [hsplit]

/-! ### From small nonzero linear forms to irrationality -/

/-- If integer linear forms in `x` take arbitrarily small nonzero values then
`x` is irrational.  A rational `x` with denominator `d` admits no nonzero value
of `|n·x − k|` below `1/d`. -/
theorem irrational_of_small_nonzero_forms {x : ℝ}
    (h : ∀ d : ℕ, 0 < d → ∃ n k : ℤ, 0 < |(n : ℝ) * x - (k : ℝ)| ∧
        |(n : ℝ) * x - (k : ℝ)| < 1 / (d : ℝ)) :
    Irrational x := by
  rintro ⟨q, rfl⟩
  obtain ⟨n, k, hpos, hlt⟩ := h q.den q.pos
  set r : ℚ := (n : ℚ) * q - (k : ℚ) with hr
  have hcast : ((r : ℚ) : ℝ) = (n : ℝ) * (q : ℝ) - (k : ℝ) := by
    simp [hr]
  have hrne : r ≠ 0 := by
    intro hzero
    rw [hzero] at hcast
    simp at hcast
    rw [← hcast] at hpos
    simp at hpos
  -- `q.den * r` is an integer, hence has absolute value at least one
  set z : ℤ := n * q.num - (k : ℤ) * (q.den : ℤ) with hz
  have hzr : (z : ℚ) = (q.den : ℚ) * r := by
    have hq : (q.num : ℚ) = q * (q.den : ℚ) := by
      rw [mul_comm]
      exact_mod_cast (Rat.den_mul_eq_num q).symm
    rw [hz, hr]
    push_cast
    rw [hq]
    ring
  have hzne : z ≠ 0 := by
    intro hzero
    apply hrne
    have : (q.den : ℚ) * r = 0 := by rw [← hzr, hzero]; norm_num
    rcases mul_eq_zero.mp this with hd | hrr
    · exact absurd hd (by exact_mod_cast q.den_nz)
    · exact hrr
  have hone : (1 : ℚ) ≤ |(z : ℚ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hzne
    exact_mod_cast this
  have hdenpos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  have hgeq : 1 / (q.den : ℝ) ≤ |(n : ℝ) * (q : ℝ) - (k : ℝ)| := by
    rw [← hcast]
    have : (1 : ℝ) ≤ (q.den : ℝ) * |((r : ℚ) : ℝ)| := by
      have h1 : ((|(z : ℚ)| : ℚ) : ℝ) = (q.den : ℝ) * |((r : ℚ) : ℝ)| := by
        rw [hzr]
        push_cast
        rw [abs_mul, abs_of_nonneg (le_of_lt hdenpos)]
      have h2 : (1 : ℝ) ≤ ((|(z : ℚ)| : ℚ) : ℝ) := by exact_mod_cast hone
      linarith [h1 ▸ h2]
    rw [div_le_iff₀ hdenpos, mul_comm]
    linarith
  linarith

/-! ### Assembly -/

/-- **Irrationality from clearing plus arbitrarily small nonzero state gaps.**

`Hgt` are the clearing normalizers and `y` the normalized tail states, so that
`y M = Hgt M · x − (integer)`.  If for every `d` there are two scales whose
normalizers differ and whose states differ by a nonzero amount below `1/d`,
then `x` is irrational.

For the pure prime-power series the hypothesis is delivered by the Sturmian
right-special combinatorics together with `state_mem_Ioo` and
`stateGap_lower_bound`: the gap is `(y_{M+L} − y_{M'+L})/P`, bounded below by
`1/(3·30·P)` and above by `1/P`, with `P ≥ 2^L`. -/
theorem irrational_of_clearing_and_small_gaps {x : ℝ} {Hgt : ℕ → ℤ} {y : ℕ → ℝ}
    (clear : ∀ M : ℕ, ∃ z : ℤ, y M = (Hgt M : ℝ) * x - (z : ℝ))
    (gaps : ∀ d : ℕ, 0 < d → ∃ M M' : ℕ,
      Hgt M ≠ Hgt M' ∧ y M ≠ y M' ∧ |y M - y M'| < 1 / (d : ℝ)) :
    Irrational x := by
  refine irrational_of_small_nonzero_forms ?_
  intro d hd
  obtain ⟨M, M', hH, hy, hsmall⟩ := gaps d hd
  obtain ⟨z, hzM⟩ := clear M
  obtain ⟨z', hzM'⟩ := clear M'
  refine ⟨Hgt M - Hgt M', z - z', ?_, ?_⟩
  · have hval : (((Hgt M - Hgt M' : ℤ)) : ℝ) * x - (((z - z' : ℤ)) : ℝ)
        = y M - y M' := by
      rw [hzM, hzM']
      push_cast
      ring
    rw [hval, abs_pos]
    exact sub_ne_zero_of_ne hy
  · have hval : (((Hgt M - Hgt M' : ℤ)) : ℝ) * x - (((z - z' : ℤ)) : ℝ)
        = y M - y M' := by
      rw [hzM, hzM']
      push_cast
      ring
    rw [hval]
    exact hsmall

end ErdosProblems.Erdos269
