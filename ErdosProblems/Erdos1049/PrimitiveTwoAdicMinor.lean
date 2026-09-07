import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Erdős #1049: 2-adic valuation of primitive minors in a three-row 2004 deformation

This is a *2004* construction family (Zudilin, Acta Arith. 111 (2004), (8)–(11)),
not the 2016 Hankel family.  The two must not be mixed.

For `n ≥ 1` and `s ∈ {0,1,2}` the source parameters are
`a₀ = 14n+2`, `a₁ = 12n+1`, `a₂ = 14n+1-s`, `β = 27n+2`.  The unique
top-degree summand of `A_{n,s}` has degree

```
K_s = (1091 n²)/2 - 13 n s + (135 n)/2 - (s²+s)/2 + 2.
```

In particular `K_2 = (1091 n² + 83 n - 2)/2`.  Evaluating the leading monomial
at `p = 3/2` gives `v₂(A) = -K_s` once the leading coefficient is a 2-adic
unit.  The companion ordinary-proof note
`PrimitiveTwoAdicMinor.md` discharges that unit, the identity `A F₂ - B = H`
with `v₂(H) = 0`, and the crossing `A_i B_j - A_j B_i = A_j L_i - A_i L_j`.
This module Lean-checks the integer degree arithmetic (on twice the degree,
so that no truncating integer division appears) and the 2-adic calculus
those steps consume.

The matching 3-adic pattern `v₃(g_n) = 2(n-1)²` is an ordinary identity once
the small-p unit is granted; this module Lean-checks the primitive valuation
subtraction and the `D_s` minor arithmetic.  No theorem here decides `F(3/2)`.
The wide quadratic family is not defined here; use the existing unimodular
collision theorems in `BezoutPluckerJets.lean` rather than a new wrapper.
-/

namespace ErdosProblems.Erdos1049

/-! ## Source parameters and twice the unique top degree -/

def zudilinDefA0 (n : ℕ) : ℤ := 14 * n + 2
def zudilinDefA1 (n : ℕ) : ℤ := 12 * n + 1
def zudilinDefA2 (n s : ℕ) : ℤ := 14 * n + 1 - s
def zudilinDefBeta (n : ℕ) : ℤ := 27 * n + 2

/-- Twice the Gaussian-binomial `x`-degree plus the explicit monomial
`e_k + a₀ k`.  Consecutive-integer products are even, so this is exactly
twice the source degree. -/
def twoMulSummandDegree (n s k : ℕ) : ℤ :=
  let a0 := zudilinDefA0 n
  let a1 := zudilinDefA1 n
  let a2 := zudilinDefA2 n s
  let β := zudilinDefBeta n
  a1 * (a1 - 1) - (β - a2) * (β - a2 - 1) + (β - k) * (β - k - 1) +
    2 * (a0 * k + (a1 - 1) * (k - a1) + (β - k - 1) * (k - a2))

/-- Twice the closed form `K_s`.  Always even for integer `n,s`. -/
def twoMulKs (n s : ℕ) : ℤ :=
  1091 * n ^ 2 - 26 * n * s + 135 * n - (s * s + s) + 4

theorem twoMulKs_of_s_two (n : ℕ) :
    twoMulKs n 2 = 1091 * n ^ 2 + 83 * n - 2 := by
  simp [twoMulKs]
  ring

/-- Twice the degree increment is `2(a₀+a₁+a₂-k-2) = 2(40n+2-s-k)`. -/
theorem twoMulSummandDegree_succ_sub (n s k : ℕ) :
    twoMulSummandDegree n s (k + 1) - twoMulSummandDegree n s k =
      2 * (40 * n + 2 - s - k) := by
  simp [twoMulSummandDegree, zudilinDefA0, zudilinDefA1, zudilinDefA2,
    zudilinDefBeta]
  ring

/-- Strict positivity of the increment throughout the summation range. -/
theorem zudilinDefSummandDegree_step_pos {n s k : ℕ}
    (hn : 0 < n) (hs : s ≤ 2) (hk : k ≤ 27 * n) :
    0 < (40 * n + 2 - s - k : ℤ) := by
  have : (k : ℤ) ≤ 27 * n := by exact_mod_cast hk
  have : (s : ℤ) ≤ 2 := by exact_mod_cast hs
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- The unique top index is `k = β-1 = 27n+1`. -/
theorem zudilinDefTopIndex (n : ℕ) : zudilinDefBeta n - 1 = 27 * n + 1 := by
  simp [zudilinDefBeta]
  ring

/-- Closed form of twice the top degree. -/
theorem twoMul_zudilinDefSummandDegree_top (n s : ℕ) :
    twoMulSummandDegree n s (27 * n + 1) = twoMulKs n s := by
  simp [twoMulSummandDegree, zudilinDefA0, zudilinDefA1, zudilinDefA2,
    zudilinDefBeta, twoMulKs]
  ring

theorem twoMul_topDegree_s_two (n : ℕ) :
    twoMulSummandDegree n 2 (27 * n + 1) =
      1091 * n ^ 2 + 83 * n - 2 := by
  rw [twoMul_zudilinDefSummandDegree_top, twoMulKs_of_s_two]

/-! ## 2-adic calculus at the base `3/2` -/

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem padicValRat_two_two : padicValRat 2 (2 : ℚ) = 1 :=
  padicValRat.self (by norm_num : (1 : ℕ) < 2)

theorem padicValRat_two_three : padicValRat 2 (3 : ℚ) = 0 := by
  have h : ¬ 2 ∣ (3 : ℕ) := by decide
  trans ↑(padicValNat 2 3)
  · exact (padicValRat_of_nat (p := 2) 3).symm
  · simp [padicValNat.eq_zero_of_not_dvd h]

theorem padicValRat_two_three_halves : padicValRat 2 (3 / 2 : ℚ) = -1 := by
  have h3 : (3 : ℚ) ≠ 0 := by norm_num
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  rw [padicValRat.div h3 h2, padicValRat_two_three, padicValRat_two_two]
  norm_num

theorem padicValRat_two_three_halves_pow (k : ℕ) :
    padicValRat 2 ((3 / 2 : ℚ) ^ k) = -k := by
  have hq : (3 / 2 : ℚ) ≠ 0 := by norm_num
  rw [padicValRat.pow hq, padicValRat_two_three_halves]
  ring

/-- A 2-adic unit times `(3/2)^K` has valuation `-K`. -/
theorem padicValRat_two_unit_mul_three_halves_pow {u : ℚ} (k : ℕ)
    (hu0 : u ≠ 0) (hu : padicValRat 2 u = 0) :
    padicValRat 2 (u * (3 / 2 : ℚ) ^ k) = -k := by
  have hq : (3 / 2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [padicValRat.mul hu0 hq, hu, padicValRat_two_three_halves_pow, zero_add]

/-- Clearing valuation `-K` by multiplying through by `2^K` yields a unit. -/
theorem padicValRat_two_scale_leading {A : ℚ} {K : ℕ}
    (hA0 : A ≠ 0) (hA : padicValRat 2 A = -K) :
    padicValRat 2 (A * (2 : ℚ) ^ K) = 0 := by
  have h2 : (2 : ℚ) ^ K ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [padicValRat.mul hA0 h2, hA, padicValRat.pow (by norm_num : (2 : ℚ) ≠ 0),
    padicValRat_two_two]
  ring

/-- If `L = A ξ - B` then the pairwise minor equals the error cross product. -/
theorem minor_eq_error_cross (Ai Bi Li Aj Bj Lj ξ : ℚ)
    (hi : Li = Ai * ξ - Bi) (hj : Lj = Aj * ξ - Bj) :
    Ai * Bj - Aj * Bi = Aj * Li - Ai * Lj := by
  rw [hi, hj]
  ring

/-- Unequal 2-adic valuations pass to a difference. -/
theorem padicValRat_two_sub_of_lt {x y : ℚ}
    (hxy : x - y ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hval : padicValRat 2 y < padicValRat 2 x) :
    padicValRat 2 (x - y) = padicValRat 2 y := by
  have hsum : (-y) + x ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hxy
  have hy' : -y ≠ 0 := neg_ne_zero.mpr hy
  have hlt : padicValRat 2 (-y) < padicValRat 2 x := by
    simpa [padicValRat.neg] using hval
  have h := padicValRat.add_eq_of_lt (p := 2) hsum hy' hx hlt
  simpa [sub_eq_add_neg, add_comm, padicValRat.neg] using h

/-- The three-row minor with `K_i > K_j` has 2-adic valuation `K_j`, once the
first coordinates are units and the primitive errors have valuations `K_s`. -/
theorem padicValRat_two_error_cross {Ai Aj Li Lj : ℚ} {Ki Kj : ℤ}
    (hAi : Ai ≠ 0) (hAj : Aj ≠ 0) (hLi : Li ≠ 0) (hLj : Lj ≠ 0)
    (hdiff : Aj * Li - Ai * Lj ≠ 0)
    (vAi : padicValRat 2 Ai = 0) (vAj : padicValRat 2 Aj = 0)
    (vLi : padicValRat 2 Li = Ki) (vLj : padicValRat 2 Lj = Kj)
    (hK : Kj < Ki) :
    padicValRat 2 (Aj * Li - Ai * Lj) = Kj := by
  have hx0 : Aj * Li ≠ 0 := mul_ne_zero hAj hLi
  have hy0 : Ai * Lj ≠ 0 := mul_ne_zero hAi hLj
  have vx : padicValRat 2 (Aj * Li) = Ki := by
    rw [padicValRat.mul hAj hLi, vAj, vLi, zero_add]
  have vy : padicValRat 2 (Ai * Lj) = Kj := by
    rw [padicValRat.mul hAi hLj, vAi, vLj, zero_add]
  have hlt : padicValRat 2 (Ai * Lj) < padicValRat 2 (Aj * Li) := by
    simpa [vx, vy] using hK
  rw [padicValRat_two_sub_of_lt hdiff hx0 hy0 hlt, vy]

/-! ## 3-adic primitive valuation subtraction and the three-row minor formula

The unit identity `v₃(A_raw)=M+dt`, `v₃(B_raw)=M` is ordinary (Type B r4,
small-p expansion).  Once that identity is granted, the primitive pair and
the three-row gcd are finite 3-adic calculus, recorded here.  The wide
quadratic family is not defined in this module; its pigeonhole consumer is
the existing unimodular theorem
`BezoutPluckerJets.zmod_binary_tail_collision_of_adjacent_det_zero_of_isCoprime`.
-/

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem padicValRat_three_three : padicValRat 3 (3 : ℚ) = 1 :=
  padicValRat.self (by norm_num : (1 : ℕ) < 3)

theorem padicValRat_three_two : padicValRat 3 (2 : ℚ) = 0 := by
  have h : ¬ 3 ∣ (2 : ℕ) := by decide
  trans ↑(padicValNat 3 2)
  · exact (padicValRat_of_nat (p := 3) 2).symm
  · simp [padicValNat.eq_zero_of_not_dvd h]

theorem padicValRat_three_three_halves : padicValRat 3 (3 / 2 : ℚ) = 1 := by
  have h3 : (3 : ℚ) ≠ 0 := by norm_num
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  rw [padicValRat.div h3 h2, padicValRat_three_three, padicValRat_three_two]
  norm_num

/-- Source cone quantity `D_s = (2n-s)(n+1-s)`. -/
def zudilinThreeAdicD (n s : ℤ) : ℤ :=
  (2 * n - s) * (n + 1 - s)

theorem zudilinThreeAdicD_s_two (n : ℤ) :
    zudilinThreeAdicD n 2 = 2 * (n - 1) ^ 2 := by
  simp [zudilinThreeAdicD]
  ring

theorem zudilinThreeAdicD_succ_sub (n s : ℤ) :
    zudilinThreeAdicD n s - zudilinThreeAdicD n (s + 1) = 3 * n - 2 * s := by
  simp [zudilinThreeAdicD]
  ring

theorem zudilinThreeAdicD_strict_anti {n s : ℤ}
    (hn : (2 : ℤ) ≤ n) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    zudilinThreeAdicD n (s + 1) < zudilinThreeAdicD n s := by
  have hdiff := zudilinThreeAdicD_succ_sub n s
  nlinarith

/-- Clearing the common published exponent `M` leaves valuations `d` and `0`. -/
theorem padicValRat_scale_min {p : ℕ} [Fact p.Prime] {A B scal : ℚ} {M d : ℤ}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hscal0 : scal ≠ 0)
    (hA : padicValRat p A = M + d) (hB : padicValRat p B = M)
    (hscal : padicValRat p scal = -M) :
    padicValRat p (scal * A) = d ∧ padicValRat p (scal * B) = 0 := by
  constructor
  · rw [padicValRat.mul hscal0 hA0, hscal, hA]; ring
  · rw [padicValRat.mul hscal0 hB0, hscal, hB]; ring

theorem padicValRat_sub_of_lt {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hxy : x - y ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hval : padicValRat p y < padicValRat p x) :
    padicValRat p (x - y) = padicValRat p y := by
  have hsum : (-y) + x ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hxy
  have hy' : -y ≠ 0 := neg_ne_zero.mpr hy
  have hlt : padicValRat p (-y) < padicValRat p x := by
    simpa [padicValRat.neg] using hval
  have h := padicValRat.add_eq_of_lt (p := p) hsum hy' hx hlt
  simpa [sub_eq_add_neg, add_comm, padicValRat.neg] using h

/-- If `v_p(A_i)=D_i`, `v_p(B_i)=0` and `D_j < D_i`, the minor has valuation `D_j`. -/
theorem padicValRat_minor_of_unequal_A {p : ℕ} [Fact p.Prime]
    {Ai Bi Aj Bj : ℚ} {Di Dj : ℤ}
    (hAi : Ai ≠ 0) (hAj : Aj ≠ 0) (hBi : Bi ≠ 0) (hBj : Bj ≠ 0)
    (hdiff : Ai * Bj - Aj * Bi ≠ 0)
    (vAi : padicValRat p Ai = Di) (vBi : padicValRat p Bi = 0)
    (vAj : padicValRat p Aj = Dj) (vBj : padicValRat p Bj = 0)
    (hD : Dj < Di) :
    padicValRat p (Ai * Bj - Aj * Bi) = Dj := by
  have hx0 : Ai * Bj ≠ 0 := mul_ne_zero hAi hBj
  have hy0 : Aj * Bi ≠ 0 := mul_ne_zero hAj hBi
  have vx : padicValRat p (Ai * Bj) = Di := by
    rw [padicValRat.mul hAi hBj, vAi, vBj, add_zero]
  have vy : padicValRat p (Aj * Bi) = Dj := by
    rw [padicValRat.mul hAj hBi, vAj, vBi, add_zero]
  have hlt : padicValRat p (Aj * Bi) < padicValRat p (Ai * Bj) := by
    simpa [vx, vy] using hD
  rw [padicValRat_sub_of_lt hdiff hx0 hy0 hlt, vy]

/-- For `n ≥ 2`, the three cone values `D_0 > D_1 > D_2` and the corner is
`2(n-1)²`.  Combined with `padicValRat_minor_of_unequal_A` this is the
all-`n` formula `v₃(g_n)=2(n-1)²` once the unit identity supplies
`v₃(A_{n,s})=D_s` and `v₃(B_{n,s})=0`. -/
theorem zudilinThreeAdicD_min_s_two {n : ℤ} (hn : (2 : ℤ) ≤ n) :
    zudilinThreeAdicD n 2 < zudilinThreeAdicD n 1 ∧
      zudilinThreeAdicD n 1 < zudilinThreeAdicD n 0 ∧
      zudilinThreeAdicD n 2 = 2 * (n - 1) ^ 2 := by
  refine ⟨?_, ?_, zudilinThreeAdicD_s_two n⟩
  · exact zudilinThreeAdicD_strict_anti hn (by norm_num) (by norm_num)
  · exact zudilinThreeAdicD_strict_anti hn (by norm_num) (by norm_num)

/-- Integer core of a regular-scale determinant obstruction: a nonzero integer
is at least `p` to the power of its `p`-adic valuation.  The Archimedean
limsup argument remains ordinary. -/
theorem natAbs_ge_pow_padicValInt {p : ℕ} [hp : Fact p.Prime] {n : ℤ}
    (hn : n ≠ 0) :
    p ^ padicValInt p n ≤ n.natAbs := by
  have hdiv : (p : ℤ) ^ padicValInt p n ∣ n := padicValInt_dvd n
  have : p ^ padicValInt p n ∣ n.natAbs := by
    exact Int.natAbs_dvd_natAbs.mpr hdiv
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn) this

end ErdosProblems.Erdos1049
