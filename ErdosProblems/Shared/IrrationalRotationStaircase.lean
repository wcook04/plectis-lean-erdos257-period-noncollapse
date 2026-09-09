import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Irrational-rotation staircases and the carry-staircase determinant

Two independent pieces of reusable machinery.

* `ErdosProblems.Shared.exists_pos_nat_fract_mem_Ioo` : the **forward** orbit
  `n ↦ Int.fract (n * α)`, `n ≥ 1`, is dense in `[0,1]` as soon as no positive
  integer multiple of `α` is an integer.  The hypothesis is packaged as
  `NoIntegerOrbit`; for real `α` it is exactly irrationality, but it is often
  cheaper to verify directly.

* `ErdosProblems.Shared.det_carryStaircase` : the exact determinant
  `det (fun i j => if j ≤ i then t else 1) = t * (t - 1) ^ n`
  of the `(n+1)`-dimensional *carry staircase*.

Combined in `exists_staircase_indices`, they say that a pair of independent
rotations without integer returns realises an arbitrarily large staircase in
the two-dimensional carry `⌊fract (i * α) + fract (j * β)⌋`.  That is the
engine behind the three-prime running-LCM rank phase transition of Erdős #269.

Nothing here mentions a specific Erdős problem; the file is Mathlib-only.
-/

namespace ErdosProblems.Shared

open Set Matrix

/-! ## Forward orbits of a rotation without integer returns -/

/-- `NoIntegerOrbit α` : no positive integer multiple of `α` is an integer.
For real `α` this is equivalent to irrationality of `α`. -/
def NoIntegerOrbit (α : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → Int.fract ((n : ℝ) * α) ≠ 0

/-- Scaling a real by a natural number is transparent to `Int.fract` as long
as the scaled fractional part has not yet wrapped. -/
theorem fract_natCast_mul_of_lt_one {x : ℝ} {m : ℕ}
    (h : (m : ℝ) * Int.fract x < 1) :
    Int.fract ((m : ℝ) * x) = (m : ℝ) * Int.fract x := by
  have h0 : (0 : ℝ) ≤ (m : ℝ) * Int.fract x :=
    mul_nonneg (Nat.cast_nonneg m) (Int.fract_nonneg x)
  have hx : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
  have key : (m : ℝ) * x = ((m * ⌊x⌋ : ℤ) : ℝ) + (m : ℝ) * Int.fract x := by
    calc (m : ℝ) * x = (m : ℝ) * ((⌊x⌋ : ℝ) + Int.fract x) := by rw [← hx]
      _ = ((m * ⌊x⌋ : ℤ) : ℝ) + (m : ℝ) * Int.fract x := by push_cast; ring
  rw [key, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨h0, h⟩]

/-- From two orbit points landing in the same `ε`-bin, extract a positive
index whose orbit point is within `ε` of `0` or of `1`. -/
private theorem step_of_close {α : ℝ} {ε : ℝ} {a b : ℕ}
    (hab : a < b) (hε1 : ε ≤ 1)
    (h : |Int.fract ((b : ℝ) * α) - Int.fract ((a : ℝ) * α)| < ε) :
    ∃ k : ℕ, 0 < k ∧
      (Int.fract ((k : ℝ) * α) < ε ∨ 1 - ε < Int.fract ((k : ℝ) * α)) := by
  refine ⟨b - a, by omega, ?_⟩
  set s : ℝ := Int.fract ((b : ℝ) * α) - Int.fract ((a : ℝ) * α) with hs
  have habs := abs_lt.1 h
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by
    rw [Nat.cast_sub hab.le]
  have hfr : Int.fract (((b - a : ℕ) : ℝ) * α) = Int.fract s := by
    refine Int.fract_eq_fract.2 ⟨⌊(b : ℝ) * α⌋ - ⌊(a : ℝ) * α⌋, ?_⟩
    rw [hcast, hs, Int.fract, Int.fract]
    push_cast
    ring
  rcases le_or_gt 0 s with hs0 | hs0
  · left
    have hs1 : s < 1 := lt_of_lt_of_le habs.2 hε1
    rw [hfr, Int.fract_eq_self.2 ⟨hs0, hs1⟩]
    exact habs.2
  · right
    have hlow : (0 : ℝ) ≤ s + 1 := by linarith [habs.1, hε1]
    have hhigh : s + 1 < 1 := by linarith
    have hshift : Int.fract s = s + 1 := by
      have hrw : Int.fract s = Int.fract (s + 1) :=
        Int.fract_eq_fract.2 ⟨-1, by push_cast; ring⟩
      rw [hrw, Int.fract_eq_self.2 ⟨hlow, hhigh⟩]
    rw [hfr, hshift]
    linarith [habs.1]

/-- Dirichlet's pigeonhole step: some positive orbit index lands `ε`-close to
`0` or to `1`.  No hypothesis on `α` is needed. -/
theorem exists_small_step {α : ℝ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ k : ℕ, 0 < k ∧
      (Int.fract ((k : ℝ) * α) < ε ∨ 1 - ε < Int.fract ((k : ℝ) * α)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNR : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hN
  have hNpos : 0 < N := by exact_mod_cast hNR
  have hinv : 1 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hNR]
    rw [div_lt_iff₀ hε] at hN
    linarith
  have hbin : ∀ i : Fin (N + 1),
      ⌊(N : ℝ) * Int.fract (((i : ℕ) : ℝ) * α)⌋₊ < N := by
    intro i
    have h0 : (0 : ℝ) ≤ (N : ℝ) * Int.fract (((i : ℕ) : ℝ) * α) :=
      mul_nonneg hNR.le (Int.fract_nonneg _)
    have h1 : (N : ℝ) * Int.fract (((i : ℕ) : ℝ) * α) < (N : ℝ) := by
      nlinarith [Int.fract_lt_one (((i : ℕ) : ℝ) * α)]
    exact (Nat.floor_lt h0).2 (by exact_mod_cast h1)
  set f : Fin (N + 1) → Fin N := fun i =>
    ⟨⌊(N : ℝ) * Int.fract (((i : ℕ) : ℝ) * α)⌋₊, hbin i⟩ with hf
  have hcard : Fintype.card (Fin N) < Fintype.card (Fin (N + 1)) := by simp
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hbins : ⌊(N : ℝ) * Int.fract (((i : ℕ) : ℝ) * α)⌋₊
      = ⌊(N : ℝ) * Int.fract (((j : ℕ) : ℝ) * α)⌋₊ := by
    simpa [hf] using congrArg Fin.val hfij
  have habs : |Int.fract (((j : ℕ) : ℝ) * α) - Int.fract (((i : ℕ) : ℝ) * α)| < ε := by
    set u := Int.fract (((i : ℕ) : ℝ) * α) with hu
    set v := Int.fract (((j : ℕ) : ℝ) * α) with hv
    have hu0 : (0 : ℝ) ≤ (N : ℝ) * u := mul_nonneg hNR.le (Int.fract_nonneg _)
    have hv0 : (0 : ℝ) ≤ (N : ℝ) * v := mul_nonneg hNR.le (Int.fract_nonneg _)
    have hul := Nat.floor_le hu0
    have huu := Nat.lt_floor_add_one ((N : ℝ) * u)
    have hvl := Nat.floor_le hv0
    have hvu := Nat.lt_floor_add_one ((N : ℝ) * v)
    rw [hbins] at hul huu
    have hup : v - u < 1 / (N : ℝ) := by
      rw [lt_div_iff₀ hNR]; linarith
    have hdn : u - v < 1 / (N : ℝ) := by
      rw [lt_div_iff₀ hNR]; linarith
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hne : (i : ℕ) ≠ (j : ℕ) := fun hval => hij (Fin.val_injective hval)
  rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with hlt | hge
  · exact step_of_close hlt hε1 habs
  · refine step_of_close (a := (j : ℕ)) (b := (i : ℕ)) (by omega) hε1 ?_
    rw [abs_sub_comm]
    exact habs

/-- **Forward orbits of an integer-return-free rotation are dense.**
For every subinterval `(c,d) ⊆ [0,1]` there is a *positive* index whose orbit
point lands strictly inside. -/
theorem exists_pos_nat_fract_mem_Ioo {α : ℝ} (hα : NoIntegerOrbit α)
    {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ c < Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < d := by
  set ε : ℝ := (d - c) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hε1 : ε ≤ 1 := by rw [hεdef]; linarith
  obtain ⟨k, hk, hstep⟩ := exists_small_step (α := α) hε hε1
  set δ : ℝ := Int.fract ((k : ℝ) * α) with hδdef
  have hδ0 : 0 < δ := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (hα k hk))
  rcases hstep with hsmall | hlarge
  · -- small forward step: climb from `0` past `c` before overshooting `d`
    set m : ℕ := ⌈c / δ⌉₊ + 1 with hm
    have hmpos : 0 < m := by omega
    have hceil_lb : c ≤ (⌈c / δ⌉₊ : ℝ) * δ := by
      have hle := Nat.le_ceil (c / δ)
      calc c = c / δ * δ := by field_simp
        _ ≤ (⌈c / δ⌉₊ : ℝ) * δ := by nlinarith
    have hceil_ub : (⌈c / δ⌉₊ : ℝ) * δ < c + δ := by
      have hnn : (0 : ℝ) ≤ c / δ := by positivity
      have hlt := Nat.ceil_lt_add_one hnn
      calc (⌈c / δ⌉₊ : ℝ) * δ < (c / δ + 1) * δ := by nlinarith
        _ = c + δ := by field_simp
    have hmδ : (m : ℝ) * δ = (⌈c / δ⌉₊ : ℝ) * δ + δ := by rw [hm]; push_cast; ring
    have hlb : c < (m : ℝ) * δ := by rw [hmδ]; linarith
    have hub : (m : ℝ) * δ < d := by
      rw [hmδ]; rw [hεdef] at hsmall; linarith
    have hcast : (((m * k : ℕ)) : ℝ) * α = (m : ℝ) * ((k : ℝ) * α) := by
      push_cast; ring
    have hval : Int.fract (((m * k : ℕ) : ℝ) * α) = (m : ℝ) * δ := by
      rw [hcast, fract_natCast_mul_of_lt_one (by rw [← hδdef]; linarith), ← hδdef]
    exact ⟨m * k, Nat.mul_pos hmpos hk, by rw [hval]; exact hlb, by rw [hval]; exact hub⟩
  · -- large forward step: descend from `1` below `d` before undershooting `c`
    set η : ℝ := 1 - δ with hη
    have hη0 : 0 < η := by rw [hη]; linarith [Int.fract_lt_one ((k : ℝ) * α)]
    have hηε : η < ε := by rw [hη]; linarith
    set m : ℕ := ⌈(1 - d) / η⌉₊ + 1 with hm
    have hmpos : 0 < m := by omega
    have h1d : (0 : ℝ) ≤ 1 - d := by linarith
    have hceil_lb : 1 - d ≤ (⌈(1 - d) / η⌉₊ : ℝ) * η := by
      have hle := Nat.le_ceil ((1 - d) / η)
      calc 1 - d = (1 - d) / η * η := by field_simp
        _ ≤ (⌈(1 - d) / η⌉₊ : ℝ) * η := by nlinarith
    have hceil_ub : (⌈(1 - d) / η⌉₊ : ℝ) * η < (1 - d) + η := by
      have hnn : (0 : ℝ) ≤ (1 - d) / η := by positivity
      have hlt := Nat.ceil_lt_add_one hnn
      calc (⌈(1 - d) / η⌉₊ : ℝ) * η < ((1 - d) / η + 1) * η := by nlinarith
        _ = (1 - d) + η := by field_simp
    have hmη : (m : ℝ) * η = (⌈(1 - d) / η⌉₊ : ℝ) * η + η := by rw [hm]; push_cast; ring
    have hlb : 1 - d < (m : ℝ) * η := by rw [hmη]; linarith
    have hub : (m : ℝ) * η < 1 - c := by rw [hmη]; rw [hεdef] at hηε; linarith
    have hmη0 : 0 < (m : ℝ) * η := by positivity
    have hmη1 : (m : ℝ) * η < 1 := by linarith
    have hfeq : Int.fract ((m : ℝ) * η) = (m : ℝ) * η :=
      Int.fract_eq_self.2 ⟨hmη0.le, hmη1⟩
    have hkey : Int.fract (((m * k : ℕ) : ℝ) * α) = 1 - (m : ℝ) * η := by
      have hcast : (((m * k : ℕ)) : ℝ) * α = (m : ℝ) * ((k : ℝ) * α) := by push_cast; ring
      have hstepd : Int.fract ((m : ℝ) * ((k : ℝ) * α)) = Int.fract ((m : ℝ) * δ) := by
        refine Int.fract_eq_fract.2 ⟨m * ⌊(k : ℝ) * α⌋, ?_⟩
        rw [hδdef, Int.fract]
        push_cast
        ring
      have hsplit : (m : ℝ) * δ = (m : ℝ) + -((m : ℝ) * η) := by rw [hη]; ring
      have hfneg : Int.fract (-((m : ℝ) * η)) = 1 - (m : ℝ) * η := by
        rw [Int.fract_neg (by rw [hfeq]; exact ne_of_gt hmη0), hfeq]
      rw [hcast, hstepd, hsplit, Int.fract_natCast_add, hfneg]
    exact ⟨m * k, Nat.mul_pos hmpos hk, by rw [hkey]; linarith, by rw [hkey]; linarith⟩

/-! ## The carry staircase and its determinant -/

variable {R : Type*} [CommRing R]

/-- The `(n+1)`-dimensional **carry staircase** with parameter `t`:
`t` on and below the diagonal, `1` strictly above. -/
def carryStaircase (t : R) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => if (j : ℕ) ≤ (i : ℕ) then t else 1

/-- The upper-triangular matrix obtained from `carryStaircase` by subtracting
each row from its successor. -/
private def staircaseReduced (t : R) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j =>
    if (i : ℕ) = 0 then (if (j : ℕ) = 0 then t else 1)
    else (if (i : ℕ) = (j : ℕ) then t - 1 else 0)

private theorem staircaseReduced_blockTriangular (t : R) (n : ℕ) :
    (staircaseReduced t n).BlockTriangular id := by
  intro i j hij
  have hji : (j : ℕ) < (i : ℕ) := hij
  have hi0 : (i : ℕ) ≠ 0 := by omega
  have hne : (i : ℕ) ≠ (j : ℕ) := by omega
  simp [staircaseReduced, hi0, hne]

/-- **Exact determinant of the carry staircase.**  The value depends only on
`t` and the size, never on which staircase was realised. -/
theorem det_carryStaircase (t : R) (n : ℕ) :
    (carryStaircase t n).det = t * (t - 1) ^ n := by
  have hAB : (carryStaircase t n).det = (staircaseReduced t n).det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_pred (c := fun _ => 1) ?_ ?_
    · intro j
      simp only [carryStaircase, staircaseReduced]
      by_cases hj : (j : ℕ) = 0 <;> simp [hj, Nat.le_zero]
    · intro i j
      have e1 : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := rfl
      have e2 : ((i.castSucc : Fin (n + 1)) : ℕ) = (i : ℕ) := rfl
      simp only [carryStaircase, staircaseReduced, e1, e2, one_mul,
        if_neg (Nat.succ_ne_zero (i : ℕ))]
      rcases Nat.lt_trichotomy ((j : ℕ)) ((i : ℕ) + 1) with h | h | h
      · rw [if_pos (by omega : (j : ℕ) ≤ (i : ℕ) + 1),
          if_neg (by omega : ¬ ((i : ℕ) + 1 = (j : ℕ))),
          if_pos (by omega : (j : ℕ) ≤ (i : ℕ))]
        ring
      · rw [if_pos (by omega : (j : ℕ) ≤ (i : ℕ) + 1),
          if_pos (by omega : (i : ℕ) + 1 = (j : ℕ)),
          if_neg (by omega : ¬ ((j : ℕ) ≤ (i : ℕ)))]
        ring
      · rw [if_neg (by omega : ¬ ((j : ℕ) ≤ (i : ℕ) + 1)),
          if_neg (by omega : ¬ ((i : ℕ) + 1 = (j : ℕ))),
          if_neg (by omega : ¬ ((j : ℕ) ≤ (i : ℕ)))]
        ring
  rw [hAB, Matrix.det_of_upperTriangular (staircaseReduced_blockTriangular t n),
    Fin.prod_univ_succ]
  simp [staircaseReduced]

/-! ## Realising an arbitrary staircase from two independent rotations -/

/-- **Staircase realisation.**  Two rotations without integer returns realise,
in the two-dimensional carry `⌊fract (i α) + fract (j β)⌋`, the full `n × n`
staircase pattern — with strictly positive and pairwise distinct indices. -/
theorem exists_staircase_indices {α β : ℝ}
    (hα : NoIntegerOrbit α) (hβ : NoIntegerOrbit β) (n : ℕ) :
    ∃ I J : Fin n → ℕ,
      (∀ a, 0 < I a) ∧ (∀ b, 0 < J b) ∧
      Function.Injective I ∧ Function.Injective J ∧
      ∀ a b : Fin n,
        ⌊Int.fract ((I a : ℝ) * α) + Int.fract ((J b : ℝ) * β)⌋
          = if (b : ℕ) ≤ (a : ℕ) then 1 else 0 := by
  obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 < D ∧ D = 8 * (n : ℝ) + 4 :=
    ⟨8 * (n : ℝ) + 4, by positivity, rfl⟩
  have hrow : ∀ a : Fin n, ∃ i : ℕ, 0 < i ∧
      8 * ((a : ℕ) : ℝ) + 7 < Int.fract ((i : ℝ) * α) * D ∧
      Int.fract ((i : ℝ) * α) * D < 8 * ((a : ℕ) : ℝ) + 9 := by
    intro a
    have haR : ((a : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast a.2
    have ha0 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsplit : (8 * ((a : ℕ) : ℝ) + 9) / D
        = (8 * ((a : ℕ) : ℝ) + 7) / D + 2 / D := by ring
    have hlt : (8 * ((a : ℕ) : ℝ) + 7) / D < (8 * ((a : ℕ) : ℝ) + 9) / D := by
      rw [hsplit]
      have h2D : (0 : ℝ) < 2 / D := by positivity
      linarith
    have hlo : (0 : ℝ) ≤ (8 * ((a : ℕ) : ℝ) + 7) / D := by positivity
    have hhi : (8 * ((a : ℕ) : ℝ) + 9) / D ≤ 1 := by
      rw [div_le_one hD0, hD]; linarith
    obtain ⟨i, hi, h1, h2⟩ := exists_pos_nat_fract_mem_Ioo hα hlo hlt hhi
    rw [div_lt_iff₀ hD0] at h1
    rw [lt_div_iff₀ hD0] at h2
    exact ⟨i, hi, h1, h2⟩
  have hcol : ∀ b : Fin n, ∃ j : ℕ, 0 < j ∧
      8 * (n : ℝ) - 8 * ((b : ℕ) : ℝ) - 1 < Int.fract ((j : ℝ) * β) * D ∧
      Int.fract ((j : ℝ) * β) * D < 8 * (n : ℝ) - 8 * ((b : ℕ) : ℝ) + 1 := by
    intro b
    have hbR : ((b : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast b.2
    have hb0 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsplit : (8 * (n : ℝ) - 8 * ((b : ℕ) : ℝ) + 1) / D
        = (8 * (n : ℝ) - 8 * ((b : ℕ) : ℝ) - 1) / D + 2 / D := by ring
    have hlt : (8 * (n : ℝ) - 8 * ((b : ℕ) : ℝ) - 1) / D
        < (8 * (n : ℝ) - 8 * ((b : ℕ) : ℝ) + 1) / D := by
      rw [hsplit]
      have h2D : (0 : ℝ) < 2 / D := by positivity
      linarith
    have hlo : (0 : ℝ) ≤ (8 * (n : ℝ) - 8 * ((b : ℕ) : ℝ) - 1) / D := by
      apply div_nonneg _ hD0.le; linarith
    have hhi : (8 * (n : ℝ) - 8 * ((b : ℕ) : ℝ) + 1) / D ≤ 1 := by
      rw [div_le_one hD0, hD]; linarith
    obtain ⟨j, hj, h1, h2⟩ := exists_pos_nat_fract_mem_Ioo hβ hlo hlt hhi
    rw [div_lt_iff₀ hD0] at h1
    rw [lt_div_iff₀ hD0] at h2
    exact ⟨j, hj, h1, h2⟩
  choose I hIpos hIlo hIhi using hrow
  choose J hJpos hJlo hJhi using hcol
  have hIinj : Function.Injective I := by
    intro a a' heq
    by_contra hne
    have hlo1 := hIlo a; have hhi1 := hIhi a
    have hlo2 := hIlo a'; have hhi2 := hIhi a'
    rw [heq] at hhi1 hlo1
    rcases Nat.lt_trichotomy ((a : ℕ)) ((a' : ℕ)) with h | h | h
    · have : ((a : ℕ) : ℝ) + 1 ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    · exact hne (Fin.val_injective h)
    · have : ((a' : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast h
      linarith
  have hJinj : Function.Injective J := by
    intro b b' heq
    by_contra hne
    have hlo1 := hJlo b; have hhi1 := hJhi b
    have hlo2 := hJlo b'; have hhi2 := hJhi b'
    rw [heq] at hhi1 hlo1
    rcases Nat.lt_trichotomy ((b : ℕ)) ((b' : ℕ)) with h | h | h
    · have : ((b : ℕ) : ℝ) + 1 ≤ ((b' : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    · exact hne (Fin.val_injective h)
    · have : ((b' : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h
      linarith
  refine ⟨I, J, hIpos, hJpos, hIinj, hJinj, ?_⟩
  intro a b
  have hIl := hIlo a; have hIh := hIhi a
  have hJl := hJlo b; have hJh := hJhi b
  have haR : ((a : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast a.2
  have hbR : ((b : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast b.2
  have ha0 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 := Int.fract_nonneg ((I a : ℝ) * α)
  have hv0 := Int.fract_nonneg ((J b : ℝ) * β)
  set u := Int.fract ((I a : ℝ) * α) with hu
  set v := Int.fract ((J b : ℝ) * β) with hv
  by_cases hba : (b : ℕ) ≤ (a : ℕ)
  · have hcmp : ((b : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast hba
    rw [if_pos hba, Int.floor_eq_iff]
    constructor
    · have key : (1 : ℝ) * D ≤ (u + v) * D := by
        have expand : (u + v) * D = u * D + v * D := by ring
        rw [expand, one_mul]
        linarith
      have h1 := le_of_mul_le_mul_right key hD0
      push_cast
      linarith
    · have key : (u + v) * D < 2 * D := by
        have expand : (u + v) * D = u * D + v * D := by ring
        rw [expand]
        linarith
      have h1 := lt_of_mul_lt_mul_right key hD0.le
      push_cast
      linarith
  · have hcmp : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by
      have hab : (a : ℕ) + 1 ≤ (b : ℕ) := by omega
      exact_mod_cast hab
    rw [if_neg hba, Int.floor_eq_iff]
    refine ⟨by push_cast; linarith, ?_⟩
    have key : (u + v) * D < 1 * D := by
      have expand : (u + v) * D = u * D + v * D := by ring
      rw [expand, one_mul]
      linarith
    have h1 := lt_of_mul_lt_mul_right key hD0.le
    push_cast
    linarith

end ErdosProblems.Shared
