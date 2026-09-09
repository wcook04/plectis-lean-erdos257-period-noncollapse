import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Erdős #1041: a Hilbert chord certificate and free-point control on hyperbolic geodesics

For `c₁, …, c_m` in the closed unit disc write `d_{jk} = |1 - conj(c_j) c_k|`,
`R_j = (∏_k d_{jk})^{1/m}` and `S_m = ∑_j R_j`.  The free-point conjecture `FP_m` asserts
`S_m ≤ m`, with equality only at the origin.  The corpus proves `FP_m` for `m ≤ 4`
(`FreePointFP4Complete.lean`, `FreePointMeanInequalityFP3.md`), reports `FP₅` closed by a box
certificate (`FreePointFP5OuterBound.md`), and lands the plurisubharmonic torus bridge
`FP_{n-1} ⟹ (S)_n` (`FreePointTorusPshReduction.lean`).

## Claim boundary

**Erdős #1041 is open and nothing in this file proves it.**  `FP_m` and `(S)_n` control an
arithmetic mean of critical-value capacities.  There is no general implication from such a mean
to the existence of a short curve connecting the roots of a polynomial: arithmetic-mean control
neither selects a pair of roots nor bounds the length of any single connecting arc.  This module
is a certificate lane for `FP_m`, not for #1041.

## What is proved here

* `freePointSum_ofReal_le`: for a real configuration `x : Fin m → ℝ` with `|x_j| ≤ 1`,
  `S_m ≤ m (1 - x̄²)` — strictly stronger than `S_m ≤ m`, unconditional, every degree.
* `eq_zero_of_freePointSum_ofReal_eq`: on the diameter, `S_m = m` forces `x = 0`.
* `freePointSum_geodesic_le` and `freePointSum_geodesic_le_card`: `S_m ≤ m (1 - x̄²) ≤ m` for a
  configuration on any hyperbolic geodesic `ψ_β(x) = (x + iβ)/(1 - iβx)` with `β² ≤ 1`, in every
  degree.  The mechanism is the exact modulus identity
  `|1 - conj(ψ_β(s)) ψ_β(t)| · √(1+β²s²) · √(1+β²t²) = (1-β²)(1 - st)`
  (`norm_one_sub_conj_geodesic_mul_denominators`), which makes every geodesic pseudo-distance
  dominated by the corresponding diameter chord.  Novelty of the geodesic statement is
  **unassessed**; no priority is claimed.
* `hilbert_chord_lemma`, with scalar kernel `mean_exp_le_hilbertMajorant`: for vectors in a real
  inner product space with `u = m⁻¹ ∑ v_j`, `‖v_j‖ ≤ B` and `r = ‖u‖`,
  `m⁻¹ ∑_j e^{-⟪v_j, u⟫} ≤ cosh(Br) - (r/B) sinh(Br) =: F_B(r)`.
* `hilbertMajorant_lt_one`: `B² ≤ 2` and `r > 0` give `F_B(r) < 1`.  The proof reduces to
  `cosh x - (x/2) sinh x < 1`, which reduces to `sinh t < t cosh t` for `t > 0`
  (`sinh_lt_mul_cosh`).  Mathlib 4.29 carries `Real.self_lt_sinh_iff` and `Real.sinh_pos_iff`
  but no `tanh t < t`, so that last step is proved here from
  `deriv (t ↦ t cosh t - sinh t) = t sinh t > 0`.  The constant `2` is sharp for this method:
  `F_B(r) = 1 + ((B² - 2)/2) r² + O(r⁴)`.  The far end is `hilbertMajorant_self`,
  `F_B(B) = e^{-B²} < 1`, the outer anchor of the balanced-cone reduction.
* `sum_exp_le_card_of_energy`: the abstract uniform central theorem.  If the row logarithms
  `h_j` satisfy `|h_j| ≤ B r` with `B² ≤ 2` and `m r² = -∑_j h_j`, then `∑_j e^{h_j} ≤ m`.
* `freePointSum_central_le_of_series`: concrete uniform central `FP_m` inside
  `|c_j| ≤ centralRadius = √(1 - e^{-2}) = 0.9298734950321937…`, **conditional** on two named
  hypotheses.

## What is NOT proved here

The `ℓ²` feature-map bridge `v(c) = (c, c²/√2, c³/√3, …)` with `‖v(c)‖² = -log(1 - |c|²)` and
`h_j = -Re⟪v(c_j), u⟫` is **not formalised**.  Accordingly
`freePointSum_central_le_of_series` carries the two series facts it needs as explicit
hypotheses:

* `hEnergy` : `∑_j h_j ≤ 0`, i.e. nonnegativity of the logarithmic energy
  `E = m⁻¹ ∑_ν |p_ν|²/ν` with `p_ν = ∑_k c_k^ν`;
* `hCauchySchwarz` : `h_j² ≤ (E/m) L_j` with `L_j = -log(1 - |c_j|²)`.

Both are ordinary analysis, proved (not in Lean) as steps (i)–(iii) of ROWCERT+ in
`FreePointFP5StructureLab.md` §3.  Everything downstream of them — the chord lemma, the decay of
`F_B`, the radius arithmetic, and the conclusion `S_m ≤ m` — is kernel-checked here.  The
diameter and geodesic theorems above are unconditional and use none of this.

## Honest comparison with the corpus certificate

The corpus's per-degree ROWCERT+ central radii (all-equal-moduli thresholds) are approximately
`0.943806` at `m = 3`, `0.931680` at `m = 4`, `0.924452` at `m = 5` and `0.919669` at `m = 6`,
decreasing to `0.896360` as `m → ∞`.  The Hilbert radius `0.929873` is therefore **weaker** at
`m = 3` and `m = 4` — both already-solved cases — and stronger for every `m ≥ 5`.  Its only
structural advantages are that it is uniform in `m` and needs no box computation.  It does not
replace ROWCERT+ at small degree.

## Notation

Mathlib 4.29 has no `Complex.abs`, so the complex modulus is `‖·‖` throughout, and `inner`
takes its scalar field explicitly (`inner ℝ x y`).
-/

namespace ErdosProblems.Erdos1041.FreePointHilbertCertificate

open Finset

/-! ## The free-point functional -/

/-- The free-point functional `S_m(c) = ∑ⱼ (∏ₖ ‖1 - conj(cⱼ) cₖ‖)^{1/m}`. -/
noncomputable def freePointSum {m : ℕ} (c : Fin m → ℂ) : ℝ :=
  ∑ j, (∏ k, ‖1 - (starRingEnd ℂ) (c j) * c k‖) ^ ((m : ℝ)⁻¹)

/-- Two reals of modulus at most one have product at most one. -/
theorem mul_le_one_of_abs_le_one {s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) : s * t ≤ 1 := by
  have h1 : s * t ≤ |s| * |t| := by
    calc s * t ≤ |s * t| := le_abs_self _
      _ = |s| * |t| := abs_mul _ _
  nlinarith [abs_nonneg s, abs_nonneg t]

/-! ## AM–GM in the row shape -/

/-- Unweighted AM–GM, in the exact `rpow` shape every row estimate below needs. -/
theorem geom_mean_le_arith_mean {m : ℕ} (hm : 0 < m) (z : Fin m → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i, z i) ^ ((m : ℝ)⁻¹) ≤ (m : ℝ)⁻¹ * ∑ i, z i := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : ∑ _i : Fin m, ((m : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin m))
      (fun _ => (m : ℝ)⁻¹) z (fun i _ => by positivity) hw (fun i _ => hz i)
  rw [Real.finset_prod_rpow _ _ (fun i _ => hz i)] at h
  simpa [Finset.mul_sum] using h

/-! ## The real-diameter majorant -/

/-- If every pseudo-distance is dominated by the real chord `1 - xⱼxₖ`, the free-point sum
obeys the diameter bound `m(1 - x̄²)`. -/
theorem freePointSum_le_of_dominated {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ) (x : Fin m → ℝ)
    (xb : ℝ) (hxb : ∑ j, x j = (m : ℝ) * xb) (hx : ∀ j, |x j| ≤ 1)
    (hdom : ∀ j k, ‖1 - (starRingEnd ℂ) (c j) * c k‖ ≤ 1 - x j * x k) :
    freePointSum c ≤ (m : ℝ) * (1 - xb ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hnn : ∀ j k, (0 : ℝ) ≤ 1 - x j * x k := fun j k => by
    have := mul_le_one_of_abs_le_one (hx j) (hx k); linarith
  have hrow : ∀ j, (∏ k, ‖1 - (starRingEnd ℂ) (c j) * c k‖) ^ ((m : ℝ)⁻¹) ≤ 1 - x j * xb := by
    intro j
    have h1 : (∏ k, ‖1 - (starRingEnd ℂ) (c j) * c k‖) ^ ((m : ℝ)⁻¹)
        ≤ (∏ k, (1 - x j * x k)) ^ ((m : ℝ)⁻¹) := by
      refine Real.rpow_le_rpow (Finset.prod_nonneg fun k _ => norm_nonneg _) ?_ (by positivity)
      exact Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hdom j k)
    have h2 := geom_mean_le_arith_mean hm (fun k => 1 - x j * x k) (fun k => hnn j k)
    have h3 : (m : ℝ)⁻¹ * ∑ k, (1 - x j * x k) = 1 - x j * xb := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, ← Finset.mul_sum, hxb]
      field_simp
    linarith
  have hsum : ∑ j, (1 - x j * xb) = (m : ℝ) * (1 - xb ^ 2) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.sum_mul, hxb]
    ring
  calc freePointSum c ≤ ∑ j, (1 - x j * xb) := Finset.sum_le_sum fun j _ => hrow j
    _ = (m : ℝ) * (1 - xb ^ 2) := hsum

/-- On the real diameter the pseudo-distance is exactly the real chord. -/
theorem norm_one_sub_conj_ofReal_mul {s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    ‖1 - (starRingEnd ℂ) ((s : ℂ)) * ((t : ℂ))‖ = 1 - s * t := by
  have hnn : (0 : ℝ) ≤ 1 - s * t := by
    have := mul_le_one_of_abs_le_one hs ht; linarith
  rw [Complex.conj_ofReal]
  have hcast : (1 : ℂ) - (s : ℂ) * (t : ℂ) = ((1 - s * t : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]

/-- **FP_m on the real diameter, every degree**, in the strictly stronger form `m(1 - x̄²)`. -/
theorem freePointSum_ofReal_le {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ 1)
    (xb : ℝ) (hxb : ∑ j, x j = (m : ℝ) * xb) :
    freePointSum (fun j => (x j : ℂ)) ≤ (m : ℝ) * (1 - xb ^ 2) :=
  freePointSum_le_of_dominated hm _ x xb hxb hx fun j k =>
    le_of_eq (norm_one_sub_conj_ofReal_mul (hx j) (hx k))

/-- The plain diameter form `S_m ≤ m`. -/
theorem freePointSum_ofReal_le_card {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    freePointSum (fun j => (x j : ℂ)) ≤ (m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hxb : ∑ j, x j = (m : ℝ) * ((m : ℝ)⁻¹ * ∑ j, x j) := by field_simp
  have h := freePointSum_ofReal_le hm x hx ((m : ℝ)⁻¹ * ∑ j, x j) hxb
  nlinarith [sq_nonneg ((m : ℝ)⁻¹ * ∑ j, x j)]

/-! ## The diameter equality case -/

/-- With a centred real configuration, each row product is at most `(1 - xⱼ²) e^{xⱼ²}`. -/
theorem prod_le_one_of_centred {m : ℕ} (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ 1)
    (hc : ∑ j, x j = 0) (j : Fin m) :
    ∏ k, (1 - x j * x k) ≤ (1 - x j ^ 2) * Real.exp (x j ^ 2) := by
  classical
  have hnn : ∀ k, (0 : ℝ) ≤ 1 - x j * x k := fun k => by
    have := mul_le_one_of_abs_le_one (hx j) (hx k); linarith
  have hstep : ∏ k ∈ Finset.univ.erase j, (1 - x j * x k)
      ≤ ∏ k ∈ Finset.univ.erase j, Real.exp (-(x j * x k)) := by
    refine Finset.prod_le_prod (fun k _ => hnn k) (fun k _ => ?_)
    have := Real.add_one_le_exp (-(x j * x k))
    linarith
  have hlin : ∑ k ∈ Finset.univ.erase j, (-(x j * x k))
      = -(x j * ∑ k ∈ Finset.univ.erase j, x k) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  have herase : (∑ k ∈ Finset.univ.erase j, x k) + x j = ∑ k, x k :=
    Finset.sum_erase_add _ _ (Finset.mem_univ j)
  have hrest : ∑ k ∈ Finset.univ.erase j, x k = -x j := by rw [hc] at herase; linarith
  have hexp : ∏ k ∈ Finset.univ.erase j, Real.exp (-(x j * x k)) = Real.exp (x j ^ 2) := by
    rw [← Real.exp_sum, hlin, hrest]
    congr 1
    ring
  have hsplit : ∏ k, (1 - x j * x k)
      = (∏ k ∈ Finset.univ.erase j, (1 - x j * x k)) * (1 - x j * x j) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
  calc ∏ k, (1 - x j * x k)
      = (∏ k ∈ Finset.univ.erase j, (1 - x j * x k)) * (1 - x j * x j) := hsplit
    _ ≤ (∏ k ∈ Finset.univ.erase j, Real.exp (-(x j * x k))) * (1 - x j * x j) :=
        mul_le_mul_of_nonneg_right hstep (hnn j)
    _ = (1 - x j ^ 2) * Real.exp (x j ^ 2) := by rw [hexp]; ring

/-- A centred real configuration with a nonzero entry has a strictly sub-unit row product. -/
theorem prod_lt_one_of_centred {m : ℕ} (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ 1)
    (hc : ∑ j, x j = 0) {j : Fin m} (hj : x j ≠ 0) :
    ∏ k, (1 - x j * x k) < 1 := by
  have h1 := prod_le_one_of_centred x hx hc j
  have hsq : x j ^ 2 ≠ 0 := pow_ne_zero 2 hj
  have h2 : -(x j ^ 2) + 1 < Real.exp (-(x j ^ 2)) := Real.add_one_lt_exp (neg_ne_zero.2 hsq)
  have h3 : Real.exp (-(x j ^ 2)) * Real.exp (x j ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : (0 : ℝ) < Real.exp (x j ^ 2) := Real.exp_pos _
  have h5 : (-(x j ^ 2) + 1) * Real.exp (x j ^ 2)
      < Real.exp (-(x j ^ 2)) * Real.exp (x j ^ 2) := mul_lt_mul_of_pos_right h2 h4
  rw [h3] at h5
  nlinarith [h1, h5]

/-- Every row of a centred real configuration is at most one. -/
theorem row_le_one_of_centred {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ 1)
    (hc : ∑ j, x j = 0) (j : Fin m) :
    (∏ k, (1 - x j * x k)) ^ ((m : ℝ)⁻¹) ≤ 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hnn : ∀ k, (0 : ℝ) ≤ 1 - x j * x k := fun k => by
    have := mul_le_one_of_abs_le_one (hx j) (hx k); linarith
  have h2 := geom_mean_le_arith_mean hm (fun k => 1 - x j * x k) hnn
  have h3 : (m : ℝ)⁻¹ * ∑ k, (1 - x j * x k) = 1 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum, hc, mul_zero, sub_zero]
    field_simp
  linarith

/-- **Equality analysis on the diameter.**  `S_m = m` forces the configuration to the origin. -/
theorem eq_zero_of_freePointSum_ofReal_eq {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ)
    (hx : ∀ j, |x j| ≤ 1) (heq : freePointSum (fun j => (x j : ℂ)) = (m : ℝ)) (j : Fin m) :
    x j = 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hxb : ∑ i, x i = (m : ℝ) * ((m : ℝ)⁻¹ * ∑ i, x i) := by field_simp
  have hle := freePointSum_ofReal_le hm x hx ((m : ℝ)⁻¹ * ∑ i, x i) hxb
  rw [heq] at hle
  have hsq0 : ((m : ℝ)⁻¹ * ∑ i, x i) ^ 2 ≤ 0 := by nlinarith
  have hbar : ((m : ℝ)⁻¹ * ∑ i, x i) = 0 :=
    sq_eq_zero_iff.1 (le_antisymm hsq0 (sq_nonneg _))
  have hc : ∑ i, x i = 0 := by
    have hmul : (m : ℝ) * ((m : ℝ)⁻¹ * ∑ i, x i) = ∑ i, x i := by field_simp
    rw [hbar, mul_zero] at hmul
    exact hmul.symm
  have hnorm : ∀ a b : Fin m, ‖1 - (starRingEnd ℂ) ((x a : ℂ)) * ((x b : ℂ))‖ = 1 - x a * x b :=
    fun a b => norm_one_sub_conj_ofReal_mul (hx a) (hx b)
  have hrewrite : ∀ a : Fin m,
      (∏ b, ‖1 - (starRingEnd ℂ) ((x a : ℂ)) * ((x b : ℂ))‖) ^ ((m : ℝ)⁻¹)
        = (∏ b, (1 - x a * x b)) ^ ((m : ℝ)⁻¹) := by
    intro a
    congr 1
    exact Finset.prod_congr rfl fun b _ => hnorm a b
  by_contra hj
  have hlt : (∏ b, (1 - x j * x b)) ^ ((m : ℝ)⁻¹) < 1 := by
    have hp := prod_lt_one_of_centred x hx hc hj
    have hpos : (0 : ℝ) ≤ ∏ b, (1 - x j * x b) :=
      Finset.prod_nonneg fun b _ => by
        have := mul_le_one_of_abs_le_one (hx j) (hx b); linarith
    calc (∏ b, (1 - x j * x b)) ^ ((m : ℝ)⁻¹)
        < (1 : ℝ) ^ ((m : ℝ)⁻¹) := Real.rpow_lt_rpow hpos hp (by positivity)
      _ = 1 := Real.one_rpow _
  have hstrict : freePointSum (fun a => (x a : ℂ)) < (m : ℝ) := by
    have hbound : ∀ a ∈ (Finset.univ : Finset (Fin m)),
        (∏ b, ‖1 - (starRingEnd ℂ) ((x a : ℂ)) * ((x b : ℂ))‖) ^ ((m : ℝ)⁻¹) ≤ (1 : ℝ) := by
      intro a _
      rw [hrewrite a]
      exact row_le_one_of_centred hm x hx hc a
    have hex : ∃ a ∈ (Finset.univ : Finset (Fin m)),
        (∏ b, ‖1 - (starRingEnd ℂ) ((x a : ℂ)) * ((x b : ℂ))‖) ^ ((m : ℝ)⁻¹) < (1 : ℝ) := by
      refine ⟨j, Finset.mem_univ j, ?_⟩
      rw [hrewrite j]
      exact hlt
    have hs := Finset.sum_lt_sum hbound hex
    simpa [freePointSum, Finset.card_univ] using hs
  rw [heq] at hstrict
  exact lt_irrefl _ hstrict

/-! ## Hyperbolic geodesics -/

/-- The Möbius parametrisation `ψ_β(x) = (x + iβ)/(1 - iβx)` of a hyperbolic geodesic. -/
noncomputable def geodesicPoint (β x : ℝ) : ℂ :=
  ((x : ℂ) + (β : ℂ) * Complex.I) / ((1 : ℂ) - ((β * x : ℝ) : ℂ) * Complex.I)

theorem norm_one_sub_mul_I (a : ℝ) :
    ‖(1 : ℂ) - (a : ℂ) * Complex.I‖ = Real.sqrt (1 + a ^ 2) := by
  have h : (1 : ℂ) - (a : ℂ) * Complex.I = ((1 : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_add_mul_I]
  congr 1
  ring

theorem norm_one_add_mul_I (a : ℝ) :
    ‖(1 : ℂ) + (a : ℂ) * Complex.I‖ = Real.sqrt (1 + a ^ 2) := by
  have h : (1 : ℂ) + (a : ℂ) * Complex.I = ((1 : ℝ) : ℂ) + ((a : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_add_mul_I]
  congr 1
  ring

theorem one_le_sqrt_one_add_sq (a : ℝ) : (1 : ℝ) ≤ Real.sqrt (1 + a ^ 2) := by
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + a ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])

theorem one_sub_mul_I_ne_zero (a : ℝ) : (1 : ℂ) - (a : ℂ) * Complex.I ≠ 0 := by
  intro h
  have h1 : ‖(1 : ℂ) - (a : ℂ) * Complex.I‖ = Real.sqrt (1 + a ^ 2) := norm_one_sub_mul_I a
  rw [h, norm_zero] at h1
  have := one_le_sqrt_one_add_sq a
  linarith

theorem one_add_mul_I_ne_zero (a : ℝ) : (1 : ℂ) + (a : ℂ) * Complex.I ≠ 0 := by
  intro h
  have h1 : ‖(1 : ℂ) + (a : ℂ) * Complex.I‖ = Real.sqrt (1 + a ^ 2) := norm_one_add_mul_I a
  rw [h, norm_zero] at h1
  have := one_le_sqrt_one_add_sq a
  linarith

/-- Every point of the geodesic lies in the closed unit disc. -/
theorem norm_geodesicPoint_le_one {β x : ℝ} (hβ : β ^ 2 ≤ 1) (hx : |x| ≤ 1) :
    ‖geodesicPoint β x‖ ≤ 1 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  have hle : x ^ 2 + β ^ 2 ≤ 1 + (β * x) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hβ)]
  rw [geodesicPoint, norm_div, norm_one_sub_mul_I, Complex.norm_add_mul_I,
    div_le_one (by positivity)]
  exact Real.sqrt_le_sqrt hle

/-- The cleared Gram identity on a geodesic: the numerator `(1-β²)(1-st)` is real. -/
theorem geodesic_gram_cleared (β s t : ℝ) :
    (1 - (starRingEnd ℂ) (geodesicPoint β s) * geodesicPoint β t)
        * (((1 : ℂ) + ((β * s : ℝ) : ℂ) * Complex.I)
            * ((1 : ℂ) - ((β * t : ℝ) : ℂ) * Complex.I))
      = (((1 - β ^ 2) * (1 - s * t) : ℝ) : ℂ) := by
  have hA : ((1 : ℂ) + ((β * s : ℝ) : ℂ) * Complex.I) ≠ 0 := one_add_mul_I_ne_zero _
  have hB : ((1 : ℂ) - ((β * t : ℝ) : ℂ) * Complex.I) ≠ 0 := one_sub_mul_I_ne_zero _
  have hconj : (starRingEnd ℂ) (geodesicPoint β s)
      = ((s : ℂ) - (β : ℂ) * Complex.I) / ((1 : ℂ) + ((β * s : ℝ) : ℂ) * Complex.I) := by
    simp only [geodesicPoint, map_div₀, map_add, map_sub, map_one, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  have hmul : (starRingEnd ℂ) (geodesicPoint β s) * geodesicPoint β t
      = (((s : ℂ) - (β : ℂ) * Complex.I) * ((t : ℂ) + (β : ℂ) * Complex.I))
          / (((1 : ℂ) + ((β * s : ℝ) : ℂ) * Complex.I)
              * ((1 : ℂ) - ((β * t : ℝ) : ℂ) * Complex.I)) := by
    rw [hconj]
    simp only [geodesicPoint]
    rw [div_mul_div_comm]
  rw [hmul, sub_mul, one_mul, div_mul_cancel₀ _ (mul_ne_zero hA hB)]
  push_cast
  linear_combination ((β : ℂ) ^ 2 * (1 - (s : ℂ) * (t : ℂ))) * Complex.I_sq

/-- The exact modulus identity on a hyperbolic geodesic. -/
theorem norm_one_sub_conj_geodesic_mul_denominators (β s t : ℝ)
    (hβ : β ^ 2 ≤ 1) (hst : s * t ≤ 1) :
    ‖1 - (starRingEnd ℂ) (geodesicPoint β s) * geodesicPoint β t‖
        * (Real.sqrt (1 + (β * s) ^ 2) * Real.sqrt (1 + (β * t) ^ 2))
      = (1 - β ^ 2) * (1 - s * t) := by
  have h := congrArg norm (geodesic_gram_cleared β s t)
  rw [norm_mul, norm_mul, norm_one_add_mul_I, norm_one_sub_mul_I, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by linarith) (by linarith))] at h
  exact h

/-- **Geodesic contraction.**  Moving a real configuration off the diameter onto the geodesic
`ψ_β` only shrinks every pseudo-distance. -/
theorem norm_one_sub_conj_geodesic_le {β s t : ℝ} (hβ : β ^ 2 ≤ 1) (hs : |s| ≤ 1)
    (ht : |t| ≤ 1) :
    ‖1 - (starRingEnd ℂ) (geodesicPoint β s) * geodesicPoint β t‖ ≤ 1 - s * t := by
  have hst : s * t ≤ 1 := mul_le_one_of_abs_le_one hs ht
  have hid := norm_one_sub_conj_geodesic_mul_denominators β s t hβ hst
  have hA : (1 : ℝ) ≤ Real.sqrt (1 + (β * s) ^ 2) := one_le_sqrt_one_add_sq _
  have hB : (1 : ℝ) ≤ Real.sqrt (1 + (β * t) ^ 2) := one_le_sqrt_one_add_sq _
  have hN : (0 : ℝ) ≤ ‖1 - (starRingEnd ℂ) (geodesicPoint β s) * geodesicPoint β t‖ :=
    norm_nonneg _
  have hAB : (1 : ℝ) ≤ Real.sqrt (1 + (β * s) ^ 2) * Real.sqrt (1 + (β * t) ^ 2) := by
    nlinarith
  have h1 : ‖1 - (starRingEnd ℂ) (geodesicPoint β s) * geodesicPoint β t‖
      ≤ ‖1 - (starRingEnd ℂ) (geodesicPoint β s) * geodesicPoint β t‖
        * (Real.sqrt (1 + (β * s) ^ 2) * Real.sqrt (1 + (β * t) ^ 2)) :=
    le_mul_of_one_le_right hN hAB
  have h2 : (1 - β ^ 2) * (1 - s * t) ≤ 1 - s * t := by nlinarith [sq_nonneg β]
  linarith

/-- **FP_m on any hyperbolic geodesic, every degree.** -/
theorem freePointSum_geodesic_le {m : ℕ} (hm : 0 < m) {β : ℝ} (hβ : β ^ 2 ≤ 1)
    (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ 1) (xb : ℝ) (hxb : ∑ j, x j = (m : ℝ) * xb) :
    freePointSum (fun j => geodesicPoint β (x j)) ≤ (m : ℝ) * (1 - xb ^ 2) :=
  freePointSum_le_of_dominated hm _ x xb hxb hx fun j k =>
    norm_one_sub_conj_geodesic_le hβ (hx j) (hx k)

/-- The plain geodesic form `S_m ≤ m`. -/
theorem freePointSum_geodesic_le_card {m : ℕ} (hm : 0 < m) {β : ℝ} (hβ : β ^ 2 ≤ 1)
    (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    freePointSum (fun j => geodesicPoint β (x j)) ≤ (m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hxb : ∑ j, x j = (m : ℝ) * ((m : ℝ)⁻¹ * ∑ j, x j) := by field_simp
  have h := freePointSum_geodesic_le hm hβ x hx ((m : ℝ)⁻¹ * ∑ j, x j) hxb
  nlinarith [sq_nonneg ((m : ℝ)⁻¹ * ∑ j, x j)]

/-! ## Two hyperbolic inequalities -/

/-- `sinh t < t cosh t` for `t > 0`; equivalently `tanh t < t`. -/
theorem sinh_lt_mul_cosh {t : ℝ} (ht : 0 < t) : Real.sinh t < t * Real.cosh t := by
  have key : StrictMonoOn (fun u : ℝ => u * Real.cosh u - Real.sinh u) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn)
      (fun u hu => ?_)
    rw [interior_Ici, Set.mem_Ioi] at hu
    have hd : HasDerivAt (fun u : ℝ => u * Real.cosh u - Real.sinh u)
        (1 * Real.cosh u + u * Real.sinh u - Real.cosh u) u :=
      ((hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)).sub (Real.hasDerivAt_sinh u)
    have hval : deriv (fun u : ℝ => u * Real.cosh u - Real.sinh u) u = u * Real.sinh u := by
      rw [hd.deriv]; ring
    rw [hval]
    exact mul_pos hu (Real.sinh_pos_iff.2 hu)
  have h := key Set.self_mem_Ici (Set.mem_Ici.2 ht.le) ht
  simp only [Real.cosh_zero, Real.sinh_zero, zero_mul, sub_self] at h
  linarith

/-- `cosh x - (x/2) sinh x < 1` for `x > 0`. -/
theorem cosh_sub_half_mul_sinh_lt_one {x : ℝ} (hx : 0 < x) :
    Real.cosh x - x / 2 * Real.sinh x < 1 := by
  have hhalf : (0 : ℝ) < x / 2 := by linarith
  have hxx : (2 : ℝ) * (x / 2) = x := by ring
  have hcosh : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
    have hd : Real.cosh (2 * (x / 2)) = Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2 := by
      rw [Real.cosh_two_mul]
    rw [hxx] at hd
    have hpy := Real.cosh_sq_sub_sinh_sq (x / 2)
    linarith
  have hsinh : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    have hd : Real.sinh (2 * (x / 2)) = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
      rw [Real.sinh_two_mul]
    rwa [hxx] at hd
  have hkey : Real.sinh (x / 2) < x / 2 * Real.cosh (x / 2) := sinh_lt_mul_cosh hhalf
  have hpos : (0 : ℝ) < Real.sinh (x / 2) := Real.sinh_pos_iff.2 hhalf
  rw [hcosh, hsinh]
  nlinarith [mul_pos hpos (sub_pos.2 hkey)]

/-! ## The Hilbert-chord majorant `F_B` -/

/-- `F_B(r) = cosh(Br) - (r/B) sinh(Br)`. -/
noncomputable def hilbertMajorant (B r : ℝ) : ℝ :=
  Real.cosh (B * r) - r / B * Real.sinh (B * r)

@[simp] theorem hilbertMajorant_zero (B : ℝ) : hilbertMajorant B 0 = 1 := by
  simp [hilbertMajorant]

/-- Exponential normal form of `F_B`. -/
theorem hilbertMajorant_eq (B r : ℝ) (hB : B ≠ 0) :
    hilbertMajorant B r
      = (Real.exp (-(r * B)) + Real.exp (r * B)) / 2
        + (Real.exp (-(r * B)) - Real.exp (r * B)) / (2 * B) * r := by
  unfold hilbertMajorant
  rw [mul_comm B r, Real.cosh_eq, Real.sinh_eq]
  field_simp
  ring

/-- `F_B(B) = e^{-B²} < 1`: the outer anchor of the balanced-cone reduction. -/
theorem hilbertMajorant_self {B : ℝ} (hB : 0 < B) :
    hilbertMajorant B B = Real.exp (-(B ^ 2)) := by
  unfold hilbertMajorant
  rw [div_self (ne_of_gt hB), one_mul, Real.cosh_eq, Real.sinh_eq]
  have hsq : B * B = B ^ 2 := by ring
  rw [hsq]
  ring

/-- **Decay of `F_B` below the critical scale.**  If `B² ≤ 2` then `F_B(r) < 1` for `r > 0`. -/
theorem hilbertMajorant_lt_one {B r : ℝ} (hB : 0 < B) (hB2 : B ^ 2 ≤ 2) (hr : 0 < r) :
    hilbertMajorant B r < 1 := by
  have hBne : B ≠ 0 := ne_of_gt hB
  have hx : 0 < B * r := mul_pos hB hr
  have hmain := cosh_sub_half_mul_sinh_lt_one hx
  have hsinh : (0 : ℝ) < Real.sinh (B * r) := Real.sinh_pos_iff.2 hx
  have hkey : r / B - B * r / 2 = r * (2 - B ^ 2) / (2 * B) := by field_simp
  have hnn : (0 : ℝ) ≤ r * (2 - B ^ 2) / (2 * B) :=
    div_nonneg (mul_nonneg hr.le (by linarith)) (by linarith)
  have hge : B * r / 2 ≤ r / B := by linarith
  have hmul : B * r / 2 * Real.sinh (B * r) ≤ r / B * Real.sinh (B * r) :=
    mul_le_mul_of_nonneg_right hge hsinh.le
  unfold hilbertMajorant
  linarith

theorem hilbertMajorant_le_one {B r : ℝ} (hB : 0 < B) (hB2 : B ^ 2 ≤ 2) (hr : 0 ≤ r) :
    hilbertMajorant B r ≤ 1 := by
  rcases hr.lt_or_eq with h | h
  · exact (hilbertMajorant_lt_one hB hB2 h).le
  · rw [← h]
    exact le_of_eq (hilbertMajorant_zero B)

/-! ## The Hilbert chord lemma -/

/-- The chord bound for the convex function `a ↦ e^{-ra}` on `[-B, B]`. -/
theorem exp_neg_mul_le_chord {B r a : ℝ} (hB : 0 < B) (ha : |a| ≤ B) :
    Real.exp (-(r * a))
      ≤ (B + a) / (2 * B) * Real.exp (-(r * B)) + (B - a) / (2 * B) * Real.exp (r * B) := by
  have hle := abs_le.1 ha
  have hBne : B ≠ 0 := ne_of_gt hB
  have hw1 : (0 : ℝ) ≤ (B + a) / (2 * B) :=
    div_nonneg (by linarith [hle.1]) (by linarith)
  have hw2 : (0 : ℝ) ≤ (B - a) / (2 * B) :=
    div_nonneg (by linarith [hle.2]) (by linarith)
  have hsum : (B + a) / (2 * B) + (B - a) / (2 * B) = 1 := by field_simp; ring
  have h := convexOn_exp.2 (Set.mem_univ (-(r * B))) (Set.mem_univ (r * B)) hw1 hw2 hsum
  simp only [smul_eq_mul] at h
  have harg : (B + a) / (2 * B) * -(r * B) + (B - a) / (2 * B) * (r * B) = -(r * a) := by
    field_simp
    ring
  rwa [harg] at h

/-- **Hilbert chord lemma (scalar form).**  If the reals `hⱼ` satisfy `|hⱼ| ≤ Br` and
`m r² = -∑ hⱼ`, then their exponential mean is at most `F_B(r)`. -/
theorem mean_exp_le_hilbertMajorant {m : ℕ} (hm : 0 < m) (h : Fin m → ℝ) {B r : ℝ}
    (hB : 0 < B) (hr : 0 ≤ r) (hr2 : (m : ℝ) * r ^ 2 = -∑ j, h j)
    (hbound : ∀ j, |h j| ≤ B * r) :
    (m : ℝ)⁻¹ * ∑ j, Real.exp (h j) ≤ hilbertMajorant B r := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hBne : B ≠ 0 := ne_of_gt hB
  rcases hr.lt_or_eq with hrpos | hr0
  · have hrne : r ≠ 0 := ne_of_gt hrpos
    have hchord : ∀ j, Real.exp (h j)
        ≤ (B + -h j / r) / (2 * B) * Real.exp (-(r * B))
          + (B - -h j / r) / (2 * B) * Real.exp (r * B) := by
      intro j
      have habs : |(-h j / r)| ≤ B := by
        have h1 : |(-h j / r)| = |h j| / r := by
          rw [abs_div, abs_neg, abs_of_pos hrpos]
        have h2 : |h j| ≤ B * r := hbound j
        have h4 : |h j| / r * r = |h j| := div_mul_cancel₀ _ hrne
        rw [h1]
        nlinarith [h2, h4, hrpos]
      have hxc := exp_neg_mul_le_chord (B := B) (r := r) (a := -h j / r) hB habs
      have harg : -(r * (-h j / r)) = h j := by field_simp
      rwa [harg] at hxc
    have haff : ∀ j : Fin m, (B + -h j / r) / (2 * B) * Real.exp (-(r * B))
          + (B - -h j / r) / (2 * B) * Real.exp (r * B)
        = (Real.exp (-(r * B)) + Real.exp (r * B)) / 2
          + (Real.exp (-(r * B)) - Real.exp (r * B)) / (2 * B) * (-h j / r) := by
      intro j; field_simp; ring
    have hA : ∑ j, (-h j / r) = (m : ℝ) * r := by
      have h1 : ∑ j, (-h j / r) = (-∑ j, h j) / r := by
        rw [← Finset.sum_div]
        congr 1
        simp
      rw [h1, ← hr2]
      field_simp
    have hval : ∑ j, ((B + -h j / r) / (2 * B) * Real.exp (-(r * B))
          + (B - -h j / r) / (2 * B) * Real.exp (r * B))
        = (m : ℝ) * ((Real.exp (-(r * B)) + Real.exp (r * B)) / 2
            + (Real.exp (-(r * B)) - Real.exp (r * B)) / (2 * B) * r) := by
      have hcong : ∑ j, ((B + -h j / r) / (2 * B) * Real.exp (-(r * B))
            + (B - -h j / r) / (2 * B) * Real.exp (r * B))
          = ∑ _j : Fin m, ((Real.exp (-(r * B)) + Real.exp (r * B)) / 2
            + (Real.exp (-(r * B)) - Real.exp (r * B)) / (2 * B) * (-h _j / r)) :=
        Finset.sum_congr rfl (fun j _ => haff j)
      rw [hcong, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hA]
      ring
    have hsumle : ∑ j, Real.exp (h j)
        ≤ (m : ℝ) * ((Real.exp (-(r * B)) + Real.exp (r * B)) / 2
            + (Real.exp (-(r * B)) - Real.exp (r * B)) / (2 * B) * r) := by
      rw [← hval]
      exact Finset.sum_le_sum fun j _ => hchord j
    rw [hilbertMajorant_eq B r hBne]
    have hstep := mul_le_mul_of_nonneg_left hsumle (le_of_lt (inv_pos.2 hm'))
    calc (m : ℝ)⁻¹ * ∑ j, Real.exp (h j)
        ≤ (m : ℝ)⁻¹ * ((m : ℝ) * ((Real.exp (-(r * B)) + Real.exp (r * B)) / 2
            + (Real.exp (-(r * B)) - Real.exp (r * B)) / (2 * B) * r)) := hstep
      _ = (Real.exp (-(r * B)) + Real.exp (r * B)) / 2
            + (Real.exp (-(r * B)) - Real.exp (r * B)) / (2 * B) * r := by
          field_simp
  · have hzero : ∀ j, h j = 0 := by
      intro j
      have hb := hbound j
      rw [← hr0, mul_zero] at hb
      have hnn := abs_nonneg (h j)
      linarith [neg_abs_le (h j), le_abs_self (h j)]
    have hs : ∑ j, Real.exp (h j) = (m : ℝ) := by
      have hc : ∀ j : Fin m, Real.exp (h j) = 1 := fun j => by rw [hzero j, Real.exp_zero]
      simp [hc]
    have hlhs : (m : ℝ)⁻¹ * ∑ j, Real.exp (h j) = 1 := by
      rw [hs]; field_simp
    have hmaj : hilbertMajorant B r = 1 := by rw [← hr0, hilbertMajorant_zero]
    linarith

/-- **Hilbert chord lemma (vector form).**  For vectors in a real inner product space with
`u = m⁻¹ ∑ vⱼ`, `‖vⱼ‖ ≤ B` and `r = ‖u‖`:
`m⁻¹ ∑ⱼ e^{-⟪vⱼ, u⟫} ≤ cosh(Br) - (r/B) sinh(Br)`. -/
theorem hilbert_chord_lemma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (hm : 0 < m) (v : Fin m → E) {B : ℝ} (hB : 0 < B) (hvB : ∀ j, ‖v j‖ ≤ B)
    (u : E) (hu : u = (m : ℝ)⁻¹ • ∑ j, v j) :
    (m : ℝ)⁻¹ * ∑ j, Real.exp (-(inner ℝ (v j) u)) ≤ hilbertMajorant B ‖u‖ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : ∑ j, v j = (m : ℝ) • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (ne_of_gt hm'), one_smul]
  have hinner : ∑ j, inner ℝ (v j) u = (m : ℝ) * ‖u‖ ^ 2 := by
    have h1 : ∑ j, inner ℝ (v j) u = inner ℝ (∑ j, v j) u := by
      rw [sum_inner]
    rw [h1, hsum, real_inner_smul_left, real_inner_self_eq_norm_sq]
  refine mean_exp_le_hilbertMajorant hm (fun j => -(inner ℝ (v j) u)) hB (norm_nonneg u) ?_ ?_
  · simp only [Finset.sum_neg_distrib, neg_neg]
    linarith [hinner]
  · intro j
    show |(-(inner ℝ (v j) u))| ≤ B * ‖u‖
    rw [abs_neg]
    calc |inner ℝ (v j) u| ≤ ‖v j‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ B * ‖u‖ := mul_le_mul_of_nonneg_right (hvB j) (norm_nonneg u)

/-! ## The abstract central theorem -/

/-- **Abstract uniform central bound.**  If the row logarithms `hⱼ` obey the Cauchy–Schwarz
envelope `|hⱼ| ≤ Br` with `B² ≤ 2` and `m r² = -∑ hⱼ`, then `∑ⱼ e^{hⱼ} ≤ m`. -/
theorem sum_exp_le_card_of_energy {m : ℕ} (hm : 0 < m) (h : Fin m → ℝ) {B r : ℝ}
    (hB : 0 < B) (hB2 : B ^ 2 ≤ 2) (hr : 0 ≤ r) (hr2 : (m : ℝ) * r ^ 2 = -∑ j, h j)
    (hbound : ∀ j, |h j| ≤ B * r) :
    ∑ j, Real.exp (h j) ≤ (m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have h1 := mean_exp_le_hilbertMajorant hm h hB hr hr2 hbound
  have h2 := hilbertMajorant_le_one hB hB2 hr
  have h3 : (m : ℝ)⁻¹ * ∑ j, Real.exp (h j) ≤ 1 := le_trans h1 h2
  calc ∑ j, Real.exp (h j) = (m : ℝ) * ((m : ℝ)⁻¹ * ∑ j, Real.exp (h j)) := by field_simp
    _ ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left h3 (le_of_lt hm')
    _ = (m : ℝ) := mul_one _

/-! ## The uniform central radius -/

/-- `√(1 - e^{-2}) = 0.9298734950321937…`, the uniform central radius of the certificate. -/
noncomputable def centralRadius : ℝ := Real.sqrt (1 - Real.exp (-2))

theorem exp_neg_two_lt_one : Real.exp (-2 : ℝ) < 1 := by
  have hprod : Real.exp (-2 : ℝ) * Real.exp (2 : ℝ) = 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 : (3 : ℝ) ≤ Real.exp (2 : ℝ) := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hpos : (0 : ℝ) < Real.exp (-2 : ℝ) := Real.exp_pos _
  nlinarith [mul_nonneg hpos.le (by linarith : (0 : ℝ) ≤ Real.exp (2 : ℝ) - 3)]

theorem centralRadius_sq : centralRadius ^ 2 = 1 - Real.exp (-2 : ℝ) := by
  unfold centralRadius
  exact Real.sq_sqrt (by linarith [exp_neg_two_lt_one])

theorem centralRadius_nonneg : 0 ≤ centralRadius := Real.sqrt_nonneg _

theorem centralRadius_lt_one : centralRadius < 1 := by
  have hpos : (0 : ℝ) < Real.exp (-2 : ℝ) := Real.exp_pos _
  nlinarith [centralRadius_sq, centralRadius_nonneg]

/-- Inside the central ball the squared feature norm `L = -log(1 - ρ²)` is at most `2`. -/
theorem neg_log_le_two {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ centralRadius) :
    -Real.log (1 - ρ ^ 2) ≤ 2 := by
  have hpos : (0 : ℝ) < Real.exp (-2 : ℝ) := Real.exp_pos _
  have hsq : ρ ^ 2 ≤ 1 - Real.exp (-2 : ℝ) := by
    nlinarith [centralRadius_sq, centralRadius_nonneg]
  have hge : Real.exp (-2 : ℝ) ≤ 1 - ρ ^ 2 := by linarith
  have hlog : Real.log (Real.exp (-2 : ℝ)) ≤ Real.log (1 - ρ ^ 2) :=
    Real.log_le_log hpos hge
  rw [Real.log_exp] at hlog
  linarith

/-! ## The conditional uniform central theorem -/

/-- **Uniform central FP_m, conditional on the two series inputs.**

`hEnergy` is nonnegativity of the logarithmic energy `E = -∑ⱼ hⱼ = m⁻¹ ∑_ν |p_ν|²/ν`, and
`hCauchySchwarz` is the Fourier Cauchy–Schwarz step `hⱼ² ≤ (E/m) Lⱼ` with
`Lⱼ = -log(1 - |cⱼ|²)`.  Both are series facts about the power sums `p_ν = ∑ₖ cₖ^ν`, proved
analytically as ROWCERT+ steps (i)–(iii) in `FreePointFP5StructureLab.md` §3.  They are NOT
formalised here; everything downstream of them is. -/
theorem freePointSum_central_le_of_series {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ centralRadius) (h : Fin m → ℝ)
    (hdef : ∀ j, h j = (m : ℝ)⁻¹ * ∑ k, Real.log ‖1 - (starRingEnd ℂ) (c j) * c k‖)
    (hEnergy : ∑ j, h j ≤ 0)
    (hCauchySchwarz : ∀ j,
      h j ^ 2 ≤ (-(∑ i, h i) / (m : ℝ)) * (-Real.log (1 - ‖c j‖ ^ 2))) :
    freePointSum c ≤ (m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hcr := centralRadius_lt_one
  have hlt : ∀ j, ‖c j‖ < 1 := fun j => lt_of_le_of_lt (hc j) hcr
  have hposd : ∀ j k, 0 < ‖1 - (starRingEnd ℂ) (c j) * c k‖ := by
    intro j k
    rw [norm_pos_iff, sub_ne_zero]
    intro hEq
    have h1 : ‖(starRingEnd ℂ) (c j) * c k‖ = 1 := by rw [← hEq, norm_one]
    rw [norm_mul, Complex.norm_conj] at h1
    nlinarith [norm_nonneg (c j), norm_nonneg (c k), hlt j, hlt k]
  have hrow : ∀ j, (∏ k, ‖1 - (starRingEnd ℂ) (c j) * c k‖) ^ ((m : ℝ)⁻¹) = Real.exp (h j) := by
    intro j
    rw [Real.rpow_def_of_pos (Finset.prod_pos fun k _ => hposd j k),
      Real.log_prod (fun k _ => ne_of_gt (hposd j k)), hdef j]
    congr 1
    ring
  have hEnergyNonneg : (0 : ℝ) ≤ -(∑ j, h j) := by linarith
  set r : ℝ := Real.sqrt (-(∑ j, h j) / (m : ℝ)) with hrdef
  have hrnn : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = -(∑ j, h j) / (m : ℝ) :=
    Real.sq_sqrt (div_nonneg hEnergyNonneg (le_of_lt hm'))
  have hB : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hB2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hbound : ∀ j, |h j| ≤ Real.sqrt 2 * r := by
    intro j
    have hxs : ‖c j‖ ^ 2 < 1 := by nlinarith [norm_nonneg (c j), hlt j]
    have hxnn : (0 : ℝ) ≤ ‖c j‖ ^ 2 := sq_nonneg _
    have hL : -Real.log (1 - ‖c j‖ ^ 2) ≤ 2 := neg_log_le_two (norm_nonneg _) (hc j)
    have hLnn : (0 : ℝ) ≤ -Real.log (1 - ‖c j‖ ^ 2) := by
      have hlog : Real.log (1 - ‖c j‖ ^ 2) ≤ 0 :=
        Real.log_nonpos (by linarith) (by linarith)
      linarith
    have hcs := hCauchySchwarz j
    rw [← hr2] at hcs
    have hsq : h j ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
      have hexp : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by rw [mul_pow, hB2]
      rw [hexp]
      nlinarith [sq_nonneg r]
    calc |h j| = Real.sqrt (h j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((Real.sqrt 2 * r) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 2 * r := Real.sqrt_sq (mul_nonneg (le_of_lt hB) hrnn)
  have hmr : (m : ℝ) * r ^ 2 = -∑ j, h j := by
    rw [hr2]; field_simp
  have hmain := sum_exp_le_card_of_energy hm h hB (le_of_eq hB2) hrnn hmr hbound
  have hfs : freePointSum c = ∑ j, Real.exp (h j) := by
    unfold freePointSum
    exact Finset.sum_congr rfl fun j _ => hrow j
  rw [hfs]
  exact hmain

end ErdosProblems.Erdos1041.FreePointHilbertCertificate
