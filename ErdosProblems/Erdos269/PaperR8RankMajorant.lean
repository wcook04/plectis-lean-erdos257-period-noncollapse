import ErdosProblems.Erdos269.PaperR7WindowResults
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The actual height-rank majorant (round 8)

This file supplies the missing geometric summation over height ranks, not a
comparison of the much larger dyadic-shell bound with `carryMajorantQ`.
It uses the live round-7 definitions without changing any of them.

Proof text: not elaborated in this return. No additional hypotheses are hidden
in the final theorem. Mathlib source checks use commit
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
-/

namespace ErdosProblems.Erdos269.PaperR8

open scoped BigOperators
open PaperR7

/-- Sum of the three actual height exponents at an integer cutoff. -/
def heightRank235 (x : ℕ) : ℕ :=
  Nat.log 2 x + Nat.log 3 x + Nat.log 5 x

/-- All three coordinates are monotone; fixing their sum fixes the profile. -/
theorem profile_eq_of_heightRank_eq {x y : ℕ}
    (h : heightRank235 x = heightRank235 y) :
    Nat.log 2 x = Nat.log 2 y ∧ Nat.log 3 x = Nat.log 3 y ∧
      Nat.log 5 x = Nat.log 5 y := by
  -- Mathlib/Data/Nat/Log.lean: Nat.log_mono_right.
  rcases le_total x y with hxy | hyx
  · have h2 : Nat.log 2 x ≤ Nat.log 2 y := Nat.log_mono_right hxy
    have h3 : Nat.log 3 x ≤ Nat.log 3 y := Nat.log_mono_right hxy
    have h5 : Nat.log 5 x ≤ Nat.log 5 y := Nat.log_mono_right hxy
    unfold heightRank235 at h
    omega
  · have h2 : Nat.log 2 y ≤ Nat.log 2 x := Nat.log_mono_right hyx
    have h3 : Nat.log 3 y ≤ Nat.log 3 x := Nat.log_mono_right hyx
    have h5 : Nat.log 5 y ≤ Nat.log 5 x := Nat.log_mono_right hyx
    unfold heightRank235 at h
    omega

theorem heightRank235_dyadic (a : ℕ) :
    heightRank235 (2 ^ a) = paperJumpIndex a := by
  -- Mathlib/Data/Nat/Log.lean: Nat.log_pow.
  unfold heightRank235 paperJumpIndex
  rw [Nat.log_pow (by decide : 1 < (2 : ℕ))]

theorem heightRank235_mono {x y : ℕ} (hxy : x ≤ y) :
    heightRank235 x ≤ heightRank235 y := by
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.log_mono_right hxy) (Nat.log_mono_right hxy))
    (Nat.log_mono_right hxy)

/-- Increasing a height rank by `k` multiplies the actual height by at least `2^k`. -/
theorem height_growth_by_rank {x y : ℕ} (hxy : x ≤ y) :
    threePrimeHeight 2 3 5 x * 2 ^ (heightRank235 y - heightRank235 x) ≤
      threePrimeHeight 2 3 5 y := by
  let a := Nat.log 2 x
  let b := Nat.log 3 x
  let c := Nat.log 5 x
  let A := Nat.log 2 y
  let B := Nat.log 3 y
  let C := Nat.log 5 y
  have h2 : a ≤ A := Nat.log_mono_right hxy
  have h3 : b ≤ B := Nat.log_mono_right hxy
  have h5 : c ≤ C := Nat.log_mono_right hxy
  have hd : heightRank235 y - heightRank235 x = (A - a) + (B - b) + (C - c) := by
    change (A + B + C) - (a + b + c) = _
    omega
  have ha : a + (A - a) = A := by omega
  have hb : b + (B - b) = B := by omega
  have hc : c + (C - c) = C := by omega
  have hpow3 : 2 ^ (B - b) ≤ 3 ^ (B - b) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 3) (B - b)
  have hpow5 : 2 ^ (C - c) ≤ 5 ^ (C - c) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 5) (C - c)
  have hg : 2 ^ (heightRank235 y - heightRank235 x) ≤
      2 ^ (A - a) * 3 ^ (B - b) * 5 ^ (C - c) := by
    rw [hd, pow_add, pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hpow3) hpow5
  calc
    threePrimeHeight 2 3 5 x * 2 ^ (heightRank235 y - heightRank235 x)
      ≤ threePrimeHeight 2 3 5 x *
          (2 ^ (A - a) * 3 ^ (B - b) * 5 ^ (C - c)) :=
        Nat.mul_le_mul_left _ hg
    _ = threePrimeHeight 2 3 5 y := by
      change (2 ^ a * 3 ^ b * 5 ^ c) *
        (2 ^ (A - a) * 3 ^ (B - b) * 5 ^ (C - c)) = 2 ^ A * 3 ^ B * 5 ^ C
      calc
        _ = (2 ^ a * 2 ^ (A - a)) * (3 ^ b * 3 ^ (B - b)) *
              (5 ^ c * 5 ^ (C - c)) := by ring
        _ = _ := by rw [← pow_add, ← pow_add, ← pow_add, ha, hb, hc]

/-- Each prime coordinate of an exponent triple is below its height coordinate. -/
theorem exponent_le_height_profile (e : Exponent235) :
    e.1 ≤ Nat.log 2 (exponentValue235 e) ∧
    e.2.1 ≤ Nat.log 3 (exponentValue235 e) ∧
    e.2.2 ≤ Nat.log 5 (exponentValue235 e) := by
  have hx : 0 < exponentValue235 e := exponentValue235_pos e
  have d2 : 2 ^ e.1 ∣ exponentValue235 e := by
    refine ⟨3 ^ e.2.1 * 5 ^ e.2.2, ?_⟩
    simp only [exponentValue235, smooth3Val]
    ring
  have d3 : 3 ^ e.2.1 ∣ exponentValue235 e := by
    refine ⟨2 ^ e.1 * 5 ^ e.2.2, ?_⟩
    simp only [exponentValue235, smooth3Val]
    ring
  have d5 : 5 ^ e.2.2 ∣ exponentValue235 e := by
    refine ⟨2 ^ e.1 * 3 ^ e.2.1, ?_⟩
    simp only [exponentValue235, smooth3Val]
    ring
  -- Mathlib/Data/Nat/Log.lean: Nat.le_log_of_pow_le.
  exact ⟨Nat.le_log_of_pow_le (by decide) (Nat.le_of_dvd hx d2),
    Nat.le_log_of_pow_le (by decide) (Nat.le_of_dvd hx d3),
    Nat.le_log_of_pow_le (by decide) (Nat.le_of_dvd hx d5)⟩

/-- The order of the bases reverses the order of their floor logarithms. -/
theorem sorted_height_profile {x : ℕ} (hx : x ≠ 0) :
    Nat.log 5 x ≤ Nat.log 3 x ∧ Nat.log 3 x ≤ Nat.log 2 x := by
  -- Mathlib/Data/Nat/Log.lean: Nat.pow_log_le_self.
  have h5 : 5 ^ Nat.log 5 x ≤ x := Nat.pow_log_le_self 5 hx
  have h3 : 3 ^ Nat.log 3 x ≤ x := Nat.pow_log_le_self 3 hx
  exact ⟨Nat.le_log_of_pow_le (by decide)
      ((Nat.pow_le_pow_left (by decide : 3 ≤ 5) _).trans h5),
    Nat.le_log_of_pow_le (by decide)
      ((Nat.pow_le_pow_left (by decide : 2 ≤ 3) _).trans h3)⟩

/-- At most `(n+3)^2/9` smooth points can have a given height rank.
The input is an arbitrary finite subset, not merely a preselected box. -/
theorem rank_fibre_card_bound (s : Finset Exponent235) (n : ℕ)
    (hn : ∀ e ∈ s, heightRank235 (exponentValue235 e) = n) :
    9 * s.card ≤ (n + 3) ^ 2 := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    simp
  · obtain ⟨e₀, he₀⟩ := hs
    let x := exponentValue235 e₀
    let A := Nat.log 2 x
    let B := Nat.log 3 x
    let C := Nat.log 5 x
    have hsub : s ⊆ smoothExponentShell 2 3 5 (2 ^ A) (2 ^ (A + 1)) A B C := by
      intro e he
      have hp := profile_eq_of_heightRank_eq ((hn e he).trans (hn e₀ he₀).symm)
      have hc := exponent_le_height_profile e
      have hA : Nat.log 2 (exponentValue235 e) = A := hp.1
      have hB : Nat.log 3 (exponentValue235 e) = B := hp.2.1
      have hC : Nat.log 5 (exponentValue235 e) = C := hp.2.2
      have heA : e.1 < A + 1 := by omega
      have heB : e.2.1 < B + 1 := by omega
      have heC : e.2.2 < C + 1 := by omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr heA,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr heB, Finset.mem_range.mpr heC⟩⟩, ?_⟩
      have hlo := Nat.pow_log_le_self 2 (exponentValue235_pos e).ne'
      have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (exponentValue235 e)
      rw [hA] at hlo hhi
      exact ⟨hlo, hhi⟩
    have hcount : s.card ≤ (B + 1) * (C + 1) :=
      (Finset.card_le_card hsub).trans
        (smoothExponentShell_card_le_dropFirst (by decide : 0 < (2 : ℕ))
          (by rw [pow_succ]; omega))
    have hsort := sorted_height_profile (exponentValue235_pos e₀).ne'
    have hsum : C + B + A = n := by
      have h := hn e₀ he₀
      change A + B + C = n at h
      omega
    have hquad : 9 * ((C + 1) * (B + 1)) ≤ (n + 3) ^ 2 :=
      sorted_pair_quadratic hsort.1 hsort.2 hsum
    have hmul : 9 * s.card ≤ 9 * ((B + 1) * (C + 1)) :=
      Nat.mul_le_mul_left 9 hcount
    have hquad' : 9 * ((B + 1) * (C + 1)) ≤ (n + 3) ^ 2 := by
      simpa only [Nat.mul_comm (C + 1) (B + 1)] using hquad
    exact hmul.trans hquad'

/-- The weight assigned to rank `n+k` in the half-height normalisation. -/
noncomputable def rankMajorant (n k : ℕ) : ℝ :=
  ((n + k + 3 : ℕ) : ℝ) ^ 2 / (18 * (2 : ℝ) ^ k)

/-- The three geometric moments, assembled at the exact printed constant. -/
theorem hasSum_rankMajorant (n : ℕ) :
    HasSum (rankMajorant n) (carryMajorantQ n : ℝ) := by
  have hs := hasSum_succ_sq_div_two_pow
  -- Mathlib/Analysis/SpecificLimits/Normed.lean:
  -- hasSum_choose_mul_geometric_of_norm_lt_one.
  have hg0 := hasSum_choose_mul_geometric_of_norm_lt_one 0
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have hg1 := hasSum_choose_mul_geometric_of_norm_lt_one 1
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h0 : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k) 2 := by
    norm_num at hg0
    exact hg0
  have h1 : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) 4 := by
    convert hg1 using 1 <;> norm_num [Nat.choose_one_right]
  have hh := ((hs.add (h1.mul_left (2 * ((n : ℝ) + 2)))).add
    (h0.mul_left (((n : ℝ) + 2) ^ 2))).div_const 18
  have hval : (12 + 2 * ((n : ℝ) + 2) * 4 + ((n : ℝ) + 2) ^ 2 * 2) / 18 =
      (carryMajorantQ n : ℝ) := by
    simp only [carryMajorantQ, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
    ring
  rw [hval] at hh
  apply hh.congr_fun
  intro k
  simp only [rankMajorant, Nat.cast_add, Nat.cast_ofNat, one_div_pow]
  ring

/-- A single normalised summand has the expected rank-decay weight. -/
theorem normalised_kernel_le_rank_weight (a : ℕ) (e : Exponent235)
    (he : 2 ^ a ≤ exponentValue235 e) :
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e ≤
      1 / (2 * (2 : ℝ) ^ (heightRank235 (exponentValue235 e) - paperJumpIndex a)) := by
  have hh := height_growth_by_rank he
  rw [heightRank235_dyadic] at hh
  have hhR : (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) *
      (2 : ℝ) ^ (heightRank235 (exponentValue235 e) - paperJumpIndex a) ≤
      (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ) := by exact_mod_cast hh
  have hH : (0 : ℝ) < (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ) :=
    threePrimeHeight235_cast_pos _
  have hP : (0 : ℝ) < (2 : ℝ) ^
      (heightRank235 (exponentValue235 e) - paperJumpIndex a) := by positivity
  unfold exponentKernel235
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hP)).mpr
  apply (mul_le_mul_iff_left₀ hH).mp
  calc
    ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 *
        (1 / (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ)) *
        (2 * (2 : ℝ) ^ (heightRank235 (exponentValue235 e) - paperJumpIndex a))) *
        (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ)
      = (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) *
          (2 : ℝ) ^ (heightRank235 (exponentValue235 e) - paperJumpIndex a) := by
            field_simp [ne_of_gt hH]
            <;> ring
    _ ≤ (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ) := hhR
    _ = 1 * (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ) := by ring

/-- Every finite collection from the actual tail is bounded by `Q(n_a)`. -/
theorem finite_normalised_tail_le_Q (a : ℕ) (s : Finset Exponent235)
    (hs : ∀ e ∈ s, 2 ^ a ≤ exponentValue235 e) :
    (∑ e ∈ s, (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e) ≤
      (carryMajorantQ (paperJumpIndex a) : ℝ) := by
  classical
  let kfun : Exponent235 → ℕ := fun e =>
    heightRank235 (exponentValue235 e) - paperJumpIndex a
  let f : Exponent235 → ℝ := fun e =>
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e
  have hfib : ∀ k ∈ s.image kfun,
      (∑ e ∈ s with kfun e = k, f e) ≤ rankMajorant (paperJumpIndex a) k := by
    intro k _hk
    let t := s.filter (fun e => kfun e = k)
    have ht : ∀ e ∈ t, heightRank235 (exponentValue235 e) = paperJumpIndex a + k := by
      intro e he
      have he' := Finset.mem_filter.mp he
      have hmono := heightRank235_mono (hs e he'.1)
      rw [heightRank235_dyadic] at hmono
      have hek : heightRank235 (exponentValue235 e) - paperJumpIndex a = k := he'.2
      omega
    have hcardN := rank_fibre_card_bound t (paperJumpIndex a + k) ht
    have hcard : (t.card : ℝ) ≤ ((paperJumpIndex a + k + 3 : ℕ) : ℝ) ^ 2 / 9 := by
      have h : (9 : ℝ) * t.card ≤ ((paperJumpIndex a + k + 3 : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast hcardN
      linarith
    change (∑ e ∈ t, f e) ≤ _
    calc
      (∑ e ∈ t, f e) ≤ ∑ _e ∈ t, 1 / (2 * (2 : ℝ) ^ k) := by
        apply Finset.sum_le_sum
        intro e he
        have he' := Finset.mem_filter.mp he
        have hw := normalised_kernel_le_rank_weight a e (hs e he'.1)
        change f e ≤ 1 / (2 * (2 : ℝ) ^ kfun e) at hw
        rw [he'.2] at hw
        exact hw
      _ = (t.card : ℝ) * (1 / (2 * (2 : ℝ) ^ k)) := by simp
      _ ≤ (((paperJumpIndex a + k + 3 : ℕ) : ℝ) ^ 2 / 9) *
          (1 / (2 * (2 : ℝ) ^ k)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = rankMajorant (paperJumpIndex a) k := by unfold rankMajorant; ring
  have hsum : (∑ e ∈ s, f e) =
      ∑ k ∈ s.image kfun, ∑ e ∈ s with kfun e = k, f e := by
    -- Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:
    -- Finset.sum_fiberwise_of_maps_to.
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun _e he => Finset.mem_image_of_mem kfun he) f
  change (∑ e ∈ s, f e) ≤ _
  rw [hsum]
  have hfinite := Finset.sum_le_sum hfib
  refine hfinite.trans ?_
  -- Mathlib/Topology/Algebra/InfiniteSum/Order.lean: sum_le_hasSum.
  exact sum_le_hasSum (s.image kfun)
    (fun k _ => by unfold rankMajorant; positivity)
    (hasSum_rankMajorant (paperJumpIndex a))

/-- A dependent index for the actual shells above `2^a`. -/
abbrev TailShellIndex (a : ℕ) :=
  Σ n : ℕ, {e : Exponent235 // e ∈ dyadicSmoothShell235 (a + n)}

def tailShellExponent (a : ℕ) (z : TailShellIndex a) : Exponent235 := z.2.val

theorem tailShellExponent_injective (a : ℕ) : Function.Injective (tailShellExponent a) := by
  intro z w h
  rcases z with ⟨n, ⟨e, he⟩⟩
  rcases w with ⟨m, ⟨f, hf⟩⟩
  change e = f at h
  subst f
  have hn := shellIndex235_eq_of_mem he
  have hm := shellIndex235_eq_of_mem hf
  have hnm : n = m := by omega
  subst m
  rfl

theorem tailShellExponent_lower (a : ℕ) (z : TailShellIndex a) :
    2 ^ a ≤ exponentValue235 (tailShellExponent a z) := by
  have hlo := (mem_dyadicSmoothShell235_iff.mp z.2.property).1
  exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_add_right a z.1)).trans hlo

/-- The literal tail, not an abstract orbit, is bounded by the printed rank cap. -/
theorem trueNormalizedState_le_carryMajorantQ (a : ℕ) :
    trueNormalizedState a ≤ (carryMajorantQ (paperJumpIndex a) : ℝ) := by
  classical
  let f : TailShellIndex a → ℝ := fun z =>
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 *
      exponentKernel235 (tailShellExponent a z)
  have hs0 : Summable (fun z : TailShellIndex a =>
      exponentKernel235 (tailShellExponent a z)) :=
    summable_exponentKernel235.comp_injective (tailShellExponent_injective a)
  have hs : Summable f := hs0.mul_left _
  have htsum : (∑' z : TailShellIndex a, f z) = trueNormalizedState a := by
    -- Mathlib/Topology/Algebra/InfiniteSum/Constructions.lean: Summable.tsum_sigma.
    rw [hs.tsum_sigma]
    change (∑' n : ℕ, ∑' e : {e : Exponent235 // e ∈ dyadicSmoothShell235 (a + n)},
      (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e.val) = _
    simp_rw [tsum_mul_left, tsum_exponentKernel235_shell]
    rfl
  rw [← htsum]
  -- Mathlib/Topology/Algebra/InfiniteSum/Order.lean:
  -- Summable.tsum_le_of_sum_le.
  apply hs.tsum_le_of_sum_le
  intro t
  let s := t.image (tailShellExponent a)
  have heq : (∑ z ∈ t, f z) =
      ∑ e ∈ s, (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e := by
    symm
    apply Finset.sum_image
    intro z _ w _ h
    exact tailShellExponent_injective a h
  rw [heq]
  apply finite_normalised_tail_le_Q a s
  intro e he
  obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp he
  exact tailShellExponent_lower a z

/-- The whole displayed actual-tail bound, including positivity. -/
theorem actual_tail_rank_bound (a : ℕ) :
    0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (carryMajorantQ (paperJumpIndex a) : ℝ) :=
  ⟨trueNormalizedState_pos a, trueNormalizedState_le_carryMajorantQ a⟩

end ErdosProblems.Erdos269.PaperR8
