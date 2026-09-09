import ErdosProblems.Erdos269.PaperR7WindowResults

/-!
# Exact-modulus pinning and eventual escape at a fixed start

The precise denominator is the actual window product, not its lower bound
2^len. A nonintegral real (even a nonintegral rational) is separated from the
integers. This yields eventual escape when the relative bound tends to zero.
These are new proof scripts, not compiler or axiom-check receipts. UNRUN.
-/
namespace ErdosProblems.Erdos269.PaperR12
open PaperR7 Filter
open scoped Topology

/-- Irrationality is not needed for separation from the integers. -/
theorem nonintegral_has_integer_gap {x : ℝ}
    (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, δ ≤ |x - (k : ℝ)| := by
  have hf0 : Int.fract x ≠ 0 := by
    intro h0
    have he : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have h := Int.floor_add_fract x
      rw [h0] at h
      linarith
    exact hx ⌊x⌋ he
  have hfp : 0 < Int.fract x :=
    lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hf0)
  have hf1 := Int.fract_lt_one x
  refine ⟨min (Int.fract x) (1 - Int.fract x), lt_min hfp (by linarith), ?_⟩
  intro k
  have h := Int.floor_add_fract x
  rcases le_or_gt k ⌊x⌋ with hk | hk
  · have hkR : (k : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast hk
    have hle : Int.fract x ≤ x - (k : ℝ) := by linarith
    exact ((min_le_left _ _).trans hle).trans (le_abs_self _)
  · have hk' : ⌊x⌋ + 1 ≤ k := by omega
    have hkR : ((⌊x⌋ : ℤ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk'
    have hle : 1 - Int.fract x ≤ (k : ℝ) - x := by linarith
    have ha : min (Int.fract x) (1 - Int.fract x) ≤ |(k : ℝ) - x| :=
      ((min_le_right _ _).trans hle).trans (le_abs_self _)
    rwa [abs_sub_comm] at ha

/-- Exact pinning with an arbitrary congruent representative. Positivity of
W and both lower endpoint bounds are indispensable hypotheses. -/
theorem exact_modulus_pinning {x y K : ℝ} {W F r : ℤ}
    (hW : 0 < W) (hwin : y = (W : ℝ) * x - (F : ℝ))
    (hcong : W ∣ F + r)
    (hy0 : 0 ≤ y) (hyK : y ≤ K)
    (hr0 : (0 : ℝ) ≤ r) (hrK : (r : ℝ) ≤ K) :
    ∃ k : ℤ, |x - (k : ℝ)| ≤ K / (W : ℝ) := by
  obtain ⟨k, hk⟩ := hcong
  have hkR : (F : ℝ) + (r : ℝ) = (W : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  have hkey : (W : ℝ) * (x - (k : ℝ)) = y - (r : ℝ) := by
    nlinarith only [hwin, hkR]
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have ha : |y - (r : ℝ)| ≤ K := by
    exact abs_le.2 ⟨by linarith, by linarith⟩
  refine ⟨k, (le_div_iff₀ hWR).2 ?_⟩
  calc
    |x - (k : ℝ)| * (W : ℝ) = |(W : ℝ) * (x - (k : ℝ))| := by
      rw [abs_mul, abs_of_pos hWR, mul_comm]
    _ = |y - (r : ℝ)| := by rw [hkey]
    _ ≤ K := ha

/-- A fixed nonintegral launch forces ALL sufficiently long representatives
to exceed the bound. The quotient in the premise uses the exact modulus. -/
theorem eventual_escape_of_exact_decay {x : ℝ}
    (hx : ∀ k : ℤ, x ≠ (k : ℝ))
    (W F r : ℕ → ℤ) (y K : ℕ → ℝ)
    (hW : ∀ n, 0 < W n)
    (hwin : ∀ n, y n = (W n : ℝ) * x - (F n : ℝ))
    (hcong : ∀ n, W n ∣ F n + r n)
    (hy0 : ∀ n, 0 ≤ y n) (hyK : ∀ n, y n ≤ K n)
    (hr0 : ∀ n, (0 : ℝ) ≤ r n)
    (hsmall : Tendsto (fun n => K n / (W n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, K n < (r n : ℝ) := by
  obtain ⟨δ, hδ, hgap⟩ := nonintegral_has_integer_gap hx
  have hev : ∀ᶠ n in atTop, K n / (W n : ℝ) < δ :=
    (tendsto_order.1 hsmall).2 δ hδ
  filter_upwards [hev] with n hn
  by_contra hbad
  obtain ⟨k, hk⟩ := exact_modulus_pinning (hW n) (hwin n) (hcong n)
    (hy0 n) (hyK n) (hr0 n) (le_of_not_gt hbad)
  exact (not_lt_of_ge ((hgap k).trans hk)) hn

/-- Actual-source pinning; no source window equality is left as a premise. -/
theorem actual_exact_modulus_pinning (B lo len K : ℕ) (hB : 0 < B)
    (hK : B * bridgeWidth (lo + len) ≤ K)
    (hres : leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
      (-((B : ℤ) * actualWindowForcing lo len)) ≤ K) :
    ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)| ≤
      (K : ℝ) / (actualWindowBase lo len : ℝ) := by
  let W : ℤ := actualWindowBase lo len
  let F : ℤ := actualWindowForcing lo len
  let r : ℕ := leastPositiveResidue (Int.natAbs W) (-((B : ℤ) * F))
  have hW : 0 < W := windowBase235_pos lo len
  have hnat : ((Int.natAbs W : ℕ) : ℤ) = W := Int.natAbs_of_nonneg hW.le
  have hnp : 0 < Int.natAbs W := Int.natAbs_pos.mpr hW.ne'
  have hmod : Int.ModEq (Int.natAbs W) (r : ℤ) (-((B : ℤ) * F)) :=
    leastPositiveResidue_modEq hnp _
  have hcong : W ∣ (B : ℤ) * F + (r : ℤ) := by
    obtain ⟨t, ht⟩ : W ∣ -((B : ℤ) * F) - (r : ℤ) := by
      have h := Int.ModEq.dvd hmod
      rwa [hnat] at h
    refine ⟨-t, ?_⟩
    nlinarith only [ht]
  have hwin : (B : ℝ) * trueNormalizedState (lo + len) =
      (W : ℝ) * ((B : ℝ) * trueNormalizedState lo) -
        (((B : ℤ) * F : ℤ) : ℝ) := by
    have h := trueNormalizedState_window lo len
    change trueNormalizedState (lo + len) =
      (W : ℝ) * trueNormalizedState lo - (F : ℝ) at h
    rw [h]
    push_cast
    ring
  have hY0 : 0 ≤ (B : ℝ) * trueNormalizedState (lo + len) :=
    mul_nonneg (Nat.cast_nonneg B) (trueNormalizedState_pos (lo + len)).le
  have hY : (B : ℝ) * trueNormalizedState (lo + len) ≤
      ((B * bridgeWidth (lo + len) : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (trueNormalizedState_le_quadratic (lo + len))
      (show (0 : ℝ) ≤ (B : ℝ) by positivity)
    simpa [bridgeWidth, Nat.cast_mul, Nat.cast_pow, Nat.cast_add] using h
  have hYR : (B : ℝ) * trueNormalizedState (lo + len) ≤ (K : ℝ) :=
    hY.trans (by exact_mod_cast hK)
  have hr0 : (0 : ℝ) ≤ (r : ℤ) := by positivity
  have hrK : ((r : ℤ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hres
  exact exact_modulus_pinning hW hwin hcong hY0 hYR hr0 hrK

/-- The producer follows whenever the maximum of the requested cap and the
known state width is beaten by the ACTUAL modulus. -/
theorem escape_of_irrational_of_exact_beating
    (h : Irrational (dyadicShellTsumTailR235 1)) (G : ℕ → ℕ → ℕ)
    (hbeat : ∀ B lo : ℕ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ len : ℕ, 0 < len ∧
        ((max (G B (lo + len)) (B * bridgeWidth (lo + len)) : ℕ) : ℝ) /
          (actualWindowBase lo len : ℝ) < ε) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G := by
  intro B hB _hcop lo₀
  classical
  set lo : ℕ := lo₀ + 1 with hlo
  obtain ⟨δ, hδ, hgap⟩ := exists_dist_lower_bound_of_irrational
    ((irrational_trueNormalizedState h lo (by omega)).natCast_mul
      (m := B) (by omega))
  obtain ⟨len, hlen, hlt⟩ := hbeat B lo hB δ hδ
  refine ⟨lo, len, by omega, hlen,
    Int.natAbs_pos.mpr (windowBase235_pos lo len).ne', ?_⟩
  by_contra hbad
  rw [not_lt] at hbad
  obtain ⟨k, hk⟩ := actual_exact_modulus_pinning B lo len
    (max (G B (lo + len)) (B * bridgeWidth (lo + len))) hB
    (le_max_right _ _) (hbad.trans (le_max_left _ _))
  exact (not_lt_of_ge ((hgap k).trans hk)) hlt

end ErdosProblems.Erdos269.PaperR12
