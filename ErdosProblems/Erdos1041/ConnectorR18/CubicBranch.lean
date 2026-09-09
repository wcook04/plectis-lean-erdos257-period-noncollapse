import ErdosProblems.Erdos1041.ConnectorR18.PolynomialBranches
import ErdosProblems.Erdos1041.PaperCubicCompletion

/-!
# Scale-free cubic branch, using the supplied algebraic Schur root count

AUTHORED / UNRUN. The supplied `PaperCubicCompletion` constructs unit-scale
connectors. This file removes the unnecessary unit-scale restriction from
its normalized hub, using the actual minimum critical modulus instead.
There is no assumed root pair, area theorem, coarea theorem, or curve supplier.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.ConnectorR18
open Polynomial Set PaperAnalyticTargets

/-- Uniqueness of a nonnegative real cube root, by the exact factorization. -/
theorem nonneg_cube_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 3 = y ^ 3) : x = y := by
  have hnotlt : ¬ x < y := by
    intro hxy
    have hyp : 0 < y := lt_of_le_of_lt hx hxy
    have hs : 0 < x ^ 2 + x * y + y ^ 2 := by
      have hxy0 := mul_nonneg hx hy
      have hy2 := sq_pos_of_pos hyp
      nlinarith [sq_nonneg x]
    have hp := mul_pos (sub_pos.mpr hxy) hs
    nlinarith
  have hnotgt : ¬ y < x := by
    intro hyx
    have hxp : 0 < x := lt_of_le_of_lt hy hyx
    have hs : 0 < x ^ 2 + x * y + y ^ 2 := by
      have hxy0 := mul_nonneg hx hy
      have hx2 := sq_pos_of_pos hxp
      nlinarith [sq_nonneg y]
    have hp := mul_pos (sub_pos.mpr hyx) hs
    nlinarith
  exact le_antisymm (le_of_not_gt hnotgt) (le_of_not_gt hnotlt)

/-- The normalized cubic root-count result yields a closed hub at ANY positive
critical-value scale. The other critical value need only be no smaller. -/
theorem scaled_hub_from_critical_expansion (p : ℂ[X]) (c δ v : ℂ)
    (hv0 : v ≠ 0)
    (hform : ∀ x : ℂ, p.eval (c + x) = x ^ 3 - (3 / 2 : ℂ) * δ * x ^ 2 + v)
    (hmin : ‖v‖ ≤ ‖p.eval (c + δ)‖) :
    ∃ a b : ℂ, a ≠ b ∧ p.eval a = 0 ∧ p.eval b = 0 ∧
      ConnectedAtMost p.eval ‖v‖ (2 * ‖v‖ ^ ((1 : ℝ) / 3)) a b := by
  obtain ⟨α, hα⟩ := PaperCubicFibres.exists_nth_root (q := 3) (by norm_num) v
  have hα0 : α ≠ 0 := by
    intro he
    rw [he, zero_pow (by norm_num)] at hα
    exact hv0 hα.symm
  have hnorm : ‖α‖ = ‖v‖ ^ ((1 : ℝ) / 3) := by
    have hleft : ‖α‖ ^ (3 : ℕ) = ‖v‖ := by
      simpa only [norm_pow] using congrArg norm hα
    have hright : (‖v‖ ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = ‖v‖ := by
      rw [← Real.rpow_mul_natCast (norm_nonneg v)]
      norm_num [Real.rpow_natCast]
    exact nonneg_cube_eq (norm_nonneg α) (Real.rpow_nonneg (norm_nonneg v) _)
      (hleft.trans hright.symm)
  let B : ℂ := δ / α
  have hpull (w : ℂ) : p.eval (c + α * w) = v * normalizedCubic B w := by
    rw [hform, ← hα]
    dsimp [normalizedCubic, B]
    field_simp [hα0]
    <;> ring
  have hother : p.eval (c + δ) = v * (1 - B ^ 3 / 2) := by
    rw [hform, ← hα]
    dsimp [B]
    field_simp [hα0]
    <;> ring
  have hB : 1 ≤ ‖1 - B ^ 3 / 2‖ := by
    rw [hother, norm_mul] at hmin
    have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    by_contra hlt
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hlt) hvp
    simp only [mul_one] at hh
    exact hh.not_ge hmin
  obtain ⟨u, w, huw, hu, hw, huroot, hwroot⟩ := PaperCubicSchur.cubic_root_count B hB
  have huroot' : normalizedCubic B u = 0 := by
    simpa [normalizedCubic] using huroot
  have hwroot' : normalizedCubic B w = 0 := by
    simpa [normalizedCubic] using hwroot
  have ha : p.eval (c + α * u) = 0 := by rw [hpull, huroot', mul_zero]
  have hb : p.eval (c + α * w) = 0 := by rw [hpull, hwroot', mul_zero]
  have hab : c + α * u ≠ c + α * w := by
    intro he
    exact huw ((mul_left_cancel₀ hα0) (add_left_cancel he))
  have hspoke (q : ℂ) (hq : normalizedCubic B q = 0) (hqn : ‖q‖ ≤ 1)
      (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      ‖p.eval (c + (t : ℂ) * ((c + α * q) - c))‖ ≤ ‖v‖ := by
    have he : c + (t : ℂ) * ((c + α * q) - c) = c + α * ((t : ℂ) * q) := by ring
    rw [he, hpull, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg v)
      (normalizedCubic_spoke_norm_le_one hq hqn ht0 ht1)
  have hlength : ‖c - (c + α * u)‖ + ‖(c + α * w) - c‖ ≤
      2 * ‖v‖ ^ ((1 : ℝ) / 3) := by
    have he1 : c - (c + α * u) = -(α * u) := by ring
    have he2 : (c + α * w) - c = α * w := by ring
    rw [he1, he2, norm_neg, norm_mul, norm_mul, ← hnorm]
    have h1 := mul_le_mul_of_nonneg_left hu (norm_nonneg α)
    have h2 := mul_le_mul_of_nonneg_left hw (norm_nonneg α)
    nlinarith
  exact ⟨c + α * u, c + α * w, hab, ha, hb,
    connectedAtMost_of_spokes (hspoke u huroot hu) (hspoke w hwroot hw) hlength⟩

/-- An arbitrary monic cubic presented by its root enumeration, with its true
minimum critical modulus, has a two-spoke connector in K_μ of length ≤2 μ^(1/3).
This is the squarefree-location branch; repeated occurrences are handled in
`repeated_occurrences_complete` without an analytic assumption. -/
theorem cubic_minimum_connector {p : ℂ[X]} {z : Fin 3 → ℂ} {μ : ℝ}
    (hp : RootEnumeration p z) (hm : CriticalMinimum p μ)
    (hz : Function.Injective z) :
    ∃ i j : Fin 3, i ≠ j ∧ z i ≠ z j ∧
      ConnectedAtMost p.eval μ (2 * μ ^ ((1 : ℝ) / 3)) (z i) (z j) := by
  obtain ⟨A, B, C, hpoly⟩ := PaperCubicCompletion.cubic_coefficients p z hp
  obtain ⟨c, hc, hμ⟩ := hm.1
  let d : ℂ := -(2 / 3 : ℂ) * A - c
  have hsum : c + d = -(2 / 3 : ℂ) * A := by dsimp [d]; ring
  have hd : p.derivative.eval d = 0 := by
    rw [(PaperCubicCompletion.cubic_formulas p A B C hpoly d).2]
    rw [(PaperCubicCompletion.cubic_formulas p A B C hpoly c).2] at hc
    dsimp [d]
    linear_combination hc
  have hmin : ‖p.eval c‖ ≤ ‖p.eval d‖ := by
    rw [← hμ]
    exact hm.2 ⟨d, hd, rfl⟩
  have hnz : p.eval c ≠ 0 := by
    have hpos := criticalMinimum_pos_of_injective hp hm hz
    rw [hμ] at hpos
    exact norm_pos_iff.mp hpos
  have hform := PaperCubicCompletion.expansion_at_critical p A B C c d hpoly hc hsum
  obtain ⟨a, b, hab, ha, hb, H⟩ := scaled_hub_from_critical_expansion p c (d - c)
    (p.eval c) hnz hform (by
      have he : c + (d - c) = d := by ring
      simpa only [he] using hmin)
  obtain ⟨i, hi⟩ := ((PaperCubicCompletion.enumeration_facts p z hp).2.2 a).mp ha
  obtain ⟨j, hj⟩ := ((PaperCubicCompletion.enumeration_facts p z hp).2.2 b).mp hb
  have hval : z i ≠ z j := by simpa only [hi, hj] using hab
  refine ⟨i, j, ?_, hval, ?_⟩
  · intro he
    exact hval (congrArg z he)
  · simpa only [hi, hj, ← hμ] using H

/-- Both exact ConstantFactorPath conclusions in degree three, with no analytic
supplier and no use of the roots-in-unit-disc premise in the small-μ branch. -/
theorem cubic_complete {p : ℂ[X]} {z : Fin 3 → ℂ} {μ : ℝ}
    (hp : RootEnumeration p z) (hm : CriticalMinimum p μ) : Conclusion 3 p z μ := by
  classical
  by_cases hz : Function.Injective z
  · obtain ⟨i, j, hij, hval, H⟩ := cubic_minimum_connector hp hm hz
    have hμ := criticalMinimum_nonneg hm
    have hρ := Real.rpow_nonneg hμ ((1 : ℝ) / 3)
    constructor
    · refine ⟨i, j, hij, ?_, fun _ => hval⟩
      apply connectedAtMost_mono H (by linarith)
      norm_num only [Nat.cast_ofNat]
      nlinarith
    · intro hdisc hhalf
      refine ⟨i, j, hij, ?_⟩
      apply closed_to_open_mono H (by linarith)
      have hr : μ ^ ((1 : ℝ) / 3) ≤ 1 :=
        Real.rpow_le_one hμ (by linarith) (by positivity)
      nlinarith
  · have hd : ∃ i j : Fin 3, i ≠ j ∧ z i = z j := by
      by_contra h
      apply hz
      intro i j he
      by_contra hij
      exact h ⟨i, j, hij, he⟩
    obtain ⟨i, j, hij, he⟩ := hd
    exact repeated_occurrences_complete hp hm hij he

end ErdosProblems.Erdos1041.ConnectorR18
