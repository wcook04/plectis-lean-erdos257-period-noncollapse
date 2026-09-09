import ErdosProblems.Erdos1041.WeightedBoundaryDeficitR10
import ErdosProblems.Erdos1041.GroupedPoleNearZero

/-! Equality rigidity, with repeated centres genuinely grouped.
Zero-weight points are allowed and correctly disappear from the equality test.
All Lean compilation and axiom audits are UNRUN. -/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate Topology
noncomputable section
namespace ErdosProblems.Erdos1041
open Complex Metric Filter

/-- The finite set of distinct centres, including zero when it occurs. -/
def weightedCentreSet {ι : Type*} [Fintype ι] (c : ι → ℂ) : Finset ℂ := by
  classical
  exact Finset.univ.image c

/-- Repeated centres carry the sum of their weights. -/
def groupedCentreWeight {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (a : ↥(weightedCentreSet c)) : ℝ := by
  classical
  exact ∑ j, if c j = (a : ℂ) then w j else 0

theorem centre_mem {ι : Type*} [Fintype ι] (c : ι → ℂ) (i : ι) :
    c i ∈ weightedCentreSet c := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem groupedCentreWeight_ge {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j) (i : ι) :
    w i ≤ groupedCentreWeight w c ⟨c i, centre_mem c i⟩ := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => if c j = c i then w j else 0)
    (fun j _ => by
      change 0 ≤ if c j = c i then w j else 0
      split_ifs
      · exact hw0 j
      · exact le_rfl) (Finset.mem_univ i)
  simpa only [groupedCentreWeight, if_pos rfl] using h

/-- Exact finite regrouping. No injectivity assumption on the original list. -/
theorem sum_groupedCentreWeight {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (F : ℂ → ℂ) :
    (∑ a : ↥(weightedCentreSet c), (groupedCentreWeight w c a : ℂ) * F a) =
      ∑ j, (w j : ℂ) * F (c j) := by
  classical
  have hwcast (a : ↥(weightedCentreSet c)) :
      (groupedCentreWeight w c a : ℂ) =
        ∑ j, if c j = (a : ℂ) then (w j : ℂ) else 0 := by
    simp only [groupedCentreWeight, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : c j = (a : ℂ) <;> simp [hj]
  simp only [hwcast, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let a : ↥(weightedCentreSet c) := ⟨c j, centre_mem c j⟩
  rw [Finset.sum_eq_single a]
  · simp [a]
  · intro b _ hba
    have hne : c j ≠ (b : ℂ) := by
      intro he
      apply hba
      exact Subtype.ext he.symm
    simp only [if_neg hne, zero_mul]
  · simp

/-- A zero logarithmic derivative on a ball forces every positively weighted
centre to be zero. The pole argument is applied to the distinct-centre subtype. -/
theorem weighted_centres_zero_of_rational_vanishing {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hc : ∀ j, ‖c j‖ ≤ 1)
    (hz : ∀ z ∈ ball (0 : ℂ) (1 / 2),
      (∑ j, (w j : ℂ) * conj (c j) / (1 - conj (c j) * z)) = 0) :
    ∀ j, 0 < w j → c j = 0 := by
  classical
  intro i hwi
  by_contra hci
  let a : ↥(weightedCentreSet c) → ℂ := fun b => conj (b : ℂ)
  let W := groupedCentreWeight w c
  let b : ↥(weightedCentreSet c) := ⟨c i, centre_mem c i⟩
  have ha : Function.Injective a := by
    intro x y hxy
    apply Subtype.ext
    have he := congrArg (fun z : ℂ => conj z) hxy
    simpa [a] using he
  have hb : a b ≠ 0 := by simpa [a, b] using hci
  have hW : 0 < W b := lt_of_lt_of_le hwi (groupedCentreWeight_ge w c hw0 i)
  have ha1 (x : ↥(weightedCentreSet c)) : ‖a x‖ ≤ 1 := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp x.property
    simpa only [a, Complex.norm_conj, ← hj] using hc j
  have hden (z : ℂ) (hzball : z ∈ ball (0 : ℂ) (1 / 2))
      (x : ↥(weightedCentreSet c)) : 1 - a x * z ≠ 0 := by
    have hzn : ‖z‖ < 1 / 2 := by simpa [mem_ball, dist_zero_right] using hzball
    have hlt : ‖a x * z‖ < 1 := by
      rw [norm_mul]
      have hle := mul_le_mul_of_nonneg_right (ha1 x) (norm_nonneg z)
      nlinarith
    intro he
    have he' : a x * z = 1 := (sub_eq_zero.mp he).symm
    exact (lt_irrefl (1 : ℝ)) (by simpa only [he', norm_one] using hlt)
  obtain ⟨z, hzball, hn⟩ := groupedPole_positive_exists_nonzero a W ha b hb hW
    (1 / 2) (by norm_num) hden
  apply hn
  have hreg := sum_groupedCentreWeight w c
    (fun x => conj x / (1 - conj x * z))
  simp only [← mul_div_assoc] at hreg
  simpa only [W, a] using hreg.trans (hz z hzball)

/-- Equality in the actual closed-disc quadratic sum gives the rational identity;
it is not supplied as an assumption to the paper theorem. -/
theorem weighted_positive_support_zero_of_equality {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1)
    (heq : weightedQuadratic w c = 1) : ∀ j, 0 < w j → c j = 0 := by
  have ha := weightedTaylorCoeff_eq_zero_of_equality w c hw0 hw hc heq
  have hg (z : ℂ) (hz : z ∈ ball (0 : ℂ) (1 / 2)) : weightedAnalyticLog w c z = 1 :=
    weightedAnalyticLog_eq_one_on_halfDisc w c hc ha
      (by simpa [mem_ball, dist_zero_right] using hz)
  apply weighted_centres_zero_of_rational_vanishing w c hw0 hc
  intro z hz
  have hz' : ‖z‖ < 1 / 2 := by simpa [mem_ball, dist_zero_right] using hz
  have hevent : weightedAnalyticLog w c =ᶠ[𝓝 z] (fun _ : ℂ => (1 : ℂ)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with t ht
    exact hg t ht
  have hd0 : deriv (weightedAnalyticLog w c) z = 0 := by
    simpa only [deriv_const] using hevent.deriv_eq
  have hd := (hasDerivAt_weightedAnalyticLog w c z (by
    intro j
    have h := mul_le_mul_of_nonneg_right (hc j) (norm_nonneg z)
    nlinarith)).deriv
  rw [hd0, hg z hz, one_mul] at hd
  have hneg : (∑ j, (w j : ℂ) * (-conj (c j) / (1 - conj (c j) * z))) =
      -(∑ j, (w j : ℂ) * conj (c j) / (1 - conj (c j) * z)) := by
    simp only [neg_div, mul_neg, mul_div_assoc, Finset.sum_neg_distrib]
  rw [hneg] at hd
  exact neg_eq_zero.mp hd.symm

/-- Zero-weight centres have no effect, even when a factor vanishes. -/
theorem weightedGeometric_eq_one_of_support_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hs : ∀ j, 0 < w j → c j = 0) (z : ℂ) : weightedGeometric w c z = 1 := by
  apply Finset.prod_eq_one
  intro j _
  by_cases hj : w j = 0
  · simp only [hj, Real.rpow_zero]
  · have hcj := hs j (lt_of_le_of_ne (hw0 j) (Ne.symm hj))
    simp only [hcj, map_zero, zero_mul, sub_zero, norm_one, Real.one_rpow]

theorem weighted_equality_iff_positive_support_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) :
    weightedQuadratic w c = 1 ↔ ∀ j, 0 < w j → c j = 0 := by
  refine ⟨weighted_positive_support_zero_of_equality w c hw0 hw hc, ?_⟩
  intro hs
  unfold weightedQuadratic
  simp only [weightedGeometric_eq_one_of_support_zero w c hw0 hs, one_pow, mul_one]
  exact hw

theorem weighted_equality_iff_all_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw : ∀ j, 0 < w j)
    (hsum : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) :
    weightedQuadratic w c = 1 ↔ ∀ j, c j = 0 := by
  rw [weighted_equality_iff_positive_support_zero w c (fun j => (hw j).le) hsum hc]
  exact ⟨fun h j => h j (hw j), fun h j _ => h j⟩

end ErdosProblems.Erdos1041
end
