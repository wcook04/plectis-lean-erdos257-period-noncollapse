import ErdosProblems.Erdos1041.ConnectorR18.Averaging
import ErdosProblems.Erdos1041.ConnectorR18.SupplierReduction

/-!
# Collective complete-radial budget: exact 573/100 specialization

AUTHORED / UNRUN. This formalizes a consumer of the stronger ordinary route
ALREADY PRESENT in `CollectiveRadialWindowBound.md`; it is not a novelty claim.
No analytic supplier is constructed here. In particular, `s` and `h` below
bound the two MEANS before selecting an angle. Only their SUM bounds the
selected total lift length. There is no invalid simultaneous separate-mean
selection hidden in the interface.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.ConnectorR18
open Polynomial Set PaperAnalyticTargets
open scoped BigOperators

def collectiveLogUpper : ℝ := 10407 / 12500
def collectiveBoundaryUpper : ℝ := 3141593 / 832550
def collectiveQ : ℝ := 48183 / 10000

theorem collective_log_bounds :
    (16651 / 20000 : ℝ) ^ 2 < Real.log 2 ∧
      Real.log 2 < collectiveLogUpper ^ 2 := by
  constructor
  · exact lt_trans (by norm_num) Real.log_two_gt_d9
  · exact lt_trans Real.log_two_lt_d9 (by norm_num [collectiveLogUpper])

theorem collective_boundary_squared : Real.pi ^ 2 / Real.log 2 ≤
    collectiveBoundaryUpper ^ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hl).mpr
  have hp : Real.pi ^ 2 ≤ (3141593 / 1000000 : ℝ) ^ 2 := by
    nlinarith [Real.pi_lt_d6, Real.pi_pos]
  have hb := mul_le_mul_of_nonneg_left collective_log_bounds.1.le
    (show 0 ≤ collectiveBoundaryUpper ^ 2 by positivity)
  norm_num [collectiveBoundaryUpper] at hb ⊢
  nlinarith

theorem collective_energy_constant :
    2 + (collectiveLogUpper + collectiveBoundaryUpper) ^ 2 < collectiveQ ^ 2 := by
  norm_num [collectiveLogUpper, collectiveBoundaryUpper, collectiveQ]

theorem collectiveQ_positive : 0 < collectiveQ := by norm_num [collectiveQ]
theorem collectiveQ_lt_open : collectiveQ < (57 / 10 : ℝ) := by norm_num [collectiveQ]

theorem two_rpow_one_fourth_lt : (2 : ℝ) ^ ((1 : ℝ) / 4) < 118921 / 100000 := by
  have he : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 2 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_natCast]
  apply lt_of_pow_lt_pow_left₀ 4 (by norm_num : (0 : ℝ) ≤ 118921 / 100000)
  rw [he]
  norm_num

theorem collective_top_scale {n : ℕ} {μ : ℝ} (hn : 4 ≤ n) (hμ : 0 ≤ μ) :
    (2 * μ) ^ ((1 : ℝ) / (n : ℝ)) ≤
      (118921 / 100000 : ℝ) * μ ^ ((1 : ℝ) / (n : ℝ)) := by
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he : (1 : ℝ) / (n : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ))).mpr
    linarith
  have ht := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he).trans
    two_rpow_one_fourth_lt.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hμ]
  exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hμ _)

theorem collective_closed_constant :
    collectiveQ * (118921 / 100000 : ℝ) < (573 / 100 : ℝ) := by
  norm_num [collectiveQ]

/-- Pure finite two-area estimate. X and Y are areas DIVIDED by π.
The numbers s,h are nonnegative bounds for the low and high MEANS;
L is the sum of actual lift lengths at a single selected good angle. -/
theorem collective_area_budget {K X Y τ s h L A : ℝ}
    (hK : 2 ≤ K) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hτ : 0 ≤ τ)
    (hs : 0 ≤ s) (hh : 0 ≤ h) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (harea : X + Y ≤ τ ^ 2)
    (hsq : s ^ 2 ≤ K * X)
    (hhq : h ^ 2 ≤ (K / 2) * Real.log 2 * Y)
    (hselected : L ≤ s + h)
    (hboundary : A ^ 2 ≤ (2 * Real.pi ^ 2 * K / Real.log 2) * Y) :
    2 * L + A ≤ K * (collectiveQ * τ) := by
  have hK0 : 0 ≤ K := by linarith
  let x := Real.sqrt (2 * K * X)
  let y := Real.sqrt (2 * K * Y)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hxq : x ^ 2 = 2 * K * X := Real.sq_sqrt (by positivity)
  have hyq : y ^ 2 = 2 * K * Y := Real.sq_sqrt (by positivity)
  have htwo : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 ≤ collectiveLogUpper := by norm_num [collectiveLogUpper]
  have hv0 : 0 ≤ collectiveBoundaryUpper := by norm_num [collectiveBoundaryUpper]
  have hlow : 2 * s ≤ Real.sqrt 2 * x := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow, htwo]
    nlinarith
  have hhcomp := mul_le_mul_of_nonneg_left collective_log_bounds.2.le
    (show 0 ≤ 2 * K * Y by positivity)
  have hhigh : 2 * h ≤ collectiveLogUpper * y := by
    apply (sq_le_sq₀ (by positivity) (mul_nonneg hu0 hy)).mp
    simp only [mul_pow, hyq]
    nlinarith
  have hbcomp := mul_le_mul_of_nonneg_left collective_boundary_squared
    (show 0 ≤ 2 * K * Y by positivity)
  have hbr : (2 * Real.pi ^ 2 * K / Real.log 2) * Y =
      (2 * K * Y) * (Real.pi ^ 2 / Real.log 2) := by ring
  have harc : A ≤ collectiveBoundaryUpper * y := by
    apply (sq_le_sq₀ hA (mul_nonneg hv0 hy)).mp
    simp only [mul_pow, hyq]
    rw [hbr] at hboundary
    nlinarith
  let b := collectiveLogUpper + collectiveBoundaryUpper
  have hb : 0 ≤ b := add_nonneg hu0 hv0
  have hsum : 2 * L + A ≤ Real.sqrt 2 * x + b * y := by
    dsimp [b]
    nlinarith
  have hsum0 : 0 ≤ Real.sqrt 2 * x + b * y := by positivity
  have hsumq := (sq_le_sq₀ (by positivity : 0 ≤ 2 * L + A) hsum0).mpr hsum
  have hcauchy := two_component_cauchy (Real.sqrt 2) b x y
  have hecomp := mul_le_mul_of_nonneg_right collective_energy_constant.le
    (show 0 ≤ x ^ 2 + y ^ 2 by positivity)
  have hacomp := mul_le_mul_of_nonneg_left harea
    (show 0 ≤ 2 * K * collectiveQ ^ 2 by positivity)
  apply linear_bound_of_quadratic hK (by positivity)
    (mul_nonneg collectiveQ_positive.le hτ)
  calc
    (2 * L + A) ^ 2 ≤ (Real.sqrt 2 * x + b * y) ^ 2 := hsumq
    _ ≤ (2 + b ^ 2) * (x ^ 2 + y ^ 2) := by simpa only [htwo] using hcauchy
    _ ≤ collectiveQ ^ 2 * (x ^ 2 + y ^ 2) := hecomp
    _ = (2 * K * collectiveQ ^ 2) * (X + Y) := by rw [hxq, hyq]; ring
    _ ≤ (2 * K * collectiveQ ^ 2) * τ ^ 2 := hacomp
    _ = 2 * K * (collectiveQ * τ) ^ 2 := by ring

/-- Missing analytic output for the complete-radial route. Existence is NOT
proved. The topology, area/Parseval/coarea identities, strict regular level,
common-angle selection, and geometric cyclic arcs remain supplier duties. -/
structure CollectiveBudgetData {n : ℕ} (p : ℂ[X]) (z : Fin n → ℂ) (μ : ℝ) where
  k : ℕ
  two_le : 2 ≤ k
  label : Fin k → Fin n
  label_injective : Function.Injective label
  boundary : Fin k → ℂ
  next : Equiv.Perm (Fin k)
  next_ne : ∀ i, next i ≠ i
  level : ℝ
  level_gt : μ < level
  level_lt : level < 2 * μ
  length : Fin k → ℝ
  arc : Fin k → ℝ
  length_nonneg : ∀ i, 0 ≤ length i
  arc_nonneg : ∀ i, 0 ≤ arc i
  lift_curve : ∀ i, ConnectedAtMost p.eval level (length i)
    (z (label i)) (boundary i)
  boundary_curve : ∀ i, ConnectedAtMost p.eval level (arc i)
    (boundary i) (boundary (next i))
  X : ℝ
  Y : ℝ
  X_nonneg : 0 ≤ X
  Y_nonneg : 0 ≤ Y
  area_budget : X + Y ≤ ((2 * μ) ^ ((1 : ℝ) / (n : ℝ))) ^ 2
  lowMean : ℝ
  highMean : ℝ
  lowMean_nonneg : 0 ≤ lowMean
  highMean_nonneg : 0 ≤ highMean
  lowMean_energy : lowMean ^ 2 ≤ (k : ℝ) * X
  highMean_energy : highMean ^ 2 ≤ ((k : ℝ) / 2) * Real.log 2 * Y
  combined_selection : (∑ i, length i) ≤ lowMean + highMean
  boundary_energy : (∑ i, arc i) ^ 2 ≤
    (2 * Real.pi ^ 2 * (k : ℝ) / Real.log 2) * Y

theorem connector_of_collectiveBudget {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hμ : 0 ≤ μ) (D : CollectiveBudgetData p z μ) :
    ∃ i j : Fin n, i ≠ j ∧ ConnectedAtMost p.eval D.level
      (collectiveQ * (2 * μ) ^ ((1 : ℝ) / (n : ℝ))) (z i) (z j) := by
  have hbudget := collective_area_budget (by exact_mod_cast D.two_le)
    D.X_nonneg D.Y_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 2 * μ) _)
    D.lowMean_nonneg D.highMean_nonneg
    (Finset.sum_nonneg fun i _ => D.length_nonneg i)
    (Finset.sum_nonneg fun i _ => D.arc_nonneg i)
    D.area_budget D.lowMean_energy D.highMean_energy D.combined_selection D.boundary_energy
  exact adjacent_connector_of_budget D.two_le z D.label D.label_injective D.boundary
    D.next D.next_ne D.length D.arc D.length_nonneg D.arc_nonneg
    D.lift_curve D.boundary_curve hbudget

/-- The supplied collective data yield the stronger closed 5.73 coefficient. -/
theorem collective_connector_573 {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hn : 4 ≤ n) (hμ : 0 ≤ μ) (D : CollectiveBudgetData p z μ) :
    ∃ i j : Fin n, i ≠ j ∧ ConnectedAtMost p.eval (2 * μ)
      ((573 / 100 : ℝ) * μ ^ ((1 : ℝ) / (n : ℝ))) (z i) (z j) := by
  obtain ⟨i, j, hij, H⟩ := connector_of_collectiveBudget hμ D
  have hscale := mul_le_mul_of_nonneg_left (collective_top_scale hn hμ)
    collectiveQ_positive.le
  have hc := mul_le_mul_of_nonneg_right collective_closed_constant.le
    (Real.rpow_nonneg hμ ((1 : ℝ) / (n : ℝ)))
  refine ⟨i, j, hij, connectedAtMost_mono H D.level_lt.le ?_⟩
  nlinarith

theorem conclusion_of_collectiveBudget {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hn : 4 ≤ n) (hm : CriticalMinimum p μ) (hz : Function.Injective z)
    (D : CollectiveBudgetData p z μ) : Conclusion n p z μ := by
  have hμ := criticalMinimum_nonneg hm
  constructor
  · obtain ⟨i, j, hij, H⟩ := collective_connector_573 hn hμ D
    refine ⟨i, j, hij, connectedAtMost_mono H le_rfl ?_, fun _ => hz.ne hij⟩
    exact mul_le_mul_of_nonneg_right (by norm_num : (573 / 100 : ℝ) ≤ 71 / 10)
      (Real.rpow_nonneg hμ _)
  · intro hdisc hhalf
    obtain ⟨i, j, hij, H⟩ := connector_of_collectiveBudget hμ D
    have hs := mul_le_mul_of_nonneg_left (small_scale_le_one (n := n) hμ hhalf).2
      collectiveQ_positive.le
    have hl : collectiveQ * (2 * μ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 57 / 10 := by
      linarith [collectiveQ_lt_open]
    exact ⟨i, j, hij, closed_to_open_mono H (D.level_lt.trans_le (by linarith)) hl⟩

/-- Alternative conditional reduction. Its analytic `supply` premise remains
uninstantiated; permitted-axiom auditing alone does not erase that premise. -/
theorem constantFactorPath_of_collectiveBudgets
    (supply : ∀ (n : ℕ) (p : ℂ[X]) (z : Fin n → ℂ) (μ : ℝ),
      4 ≤ n → p.Monic → p.natDegree = n → RootEnumeration p z →
      CriticalMinimum p μ → Function.Injective z → Nonempty (CollectiveBudgetData p z μ)) :
    PaperAnalyticTargets.ConstantFactorPath := by
  classical
  intro n p z μ hn hmonic hdegree hp hm
  change Conclusion n p z μ
  by_cases hz : Function.Injective z
  · by_cases h2 : n = 2
    · rcases h2 with rfl
      exact quadratic_complete (p := p) (z := z) (μ := μ) hp hm
    · by_cases h3 : n = 3
      · rcases h3 with rfl
        exact cubic_complete (p := p) (z := z) (μ := μ) hp hm
      · obtain ⟨D⟩ := supply n p z μ (by omega) hmonic hdegree hp hm hz
        exact conclusion_of_collectiveBudget (by omega) hm hz D
  · have hd : ∃ i j : Fin n, i ≠ j ∧ z i = z j := by
      by_contra h
      apply hz
      intro i j he
      by_contra hij
      exact h ⟨i, j, hij, he⟩
    obtain ⟨i, j, hij, he⟩ := hd
    exact repeated_occurrences_complete hp hm hij he

end ErdosProblems.Erdos1041.ConnectorR18
