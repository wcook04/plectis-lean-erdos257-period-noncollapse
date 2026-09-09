import ErdosProblems.Erdos1041.ConnectorR18.CubicBranch
import ErdosProblems.Erdos1041.ConnectorR18.FiniteAssembly

/-!
# Explicit remaining analytic interface and its proved consumer

AUTHORED / UNRUN. WARNING: existence of `RayBudgetData` is NOT proved here.
The final theorem is CONDITIONAL, with the supplier visibly quantified as a
hypothesis. It must never be cited as an unconditional ConstantFactorPath proof.

What this removes from the open interface: repeated occurrences, degrees two
and three, finite energy aggregation, the adjacent-candidate average, actual
curve concatenation, squarefree endpoint distinction, numerical constants,
and the strict-level transport needed when 2μ = 1.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.ConnectorR18
open Polynomial Set PaperAnalyticTargets
open scoped BigOperators

/-- Exact output required from the ordinary CF analytic construction at
λ=2 and r=3/20. None of its existence claims is silently postulated as an axiom.
`level_lt` is strict: weakening it to ≤ does NOT prove the open-unit result. -/
structure RayBudgetData {n : ℕ} (p : ℂ[X]) (z : Fin n → ℂ) (μ : ℝ) where
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
  low : Fin k → ℝ
  high : Fin k → ℝ
  arc : Fin k → ℝ
  low_nonneg : ∀ i, 0 ≤ low i
  high_nonneg : ∀ i, 0 ≤ high i
  arc_nonneg : ∀ i, 0 ≤ arc i
  lift_curve : ∀ i, ConnectedAtMost p.eval level (low i + high i)
    (z (label i)) (boundary i)
  boundary_curve : ∀ i, ConnectedAtMost p.eval level (arc i)
    (boundary i) (boundary (next i))
  low_energy : (∑ i, low i ^ 2) ≤
    (60 / 289 : ℝ) ^ 2 * (μ ^ ((1 : ℝ) / (n : ℝ))) ^ 2
  high_energy : (∑ i, high i) ^ 2 ≤
    ((k : ℝ) / 2) * Real.log (40 / 3 : ℝ) * ((2 * μ) ^ ((1 : ℝ) / (n : ℝ))) ^ 2
  boundary_energy : (∑ i, arc i) ^ 2 ≤
    (2 * Real.pi ^ 2 * (k : ℝ) / Real.log 2) * ((2 * μ) ^ ((1 : ℝ) / (n : ℝ))) ^ 2

/-- A concrete analytic data witness yields the same pair at an interior
working level, with an explicit two-scale length budget. -/
theorem connector_of_rayBudget {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hμ : 0 ≤ μ) (D : RayBudgetData p z μ) :
    ∃ i j : Fin n, i ≠ j ∧ ConnectedAtMost p.eval D.level
      (lowConstant * μ ^ ((1 : ℝ) / (n : ℝ)) +
       highConstant * (2 * μ) ^ ((1 : ℝ) / (n : ℝ))) (z i) (z j) := by
  have hbudget := three_energy_budget D.two_le D.low D.high D.arc
    (Real.rpow_nonneg hμ ((1 : ℝ) / (n : ℝ)))
    (Real.rpow_nonneg (by positivity : 0 ≤ 2 * μ) ((1 : ℝ) / (n : ℝ)))
    D.low_nonneg D.high_nonneg D.arc_nonneg D.low_energy D.high_energy D.boundary_energy
  exact adjacent_connector_of_budget D.two_le z D.label D.label_injective D.boundary
    D.next D.next_ne (fun i => D.low i + D.high i) D.arc
    (fun i => add_nonneg (D.low_nonneg i) (D.high_nonneg i)) D.arc_nonneg
    D.lift_curve D.boundary_curve hbudget

/-- The original two-scale rational budget implies BOTH exact paper
conclusions. The open-part root-disc assumption is not used. -/
theorem conclusion_of_rayBudget {n : ℕ} {p : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hn : 3 ≤ n) (hp : RootEnumeration p z) (hm : CriticalMinimum p μ)
    (hz : Function.Injective z) (D : RayBudgetData p z μ) : Conclusion n p z μ := by
  have hμ := criticalMinimum_nonneg hm
  let ρ : ℝ := μ ^ ((1 : ℝ) / (n : ℝ))
  let τ : ℝ := (2 * μ) ^ ((1 : ℝ) / (n : ℝ))
  have hρ : 0 ≤ ρ := Real.rpow_nonneg hμ _
  have htop : τ ≤ (63 / 50 : ℝ) * ρ := top_scale_le hn hμ
  obtain ⟨i, j, hij, H⟩ := connector_of_rayBudget hμ D
  have hclosed : lowConstant * ρ + highConstant * τ ≤ (71 / 10 : ℝ) * ρ := by
    have hstep := mul_le_mul_of_nonneg_left htop highConstant_nonneg
    have heq : lowConstant * ρ + highConstant * ((63 / 50 : ℝ) * ρ) =
        rationalConstant * ρ := by
      rw [← rationalConstant_identity]
      ring
    calc
      lowConstant * ρ + highConstant * τ ≤
          lowConstant * ρ + highConstant * ((63 / 50 : ℝ) * ρ) :=
        add_le_add (le_refl _) hstep
      _ = rationalConstant * ρ := heq
      _ ≤ (71 / 10 : ℝ) * ρ := mul_le_mul_of_nonneg_right rationalConstant_lt.le hρ
  constructor
  · exact ⟨i, j, hij, connectedAtMost_mono H D.level_lt.le hclosed,
      fun _ => hz.ne hij⟩
  · intro hdisc hhalf
    have hscales := small_scale_le_one (n := n) hμ hhalf
    have hlow := mul_le_mul_of_nonneg_left hscales.1 lowConstant_nonneg
    have hhigh := mul_le_mul_of_nonneg_left hscales.2 highConstant_nonneg
    have hlength : lowConstant * ρ + highConstant * τ ≤ (57 / 10 : ℝ) := by
      dsimp [ρ, τ]
      linarith [openConstant_lt]
    have hlevel : D.level < 1 := D.level_lt.trans_le (by linarith)
    exact ⟨i, j, hij, closed_to_open_mono H hlevel hlength⟩

/-- The remaining all-degree theorem has been reduced to the genuine analytic
construction only in degrees ≥4. THIS IS A CONDITIONAL REDUCTION, NOT A PROOF
THAT ITS `supply` HYPOTHESIS HOLDS. No declaration in this return instantiates
`supply` for general polynomials. -/
theorem constantFactorPath_of_rayBudgets
    (supply : ∀ (n : ℕ) (p : ℂ[X]) (z : Fin n → ℂ) (μ : ℝ),
      4 ≤ n → p.Monic → p.natDegree = n → RootEnumeration p z →
      CriticalMinimum p μ → Function.Injective z → Nonempty (RayBudgetData p z μ)) :
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
        exact conclusion_of_rayBudget (by omega) hp hm hz D
  · have hd : ∃ i j : Fin n, i ≠ j ∧ z i = z j := by
      by_contra h
      apply hz
      intro i j he
      by_contra hij
      exact h ⟨i, j, hij, he⟩
    obtain ⟨i, j, hij, he⟩ := hd
    exact repeated_occurrences_complete hp hm hij he

end ErdosProblems.Erdos1041.ConnectorR18
