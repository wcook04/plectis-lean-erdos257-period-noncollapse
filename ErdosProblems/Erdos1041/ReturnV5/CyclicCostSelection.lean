import ErdosProblems.Erdos1041.ReturnV5.CurveInfrastructure
import ErdosProblems.Erdos1041.AttachmentAwareReeb

/-!
# Select total connector cost, not a boundary arc in isolation

AUTHORED / UNRUN. Finite cost selection and its actual-curve consumer are
separate. No geometric lift, Jordan boundary, or coarea theorem is assumed to
have been proved by the finite argument.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ReturnV5
open scoped BigOperators
open PaperAnalyticTargets

/-- A permutation counts each lift twice in the cyclic concatenation budget. -/
theorem cyclic_cost_sum {k : ℕ} (σ : Equiv.Perm (Fin k))
    (lift arc : Fin k → ℝ) :
    (∑ i, (lift i + lift (σ i) + arc i)) = 2 * (∑ i, lift i) + ∑ i, arc i := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, σ.sum_comp] <;> simp
  ring

/-- Select the whole cost of a pair of lifts and the connecting boundary arc. -/
theorem exists_cyclic_cost_le {k : ℕ} (hk : 0 < k)
    (σ : Equiv.Perm (Fin k)) (lift arc : Fin k → ℝ) (B : ℝ)
    (hbudget : 2 * (∑ i, lift i) + ∑ i, arc i ≤ (k : ℝ) * B) :
    ∃ i : Fin k, lift i + lift (σ i) + arc i ≤ B := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hsum : (∑ i, (lift i + lift (σ i) + arc i)) ≤ (k : ℝ) * B := by
    rw [cyclic_cost_sum]
    exact hbudget
  obtain ⟨i, hi, hle⟩ :=
    AttachmentAwareReeb.exists_le_of_sum_le_card_mul hne
      (fun i => lift i + lift (σ i) + arc i) B (by simpa [mul_comm] using hsum)
  exact ⟨i, hle⟩

/-- Exact average form; no positivity of the individual costs is needed. -/
theorem exists_cyclic_cost_le_average {k : ℕ} (hk : 0 < k)
    (σ : Equiv.Perm (Fin k)) (lift arc : Fin k → ℝ) :
    ∃ i : Fin k, lift i + lift (σ i) + arc i ≤
      (2 * (∑ j, lift j) + ∑ j, arc j) / (k : ℝ) := by
  apply exists_cyclic_cost_le hk σ lift arc
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have he (N : ℝ) : (k : ℝ) * (N / (k : ℝ)) = N := by
    field_simp [hkR]
  rw [he]

/-- Actual-curve consumer: the analytic/topological construction has to supply
all `Hpath` curves. This theorem is NOT a producer of those curves. -/
theorem actual_cyclic_connector_of_budget {k : ℕ} (hk : 0 < k)
    (σ : Equiv.Perm (Fin k)) (hσ : ∀ i, i ≠ σ i)
    (z : Fin k → ℂ) (f : ℂ → ℂ) (R B : ℝ) (lift arc : Fin k → ℝ)
    (Hpath : ∀ i, ConnectedAtMost f R (lift i + lift (σ i) + arc i) (z i) (z (σ i)))
    (hbudget : 2 * (∑ i, lift i) + ∑ i, arc i ≤ (k : ℝ) * B) :
    ∃ i j, i ≠ j ∧ ConnectedAtMost f R B (z i) (z j) := by
  obtain ⟨i, hi⟩ := exists_cyclic_cost_le hk σ lift arc B hbudget
  exact ⟨i, σ i, hσ i, connectedAtMost_mono le_rfl hi (Hpath i)⟩

/-- Minimal arc length alone need not select a minimal connector cost. The
three cyclic edges have costs 100, 1, 101, but arc zero is shortest. -/
theorem shortest_arc_not_shortest_total :
    let lift : Fin 3 → ℝ := ![100, 0, 0]
    let arc : Fin 3 → ℝ := ![0, 1, 1]
    (∀ i : Fin 3, arc 0 ≤ arc i) ∧
      lift 0 + lift 1 + arc 0 > lift 1 + lift 2 + arc 1 := by
  dsimp
  constructor
  · intro i
    fin_cases i <;> norm_num
  · norm_num

/-- The numerator bound can be assembled before any division by root count. -/
theorem cyclic_budget_of_separate_bounds {k : ℕ} (lift arc : Fin k → ℝ)
    {A P B : ℝ} (hlift : (∑ i, lift i) ≤ A) (harc : (∑ i, arc i) ≤ P)
    (hnum : 2 * A + P ≤ (k : ℝ) * B) :
    2 * (∑ i, lift i) + ∑ i, arc i ≤ (k : ℝ) * B := by
  linarith

end ErdosProblems.Erdos1041.ReturnV5
