import ErdosProblems.Erdos243.PaperCompleteR11.CubicZeroDensityShape

/-!
# Density quantifiers, without a uniform-constant substitution

Authored candidate, UNRUN. Prefixes are `Finset.range X`. In particular this
file does not identify zero lower density with convergence of all proportions.
-/

namespace Erdos243V5

open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11

/-- A positive, possibly orbit-dependent, lower density bound. -/
def PositiveLowerDensity (E : Set ℕ) : Prop :=
  ∃ d : ℝ, 0 < d ∧ LowerDensityAtLeast E d

/-- The exact classical contradiction principle used in the cubic proof. -/
theorem positiveLowerDensity_iff_not_zero (E : Set ℕ) :
    PositiveLowerDensity E ↔ ¬ ZeroLowerDensity E := by
  classical
  constructor
  · rintro ⟨d, hd, hb⟩ hz
    exact hz.not_positive_lower_bound d hd hb
  · intro hn
    by_contra hp
    apply hn
    apply (zeroLowerDensity_iff_no_positive_lower_bound E).mpr
    intro d hd hb
    exact hp ⟨d, hd, hb⟩

/-- A finite disagreement of predicates does not change zero lower density. -/
theorem zeroLowerDensity_iff_of_eventual_iff (E F : Set ℕ) (T : ℕ)
    (heq : ∀ n, T ≤ n → (n ∈ E ↔ n ∈ F)) :
    ZeroLowerDensity E ↔ ZeroLowerDensity F := by
  rw [zeroLowerDensity_iff_no_positive_lower_bound,
    zeroLowerDensity_iff_no_positive_lower_bound]
  constructor
  · intro h d hd hF
    exact h d hd ((lowerDensityAtLeast_iff_of_eventual_iff E F T d heq).mpr hF)
  · intro h d hd hE
    exact h d hd ((lowerDensityAtLeast_iff_of_eventual_iff E F T d heq).mp hE)

/-- Positive lower density is also unchanged by a finite disagreement. -/
theorem positiveLowerDensity_iff_of_eventual_iff (E F : Set ℕ) (T : ℕ)
    (heq : ∀ n, T ≤ n → (n ∈ E ↔ n ∈ F)) :
    PositiveLowerDensity E ↔ PositiveLowerDensity F := by
  rw [positiveLowerDensity_iff_not_zero, positiveLowerDensity_iff_not_zero,
    zeroLowerDensity_iff_of_eventual_iff E F T heq]

/-- The divided, usual eventual-prefix formulation. Zero denominators are
irrelevant because the existential starting index can be at least one. -/
def RatioLowerDensityAtLeast (E : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    d - ε ≤ (exceptionCount E X : ℝ) / (X : ℝ)

theorem lowerDensityAtLeast_iff_ratio (E : Set ℕ) (d : ℝ) :
    LowerDensityAtLeast E d ↔ RatioLowerDensityAtLeast E d := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N 1, ?_⟩
    intro X hX
    have hx : (0 : ℝ) < (X : ℝ) := by
      have : 0 < X := by omega
      exact_mod_cast this
    exact (le_div_iff₀ hx).mpr (hN X (by omega))
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N 1, ?_⟩
    intro X hX
    have hx : (0 : ℝ) < (X : ℝ) := by
      have : 0 < X := by omega
      exact_mod_cast this
    exact (le_div_iff₀ hx).mp (hN X (by omega))

theorem zeroLowerDensity_empty : ZeroLowerDensity (∅ : Set ℕ) := by
  intro ε hε N
  refine ⟨max N 1, le_max_left _ _, ?_⟩
  have hX : (0 : ℝ) < (max N 1 : ℕ) := by
    have : 0 < max N 1 := by omega
    exact_mod_cast this
  simpa [exceptionCount, exceptionFinset] using mul_pos hε hX

/-- In particular, eventual equality cannot coexist with positive lower
exceptional density. -/
theorem zeroLowerDensity_of_eventually_empty (E : Set ℕ) (T : ℕ)
    (hE : ∀ n, T ≤ n → n ∉ E) : ZeroLowerDensity E := by
  apply (zeroLowerDensity_iff_of_eventual_iff E ∅ T ?_).mpr zeroLowerDensity_empty
  intro n hn
  simp only [Set.mem_empty_iff_false, iff_false]
  exact hE n hn

theorem not_eventually_empty_of_positive {E : Set ℕ}
    (h : PositiveLowerDensity E) : ¬ ∃ T, ∀ n, T ≤ n → n ∉ E := by
  rintro ⟨T, hT⟩
  exact (positiveLowerDensity_iff_not_zero E).mp h
    (zeroLowerDensity_of_eventually_empty E T hT)

end Erdos243V5
