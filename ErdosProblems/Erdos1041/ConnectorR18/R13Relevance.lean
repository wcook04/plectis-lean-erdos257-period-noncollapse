import ErdosProblems.Erdos1041.ConnectorR18.PolynomialBranches
import ErdosProblems.Erdos1041.ConnectorR18.NumericalBounds
import ErdosProblems.Erdos1041.SeparationCounterexampleR13

/-!
# R13 tests the hypothesis, not the conclusion of the value-separated theorem

AUTHORED / UNRUN. Exact arithmetic shows that the R13 quartic has a SIMPLE
MINIMIZING critical point at 1, but fails normalized critical-VALUE separation
for every S>1. Its critical-POINT separation is a different assertion.
The quoted point separation and exhaustive root enumeration remain available
in the imported, byte-preserved R13 source; no sign sampling substitutes for it.
-/
noncomputable section
namespace ErdosProblems.Erdos1041.ConnectorR18
open Polynomial Set PaperAnalyticTargets

/-- Branch-centred normalized critical-value separation. Unlike critical-point
separation, this predicate is on the images p(d)/p(c). -/
def ValueSeparatedAt (p : ℂ[X]) (c : ℂ) (S : ℝ) : Prop :=
  ∀ d : ℂ, p.derivative.eval d = 0 → d ≠ c → S ≤ ‖1 - p.eval d / p.eval c‖

theorem ValueSeparatedAt.mono {p : ℂ[X]} {c : ℂ} {S T : ℝ}
    (H : ValueSeparatedAt p c S) (hTS : T ≤ S) : ValueSeparatedAt p c T := by
  intro d hd hdc
  exact hTS.trans (H d hd hdc)

theorem r13_eval_minus_one : SeparationCounterexampleR13.p.eval (-1) = (-65537 / 131072 : ℂ) := by
  norm_num [SeparationCounterexampleR13.p]

theorem r13_eval_one : SeparationCounterexampleR13.p.eval 1 = (-65535 / 131072 : ℂ) := by
  norm_num [SeparationCounterexampleR13.p]

theorem r13_norm_minus_one : ‖SeparationCounterexampleR13.p.eval (-1)‖ = (65537 / 131072 : ℝ) := by
  rw [r13_eval_minus_one]
  norm_num [norm_div]

theorem r13_norm_one : ‖SeparationCounterexampleR13.p.eval 1‖ = (65535 / 131072 : ℝ) := by
  rw [r13_eval_one]
  norm_num [norm_div]

theorem r13_normalized_gap_at_minus_one :
    ‖1 - SeparationCounterexampleR13.p.eval 1 / SeparationCounterexampleR13.p.eval (-1)‖ = (2 / 65537 : ℝ) := by
  rw [r13_eval_one, r13_eval_minus_one]
  norm_num [norm_div]

theorem r13_normalized_gap_at_one :
    ‖1 - SeparationCounterexampleR13.p.eval (-1) / SeparationCounterexampleR13.p.eval 1‖ = (2 / 65535 : ℝ) := by
  rw [r13_eval_one, r13_eval_minus_one]
  norm_num [norm_div]

theorem r13_critical_one : SeparationCounterexampleR13.p.derivative.eval 1 = 0 :=
  (SeparationCounterexampleR13.derivative_root_iff 1).mpr (Or.inr (Or.inr rfl))

theorem r13_critical_minus_one : SeparationCounterexampleR13.p.derivative.eval (-1) = 0 :=
  (SeparationCounterexampleR13.derivative_root_iff (-1)).mpr (Or.inl rfl)

theorem r13_simple_critical_one : SeparationCounterexampleR13.p.derivative.derivative.eval 1 ≠ 0 := by
  norm_num [SeparationCounterexampleR13.p, Polynomial.derivative_mul, Polynomial.derivative_pow]

theorem r13_simple_critical_minus_one : SeparationCounterexampleR13.p.derivative.derivative.eval (-1) ≠ 0 := by
  norm_num [SeparationCounterexampleR13.p, Polynomial.derivative_mul, Polynomial.derivative_pow]

theorem r13_middle_value_gt_half :
    (1 / 2 : ℝ) < ‖SeparationCounterexampleR13.p.eval (SeparationCounterexampleR13.t : ℂ)‖ := by
  rw [SeparationCounterexampleR13.eval_real, Complex.norm_real, Real.norm_eq_abs]
  norm_num [SeparationCounterexampleR13.f, SeparationCounterexampleR13.t]

/-- R13's failure of value separation occurs at the actual minimum, not merely
at an irrelevant critical point. The complete derivative-root classification
is used to compare ALL critical values. -/
theorem r13_criticalMinimum : CriticalMinimum SeparationCounterexampleR13.p (65535 / 131072 : ℝ) := by
  constructor
  · exact ⟨1, r13_critical_one, r13_norm_one.symm⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := hx
    rcases (SeparationCounterexampleR13.derivative_root_iff c).mp hc with h | h | h
    · rw [h, r13_norm_minus_one]
      norm_num
    · rw [h]
      linarith [r13_middle_value_gt_half]
    · rw [h, r13_norm_one]

/-- The normalized gap is <1 at either of the two separated saddles. -/
theorem r13_not_valueSeparated_minus_one {S : ℝ} (hS : 1 < S) :
    ¬ ValueSeparatedAt SeparationCounterexampleR13.p (-1) S := by
  intro H
  have hh := H 1 r13_critical_one (by norm_num)
  rw [r13_normalized_gap_at_minus_one] at hh
  nlinarith

theorem r13_not_valueSeparated_one {S : ℝ} (hS : 1 < S) :
    ¬ ValueSeparatedAt SeparationCounterexampleR13.p 1 S := by
  intro H
  have hh := H (-1) r13_critical_minus_one (by norm_num)
  rw [r13_normalized_gap_at_one] at hh
  nlinarith

theorem r13_minimum_fails_four_thirds :
    CriticalMinimum SeparationCounterexampleR13.p (65535 / 131072 : ℝ) ∧
    SeparationCounterexampleR13.p.derivative.eval 1 = 0 ∧ SeparationCounterexampleR13.p.derivative.derivative.eval 1 ≠ 0 ∧
    ¬ ValueSeparatedAt SeparationCounterexampleR13.p 1 (4 / 3) := by
  exact ⟨r13_criticalMinimum, r13_critical_one, r13_simple_critical_one,
    r13_not_valueSeparated_one (by norm_num)⟩

/-- An ACTUAL curve with the old separated-branch logarithmic length estimate
at S=4/3 meets the 71/10 budget in the same sublevel. The analytic existence of
such a curve is deliberately not inferred from ValueSeparatedAt in this file. -/
theorem separated_length_certificate_to_71_10 {n : ℕ} {f : ℂ → ℂ}
    {μ R : ℝ} {a b : ℂ} (hn : 3 ≤ n) (hμ : 0 ≤ μ)
    (H : ConnectedAtMost f R
      ((2 * (1 + (4 / 3 : ℝ)) ^ ((1 : ℝ) / (n : ℝ)) *
        Real.sqrt (Real.log ((4 / 3 : ℝ) / (4 / 3 - 1)))) *
        μ ^ ((1 : ℝ) / (n : ℝ))) a b) :
    ConnectedAtMost f R ((71 / 10 : ℝ) * μ ^ ((1 : ℝ) / (n : ℝ))) a b := by
  apply connectedAtMost_mono H le_rfl
  have hcoef : 2 * (1 + (4 / 3 : ℝ)) ^ ((1 : ℝ) / (n : ℝ)) *
      Real.sqrt (Real.log ((4 / 3 : ℝ) / (4 / 3 - 1))) ≤ (71 / 10 : ℝ) := by
    linarith [separatedCoefficient_four_thirds hn]
  exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hμ _)

end ErdosProblems.Erdos1041.ConnectorR18
