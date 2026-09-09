import ErdosProblems.Erdos1041.SeparationCounterexampleR13

/-!
# The R13 quartic is not a counterexample to the value-plane theorem

AUTHORED / UNRUN. R13 refutes a proposed inference from separation in the
z-plane to separation of critical values. Here the normalized value gaps at
both critical points -1 and 1 are calculated exactly. They are less than one,
so neither hub satisfies the paper's S > 1 value-plane hypothesis.
-/

namespace ErdosProblems.Erdos1041.ReturnV5
open SeparationCounterexampleR13

/-- Exact normalized gap with the -1 critical point as base. -/
theorem quartic_normalized_gap_minus_one :
    ‖(1 : ℂ) - p.eval 1 / p.eval (-1)‖ = (2 / 65537 : ℝ) := by
  have he : (1 : ℂ) - p.eval 1 / p.eval (-1) = (2 / 65537 : ℂ) := by
    norm_num [p]
  rw [he]
  norm_num [norm_div]

/-- Exact normalized gap with the +1 critical point as base. -/
theorem quartic_normalized_gap_plus_one :
    ‖(1 : ℂ) - p.eval (-1) / p.eval 1‖ = (2 / 65535 : ℝ) := by
  have he : (1 : ℂ) - p.eval (-1) / p.eval 1 = (-2 / 65535 : ℂ) := by
    norm_num [p]
  rw [he]
  norm_num [norm_div]

/-- The necessary premise fails at -1 for EVERY S > 1. -/
theorem quartic_fails_value_separation_minus_one {S : ℝ} (hS : 1 < S) :
    ¬ (∀ d : ℂ, p.derivative.eval d = 0 → d ≠ -1 →
      S ≤ ‖(1 : ℂ) - p.eval d / p.eval (-1)‖) := by
  intro h
  have hg := h 1 ((derivative_root_iff 1).2 (Or.inr (Or.inr rfl))) (by norm_num)
  rw [quartic_normalized_gap_minus_one] at hg
  norm_num at hg
  linarith

/-- The necessary premise likewise fails at +1 for EVERY S > 1. -/
theorem quartic_fails_value_separation_plus_one {S : ℝ} (hS : 1 < S) :
    ¬ (∀ d : ℂ, p.derivative.eval d = 0 → d ≠ 1 →
      S ≤ ‖(1 : ℂ) - p.eval d / p.eval 1‖) := by
  intro h
  have hg := h (-1) ((derivative_root_iff (-1)).2 (Or.inl rfl)) (by norm_num)
  rw [quartic_normalized_gap_plus_one] at hg
  norm_num at hg
  linarith

end ErdosProblems.Erdos1041.ReturnV5
