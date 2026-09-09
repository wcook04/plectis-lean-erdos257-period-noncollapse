import Mathlib

/-!
# Auditable rational envelopes at the end of the connector proof

AUTHORED / UNRUN. These are algebraic envelope lemmas. The square-root,
logarithmic and geometric upper bounds must be separately justified; no
numerical identity in this file constructs a connector.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.ReturnV5

def lowEnvelope : ℝ := (60 / 289) * (283 / 200)
def highEnvelope : ℝ := (161 / 100) + (1375 / 364)

theorem closed_envelope_exact :
    lowEnvelope + (63 / 50) * highEnvelope = (66517563 / 9392500 : ℝ) := by
  norm_num [lowEnvelope, highEnvelope]

theorem closed_envelope_lt :
    lowEnvelope + (63 / 50) * highEnvelope < (71 / 10 : ℝ) := by
  norm_num [lowEnvelope, highEnvelope]

theorem open_envelope_lt : lowEnvelope + highEnvelope < (57 / 10 : ℝ) := by
  norm_num [lowEnvelope, highEnvelope]

/-- A nonnegative supplied radius bound multiplies a rational comparison. -/
theorem closed_numeric_consumer {ρ A B q : ℝ} (hρ : 0 ≤ ρ)
    (hA : A ≤ lowEnvelope) (hB0 : 0 ≤ B) (hB : B ≤ highEnvelope)
    (hq : q ≤ 63 / 50) :
    (A + q * B) * ρ ≤ (71 / 10 : ℝ) * ρ := by
  have hqB : q * B ≤ (63 / 50 : ℝ) * highEnvelope :=
    (mul_le_mul_of_nonneg_right hq hB0).trans
      (mul_le_mul_of_nonneg_left hB (by norm_num))
  apply mul_le_mul_of_nonneg_right _ hρ
  linarith [closed_envelope_lt]

/-- Open-level arithmetic uses ρ ≤ 1 and (2μ)^(1/n) ≤ 1 separately;
it does not discard the strict-containment proof obligation. -/
theorem open_numeric_consumer {ρ τ A B : ℝ} (hρ : ρ ≤ 1) (hτ : τ ≤ 1)
    (hA0 : 0 ≤ A) (hA : A ≤ lowEnvelope)
    (hB0 : 0 ≤ B) (hB : B ≤ highEnvelope) :
    A * ρ + B * τ < (57 / 10 : ℝ) := by
  have hAρ := mul_le_mul_of_nonneg_left hρ hA0
  have hBτ := mul_le_mul_of_nonneg_left hτ hB0
  linarith [open_envelope_lt]

/-- Guard against a tempting but invalid strict-threshold relabelling. -/
theorem strict_threshold_needs_slack :
    ¬ (∀ x L : ℝ, x ≤ L → x < L) := by
  intro h
  exact lt_irrefl (0 : ℝ) (h 0 0 le_rfl)

end ErdosProblems.Erdos1041.ReturnV5
