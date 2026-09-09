import ErdosProblems.Erdos1041.PaperCurveAssembly
import Mathlib

/-!
# Explicit, UNPROVED targets for the remaining analytic assemblies

These are proposition DEFINITIONS, not theorems, axioms, or admitted proofs.
Nothing in another returned module consumes one as an established fact.
They make several major remaining paper obligations precise for the next
compilation/proof pass. Creating these definitions earns no theorem coverage.

All curve predicates below use actual extended variation. Root and derivative
enumerations are polynomial identities and therefore retain multiplicities.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperAnalyticTargets

open Polynomial Set PaperCurve
open scoped ComplexConjugate BigOperators

/-- A closed sublevel connector, allowing the zero-length repeated-root case. -/
def ConnectedAtMost (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ ≤ R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L

def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R

def RootsInOpenUnitDisc (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1

def RootEnumeration {n : ℕ} (p : ℂ[X]) (z : Fin n → ℂ) : Prop :=
  p = ∏ i, (X - C (z i))

def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))

def CriticalMinimum (p : ℂ[X]) (μ : ℝ) : Prop :=
  IsLeast {x : ℝ | ∃ c : ℂ, p.derivative.eval c = 0 ∧ x = ‖p.eval c‖} μ

def HasDistinctConnection (p : ℂ[X]) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ p.eval a = 0 ∧ p.eval b = 0 ∧ ConnectedBelow p.eval R L a b

/-- Target shared by both `res:low-critical-thirteen-twentyfifths` rows. -/
def LowCriticalThirteenTwentyFifths : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ → μ ≤ 13 / 25 → HasDistinctConnection p 1 2

/-- Main bound in both scale-free corollaries. -/
def ScaledLowCritical : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      (2 * (((25 / 13 : ℝ) * μ) ^ (1 / (p.natDegree : ℝ))))

/-- The additional `5/2` bound in the short-note scaling corollary. -/
def ScaledLowCriticalFiveHalves : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      ((5 / 2 : ℝ) * (μ ^ (1 / (p.natDegree : ℝ))))

/-- The two numerical conclusions are separate parts of the displayed
constant-factor result; the second one retains open containment. -/
def ConstantFactorPath : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (z : Fin n → ℂ) (μ : ℝ), 2 ≤ n → p.Monic →
    p.natDegree = n → RootEnumeration p z → CriticalMinimum p μ →
    (∃ i j : Fin n, i ≠ j ∧
      ConnectedAtMost p.eval (2 * μ) ((71 / 10 : ℝ) * μ ^ (1 / (n : ℝ))) (z i) (z j) ∧
      (Squarefree p → z i ≠ z j)) ∧
    (RootsInOpenUnitDisc p → μ ≤ 1 / 2 →
      ∃ i j : Fin n, i ≠ j ∧
        ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
          (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
          BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
          eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal (57 / 10))

def weightedProduct {m : ℕ} (c : Fin m → ℂ) (w : Fin m → ℝ) (z : ℂ) : ℝ :=
  ∏ k, ‖1 - conj (c k) * z‖ ^ w k

/-- Includes the displayed equality classification; proving the inequality
alone is not counted as proving this target. -/
def WeightedFreePoint : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (w : Fin m → ℝ),
    (∀ j, ‖c j‖ ≤ 1) → (∀ j, 0 < w j) → (∑ j, w j) = 1 →
      (∑ j, w j * weightedProduct c w (c j) ^ 2) ≤ 1 ∧
      ((∑ j, w j * weightedProduct c w (c j) ^ 2) = 1 ↔ ∀ j, c j = 0)

/-- Reflected-derivative bound, with the derivative root multiplicities
specified by an exact polynomial factorisation. -/
def ReflectedCriticalValue : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ), 2 ≤ n → p.Monic →
    p.natDegree = n → RootsInClosedDisc p 0 1 → CriticalEnumeration p c →
      ∀ j, ‖p.eval (c j)‖ ≤ ∏ k, ‖1 - conj (c k) * c j‖

/-- Both conclusions of the current all-degree critical-value-mean theorem.
The zero-radius case is included, not silently discarded by division by R. -/
def CriticalValueMean : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ) (h : ℂ) (R : ℝ),
    2 ≤ n → p.Monic → p.natDegree = n → 0 ≤ R →
    RootsInClosedDisc p h R → CriticalEnumeration p c →
      (∑ j, ‖p.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
        ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
      (∑ j, ‖p.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R

/-- An analytic root-count supplier used by the ordinary cubic hub proof.
It is not supplied by the existing algebraic cubic-spoke kernel. -/
def CubicRootCount : Prop :=
  ∀ b : ℂ, 1 ≤ ‖1 - b ^ 3 / 2‖ →
    ∃ u v : ℂ, u ≠ v ∧ ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧
      u ^ 3 - (3 / 2 : ℂ) * b * u ^ 2 + 1 = 0 ∧
      v ^ 3 - (3 / 2 : ℂ) * b * v ^ 2 + 1 = 0

/-- The selector obligation is kept separate from the returned path consumer. -/
def PrimitiveQuinticSelector : Prop :=
  ∀ (p : ℂ[X]) (a b c : ℂ) (w : Fin 5 → ℂ),
    (∀ z : ℂ, p.eval z = z ^ 5 + a * z ^ 4 + b * z + c) →
    RootEnumeration p w → (∀ i, ‖w i‖ < 1) →
      ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1

end ErdosProblems.Erdos1041.PaperAnalyticTargets
