import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Erdős #243: algebraic core of a signed Duverney specialisation

Type B r4 supplies an ordinary signed criterion: if `∑ η_n` converges and
`∑ η_n² < ∞`, with `η_n = a_{n+1}/a_n² - 1`, then a signed reciprocal sum is
rational iff the signed Sylvester recurrence holds eventually.  The
square-summable hypothesis is what makes the infinite product of `1+η_n`
converge to a positive limit; it is not claimed here.

This module kernel-checks only the algebraic slice that remains after that
analytic input has produced a constant-magnitude signed numerator
`C_n = c σ_n`: the recurrence in multiplication form, the denominator
transport `b_{n+1} = a_n b_n`, and the cleared telescoping identity.  No
logarithm series, no product limit, and no CRT.

Not imported into `ErdosProblems/Root.lean`.  Erdős #243 remains open.
-/

namespace ErdosProblems.Erdos243

/-- A sequence of signs `±1`. -/
def IsSignSeq (σ : ℕ → ℤ) : Prop := ∀ n, σ n = 1 ∨ σ n = -1

lemma IsSignSeq.sq {σ : ℕ → ℤ} (h : IsSignSeq σ) (n : ℕ) :
    σ n * σ n = 1 := by
  rcases h n with hn | hn <;> simp [hn]

lemma IsSignSeq.ne_zero {σ : ℕ → ℤ} (h : IsSignSeq σ) (n : ℕ) :
    σ n ≠ 0 := by
  rcases h n with hn | hn <;> simp [hn]

/-- Signed Sylvester recurrence, written without division by using `σ² = 1`.
Equivalent to `a_{n+1} = a_n² - (σ_{n+1}/σ_n) a_n + σ_{n+2}/σ_{n+1}`. -/
def signedSylvesterRec (a σ : ℕ → ℤ) (n : ℕ) : Prop :=
  a (n + 1)
    = a n * a n - σ n * σ (n + 1) * a n + σ (n + 1) * σ (n + 2)

/-- Auxiliary denominator `b_n = a_n - σ_n σ_{n+1}`. -/
def signedDenom (a σ : ℕ → ℤ) (n : ℕ) : ℤ :=
  a n - σ n * σ (n + 1)

/-- The recurrence is equivalent to `b_{n+1} = a_n b_n`. -/
theorem signedDenom_succ_iff_rec {a σ : ℕ → ℤ} (n : ℕ) :
    signedDenom a σ (n + 1) = a n * signedDenom a σ n
      ↔ signedSylvesterRec a σ n := by
  unfold signedDenom signedSylvesterRec
  constructor <;> intro h <;> linarith

/-- From the signed state recurrences and constant magnitude `C_n = c σ_n`,
the denominator is `D_n = c b_n`. -/
theorem signed_error_denom
    {a σ C D : ℕ → ℤ} {c : ℤ}
    (hσ : IsSignSeq σ)
    (hC : ∀ n, C n = c * σ n)
    (hCup : ∀ n, C (n + 1) = a n * C n - σ n * D n)
    (n : ℕ) :
    D n = c * signedDenom a σ n := by
  have hsq := hσ.sq n
  have hD : D n = σ n * (a n * C n - C (n + 1)) := by
    have hup := hCup n
    have : a n * C n - C (n + 1) = σ n * D n := by linarith
    calc
      D n = 1 * D n := by ring
      _ = (σ n * σ n) * D n := by rw [hsq]
      _ = σ n * (σ n * D n) := by ring
      _ = σ n * (a n * C n - C (n + 1)) := by rw [this]
  rw [hD, hC n, hC (n + 1)]
  unfold signedDenom
  calc
    σ n * (a n * (c * σ n) - c * σ (n + 1))
        = c * (σ n * σ n) * a n - c * σ n * σ (n + 1) := by ring
    _ = c * 1 * a n - c * σ n * σ (n + 1) := by rw [hsq]
    _ = c * (a n - σ n * σ (n + 1)) := by ring

/-- Constant-magnitude signed exact states satisfy the signed recurrence. -/
theorem signed_state_forces_rec
    {a σ C D : ℕ → ℤ} {c : ℤ}
    (hσ : IsSignSeq σ)
    (hC : ∀ n, C n = c * σ n)
    (hCup : ∀ n, C (n + 1) = a n * C n - σ n * D n)
    (hDup : ∀ n, D (n + 1) = a n * D n)
    (hc : c ≠ 0)
    (n : ℕ) :
    signedSylvesterRec a σ n := by
  have hDn := signed_error_denom hσ hC hCup n
  have hDn1 := signed_error_denom hσ hC hCup (n + 1)
  have hb : signedDenom a σ (n + 1) = a n * signedDenom a σ n := by
    have h := hDup n
    rw [hDn1, hDn] at h
    have hmul : c * signedDenom a σ (n + 1)
        = c * (a n * signedDenom a σ n) := by
      convert h using 1
      ring
    exact mul_left_cancel₀ hc hmul
  exact (signedDenom_succ_iff_rec n).mp hb

/-- Cleared telescoping identity: `σ_n/b_n - σ_{n+1}/b_{n+1} = σ_n/a_n`
after multiplying through by `a_n b_n b_{n+1}`. -/
theorem signed_telescoping_cleared
    {a σ : ℕ → ℤ} {n : ℕ}
    (hσ : IsSignSeq σ)
    (hsucc : signedDenom a σ (n + 1) = a n * signedDenom a σ n) :
    σ n * a n * signedDenom a σ (n + 1)
      - σ (n + 1) * a n * signedDenom a σ n
      = σ n * signedDenom a σ n * signedDenom a σ (n + 1) := by
  have hsq := hσ.sq n
  have hb : a n = signedDenom a σ n + σ n * σ (n + 1) := by
    unfold signedDenom; ring
  calc
    σ n * a n * signedDenom a σ (n + 1)
        - σ (n + 1) * a n * signedDenom a σ n
        = σ n * a n * (a n * signedDenom a σ n)
            - σ (n + 1) * a n * signedDenom a σ n := by rw [hsucc]
    _ = a n * signedDenom a σ n * (σ n * a n - σ (n + 1)) := by ring
    _ = a n * signedDenom a σ n
          * (σ n * (signedDenom a σ n + σ n * σ (n + 1)) - σ (n + 1)) := by
            rw [hb]
    _ = a n * signedDenom a σ n
          * (σ n * signedDenom a σ n + (σ n * σ n) * σ (n + 1)
              - σ (n + 1)) := by ring
    _ = a n * signedDenom a σ n
          * (σ n * signedDenom a σ n + 1 * σ (n + 1) - σ (n + 1)) := by
            rw [hsq]
    _ = a n * signedDenom a σ n * (σ n * signedDenom a σ n) := by ring
    _ = σ n * signedDenom a σ n * (a n * signedDenom a σ n) := by ring
    _ = σ n * signedDenom a σ n * signedDenom a σ (n + 1) := by rw [hsucc]

#print axioms signedDenom_succ_iff_rec
#print axioms signed_error_denom
#print axioms signed_state_forces_rec
#print axioms signed_telescoping_cleared

end ErdosProblems.Erdos243
