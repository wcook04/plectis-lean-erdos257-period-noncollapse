import ErdosProblems.Erdos269.PaperR9WidthData

/-! A Boolean range checker with a propositional soundness theorem.
The range is [lo, lo + len).  The evaluator uses only an explicitly supplied
Bool; it never asks typeclass synthesis to decide an opaque universal predicate.
No finite arithmetic is trusted merely because it occurs in a data file.
All new Lean checks: UNRUN. -/
namespace ErdosProblems.Erdos269.PaperR11
open PaperR9

/-- The zero-length case is deliberate and is proved below. -/
def checkRange (f : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, n + 1 => f lo && checkRange f (lo + 1) n

theorem checkRange_iff (f : ℕ → Bool) (lo n : ℕ) :
    checkRange f lo n = true ↔ ∀ i, i < n → f (lo + i) = true := by
  induction n generalizing lo with
  | zero => simp [checkRange]
  | succ n ih =>
    rw [checkRange, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hs⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs i (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), ?_⟩
      intro i hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i + 1) (by omega)

theorem checkRange_sound {f : ℕ → Bool} {lo n : ℕ}
    (h : checkRange f lo n = true) (i : ℕ) (hi : i < n) :
    f (lo + i) = true := (checkRange_iff f lo n).mp h i hi

theorem checkRange_decide_sound (P : ℕ → Prop) [DecidablePred P] {lo n : ℕ}
    (h : checkRange (fun i => decide (P i)) lo n = true) (i : ℕ) (hi : i < n) :
    P (lo + i) := by
  exact of_decide_eq_true (checkRange_sound h i hi)

/-- Propositional interval composition: no reduction of the checked arithmetic
is repeated when larger certificates are assembled. -/
theorem range_append {P : ℕ → Prop} {lo n m : ℕ}
    (h₁ : ∀ i, i < n → P (lo + i))
    (h₂ : ∀ i, i < m → P ((lo + n) + i)) :
    ∀ i, i < n + m → P (lo + i) := by
  intro i hi
  by_cases h : i < n
  · exact h₁ i h
  · have ht := h₂ (i - n) (by omega)
    have he : lo + n + (i - n) = lo + i := by omega
    simpa only [he] using ht

/-- A width is checked against the already source-proved strict-pair evaluator.
The datum itself has no authority. -/
def widthCheck (p q r : ℕ) (data : Array ℕ) (lo n : ℕ) : Bool :=
  checkRange (fun e => decide (data[e]?.getD 0 = pairCountChecked q r (p ^ e))) lo n

theorem widthCheck_sound {p q r lo n : ℕ} {data : Array ℕ}
    (h : widthCheck p q r data lo n = true) :
    ∀ i, i < n → data[lo + i]?.getD 0 = pairCountChecked q r (p ^ (lo + i)) := by
  intro i hi
  exact of_decide_eq_true (checkRange_sound h i hi)

theorem widthCheck_actual {p q r lo n : ℕ} {data : Array ℕ}
    (hq : 1 < q) (hr : 1 < r) (h : widthCheck p q r data lo n = true)
    (i : ℕ) (hi : i < n) :
    data[lo + i]?.getD 0 = (strictSmoothPairs q r (p ^ (lo + i))).card :=
  (widthCheck_sound h i hi).trans (pairCountChecked_correct hq hr)

/-- A cumulative table is authenticated by its local additive recurrence. -/
def cumulativeCheck (w c : Array ℕ) (n : ℕ) : Bool :=
  decide (c[0]?.getD 0 = 0) &&
    checkRange (fun e => decide
      (c[e + 1]?.getD 0 = c[e]?.getD 0 + w[e + 1]?.getD 0)) 0 (n - 1)

theorem cumulativeCheck_sound {w c : Array ℕ} {n : ℕ}
    (h : cumulativeCheck w c n = true) :
    c[0]?.getD 0 = 0 ∧
      ∀ e : Fin (n - 1), c[e.val + 1]?.getD 0 = c[e.val]?.getD 0 + w[e.val + 1]?.getD 0 := by
  obtain ⟨h0, hs⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨of_decide_eq_true h0, ?_⟩
  intro e
  simpa only [Nat.zero_add] using
    (of_decide_eq_true (checkRange_sound hs e.val e.isLt))

end ErdosProblems.Erdos269.PaperR11
