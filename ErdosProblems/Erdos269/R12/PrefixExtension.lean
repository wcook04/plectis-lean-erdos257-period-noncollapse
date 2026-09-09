import ErdosProblems.Erdos269.PaperR7WindowResults

/-!
# A finite word alone cannot force irrationality of every compatible orbit

A positive integral radix prefix with nonnegative integral digits has a
positive rational completion, obtained by solving backwards from state 1
and continuing with radix 2 and digit 1. This is a countermodel for inference
from an abstract finite word. It is NOT a rational model of the actual
infinite smooth-number source; the continuation is explicitly changed.
Lean proof scripts UNRUN.
-/
namespace ErdosProblems.Erdos269.PaperR12

/-- Distance-from-the-end recursion avoids dependent vector indexing. -/
def reverseRationalState (b d : ℕ → ℤ) (N : ℕ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => ((d (N - (k + 1)) : ℚ) + reverseRationalState b d N k) /
      (b (N - (k + 1)) : ℚ)

def completedBase (b : ℕ → ℤ) (N i : ℕ) : ℤ := if i < N then b i else 2

def completedDigit (d : ℕ → ℤ) (N i : ℕ) : ℤ := if i < N then d i else 1

def completedState (b d : ℕ → ℤ) (N i : ℕ) : ℚ :=
  if i ≤ N then reverseRationalState b d N (N - i) else 1

theorem reverseRationalState_pos (b d : ℕ → ℤ) (N : ℕ)
    (hb : ∀ i, i < N → 0 < b i) (hd : ∀ i, i < N → 0 ≤ d i) :
    ∀ k, k ≤ N → 0 < reverseRationalState b d N k := by
  intro k
  induction k with
  | zero => intro _; norm_num [reverseRationalState]
  | succ k ih =>
    intro hk
    have hi : N - (k + 1) < N := by omega
    have hbQ : (0 : ℚ) < b (N - (k + 1)) := by exact_mod_cast hb _ hi
    have hdQ : (0 : ℚ) ≤ d (N - (k + 1)) := by exact_mod_cast hd _ hi
    have hp := ih (by omega)
    change 0 < ((d (N - (k + 1)) : ℚ) + reverseRationalState b d N k) /
      (b (N - (k + 1)) : ℚ)
    exact div_pos (by linarith) hbQ

theorem completedState_pos (b d : ℕ → ℤ) (N : ℕ)
    (hb : ∀ i, i < N → 0 < b i) (hd : ∀ i, i < N → 0 ≤ d i)
    (i : ℕ) : 0 < completedState b d N i := by
  unfold completedState
  split_ifs with hi
  · exact reverseRationalState_pos b d N hb hd _ (Nat.sub_le _ _)
  · norm_num

theorem completedState_recurrence (b d : ℕ → ℤ) (N : ℕ)
    (hb : ∀ i, i < N → 0 < b i) (i : ℕ) :
    completedState b d N (i + 1) =
      (completedBase b N i : ℚ) * completedState b d N i -
        (completedDigit d N i : ℚ) := by
  by_cases hi : i < N
  · have hi0 : i ≤ N := by omega
    have hi1 : i + 1 ≤ N := by omega
    have hsub : N - i = (N - (i + 1)) + 1 := by omega
    have hidx : N - ((N - (i + 1)) + 1) = i := by omega
    have hbQ : (b i : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb i hi))
    simp only [completedState, if_pos hi0, if_pos hi1,
      completedBase, completedDigit, if_pos hi]
    rw [hsub, reverseRationalState, hidx]
    field_simp [hbQ] <;> ring
  · have hi1 : ¬ i + 1 ≤ N := by omega
    by_cases he : i = N
    · subst i
      norm_num [completedState, completedBase, completedDigit, reverseRationalState]
    · have hi0 : ¬ i ≤ N := by omega
      norm_num [completedState, completedBase, completedDigit, hi, hi0, hi1]

/-- The completion preserves every supplied transition, not just its length. -/
theorem finite_prefix_has_positive_rational_completion (b d : ℕ → ℤ) (N : ℕ)
    (hb : ∀ i, i < N → 0 < b i) (hd : ∀ i, i < N → 0 ≤ d i) :
    ∃ b' d' : ℕ → ℤ, ∃ X : ℕ → ℚ,
      (∀ i, i < N → b' i = b i ∧ d' i = d i) ∧
      (∀ i, 0 < b' i ∧ 0 ≤ d' i ∧ 0 < X i) ∧
      (∀ i, X (i + 1) = (b' i : ℚ) * X i - (d' i : ℚ)) ∧
      (∀ i, N ≤ i → b' i = 2 ∧ d' i = 1 ∧ X i = 1) := by
  refine ⟨completedBase b N, completedDigit d N, completedState b d N, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [completedBase, completedDigit, hi]
  · intro i
    refine ⟨?_, ?_, completedState_pos b d N hb hd i⟩
    · by_cases hi : i < N
      · simpa [completedBase, hi] using hb i hi
      · simp [completedBase, hi]
    · by_cases hi : i < N
      · simpa [completedDigit, hi] using hd i hi
      · simp [completedDigit, hi]
  · exact completedState_recurrence b d N hb
  · intro i hi
    have hin : ¬ i < N := by omega
    refine ⟨by simp [completedBase, hin], by simp [completedDigit, hin], ?_⟩
    by_cases he : i = N
    · subst i; simp [completedState, reverseRationalState]
    · have hle : ¬ i ≤ N := by omega
      simp [completedState, hle]

/-- Even an arbitrarily long ACTUAL finite prefix has an abstract rational
completion. No assertion identifies that altered continuation with the
actual infinite 2,3,5 source. -/
theorem actual_prefix_has_abstract_rational_completion (N : ℕ) :
    ∃ b' d' : ℕ → ℤ, ∃ X : ℕ → ℚ,
      (∀ i, i < N → b' i = (dyadicBlockBase235 i : ℤ) ∧
        d' i = (dyadicOrderedBlockDigit235 i : ℤ)) ∧
      (∀ i, 0 < b' i ∧ 0 ≤ d' i ∧ 0 < X i) ∧
      (∀ i, X (i + 1) = (b' i : ℚ) * X i - (d' i : ℚ)) ∧
      (∀ i, N ≤ i → b' i = 2 ∧ d' i = 1 ∧ X i = 1) := by
  exact finite_prefix_has_positive_rational_completion
    (fun i => (dyadicBlockBase235 i : ℤ))
    (fun i => (dyadicOrderedBlockDigit235 i : ℤ)) N
    (fun i _ => by
      change (0 : ℤ) < (dyadicBlockBase235 i : ℤ)
      exact_mod_cast dyadicBlockBase235_pos i)
    (fun i _ => by positivity)

end ErdosProblems.Erdos269.PaperR12
