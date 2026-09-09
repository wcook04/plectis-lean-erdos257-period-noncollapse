import ErdosProblems.Erdos269.CertificateRangeR11

/-! R12 shape-authenticated checkers and scope counterexamples.
These are complete candidate proof bodies, all UNRUN. The original total-getD
soundness theorem is not false: the extra checks authenticate array coverage,
which is a distinct claim. No axiom and no native proof admission is added. -/
namespace ErdosProblems.Erdos269.PaperR12
open PaperR9 PaperR11

/-- The entire half-open checked interval is present in the supplied array. -/
def widthCheckBoundedR12 (p q r : ℕ) (data : Array ℕ) (lo n : ℕ) : Bool :=
  decide (lo + n ≤ data.size) && widthCheck p q r data lo n

theorem widthCheckBoundedR12_sound {p q r lo n : ℕ} {data : Array ℕ}
    (h : widthCheckBoundedR12 p q r data lo n = true) :
    lo + n ≤ data.size ∧
      ∀ i, i < n → lo + i < data.size ∧
        data[lo + i]?.getD 0 = pairCountChecked q r (p ^ (lo + i)) := by
  obtain ⟨hb, hc⟩ := Bool.and_eq_true_iff.mp h
  have hsize : lo + n ≤ data.size := of_decide_eq_true hb
  refine ⟨hsize, ?_⟩
  intro i hi
  exact ⟨by omega, widthCheck_sound hc i hi⟩

theorem widthCheckBoundedR12_actual {p q r lo n : ℕ} {data : Array ℕ}
    (hq : 1 < q) (hr : 1 < r)
    (h : widthCheckBoundedR12 p q r data lo n = true)
    (i : ℕ) (hi : i < n) :
    lo + i < data.size ∧
      data[lo + i]?.getD 0 = (strictSmoothPairs q r (p ^ (lo + i))).card := by
  have hs := (widthCheckBoundedR12_sound h).2 i hi
  exact ⟨hs.1, hs.2.trans (pairCountChecked_correct hq hr)⟩

theorem widthCheckBoundedR12_append {p q r lo n m : ℕ} {data : Array ℕ}
    (h₁ : widthCheckBoundedR12 p q r data lo n = true)
    (h₂ : widthCheckBoundedR12 p q r data (lo + n) m = true) :
    widthCheckBoundedR12 p q r data lo (n + m) = true := by
  have hs₁ := widthCheckBoundedR12_sound h₁
  have hs₂ := widthCheckBoundedR12_sound h₂
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega), ?_⟩
  apply (checkRange_iff _ _ _).mpr
  intro i hi
  apply decide_eq_true
  exact range_append
    (P := fun e => data[e]?.getD 0 = pairCountChecked q r (p ^ e))
    (fun j hj => (hs₁.2 j hj).2)
    (fun j hj => (hs₂.2 j hj).2) i hi

/-- A nonempty cumulative table must contain its origin and every used entry. -/
def cumulativeCheckBoundedR12 (w c : Array ℕ) (n : ℕ) : Bool :=
  decide (0 < n ∧ n ≤ w.size ∧ n ≤ c.size) && cumulativeCheck w c n

theorem cumulativeCheckBoundedR12_sound {w c : Array ℕ} {n : ℕ}
    (h : cumulativeCheckBoundedR12 w c n = true) :
    (0 < n ∧ n ≤ w.size ∧ n ≤ c.size) ∧
    c[0]?.getD 0 = 0 ∧
      ∀ e : Fin (n - 1), c[e.val + 1]?.getD 0 =
        c[e.val]?.getD 0 + w[e.val + 1]?.getD 0 := by
  obtain ⟨hs, hc⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true hs, cumulativeCheck_sound hc⟩

/-- Default-zero acceptance is not evidence of an array entry's existence. -/
theorem width_shape_regressions_R12 :
    widthCheck 2 3 5 #[] 0 1 = true ∧
    widthCheckBoundedR12 2 3 5 #[] 0 1 = false ∧
    widthCheckBoundedR12 2 3 5 #[0] 0 1 = true ∧
    widthCheckBoundedR12 2 3 5 #[0] 0 2 = false ∧
    widthCheckBoundedR12 2 3 5 #[] 0 0 = true := by
  decide +kernel

/-- Full-height clearing cannot be replaced by half-height clearing. -/
theorem factor_two_cannot_be_cancelled_R12 :
    (2 : ℚ) * (1 / 2) = 1 ∧ ¬ ∃ z : ℤ, (1 / 2 : ℚ) = (z : ℚ) := by
  constructor
  · norm_num
  · rintro ⟨z, hz⟩
    have he : (2 : ℚ) * (z : ℚ) = 1 := by rw [← hz]; norm_num
    have heZ : (2 : ℤ) * z = 1 := by exact_mod_cast he
    omega

/-- A counterexample to the abstract finite-to-cofinal implication. This
predicate is NOT claimed to be the actual digit word or actual escape set. -/
theorem finite_coverage_not_cofinal_R12 (U : ℕ) :
    (∀ a : ℕ, a ≤ U → a ≤ U) ∧
      ¬ (∀ onset : ℕ, ∃ a : ℕ, onset ≤ a ∧ a ≤ U) := by
  refine ⟨fun _ h => h, ?_⟩
  intro h
  obtain ⟨a, ha, hb⟩ := h (U + 1)
  omega

end ErdosProblems.Erdos269.PaperR12
