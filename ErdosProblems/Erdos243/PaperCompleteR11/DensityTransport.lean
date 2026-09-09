import ErdosProblems.Erdos243.PaperCompleteR11.WindowIncidence

/-! Authored, UNRUN. Finite-prefix and constant transport for the literal
lower asymptotic density used throughout the R11 window arguments. -/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9

/-- Lower bounds can be weakened without changing the exceptional set. -/
theorem LowerDensityAtLeast.mono_bound {E : Set ℕ} {a b : ℝ}
    (h : LowerDensityAtLeast E b) (hab : a ≤ b) : LowerDensityAtLeast E a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun X hX ↦ ?_⟩
  calc
    (a - ε) * (X : ℝ) ≤ (b - ε) * (X : ℝ) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hab ε) (Nat.cast_nonneg X)
    _ ≤ (exceptionCount E X : ℝ) := hN X hX

/-- Eventual inclusion loses at most the length of the discarded prefix. -/
theorem exceptionCount_le_of_eventual_subset (E F : Set ℕ) (T X : ℕ)
    (hsub : ∀ n, T ≤ n → n ∈ E → n ∈ F) :
    exceptionCount E X ≤ T + exceptionCount F X := by
  classical
  have hs : exceptionFinset E X ⊆ Finset.range T ∪ exceptionFinset F X := by
    intro n hn
    obtain ⟨hnX, hnE⟩ := Finset.mem_filter.mp hn
    by_cases hnT : n < T
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hnT))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hnX, hsub n (by omega) hnE⟩))
  calc
    exceptionCount E X ≤ (Finset.range T ∪ exceptionFinset F X).card :=
      Finset.card_le_card hs
    _ ≤ (Finset.range T).card + (exceptionFinset F X).card := Finset.card_union_le _ _
    _ = T + exceptionCount F X := by simp [exceptionCount]

/-- No density is lost when a finite initial segment is discarded. -/
theorem LowerDensityAtLeast.of_eventual_subset {E F : Set ℕ} {d : ℝ}
    (hE : LowerDensityAtLeast E d) (T : ℕ)
    (hsub : ∀ n, T ≤ n → n ∈ E → n ∈ F) : LowerDensityAtLeast F d := by
  intro ε hε
  obtain ⟨N, hN⟩ := hE (ε / 2) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt ((2 * (T : ℝ)) / ε)
  refine ⟨max N M, ?_⟩
  intro X hX
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hXM : (M : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast le_trans (le_max_right N M) hX
  have hsmall : 2 * (T : ℝ) < (X : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (lt_of_lt_of_le hM hXM)
  have hc : (exceptionCount E X : ℝ) ≤ (T : ℝ) + (exceptionCount F X : ℝ) := by
    exact_mod_cast exceptionCount_le_of_eventual_subset E F T X hsub
  have hl := hN X hXN
  nlinarith

/-- In particular, eventual equality of exception predicates preserves every
lower-density bound, with their original indices and original prefixes. -/
theorem lowerDensityAtLeast_iff_of_eventual_iff (E F : Set ℕ) (T : ℕ) (d : ℝ)
    (heq : ∀ n, T ≤ n → (n ∈ E ↔ n ∈ F)) :
    LowerDensityAtLeast E d ↔ LowerDensityAtLeast F d := by
  constructor
  · intro h
    exact h.of_eventual_subset T (fun n hn ↦ (heq n hn).mp)
  · intro h
    exact h.of_eventual_subset T (fun n hn ↦ (heq n hn).mpr)

/-- Disjoint periodic windows cost one exception per period, not one divided
by the window length. This is useful for small-prime primitive obstructions. -/
theorem disjoint_periodic_lowerDensity (E : Set ℕ) (r s L : ℕ)
    (hs : 0 < s) (hL : L ≤ s)
    (hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ r + s * k + i ∈ E) :
    LowerDensityAtLeast E (1 / (s : ℝ)) := by
  apply lowerDensityAtLeast_of_linear_bound E 1 (s : ℝ) (r + s : ℕ)
    (by exact_mod_cast hs)
  intro X
  have h := disjoint_periodic_linear_bound E r s L hs hL hhit X
  simpa only [one_mul] using (show (X : ℝ) ≤
    (s : ℝ) * (exceptionCount E X : ℝ) + ((r + s : ℕ) : ℝ) by exact_mod_cast h)

/-- General fixed offsets are charged by their number, not their maximum size.
Repeated offsets are allowed. This repairs the inherited mapping of the paper's
periodic-obstruction lemma to a theorem that only handled disjoint windows. -/
theorem fixed_offset_incidence_bound (A : Finset ℕ) (E : Set ℕ) (L X : ℕ)
    (offset : Fin L → ℕ)
    (hhit : ∀ n ∈ A, ∃ i : Fin L, n + offset i < X ∧ n + offset i ∈ E) :
    A.card ≤ L * exceptionCount E X := by
  classical
  have h : ∀ n : ↥A, ∃ i : Fin L,
      (n : ℕ) + offset i < X ∧ (n : ℕ) + offset i ∈ E :=
    fun n ↦ hhit n n.property
  choose w hw using h
  let f : ↥A → (↥(exceptionFinset E X)) × Fin L := fun n ↦
    (⟨(n : ℕ) + offset (w n), Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hw n).1, (hw n).2⟩⟩, w n)
  have hf : Function.Injective f := by
    intro n m hnm
    have he := congrArg (fun z : (↥(exceptionFinset E X)) × Fin L ↦ (z.1 : ℕ)) hnm
    have hi : w n = w m := congrArg Prod.snd hnm
    change (n : ℕ) + offset (w n) = (m : ℕ) + offset (w m) at he
    rw [hi] at he
    exact Subtype.ext (Nat.add_right_cancel he)
  have hc := Fintype.card_le_of_injective f hf
  simpa [exceptionCount, Nat.mul_comm] using hc

/-- Boundary-corrected count for arbitrary fixed offsets on one progression.
The offset bound H affects only the additive boundary term, not the density. -/
theorem fixed_offset_periodic_linear_bound (E : Set ℕ) (r s L H : ℕ)
    (hs : 0 < s) (offset : Fin L → ℕ) (hoffset : ∀ i, offset i ≤ H)
    (hhit : ∀ k : ℕ, ∃ i : Fin L, r + s * k + offset i ∈ E) :
    ∀ X : ℕ, X ≤ s * L * exceptionCount E X + (r + H + s) := by
  classical
  intro X
  by_cases hsmall : X < r + H
  · omega
  let K := (X - (r + H)) / s
  have hsub := Nat.sub_add_cancel (show r + H ≤ X by omega)
  have hmod := Nat.mod_add_div (X - (r + H)) s
  have hrem := Nat.mod_lt (X - (r + H)) hs
  have hend : r + s * K + H ≤ X := by
    dsimp [K]
    have hle : s * ((X - (r + H)) / s) ≤ X - (r + H) := by omega
    calc
      r + s * ((X - (r + H)) / s) + H =
          s * ((X - (r + H)) / s) + (r + H) := by omega
      _ ≤ (X - (r + H)) + (r + H) := Nat.add_le_add_right hle _
      _ = X := hsub
  have hX : X ≤ s * K + r + H + s := by
    dsimp [K]
    nlinarith
  let A := (Finset.range K).image (fun k ↦ r + s * k)
  have hinj : Function.Injective (fun k : ℕ ↦ r + s * k) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left hs (Nat.add_left_cancel hxy)
  have hcard : A.card = K := by
    dsimp [A]
    rw [Finset.card_image_iff.mpr hinj.injOn, Finset.card_range]
  have hA : ∀ n ∈ A, ∃ i : Fin L, n + offset i < X ∧ n + offset i ∈ E := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have hkK : k < K := Finset.mem_range.mp hk
    obtain ⟨i, hi⟩ := hhit k
    refine ⟨i, ?_, hi⟩
    have hmul := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hkK)
    have ho := hoffset i
    nlinarith
  have hcount := fixed_offset_incidence_bound A E L X offset hA
  rw [hcard] at hcount
  have hscaled := Nat.mul_le_mul_left s hcount
  nlinarith

/-- The paper's periodic obstruction principle for arbitrary fixed natural
index offsets, with arbitrary overlaps and repeated offsets. The progression
starts after the original threshold; its phase is not silently reset. -/
theorem fixed_offsets_periodic_lowerDensity (E : Set ℕ) (s L T r : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hr : r < s) (offset : Fin L → ℕ)
    (hhit : ∀ n : ℕ, T ≤ n → n % s = r →
      ∃ i : Fin L, n + offset i ∈ E) :
    LowerDensityAtLeast E (1 / ((L : ℝ) * (s : ℝ))) := by
  classical
  let H : ℕ := ∑ i : Fin L, offset i
  have hoffset : ∀ i, offset i ≤ H := by
    intro i
    exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (offset j)) (Finset.mem_univ i)
  have hprogression : ∀ k : ℕ, ∃ i : Fin L,
      (r + s * T) + s * k + offset i ∈ E := by
    intro k
    apply hhit
    · have hmul := Nat.mul_le_mul_right T (show 1 ≤ s by omega)
      nlinarith
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  have hbound := fixed_offset_periodic_linear_bound E (r + s * T) s L H
    hs offset hoffset hprogression
  have hden : 0 < (s : ℝ) * (L : ℝ) := by positivity
  have h := lowerDensityAtLeast_of_linear_bound E 1 ((s : ℝ) * (L : ℝ))
    (((r + s * T) + H + s : ℕ) : ℝ) hden (by
      intro X
      simpa only [one_mul] using (show (X : ℝ) ≤
        ((s : ℝ) * (L : ℝ)) * (exceptionCount E X : ℝ) +
          (((r + s * T) + H + s : ℕ) : ℝ) by exact_mod_cast hbound X))
  simpa only [mul_comm] using h

end ErdosProblems.Erdos243.PaperCompleteR11
