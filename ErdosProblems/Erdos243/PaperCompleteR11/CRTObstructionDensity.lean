import ErdosProblems.Erdos243.PaperCompleteR11.WindowIncidence
import Mathlib.Data.ZMod.QuotientRing

/-!
# Combining all finite good-prime obstructions

Authored candidate, UNRUN. The Chinese remainder equivalence is constructed by
mathlib, and the cardinality is proved by an explicit equivalence of the
avoiding subtype with a product of punctured residue fields. No independence
or density formula is supplied as a hypothesis. Moduli may be any positive
pairwise coprime natural numbers; the application uses distinct primes.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators

/-- Exact finite CRT union, including natural representatives and the
membership dictionary required by the window-counting theorem. -/
theorem exists_crt_union_residues {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hc : Pairwise (fun i j ↦ Nat.Coprime (m i) (m j)))
    (r : ∀ i, ZMod (m i)) :
    ∃ R : Finset ℕ,
      (∀ t ∈ R, t < ∏ i, m i) ∧
      R.card + ∏ i, (m i - 1) = ∏ i, m i ∧
      (∀ n : ℕ, n % (∏ i, m i) ∈ R ↔ ∃ i, (n : ZMod (m i)) = r i) := by
  classical
  let M := ∏ i, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ ↦ hm i)
  letI : ∀ i, NeZero (m i) := fun i ↦ ⟨Nat.ne_of_gt (hm i)⟩
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  let e : ZMod M ≃+* (∀ i, ZMod (m i)) := ZMod.prodEquivPi m hc
  let B : Finset (ZMod M) := Finset.univ.filter (fun z ↦ ∃ i, e z i = r i)
  let R : Finset ℕ := B.image ZMod.val
  let avoid : {z : ZMod M // ∀ i, e z i ≠ r i} ≃
      (∀ i, {z : ZMod (m i) // z ≠ r i}) :=
    { toFun := fun z i ↦ ⟨e z.val i, z.property i⟩
      invFun := fun z ↦ ⟨e.symm (fun i ↦ (z i).val), by
        intro i
        simpa using (z i).property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact e.symm_apply_apply z.val
      right_inv := by
        intro z
        funext i
        apply Subtype.ext
        exact congrFun (e.apply_symm_apply (fun i ↦ (z i).val)) i }
  have hgood : Fintype.card {z : ZMod M // ∀ i, e z i ≠ r i} =
      ∏ i, (m i - 1) := by
    simpa only [Fintype.card_pi, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, ZMod.card] using Fintype.card_congr avoid
  have hbad : B.card = M - ∏ i, (m i - 1) := by
    have hb : Fintype.card {z : ZMod M // ∃ i, e z i = r i} = B.card :=
      Fintype.card_of_subtype B (by intro z; simp [B])
    rw [← hb]
    have h := Fintype.card_subtype_compl (fun z : ZMod M ↦ ∀ i, e z i ≠ r i)
    simpa only [not_forall, not_not, ZMod.card, hgood] using h
  have hRcard : R.card = B.card :=
    Finset.card_image_iff.mpr (ZMod.val_injective M).injOn
  have hle : (∏ i, (m i - 1)) ≤ M := by
    have h := Fintype.card_le_of_injective
      (Subtype.val : {z : ZMod M // ∀ i, e z i ≠ r i} → ZMod M)
      Subtype.val_injective
    simpa only [hgood, ZMod.card] using h
  have hcast (n : ℕ) (i : ι) : e (n : ZMod M) i = (n : ZMod (m i)) := by
    exact congrFun (map_natCast e n) i
  refine ⟨R, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp ht
    exact ZMod.val_lt z
  · change R.card + ∏ i, (m i - 1) = M
    rw [hRcard, hbad, Nat.sub_add_cancel hle]
  · intro n
    constructor
    · intro hn
      obtain ⟨z, hz, hzn⟩ := Finset.mem_image.mp hn
      have heq : z = (n : ZMod M) := (ZMod.val_injective M) (by
        rw [ZMod.val_natCast]
        exact hzn)
      obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hz).2
      exact ⟨i, by simpa only [heq, hcast] using hi⟩
    · rintro ⟨i, hi⟩
      apply Finset.mem_image.mpr
      refine ⟨(n : ZMod M), ?_, ZMod.val_natCast M n⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, by rw [hcast]; exact hi⟩⟩

/-- Cast the exact CRT cardinality to its multiplicative complement formula. -/
theorem crt_union_card_ratio {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (R : Finset ℕ)
    (hcard : R.card + ∏ i, (m i - 1) = ∏ i, m i) :
    (R.card : ℝ) / ((∏ i, m i : ℕ) : ℝ) =
      1 - ∏ i, (1 - 1 / (m i : ℝ)) := by
  have hM : (0 : ℝ) < ((∏ i, m i : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i _ ↦ hm i)
  have hp : ((∏ i, (m i - 1) : ℕ) : ℝ) / ((∏ i, m i : ℕ) : ℝ) =
      ∏ i, (1 - 1 / (m i : ℝ)) := by
    rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.succ_le_of_lt (hm i)), Nat.cast_one]
    have hmi : (m i : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hm i)
    field_simp [hmi]
  have hcard' : (R.card : ℝ) + ((∏ i, (m i - 1) : ℕ) : ℝ) =
      ((∏ i, m i : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [← hp]
  field_simp [ne_of_gt hM]
  linarith

/-- Exact finite-prime amplification. A hit at every selected residue yields
`(1 - product(1 - 1/p))/L`, not just the bound from one selected prime. -/
theorem crt_window_lower_density {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hc : Pairwise (fun i j ↦ Nat.Coprime (m i) (m j)))
    (r : ∀ i, ZMod (m i)) (E : Set ℕ) (L T : ℕ) (hL : 0 < L)
    (hhit : ∀ i (n : ℕ), T ≤ n → (n : ZMod (m i)) = r i →
      ∃ j : ℕ, j < L ∧ n + j ∈ E) :
    LowerDensityAtLeast E ((1 - ∏ i, (1 - 1 / (m i : ℝ))) / (L : ℝ)) := by
  obtain ⟨R, hR, hcard, hmem⟩ := exists_crt_union_residues m hm hc r
  have hM : 0 < ∏ i, m i := Finset.prod_pos (fun i _ ↦ hm i)
  have hh : ∀ n : ℕ, T ≤ n → n % (∏ i, m i) ∈ R →
      ∃ j : ℕ, j < L ∧ n + j ∈ E := by
    intro n hn hnr
    obtain ⟨i, hi⟩ := (hmem n).mp hnr
    exact hhit i n hn hi
  have hd := residue_window_lower_density E (∏ i, m i) L T hM hL R hR hh
  have hmratio := crt_union_card_ratio m hm R hcard
  simpa only [← div_div, hmratio] using hd

end ErdosProblems.Erdos243.PaperCompleteR11
