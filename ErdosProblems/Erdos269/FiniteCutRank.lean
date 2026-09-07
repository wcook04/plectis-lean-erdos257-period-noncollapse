import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

/-!
# Finite cut-rank algebra for the three-prime carry matrix

Ordinary Type B r5 (memorandum Proposition 2.1) classifies the rank of every
finite sampled two-valued threshold matrix: if the distinct columns are the
cut vectors `v_k` for `k ∈ E`, then `rank = |E| - 1_{0,m ∈ E}`.

This module formalises the linear-algebra engine of that formula: interval
support of consecutive differences, proportionality of the two extreme
columns, and linear independence of the consecutive differences.  It does
not re-prove the infinite uniform-minor theorem already in
`KernelCarryRank.lean`, and it does not prove irrationality of the repeated
three-prime series.
-/

namespace ErdosProblems.Erdos269

/-- Two-valued cut column of length `m`: `1` on `{i | i < k}` and `c` afterwards. -/
def cutCol (c : ℚ) (k : ℕ) {m : ℕ} (i : Fin m) : ℚ :=
  if (i : ℕ) < k then 1 else c

theorem cutCol_zero (c : ℚ) {m : ℕ} (i : Fin m) : cutCol c 0 i = c := by
  simp [cutCol]

theorem cutCol_full (c : ℚ) {m : ℕ} (i : Fin m) : cutCol c m i = 1 := by
  simp [cutCol, i.isLt]

/-- The two extreme cut columns are proportional on `Fin m`. -/
theorem cutCol_extremes (c : ℚ) {m : ℕ} (i : Fin m) :
    cutCol c 0 i = c * cutCol c m i := by
  simp [cutCol_zero, cutCol_full]

theorem cutCol_sub (c : ℚ) {m k l : ℕ} (hkl : k ≤ l) (i : Fin m) :
    cutCol c l i - cutCol c k i =
      if k ≤ (i : ℕ) ∧ (i : ℕ) < l then 1 - c else 0 := by
  unfold cutCol
  by_cases hik : (i : ℕ) < k
  · have hil : (i : ℕ) < l := lt_of_lt_of_le hik hkl
    have hki : ¬ k ≤ (i : ℕ) := not_le.mpr hik
    simp [hik, hil, hki]
  · have hki : k ≤ (i : ℕ) := le_of_not_gt hik
    by_cases hil : (i : ℕ) < l
    · simp [hik, hil, hki]
    · simp [hik, hil, hki]

theorem cutCol_sub_at_left (c : ℚ) {m k l : ℕ} (hkl : k < l) (hlm : l ≤ m) :
    cutCol (m := m) c l ⟨k, lt_of_lt_of_le hkl hlm⟩ -
        cutCol c k ⟨k, lt_of_lt_of_le hkl hlm⟩ =
      1 - c := by
  have hk : k ≤ k ∧ k < l := ⟨le_rfl, hkl⟩
  simp [cutCol_sub (c := c) (hkl := hkl.le), hk]

private lemma not_mem_other_cut_interval
    {t : ℕ} {ks : Fin t.succ → ℕ} (hmono : StrictMono ks)
    {i j : Fin t} (hij : i ≠ j) :
    ¬ (ks i.castSucc ≤ ks j.castSucc ∧ ks j.castSucc < ks i.succ) := by
  intro ⟨hle, hlt⟩
  have hik : (i : ℕ) ≠ (j : ℕ) := by
    intro h
    exact hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hik with hltij | hgtij
  · have : (i : ℕ) + 1 ≤ (j : ℕ) := Nat.succ_le_of_lt hltij
    have hleFin : i.succ ≤ j.castSucc :=
      Fin.mk_le_mk.mpr (by
        change (i.succ : ℕ) ≤ (j.castSucc : ℕ)
        simpa using this)
    have : ks i.succ ≤ ks j.castSucc := hmono.monotone hleFin
    exact (not_le_of_gt hlt) this
  · have hltFin : j.castSucc < i.castSucc :=
      Fin.mk_lt_mk.mpr (gt_iff_lt.mp hgtij)
    have : ks j.castSucc < ks i.castSucc := hmono hltFin
    exact (not_le_of_gt this) hle

/-- Consecutive differences of a strictly increasing cut sequence are
linearly independent when `c ≠ 1`. -/
theorem consecutive_cut_differences_linearIndependent
    {m t : ℕ} (c : ℚ) (hc : c ≠ 1)
    (ks : Fin t.succ → ℕ) (hmono : StrictMono ks) (hbound : ∀ i, ks i ≤ m) :
    LinearIndependent ℚ fun j : Fin t =>
      fun i : Fin m =>
        cutCol (m := m) c (ks j.succ) i - cutCol c (ks j.castSucc) i := by
  classical
  have hstep : ∀ i : Fin t, i.castSucc < i.succ := by
    intro i
    exact Fin.mk_lt_mk.mpr (by
      change (i.castSucc : ℕ) < (i.succ : ℕ)
      simp)
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hlt : ks j.castSucc < m :=
    lt_of_lt_of_le (hmono (hstep j)) (hbound j.succ)
  let x : Fin m := ⟨ks j.castSucc, hlt⟩
  have hxval : (x : ℕ) = ks j.castSucc := rfl
  have hterm : ∀ i : Fin t,
      g i *
          (cutCol (m := m) c (ks i.succ) x - cutCol c (ks i.castSucc) x) =
        if i = j then g j * (1 - c) else 0 := by
    intro i
    have hdiff :=
      cutCol_sub (c := c) (m := m) (k := ks i.castSucc) (l := ks i.succ)
        (hkl := (hmono (hstep i)).le) x
    by_cases hij : i = j
    · subst hij
      have hx : ks i.castSucc ≤ (x : ℕ) ∧ (x : ℕ) < ks i.succ :=
        ⟨le_rfl, by simpa [hxval] using hmono (hstep i)⟩
      simp [hdiff, hx]
    · have hnot :
          ¬ (ks i.castSucc ≤ (x : ℕ) ∧ (x : ℕ) < ks i.succ) := by
        simpa [hxval] using not_mem_other_cut_interval hmono hij
      simp [hdiff, hnot, hij]
  have hsum :
      (∑ i : Fin t,
          g i *
            (cutCol (m := m) c (ks i.succ) x -
              cutCol c (ks i.castSucc) x)) =
        g j * (1 - c) := by
    simp_rw [hterm]
    simp [Finset.sum_ite_eq]
  have hx0 :
      (∑ i : Fin t,
          g i *
            (cutCol (m := m) c (ks i.succ) x -
              cutCol c (ks i.castSucc) x)) = 0 := by
    have hfun := congrFun hg x
    simpa [Pi.smul_apply, smul_eq_mul] using hfun
  have hprod : g j * (1 - c) = 0 := by
    rw [← hsum, hx0]
  have hsub : (1 - c : ℚ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  exact (mul_eq_zero.mp hprod).resolve_right hsub

end ErdosProblems.Erdos269
