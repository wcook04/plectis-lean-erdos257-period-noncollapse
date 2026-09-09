import Mathlib

/-!
# Exact obstruction to the proposed full critical-value separation theorem

R13. AUTHORED / UNRUN. No kernel verification is claimed.

The quartic has four simple real roots in the four displayed open intervals.
Together with its three explicitly known critical points these are pairwise
more than 1/4 apart. The two critical values at -1 and 1 differ by 1/65536,
whereas the proposed lower bound is 3/65536.

The finite root-count argument below is essential: endpoint signs alone are
not used as a substitute for exhaustiveness of the complex roots.
-/

noncomputable section
open Polynomial Set

namespace ErdosProblems.Erdos1041.SeparationCounterexampleR13

def p : Polynomial ℂ :=
  X ^ 4 - C (1 / 262144) * X ^ 3 - C 2 * X ^ 2 +
    C (3 / 262144) * X + C (1 / 2)

def f (x : ℝ) : ℝ :=
  x ^ 4 - (1 / 262144) * x ^ 3 - 2 * x ^ 2 +
    (3 / 262144) * x + 1 / 2

def t : ℝ := 3 / 1048576

theorem degree_p : p.natDegree = 4 := by
  unfold p
  compute_degree!

theorem monic_p : p.Monic := by
  change p.coeff p.natDegree = 1
  rw [degree_p]
  norm_num [p]

theorem p_ne_zero : p ≠ 0 := monic_p.ne_zero

theorem eval_real (x : ℝ) : p.eval (x : ℂ) = (f x : ℂ) := by
  simp only [p, f, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  push_cast
  ring

theorem derivative_factorisation :
    p.derivative = C 4 * (X - C (-1)) * (X - C (t : ℂ)) * (X - C 1) := by
  norm_num [p, t, Polynomial.derivative_mul, Polynomial.derivative_pow] <;>
    ring_nf <;> norm_num [← C_pow, ← C_mul] <;> abel

theorem derivative_root_iff (z : ℂ) :
    p.derivative.eval z = 0 ↔ z = -1 ∨ z = (t : ℂ) ∨ z = 1 := by
  rw [derivative_factorisation]
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero]
  norm_num <;> tauto

theorem continuous_f : Continuous f := by unfold f; fun_prop

/-- A strictly signed endpoint version of the intermediate value theorem. -/
theorem exists_zero_open {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ} (hab : a < b) (ha : g a < 0) (hb : 0 < g b) :
    ∃ r, r ∈ Ioo a b ∧ g r = 0 := by
  obtain ⟨r, hr, hgr⟩ :=
    intermediate_value_Icc hab.le hg.continuousOn
      (show (0 : ℝ) ∈ Icc (g a) (g b) from ⟨ha.le, hb.le⟩)
  refine ⟨r, ⟨?_, ?_⟩, hgr⟩
  · by_contra h
    have he : r = a := le_antisymm (not_lt.mp h) hr.1
    subst r
    linarith
  · by_contra h
    have he : r = b := le_antisymm hr.2 (not_lt.mp h)
    subst r
    linarith

/-- Four roots with strict, exact rational localisation. -/
structure RootBoxes where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  ha : a ∈ Ioo (-3 / 2) (-5 / 4)
  hb : b ∈ Ioo (-3 / 4) (-1 / 2)
  hc : c ∈ Ioo (1 / 2) (3 / 4)
  hd : d ∈ Ioo (5 / 4) (3 / 2)
  fa : f a = 0
  fb : f b = 0
  fc : f c = 0
  fd : f d = 0

theorem exists_rootBoxes : Nonempty RootBoxes := by
  obtain ⟨a, ha, hfa⟩ := exists_zero_open continuous_f.neg
    (a := -3 / 2) (b := -5 / 4) (by norm_num)
    (by norm_num [f]) (by norm_num [f])
  obtain ⟨b, hb, hfb⟩ := exists_zero_open continuous_f
    (a := -3 / 4) (b := -1 / 2) (by norm_num)
    (by norm_num [f]) (by norm_num [f])
  obtain ⟨c, hc, hfc⟩ := exists_zero_open continuous_f.neg
    (a := 1 / 2) (b := 3 / 4) (by norm_num)
    (by norm_num [f]) (by norm_num [f])
  obtain ⟨d, hd, hfd⟩ := exists_zero_open continuous_f
    (a := 5 / 4) (b := 3 / 2) (by norm_num)
    (by norm_num [f]) (by norm_num [f])
  exact ⟨⟨a, b, c, d, ha, hb, hc, hd, by simpa using hfa,
    hfb, by simpa using hfc, hfd⟩⟩

/-- Increasing order of all four roots and all three critical points. -/
def realPoints (R : RootBoxes) : Fin 7 → ℝ :=
  ![R.a, -1, R.b, t, R.c, 1, R.d]

def points (R : RootBoxes) (i : Fin 7) : ℂ := (realPoints R i : ℂ)

theorem realPoints_separated (R : RootBoxes) (i j : Fin 7) (hij : i ≠ j) :
    (1 / 4 : ℝ) < |realPoints R i - realPoints R j| := by
  have ha0 := R.ha.1
  have ha1 := R.ha.2
  have hb0 := R.hb.1
  have hb1 := R.hb.2
  have hc0 := R.hc.1
  have hc1 := R.hc.2
  have hd0 := R.hd.1
  have hd1 := R.hd.2
  norm_num at ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1
  have hadj : ∀ k : Fin 6,
      (1 / 4 : ℝ) < realPoints R k.succ - realPoints R k.castSucc := by
    intro k
    fin_cases k <;> simp [realPoints, t] at * <;> linarith
  have hmono : StrictMono (realPoints R) :=
    Fin.strictMono_iff_lt_succ.mpr fun k => by
      have h := hadj k
      linarith
  have hforward : ∀ i j : Fin 7, i < j →
      (1 / 4 : ℝ) < realPoints R j - realPoints R i := by
    intro k l hkl
    let m : Fin 6 := ⟨k, by omega⟩
    have hm : m.castSucc = k := by ext; rfl
    have hml : m.succ ≤ l := by
      apply Fin.le_iff_val_le_val.mpr
      change k.val + 1 ≤ l.val
      exact Nat.succ_le_iff.mpr hkl
    have hle := hmono.monotone hml
    have hgap := hadj m
    rw [hm] at hgap
    linarith
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have h := hforward i j hij'
    rw [abs_of_neg (by linarith), neg_sub]
    exact h
  · have h := hforward j i hji'
    rw [abs_of_pos (by linarith)]
    exact h

theorem points_separated (R : RootBoxes) (i j : Fin 7) (hij : i ≠ j) :
    (1 / 4 : ℝ) < dist (points R i) (points R j) := by
  simpa only [points, dist_eq_norm, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using realPoints_separated R i j hij

theorem points_injective (R : RootBoxes) : Function.Injective (points R) := by
  intro i j he
  by_contra hne
  have h := points_separated R i j hne
  rw [he, dist_self] at h
  norm_num at h

def roots (R : RootBoxes) : Fin 4 → ℂ := ![(R.a : ℂ), R.b, R.c, R.d]

theorem root_eval_zero (R : RootBoxes) (i : Fin 4) : p.eval (roots R i) = 0 := by
  fin_cases i <;> simp [roots, eval_real, R.fa, R.fb, R.fc, R.fd]

theorem roots_injective (R : RootBoxes) : Function.Injective (roots R) := by
  have h : roots R = fun i => points R (![0, 2, 4, 6] i) := by
    funext i; fin_cases i <;> rfl
  rw [h]
  intro i j hij
  have he : (![0, 2, 4, 6] : Fin 4 → Fin 7) i =
      (![0, 2, 4, 6] : Fin 4 → Fin 7) j := (points_injective R) hij
  exact (by decide : Function.Injective (![0, 2, 4, 6] : Fin 4 → Fin 7)) he

/-- There are no further, non-real complex roots. -/
theorem root_exhaustion (R : RootBoxes) (z : ℂ) :
    p.eval z = 0 ↔ ∃ i : Fin 4, roots R i = z := by
  classical
  constructor
  · intro hz
    let S : Finset ℂ := Finset.univ.image (roots R)
    have hcard : S.card = 4 := by
      dsimp [S]
      rw [Finset.card_image_of_injective _ (roots_injective R)]
      simp
    have hsub : S ⊆ p.roots.toFinset := by
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots p_ne_zero).mpr
        (root_eval_zero R i))
    have hbound : p.roots.toFinset.card ≤ 4 := by
      calc
        p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
        _ ≤ p.natDegree := Polynomial.card_roots' p
        _ = 4 := degree_p
    have hEq : S = p.roots.toFinset :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [hcard] using hbound)
    have hzmem : z ∈ S := by
      rw [hEq]
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots p_ne_zero).mpr hz)
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzmem
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact root_eval_zero R i

def criticals : Fin 3 → ℂ := ![-1, (t : ℂ), 1]

theorem critical_exhaustion (z : ℂ) :
    p.derivative.eval z = 0 ↔ ∃ i : Fin 3, criticals i = z := by
  rw [derivative_root_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [criticals]

def combined (R : RootBoxes) : Fin 4 ⊕ Fin 3 → ℂ :=
  Sum.elim (roots R) criticals

def combinedIndex : Fin 4 ⊕ Fin 3 → Fin 7 :=
  Sum.elim (fun i => ![0, 2, 4, 6] i) (fun i => ![1, 3, 5] i)

theorem combinedIndex_injective : Function.Injective combinedIndex := by
  decide

theorem combined_eq (R : RootBoxes) (u : Fin 4 ⊕ Fin 3) :
    combined R u = points R (combinedIndex u) := by
  rcases u with i | i <;> fin_cases i <;>
    simp [combined, combinedIndex, roots, criticals, points, realPoints]

theorem combined_separated (R : RootBoxes) (u v : Fin 4 ⊕ Fin 3) (huv : u ≠ v) :
    (1 / 4 : ℝ) < dist (combined R u) (combined R v) := by
  rw [combined_eq, combined_eq]
  exact points_separated R _ _ (fun h => huv (combinedIndex_injective h))

/-- The exact finite, multiplicity-sensitive separation hypothesis of the paper. -/
theorem separated_enumerations :
    ∃ (r : Fin 4 → ℂ) (c : Fin 3 → ℂ),
      (∀ z, p.eval z = 0 ↔ ∃ i, r i = z) ∧
      (∀ z, p.derivative.eval z = 0 ↔ ∃ j, c j = z) ∧
      (∀ u v : Fin 4 ⊕ Fin 3, u ≠ v →
        (1 / 4 : ℝ) < dist (Sum.elim r c u) (Sum.elim r c v)) := by
  obtain ⟨R⟩ := exists_rootBoxes
  exact ⟨roots R, criticals, root_exhaustion R,
    critical_exhaustion, combined_separated R⟩

theorem no_common_root (z : ℂ) (hz : p.eval z = 0) : p.derivative.eval z ≠ 0 := by
  intro hd
  rcases (derivative_root_iff z).mp hd with rfl | rfl | rfl <;>
    norm_num [p, t] at hz

theorem eval_gap : p.eval 1 - p.eval (-1) = (1 / 65536 : ℂ) := by
  norm_num [p]

theorem eval_gap_norm : ‖p.eval 1 - p.eval (-1)‖ = (1 / 65536 : ℝ) := by
  rw [eval_gap]
  norm_num [norm_div]

theorem critical_values_distinct : p.eval 1 ≠ p.eval (-1) := by
  intro h
  have hh := eval_gap
  rw [h, sub_self] at hh
  norm_num at hh


/-- The obstruction remains even when all critical values are distinct. -/
theorem critical_values_injective :
    Function.Injective (fun i : Fin 3 => p.eval (criticals i)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [criticals, p, t] at *

theorem strict_violation :
    ‖p.eval 1 - p.eval (-1)‖ <
      (((p.natDegree - 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) / 4) ^ p.natDegree) := by
  rw [eval_gap_norm, degree_p]
  norm_num

/-- A monic degree-four counterexample with complete separated enumerations. -/
theorem full_separation_counterexample :
    p.Monic ∧ p.natDegree = 4 ∧
    (∃ (r : Fin 4 → ℂ) (c : Fin 3 → ℂ),
      (∀ z, p.eval z = 0 ↔ ∃ i, r i = z) ∧
      (∀ z, p.derivative.eval z = 0 ↔ ∃ j, c j = z) ∧
      (∀ u v : Fin 4 ⊕ Fin 3, u ≠ v →
        (1 / 4 : ℝ) < dist (Sum.elim r c u) (Sum.elim r c v))) ∧
    p.derivative.eval 1 = 0 ∧ p.derivative.eval (-1) = 0 ∧
    p.eval 1 ≠ p.eval (-1) ∧
    ‖p.eval 1 - p.eval (-1)‖ < (3 : ℝ) * ((1 / 4 : ℝ) / 4) ^ 4 := by
  refine ⟨monic_p, degree_p, separated_enumerations, ?_, ?_,
    critical_values_distinct, ?_⟩
  · exact (derivative_root_iff 1).mpr (Or.inr (Or.inr rfl))
  · exact (derivative_root_iff (-1)).mpr (Or.inl rfl)
  · simpa [degree_p] using strict_violation

end ErdosProblems.Erdos1041.SeparationCounterexampleR13
