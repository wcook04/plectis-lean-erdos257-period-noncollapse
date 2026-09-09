import ErdosProblems.Erdos68.CompanionOrbitRationality

/-!
# Erdős's shifted-factorial family under one companion-orbit boundary

Erdős asked whether `S_t = ∑_{n≥2} 1/(n!+t)` is irrational for every integer
`t`; Problem #68 is the member `t = −1`.  The termwise identity

`1/(n!+t) = 1/n! − t/(n!(n!+t))`

writes every member as `S_t = (e − 2) − t·C_t` with the shifted companion
constant `C_t = ∑_{n≥2} 1/(n!(n!+t))`.  The generic fixed-orbit boundary of
`CompanionOrbitRationality` therefore applies uniformly: for every integer
`t ≥ −1`,

`S_t ∈ ℚ  ⟺  ⌈t·m!·C_t⌉ ≡ 2 (mod m)  for all sufficiently large m`,

equivalently `S_t ∉ ℚ` iff the ceiling escapes the residue `2` cofinally.
The member `t = −1` recovers `⌊m!·C⌋ ≡ −2 (mod m)`, and the member `t = 0`
has `C_0`-orbit `⌈0⌉ = 0`, which never lies in the residue class `2` for
`m ≥ 3`; this reproves the irrationality of `e`.

No member with `t ≠ 0` is decided here.  The theorem is the exact family
boundary, not an irrationality proof for any nonzero shift.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- The shifted factorial-gap term `1/(n!+t)`, anchored at `n ≥ 2`. -/
noncomputable def shiftGapTerm (t : ℤ) (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n.factorial : ℝ) + (t : ℝ)) else 0

/-- The shifted companion term `1/(n!(n!+t))`, anchored at `n ≥ 2`. -/
noncomputable def shiftCompanionTerm (t : ℤ) (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n.factorial : ℝ) * ((n.factorial : ℝ) + (t : ℝ))) else 0

/-- Erdős's shifted series `S_t = ∑_{n≥2} 1/(n!+t)`. -/
noncomputable def shiftGapSeries (t : ℤ) : ℝ :=
  ∑' n : ℕ, shiftGapTerm t n

/-- The shifted companion constant `C_t = ∑_{n≥2} 1/(n!(n!+t))`. -/
noncomputable def shiftCompanionConstant (t : ℤ) : ℝ :=
  ∑' n : ℕ, shiftCompanionTerm t n

/-- For `t ≥ −1` and `n ≥ 2` the shifted denominator dominates `n! − 1 ≥ 1`. -/
private theorem factorial_sub_one_le_add_shift {t : ℤ} (ht : -1 ≤ t)
    {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) ≤ (n.factorial : ℝ) - 1 ∧
      (n.factorial : ℝ) - 1 ≤ (n.factorial : ℝ) + (t : ℝ) := by
  have hfac : (2 : ℕ) ≤ n.factorial := by
    calc
      2 = (2 : ℕ).factorial := by norm_num
      _ ≤ n.factorial := Nat.factorial_le hn
  have hfacR : (2 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast hfac
  have htR : (-1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  constructor <;> linarith

/-- Termwise decomposition `1/(n!+t) = 1/n! − t/(n!(n!+t))`. -/
theorem shiftGapTerm_eq_unitFact_sub_mul {t : ℤ} (ht : -1 ≤ t) (n : ℕ) :
    shiftGapTerm t n = unitFactTerm n - (t : ℝ) * shiftCompanionTerm t n := by
  by_cases hn : 2 ≤ n
  · rw [shiftGapTerm, if_pos hn, unitFactTerm, if_pos hn,
      shiftCompanionTerm, if_pos hn]
    obtain ⟨h1, h2⟩ := factorial_sub_one_le_add_shift ht hn
    have hF : (n.factorial : ℝ) ≠ 0 := by positivity
    have hFt : (n.factorial : ℝ) + (t : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  · simp [shiftGapTerm, unitFactTerm, shiftCompanionTerm, hn]

theorem summable_shiftGapTerm {t : ℤ} (ht : -1 ≤ t) :
    Summable (shiftGapTerm t) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    summable_invFactSubOneTerm
  · by_cases hn : 2 ≤ n
    · rw [shiftGapTerm, if_pos hn]
      obtain ⟨h1, h2⟩ := factorial_sub_one_le_add_shift ht hn
      exact one_div_nonneg.mpr (by linarith)
    · simp [shiftGapTerm, hn]
  · by_cases hn : 2 ≤ n
    · rw [shiftGapTerm, if_pos hn]
      obtain ⟨h1, h2⟩ := factorial_sub_one_le_add_shift ht hn
      simp only [invFactSubOneTerm, Set.indicator, Set.mem_setOf_eq, hn,
        if_true]
      push_cast
      exact one_div_le_one_div_of_le (by linarith) h2
    · simp [shiftGapTerm, invFactSubOneTerm, Set.indicator, hn]

theorem summable_shiftCompanionTerm {t : ℤ} (ht : -1 ≤ t) :
    Summable (shiftCompanionTerm t) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    summable_compConstTerm
  · by_cases hn : 2 ≤ n
    · rw [shiftCompanionTerm, if_pos hn]
      obtain ⟨h1, h2⟩ := factorial_sub_one_le_add_shift ht hn
      exact one_div_nonneg.mpr (mul_nonneg (by positivity) (by linarith))
    · simp [shiftCompanionTerm, hn]
  · by_cases hn : 2 ≤ n
    · rw [shiftCompanionTerm, if_pos hn, compConstTerm, if_pos hn]
      obtain ⟨h1, h2⟩ := factorial_sub_one_le_add_shift ht hn
      push_cast
      apply one_div_le_one_div_of_le
      · exact mul_pos (by positivity) (by linarith)
      · exact mul_le_mul_of_nonneg_left h2 (by positivity)
    · simp [shiftCompanionTerm, compConstTerm, hn]

/-- **Family decomposition.**  `S_t = (−t·C_t) + (e − 2)` in the anchored
form used by the generic companion-orbit boundary. -/
theorem shiftGapSeries_eq_neg_mul_companion_add_unitFact {t : ℤ} (ht : -1 ≤ t) :
    shiftGapSeries t =
      (-(t : ℝ) * shiftCompanionConstant t) + ∑' n : ℕ, unitFactTerm n := by
  unfold shiftGapSeries shiftCompanionConstant
  have hterm : shiftGapTerm t = fun n =>
      unitFactTerm n - (t : ℝ) * shiftCompanionTerm t n := by
    funext n
    exact shiftGapTerm_eq_unitFact_sub_mul ht n
  rw [hterm, summable_unitFactTerm.tsum_sub
    ((summable_shiftCompanionTerm ht).mul_left (t : ℝ)), tsum_mul_left]
  ring

/-- Pointwise translation between the floor residue of the generic boundary
and the ceiling residue of the shifted orbit. -/
theorem facFloor_neg_mul_add_two_emod_eq_zero_iff (t : ℤ) (K : ℝ) (m : ℕ) :
    ((facFloor (-(t : ℝ) * K) m + 2 : ℤ) % (m : ℤ)) = 0 ↔
      (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * K⌉ - 2 := by
  have hrewrite : (m.factorial : ℝ) * (-(t : ℝ) * K) =
      -((t : ℝ) * (m.factorial : ℝ) * K) := by ring
  unfold facFloor
  rw [hrewrite, Int.floor_neg, ← Int.dvd_iff_emod_eq_zero]
  have hneg : -⌈(t : ℝ) * (m.factorial : ℝ) * K⌉ + 2 =
      -(⌈(t : ℝ) * (m.factorial : ℝ) * K⌉ - 2) := by ring
  rw [hneg, dvd_neg]

/-- **Uniform family boundary.**  For every integer `t ≥ −1`, the shifted
series `S_t` is rational exactly when `⌈t·m!·C_t⌉ ≡ 2 (mod m)` for all
sufficiently large `m`. -/
theorem not_irrational_shiftGapSeries_iff_eventually_ceil_residue_two
    {t : ℤ} (ht : -1 ≤ t) :
    ¬ Irrational (shiftGapSeries t) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2 := by
  rw [shiftGapSeries_eq_neg_mul_companion_add_unitFact ht,
    not_irrational_add_unitFact_iff_eventually_facFloor_mod_neg_two]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun m hm =>
      (facFloor_neg_mul_add_two_emod_eq_zero_iff t _ m).mp (hM m hm)⟩
  · rintro ⟨M, hM⟩
    exact ⟨M, fun m hm =>
      (facFloor_neg_mul_add_two_emod_eq_zero_iff t _ m).mpr (hM m hm)⟩

/-- **Uniform family boundary, escape form.**  `S_t` is irrational exactly
when the shifted ceiling orbit escapes the residue `2` cofinally. -/
theorem irrational_shiftGapSeries_iff_cofinal_ceil_residue_misses
    {t : ℤ} (ht : -1 ≤ t) :
    Irrational (shiftGapSeries t) ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2 := by
  constructor
  · intro hirr B
    by_contra hnone
    push Not at hnone
    exact (not_irrational_shiftGapSeries_iff_eventually_ceil_residue_two ht).mpr
      ⟨B + 1, fun m hm => hnone m (by omega)⟩ hirr
  · intro hcof
    by_contra hrat
    obtain ⟨M, hM⟩ :=
      (not_irrational_shiftGapSeries_iff_eventually_ceil_residue_two ht).mp hrat
    obtain ⟨m, hm, hmiss⟩ := hcof M
    exact hmiss (hM m (by omega))

/-- The member `t = −1` is the Erdős #68 series. -/
theorem shiftGapSeries_neg_one_eq_factorialGapSeries :
    shiftGapSeries (-1) = _root_.Erdos68.factorialGapSeries := by
  unfold shiftGapSeries _root_.Erdos68.factorialGapSeries
    _root_.Erdos68.factorialGapTail
  apply tsum_congr
  intro d
  unfold shiftGapTerm _root_.Erdos68.factorialGapTailTerm
  by_cases hd : 2 ≤ d
  · rw [if_pos hd, if_pos (by omega : 1 < d)]
    push_cast
    ring_nf
  · rw [if_neg hd, if_neg (by omega : ¬ 1 < d)]

/-- The member `t = 0` is `e − 2`. -/
theorem shiftGapSeries_zero_eq_exp_one_sub_two :
    shiftGapSeries 0 = Real.exp 1 - 2 := by
  rw [← tsum_unitFactTerm_eq_exp_one_sub_two]
  unfold shiftGapSeries
  apply tsum_congr
  intro n
  unfold shiftGapTerm unitFactTerm
  by_cases hn : 2 ≤ n <;> simp [hn]

/-- The family boundary decides the member `t = 0`: the orbit `⌈0⌉ = 0` never
lies in the residue class `2` once `m ≥ 3`, so `e − 2`, hence `e`, is
irrational. -/
theorem irrational_shiftGapSeries_zero : Irrational (shiftGapSeries 0) := by
  rw [irrational_shiftGapSeries_iff_cofinal_ceil_residue_misses (by norm_num)]
  intro B
  refine ⟨B + 3, by omega, ?_⟩
  intro hdvd
  simp only [Int.cast_zero, zero_mul, Int.ceil_zero, zero_sub] at hdvd
  have habs := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2)
    ((dvd_neg).mp hdvd)
  omega

theorem irrational_exp_one_of_family_boundary : Irrational (Real.exp 1) := by
  have h := irrational_shiftGapSeries_zero
  rw [shiftGapSeries_zero_eq_exp_one_sub_two] at h
  exact Irrational.of_sub_intCast 2 (by simpa using h)

#print axioms shiftGapSeries_eq_neg_mul_companion_add_unitFact
#print axioms not_irrational_shiftGapSeries_iff_eventually_ceil_residue_two
#print axioms irrational_shiftGapSeries_iff_cofinal_ceil_residue_misses
#print axioms shiftGapSeries_neg_one_eq_factorialGapSeries
#print axioms shiftGapSeries_zero_eq_exp_one_sub_two
#print axioms irrational_shiftGapSeries_zero
#print axioms irrational_exp_one_of_family_boundary

end ErdosProblems.Erdos68
