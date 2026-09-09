import ErdosProblems.Erdos68.CarryCongruenceNormalForm
import ErdosProblems.Erdos68.GapScalarNormalForm

/-!
# Erdős #68: companion-constant telescope and lower-window certificate

Two completions of the carry congruence normal form.

**Telescope.**  With `d_n = 1/(n!(n!−1))` for `n ≥ 2` and the factorial-gap
series `S = ∑_{n≥2} 1/(n!−1)`:

`(∑' d_n) + (∑' 1/n!) = S`,

via the pointwise identity `d_n + 1/n! = 1/(n!−1)`.  Naming the second
series `e − 2` analytically, this reads `C_∞ = S − (e − 2)`: the carry
congruence normal form tests congruences of one fixed constant whose
irrationality-flavor is tied to `e`.

**Lower-window certificate.**  The gap-scalar expansion gave an upper-jump
miss certificate from below-domination; here we add the symmetric
lower-cylinder one: if the finite weighted digit block through `m+k`
together with its explicit remainder weight stays `≤ (1+ε_m)/m`, then index
`m` cannot be a unit carry — also a frontier miss.  Together both windows
certify every non-unit carry from finitely many certified digits.

No cofinality claim is made here.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- Companion-constant term, anchored at `n ≥ 2`. -/
noncomputable def compConstTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (1 : ℝ) /
      ((((n.factorial : ℕ) : ℝ)) *
        ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0

/-- Unit-fractional term `1/(n!−1)`, anchored at `n ≥ 2`. -/
noncomputable def invFactSubOneTerm (n : ℕ) : ℝ :=
  Set.indicator {d : ℕ | 2 ≤ d} (fun k =>
    (1 : ℝ) / ((((k.factorial : ℤ) - 1 : ℤ) : ℝ))) n

/-- Unit-factorial term `1/n!`, anchored at `n ≥ 2`. -/
noncomputable def unitFactTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ)) else 0

theorem summable_invFactSubOneTerm : Summable invFactSubOneTerm := by
  have hbase := _root_.Erdos68.summable_one_div_factorial_sub_one
  have h := hbase.indicator {d : ℕ | 2 ≤ d}
  exact h.congr (fun n => by simp [invFactSubOneTerm, Set.indicator])

theorem summable_unitFactTerm : Summable unitFactTerm := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n.factorial : ℝ)) := by
    have h :=
      NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) (1 : ℝ)
    simpa [div_eq_mul_inv] using h
  have h := hbase.indicator {n : ℕ | 2 ≤ n}
  refine h.congr fun n => ?_
  simp [unitFactTerm, Set.indicator]

theorem summable_compConstTerm : Summable compConstTerm := by
  have hdv : Summable fun n : ℕ => (1 / (2 : ℝ)) * invFactSubOneTerm n :=
    summable_invFactSubOneTerm.mul_left (1 / (2 : ℝ))
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hdv
  · by_cases hn : 2 ≤ n
    · rw [compConstTerm, if_pos hn]
      push_cast
      have hfac : (1 : ℝ) < (n.factorial : ℝ) := by
        exact_mod_cast Nat.one_lt_factorial.mpr hn
      apply one_div_nonneg.mpr
      exact mul_nonneg (by positivity) (by linarith)
    · simp [compConstTerm, hn]
  by_cases hn : 2 ≤ n
  · rw [compConstTerm, if_pos hn]
    simp [invFactSubOneTerm, Set.indicator, hn]
    have hfac2 : (2 : ℝ) ≤ (n.factorial : ℝ) := by
      have hnat : (2 : ℕ) ≤ n.factorial := by
        calc
          2 = (2 : ℕ).factorial := by norm_num
          _ ≤ n.factorial := Nat.factorial_le hn
      norm_cast
    have hgap : (0 : ℝ) < (n.factorial : ℝ) - 1 := by linarith
    have hinv : ((n.factorial : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) hfac2
    have hgapInv : 0 ≤ ((n.factorial : ℝ) - 1)⁻¹ := by positivity
    simpa [div_eq_mul_inv, mul_comm] using
      (mul_le_mul_of_nonneg_left hinv hgapInv)
  · simp [compConstTerm, invFactSubOneTerm, Set.indicator, hn]

/-- **Telescope identity.**  The companion constant series plus the unit-
factorial series reproduces the Erdős #68 series termwise. -/
theorem companion_tsum_add_unitFact_eq_series :
    (∑' n : ℕ, compConstTerm n) + (∑' n : ℕ, unitFactTerm n)
      = _root_.Erdos68.factorialGapSeries := by
  classical
  rw [← summable_compConstTerm.tsum_add summable_unitFactTerm]
  refine tsum_congr fun n => ?_
  by_cases hn : 2 ≤ n
  · rw [compConstTerm, if_pos hn, unitFactTerm, if_pos hn]
    rw [_root_.Erdos68.factorialGapTailTerm, if_pos (by omega : 1 < n)]
    push_cast
    have hgap : (0 : ℝ) < (n.factorial : ℝ) - 1 := by
      have hfac : (1 : ℝ) < (n.factorial : ℝ) := by
        exact_mod_cast Nat.one_lt_factorial.mpr hn
      linarith
    field_simp [ne_of_gt hgap]
    ring
  · rw [compConstTerm, if_neg hn, unitFactTerm, if_neg hn]
    rw [_root_.Erdos68.factorialGapTailTerm, if_neg (by omega : ¬1 < n)]
    norm_num

/-- **Lower-window certificate.**  If the finite weighted carry stream from
`m` through `m+k`, augmented by its explicit remainder weight, stays below
`(1+ε_m)/m`, then index `m` sits in the lower cylinder and is again a
frontier miss. -/
theorem factorialGapStepCarry_ne_one_of_stream_domination_below
    (m : ℕ) (hm : 3 ≤ m) (k : ℕ)
    (hdom :
      (∑ j ∈ Finset.Icc m (m + k),
          (((factorialGapStepCarry j : ℝ) + 1 / ((j.factorial : ℝ) - 1)) *
            (((m - 1).factorial : ℝ) / (j.factorial : ℝ)))) +
        (((m - 1).factorial : ℝ) / ((m + k).factorial : ℝ))
      ≤ (1 + 1 / ((m.factorial : ℝ) - 1)) / (m : ℝ)) :
    factorialGapStepCarry m ≠ 1 := by
  have hm2 : 2 ≤ m := by omega
  have hexact := predGap_eq_carry_stream m hm2 k
  obtain ⟨hremPos, hremLe⟩ := carry_stream_remainder_bounds m hm2 k
  have hsum : ∑ j ∈ Finset.Icc m (m + k),
      (((factorialGapStepCarry j : ℝ) + 1 / ((j.factorial : ℝ) - 1)) *
        (((m - 1).factorial : ℝ) / (j.factorial : ℝ))) <
      factorialGapPredecessorGap m := by
    rw [hexact]
    linarith
  have hmPos : (0 : ℝ) < (m : ℝ) := by positivity
  have hge : factorialGapPredecessorGap m ≤
      (∑ j ∈ Finset.Icc m (m + k),
        (((factorialGapStepCarry j : ℝ) + 1 / ((j.factorial : ℝ) - 1)) *
          (((m - 1).factorial : ℝ) / (j.factorial : ℝ)))) +
        (((m - 1).factorial : ℝ) / ((m + k).factorial : ℝ)) := by
    rw [hexact]
    linarith
  have htle : ((m : ℝ)) * factorialGapPredecessorGap m
      ≤ 1 + 1 / ((m.factorial : ℝ) - 1) := by
    calc
      (m : ℝ) * factorialGapPredecessorGap m ≤
          (m : ℝ) *
            ((∑ j ∈ Finset.Icc m (m + k),
                (((factorialGapStepCarry j : ℝ) +
                    1 / ((j.factorial : ℝ) - 1)) *
                  (((m - 1).factorial : ℝ) / (j.factorial : ℝ)))) +
              (((m - 1).factorial : ℝ) / ((m + k).factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left hge hmPos.le
      _ ≤ (m : ℝ) *
          ((1 + 1 / ((m.factorial : ℝ) - 1)) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hdom hmPos.le
      _ = 1 + 1 / ((m.factorial : ℝ) - 1) := by
        field_simp
  intro hunit
  have hwindow :=
    (factorialGapStepCarry_eq_one_iff_scaled_gap m hm).mp hunit
  linarith [hwindow.1]

#print axioms companion_tsum_add_unitFact_eq_series
#print axioms summable_compConstTerm
#print axioms factorialGapStepCarry_ne_one_of_stream_domination_below

end ErdosProblems.Erdos68
