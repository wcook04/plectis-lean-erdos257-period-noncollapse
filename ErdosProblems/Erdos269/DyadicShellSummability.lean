import ErdosProblems.Erdos269.DyadicOrderedTailRecurrence

/-!
# Erdős #269: summability of the actual dyadic shell masses

The ordered source digit has a deliberately coarse quadratic majorant.  The
key point is structural: in a multiplicative interval of width two, fixing the
`3`- and `5`-exponents determines the `2`-exponent, while both odd exponents
are smaller than the dyadic scale.  This gives at most `(a+1)^2` shell points.
-/

namespace ErdosProblems.Erdos269

/-- A half-open dyadic `{2,3,5}`-smooth shell contains at most `(a+1)^2`
exponent triples. -/
theorem dyadicSmoothShell235_card_le_square (a : ℕ) :
    (dyadicSmoothShell235 a).card ≤ (a + 1) ^ 2 := by
  classical
  let target := (Finset.range (a + 1)).product (Finset.range (a + 1))
  have hcard : (dyadicSmoothShell235 a).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn
      (fun e : ℕ × ℕ × ℕ => e.2) ?_ ?_
    · intro e he
      rcases e with ⟨i, j, k⟩
      have hshell := mem_dyadicSmoothShell235_iff.mp he
      change 2 ^ a ≤ smooth3Val 2 3 5 i j k ∧
        smooth3Val 2 3 5 i j k < 2 ^ (a + 1) at hshell
      have hpos : 0 < smooth3Val 2 3 5 i j k := by
        simp [smooth3Val]
      have hjDvd : 3 ^ j ∣ smooth3Val 2 3 5 i j k := by
        refine ⟨2 ^ i * 5 ^ k, ?_⟩
        simp [smooth3Val]
        ring
      have hkDvd : 5 ^ k ∣ smooth3Val 2 3 5 i j k := by
        refine ⟨2 ^ i * 3 ^ j, ?_⟩
        simp [smooth3Val]
        ring
      have hj : j < a + 1 := by
        by_contra hnot
        have haj : a + 1 ≤ j := Nat.le_of_not_gt hnot
        have hpowExp : 2 ^ (a + 1) ≤ 2 ^ j :=
          Nat.pow_le_pow_right (by norm_num) haj
        have hpowBase : 2 ^ j ≤ 3 ^ j :=
          Nat.pow_le_pow_left (by norm_num) j
        have hdivLe := Nat.le_of_dvd hpos hjDvd
        exact (not_lt_of_ge (hpowExp.trans (hpowBase.trans hdivLe))) hshell.2
      have hk : k < a + 1 := by
        by_contra hnot
        have hak : a + 1 ≤ k := Nat.le_of_not_gt hnot
        have hpowExp : 2 ^ (a + 1) ≤ 2 ^ k :=
          Nat.pow_le_pow_right (by norm_num) hak
        have hpowBase : 2 ^ k ≤ 5 ^ k :=
          Nat.pow_le_pow_left (by norm_num) k
        have hdivLe := Nat.le_of_dvd hpos hkDvd
        exact (not_lt_of_ge (hpowExp.trans (hpowBase.trans hdivLe))) hshell.2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hk⟩
    · intro e₁ he₁ e₂ he₂ hproj
      rcases e₁ with ⟨i₁, j₁, k₁⟩
      rcases e₂ with ⟨i₂, j₂, k₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      have hshell₁ := mem_dyadicSmoothShell235_iff.mp he₁
      have hshell₂ := mem_dyadicSmoothShell235_iff.mp he₂
      have hi : i₁ = i₂ := exponent_unique_in_short_interval
        (base := 2) (lo := 2 ^ a) (hi := 2 ^ (a + 1))
        (weight := 3 ^ j₁ * 5 ^ k₁)
        (by norm_num)
        (by rw [pow_succ]; simp [Nat.mul_comm])
        (by simpa [smooth3Val, mul_assoc] using hshell₁.1)
        (by simpa [smooth3Val, mul_assoc] using hshell₁.2)
        (by simpa [smooth3Val, mul_assoc] using hshell₂.1)
        (by simpa [smooth3Val, mul_assoc] using hshell₂.2)
      simp [hi]
  simpa [target, pow_two] using hcard

/-- The exact ordered block digit is at most fifteen times the shell
cardinality: each threshold count is the cardinality of a filter. -/
theorem dyadicOrderedBlockDigit235_le_fifteen_mul_card (a : ℕ) :
    dyadicOrderedBlockDigit235 a ≤ 15 * (dyadicSmoothShell235 a).card := by
  have hthree := Finset.card_filter_le (dyadicSmoothShell235 a)
    (fun e => smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      3 ^ Nat.log 3 (2 ^ (a + 1)))
  have hfive := Finset.card_filter_le (dyadicSmoothShell235 a)
    (fun e => smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      5 ^ Nat.log 5 (2 ^ (a + 1)))
  unfold dyadicOrderedBlockDigit235 dyadicBeforeThresholdCount235
  split_ifs <;> omega

/-- A simple all-scale quadratic digit majorant. -/
theorem dyadicOrderedBlockDigit235_le_quadratic (a : ℕ) :
    dyadicOrderedBlockDigit235 a ≤ 15 * (a + 1) ^ 2 :=
  (dyadicOrderedBlockDigit235_le_fifteen_mul_card a).trans
    (Nat.mul_le_mul_left 15 (dyadicSmoothShell235_card_le_square a))

/-- The dyadic endpoint height contains its complete binary factor. -/
theorem pow_two_succ_le_threePrimeHeight235 (a : ℕ) :
    2 ^ (a + 1) ≤ threePrimeHeight 2 3 5 (2 ^ (a + 1)) := by
  unfold threePrimeHeight
  rw [Nat.log_pow (by norm_num : 1 < 2)]
  exact (Nat.le_mul_of_pos_right _ (by positivity)).trans
    (Nat.le_mul_of_pos_right _ (by positivity))

/-- The real shell masses are nonnegative. -/
theorem dyadicShellMassR235_nonneg (a : ℕ) :
    0 ≤ dyadicShellMassR235 a := by
  unfold dyadicShellMassR235 dyadicShellMassQ235
  positivity

/-- Polynomial-times-geometric all-scale majorant for the literal shell mass. -/
theorem dyadicShellMassR235_le_majorant (a : ℕ) :
    dyadicShellMassR235 a ≤
      30 * (((a + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (a + 1)) := by
  let H : ℝ := threePrimeHeight 2 3 5 (2 ^ (a + 1))
  let d : ℝ := dyadicOrderedBlockDigit235 a
  have hHpos : 0 < H := by
    dsimp [H]
    norm_num [threePrimeHeight]
  have hmass := half_threePrimeHeight_mul_dyadicShellMassR235 a
  have hmassEq : dyadicShellMassR235 a = 2 * d / H := by
    apply (eq_div_iff (ne_of_gt hHpos)).2
    dsimp [H, d] at hmass ⊢
    field_simp at hmass
    nlinarith
  have hd : d ≤ 15 * (((a + 1 : ℕ) : ℝ) ^ 2) := by
    dsimp [d]
    exact_mod_cast dyadicOrderedBlockDigit235_le_quadratic a
  have hH : (2 : ℝ) ^ (a + 1) ≤ H := by
    dsimp [H]
    exact_mod_cast pow_two_succ_le_threePrimeHeight235 a
  rw [hmassEq]
  calc
    2 * d / H ≤ 2 * (15 * (((a + 1 : ℕ) : ℝ) ^ 2)) / H := by
      exact div_le_div_of_nonneg_right (by nlinarith) hHpos.le
    _ ≤ 2 * (15 * (((a + 1 : ℕ) : ℝ) ^ 2)) / (2 : ℝ) ^ (a + 1) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hH
    _ = 30 * (((a + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (a + 1)) := by
      rw [one_div_pow]
      ring

/-- The actual all-scale dyadic shell masses are summable. -/
theorem summable_dyadicShellMassR235 : Summable dyadicShellMassR235 := by
  have hpoly : Summable
      (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
  have hshift : Summable
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2) *
        (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa only [Function.comp_apply, Nat.add_comm] using
      hpoly.comp_injective (add_right_injective 1)
  have hmajor : Summable
      (fun n : ℕ => 30 * ((((n + 1 : ℕ) : ℝ) ^ 2) *
        (1 / 2 : ℝ) ^ (n + 1))) := hshift.mul_left 30
  refine Summable.of_nonneg_of_le dyadicShellMassR235_nonneg ?_ hmajor
  exact dyadicShellMassR235_le_majorant

/-- The literal infinite tail beginning at dyadic shell `a`. -/
noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)

/-- The actual convergent shell tail splits into its first shell and the next
tail.  Thus the source decomposition required by the radix recurrence is not
an abstract hypothesis. -/
theorem dyadicShellTsumTailR235_eq_shell_add (a : ℕ) :
    dyadicShellTsumTailR235 a =
      dyadicShellMassR235 a + dyadicShellTsumTailR235 (a + 1) := by
  have ha : Summable (fun n : ℕ => dyadicShellMassR235 (a + n)) :=
    summable_dyadicShellMassR235.comp_injective fun _ _ h =>
      Nat.add_left_cancel h
  have hsplit := ha.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hsplit
  unfold dyadicShellTsumTailR235
  simpa only [Nat.add_zero, Nat.add_assoc, Nat.one_add] using hsplit.symm

/-- The genuine infinite dyadic-shell tail obeys the exact ordered affine
radix recurrence at every scale. -/
theorem dyadicNormalizedShellTsumTailR235_succ (a : ℕ) :
    dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (a + 1) =
      dyadicBlockBase235 a *
          dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a -
        dyadicOrderedBlockDigit235 a :=
  dyadicNormalizedTailStateR235_succ dyadicShellTsumTailR235
    dyadicShellTsumTailR235_eq_shell_add a

/-- The bounded-radix escape theorem now applies to the genuine infinite
source tail, with no abstract tail or digit input left.  The sole surviving
branch is an exact integral normalized state. -/
theorem dyadicShellTsumTail_integer_or_cofinal_far :
    (∃ a : ℕ, ∃ z : ℤ,
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a = (z : ℝ)) ∨
      ∀ a₀, ∃ a, a₀ ≤ a ∧
        FarFromIntegers
          (dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a)
          ((1 : ℝ) / 31) := by
  apply dyadicBlockBase235_integer_or_cofinal_far
    (fun a => (dyadicOrderedBlockDigit235 a : ℤ))
  intro a
  simpa using dyadicNormalizedShellTsumTailR235_succ a

end ErdosProblems.Erdos269
