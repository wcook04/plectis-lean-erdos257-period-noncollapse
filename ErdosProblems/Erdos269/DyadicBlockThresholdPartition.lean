import ErdosProblems.Erdos269.DyadicBlockMassIdentity
import ErdosProblems.Erdos269.ThreePrimeRunningLcm

/-!
# Erdős #269: all-scale internal-threshold partition

The preceding block-mass module proves that every cleared dyadic-shell term is
`2` times an odd suffix product.  Here that suffix is identified pointwise and
then summed: the only tests are whether the smooth point lies before the unique
internal `3`-power and `5`-power thresholds.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- A logarithmic coordinate can rise by at most one across a dyadic block, so
its power suffix is either `1` or the base itself.  The latter occurs exactly
before the new pure-power threshold. -/
theorem pow_log_dyadic_suffix_eq_if
    {p a x : ℕ} (hp : 2 ≤ p) (hx : 0 < x)
    (hlower : 2 ^ a ≤ x) (hupper : x < 2 ^ (a + 1)) :
    p ^ (Nat.log p (2 ^ (a + 1)) - Nat.log p x) =
      if x < p ^ Nat.log p (2 ^ (a + 1)) then p else 1 := by
  have hpOne : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hlogLower : Nat.log p (2 ^ a) ≤ Nat.log p x :=
    Nat.log_mono_right hlower
  have hlogUpper : Nat.log p x ≤ Nat.log p (2 ^ (a + 1)) :=
    Nat.log_mono_right hupper.le
  have hstep := log_dyadic_succ_le (a := a) hp
  by_cases hthreshold : x < p ^ Nat.log p (2 ^ (a + 1))
  · have hlt : Nat.log p x < Nat.log p (2 ^ (a + 1)) :=
      (Nat.log_lt_iff_lt_pow hpOne (Nat.ne_of_gt hx)).2 hthreshold
    have hdiff : Nat.log p (2 ^ (a + 1)) - Nat.log p x = 1 := by omega
    simp [hthreshold, hdiff]
  · have hnlt : ¬ Nat.log p x < Nat.log p (2 ^ (a + 1)) := by
      intro hlt
      exact hthreshold ((Nat.log_lt_iff_lt_pow hpOne (Nat.ne_of_gt hx)).1 hlt)
    have heq : Nat.log p x = Nat.log p (2 ^ (a + 1)) := by omega
    simp [hthreshold, heq]

/-- Indicator form of the odd suffix product for an actual shell point. -/
theorem oddHeightSuffix235_eq_thresholdFactors
    {a : ℕ} {e : ℕ × ℕ × ℕ} (he : e ∈ dyadicSmoothShell235 a) :
    oddHeightSuffix235 a e =
      (if smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
          3 ^ Nat.log 3 (2 ^ (a + 1)) then 3 else 1) *
      (if smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
          5 ^ Nat.log 5 (2 ^ (a + 1)) then 5 else 1) := by
  have hshell := mem_dyadicSmoothShell235_iff.mp he
  have hx : 0 < smooth3Val 2 3 5 e.1 e.2.1 e.2.2 := by
    simp [smooth3Val]
  unfold oddHeightSuffix235
  rw [pow_log_dyadic_suffix_eq_if (by norm_num : 2 ≤ 3) hx hshell.1 hshell.2,
    pow_log_dyadic_suffix_eq_if (by norm_num : 2 ≤ 5) hx hshell.1 hshell.2]

/-- The half-height-cleared mass of the actual dyadic smooth shell. -/
def dyadicHalfClearedMass235 (a : ℕ) : ℕ :=
  ∑ e ∈ dyadicSmoothShell235 a, oddHeightSuffix235 a e

/-- Number of shell points before the new `p`-power threshold. -/
def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card

/-- Number of shell points lying before both odd-channel thresholds. -/
def dyadicBeforeBothThresholdsCount235 (a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
        3 ^ Nat.log 3 (2 ^ (a + 1)) ∧
      smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
        5 ^ Nat.log 5 (2 ^ (a + 1))).card

/-- Generic two-threshold summation identity specialized to weights `3` and
`5`. -/
theorem sum_three_five_thresholdFactors
    (s : Finset (ℕ × ℕ × ℕ)) (P Q : (ℕ × ℕ × ℕ) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (∑ e ∈ s, (if P e then 3 else 1) * (if Q e then 5 else 1)) =
      s.card + 2 * (s.filter P).card + 4 * (s.filter Q).card +
        8 * (s.filter fun e => P e ∧ Q e).card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert x s hx ih =>
      by_cases hP : P x <;> by_cases hQ : Q x <;>
        rw [Finset.sum_insert hx, ih] <;>
        simp [Finset.filter_insert, hx, hP, hQ] <;> omega

/-- **All-scale threshold partition.**  The actual half-cleared block mass is
the shell cardinality plus the `3`-threshold correction, the `5`-threshold
correction, and their interaction.  This is the source-faithful summation
formula behind the checker's ordered suffix corrections. -/
theorem dyadicHalfClearedMass235_eq_thresholdCounts (a : ℕ) :
    dyadicHalfClearedMass235 a =
      (dyadicSmoothShell235 a).card +
        2 * dyadicBeforeThresholdCount235 3 a +
        4 * dyadicBeforeThresholdCount235 5 a +
        8 * dyadicBeforeBothThresholdsCount235 a := by
  classical
  unfold dyadicHalfClearedMass235
  rw [Finset.sum_congr rfl (fun e he => oddHeightSuffix235_eq_thresholdFactors he)]
  exact sum_three_five_thresholdFactors
    (dyadicSmoothShell235 a)
    (fun e => smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      3 ^ Nat.log 3 (2 ^ (a + 1)))
    (fun e => smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      5 ^ Nat.log 5 (2 ^ (a + 1)))

/-- If the new `3`-power occurs first, being before both odd thresholds is
exactly being before the `3`-threshold. -/
theorem dyadicBeforeBothThresholdsCount235_eq_three
    {a : ℕ}
    (horder : 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤
      5 ^ Nat.log 5 (2 ^ (a + 1))) :
    dyadicBeforeBothThresholdsCount235 a =
      dyadicBeforeThresholdCount235 3 a := by
  unfold dyadicBeforeBothThresholdsCount235 dyadicBeforeThresholdCount235
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, hthree, -⟩
    exact ⟨he, hthree⟩
  · rintro ⟨he, hthree⟩
    exact ⟨he, hthree, lt_of_lt_of_le hthree horder⟩

/-- If the new `5`-power occurs first, being before both odd thresholds is
exactly being before the `5`-threshold. -/
theorem dyadicBeforeBothThresholdsCount235_eq_five
    {a : ℕ}
    (horder : 5 ^ Nat.log 5 (2 ^ (a + 1)) ≤
      3 ^ Nat.log 3 (2 ^ (a + 1))) :
    dyadicBeforeBothThresholdsCount235 a =
      dyadicBeforeThresholdCount235 5 a := by
  unfold dyadicBeforeBothThresholdsCount235 dyadicBeforeThresholdCount235
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, -, hfive⟩
    exact ⟨he, hfive⟩
  · rintro ⟨he, hfive⟩
    exact ⟨he, lt_of_lt_of_le hfive horder, hfive⟩

/-- The source-faithful ordered block digit.  Its coefficients are the suffix
products from processing the later odd jump first: `10,4` when the `3`-jump
precedes the `5`-jump, and `2,12` in the reverse order. -/
def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a

/-- **All-scale ordered source identity.**  The half-cleared mass is exactly
the ordered suffix-correction digit, for every dyadic scale. -/
theorem dyadicHalfClearedMass235_eq_orderedBlockDigit235 (a : ℕ) :
    dyadicHalfClearedMass235 a = dyadicOrderedBlockDigit235 a := by
  rw [dyadicHalfClearedMass235_eq_thresholdCounts]
  unfold dyadicOrderedBlockDigit235
  by_cases horder : 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤
      5 ^ Nat.log 5 (2 ^ (a + 1))
  · rw [if_pos horder, dyadicBeforeBothThresholdsCount235_eq_three horder]
    omega
  · have hreverse : 5 ^ Nat.log 5 (2 ^ (a + 1)) ≤
        3 ^ Nat.log 3 (2 ^ (a + 1)) := by omega
    rw [if_neg horder, dyadicBeforeBothThresholdsCount235_eq_five hreverse]
    omega

end ErdosProblems.Erdos269
