import ErdosProblems.Erdos269.BlockMassEngines
import ErdosProblems.Erdos269.RestrictedFloorSum

/-!
# Erdős #269: exact dyadic block-mass normalization

The integer checker compresses the smooth numbers in a half-open dyadic shell
`[2^a, 2^(a+1))`.  After clearing by the height at the right endpoint, every
summand contains the terminal dyadic factor `2`.  Dividing that common factor
leaves a suffix product of the zero, one, or two internal odd-prime jumps.

This file kernel-checks the complete cell algebra used by the checker.  The
remaining source-specific step is to identify the cell cardinalities with the
appropriate `strictSmoothShell` filters for every `a`.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- For the positive bases `2,3,5`, the redundant exponent box in
`strictSmoothExponents` imposes no extra condition: strict source membership is
exactly the value inequality. -/
theorem mem_strictSmoothExponents235_iff
    {x : ℕ} {e : ℕ × ℕ × ℕ} :
    e ∈ strictSmoothExponents 2 3 5 x ↔
      smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < x := by
  rcases e with ⟨i, j, k⟩
  constructor
  · intro he
    exact (Finset.mem_filter.mp he).2
  · intro hval
    have hpos : 0 < smooth3Val 2 3 5 i j k := by
      simp [smooth3Val]
    have hiDvd : 2 ^ i ∣ smooth3Val 2 3 5 i j k := by
      refine ⟨3 ^ j * 5 ^ k, ?_⟩
      simp [smooth3Val, mul_assoc]
    have hjDvd : 3 ^ j ∣ smooth3Val 2 3 5 i j k := by
      refine ⟨2 ^ i * 5 ^ k, ?_⟩
      simp [smooth3Val]
      ring
    have hkDvd : 5 ^ k ∣ smooth3Val 2 3 5 i j k := by
      refine ⟨2 ^ i * 3 ^ j, ?_⟩
      simp [smooth3Val]
      ring
    have hi : i < x :=
      (Nat.lt_pow_self (by norm_num : 1 < 2)).trans_le
        ((Nat.le_of_dvd hpos hiDvd).trans hval.le)
    have hj : j < x :=
      (Nat.lt_pow_self (by norm_num : 1 < 3)).trans_le
        ((Nat.le_of_dvd hpos hjDvd).trans hval.le)
    have hk : k < x :=
      (Nat.lt_pow_self (by norm_num : 1 < 5)).trans_le
        ((Nat.le_of_dvd hpos hkDvd).trans hval.le)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hi, Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hk⟩⟩, hval⟩

/-- The actual `{2,3,5}`-smooth exponent points in the half-open dyadic shell
`[2^a,2^(a+1))`. -/
def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))

theorem mem_dyadicSmoothShell235_iff
    {a : ℕ} {e : ℕ × ℕ × ℕ} :
    e ∈ dyadicSmoothShell235 a ↔
      2 ^ a ≤ smooth3Val 2 3 5 e.1 e.2.1 e.2.2 ∧
        smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < 2 ^ (a + 1) := by
  simp only [dyadicSmoothShell235, strictSmoothShell, Finset.mem_sdiff,
    mem_strictSmoothExponents235_iff]
  omega

/-- Every point of the half-open dyadic shell has binary logarithmic
coordinate exactly `a`.  This is the all-scale source fact behind the common
terminal factor `2` in the cleared block mass. -/
theorem log_two_eq_of_mem_dyadicSmoothShell235
    {a : ℕ} {e : ℕ × ℕ × ℕ} (he : e ∈ dyadicSmoothShell235 a) :
    Nat.log 2 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) = a := by
  exact Nat.log_eq_of_pow_le_of_lt_pow
    (mem_dyadicSmoothShell235_iff.mp he).1
    (mem_dyadicSmoothShell235_iff.mp he).2

/-- The odd suffix multiplier remaining between a shell point and the right
endpoint height. -/
def oddHeightSuffix235 (a : ℕ) (e : ℕ × ℕ × ℕ) : ℕ :=
  3 ^ (Nat.log 3 (2 ^ (a + 1)) -
      Nat.log 3 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2)) *
    5 ^ (Nat.log 5 (2 ^ (a + 1)) -
      Nat.log 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2))

/-- **All-scale height factorization.**  For every actual smooth point in a
half-open dyadic shell, the right-endpoint running height is exactly the point
height times `2` and an odd suffix product.  This removes the endpoint and
normalization ambiguity from the source-to-checker bridge at every scale. -/
theorem threePrimeHeight_dyadicShell_factor_two
    {a : ℕ} {e : ℕ × ℕ × ℕ} (he : e ∈ dyadicSmoothShell235 a) :
    threePrimeHeight 2 3 5 (2 ^ (a + 1)) =
      2 * oddHeightSuffix235 a e *
        threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) := by
  let x := smooth3Val 2 3 5 e.1 e.2.1 e.2.2
  have hxUpper : x ≤ 2 ^ (a + 1) := by
    exact (mem_dyadicSmoothShell235_iff.mp he).2.le
  have hlog2 : Nat.log 2 x = a := by
    exact log_two_eq_of_mem_dyadicSmoothShell235 he
  have h3le : Nat.log 3 x ≤ Nat.log 3 (2 ^ (a + 1)) :=
    Nat.log_mono_right hxUpper
  have h5le : Nat.log 5 x ≤ Nat.log 5 (2 ^ (a + 1)) :=
    Nat.log_mono_right hxUpper
  have h3pow :
      3 ^ Nat.log 3 (2 ^ (a + 1)) =
        3 ^ (Nat.log 3 (2 ^ (a + 1)) - Nat.log 3 x) * 3 ^ Nat.log 3 x := by
    rw [← pow_add, Nat.sub_add_cancel h3le]
  have h5pow :
      5 ^ Nat.log 5 (2 ^ (a + 1)) =
        5 ^ (Nat.log 5 (2 ^ (a + 1)) - Nat.log 5 x) * 5 ^ Nat.log 5 x := by
    rw [← pow_add, Nat.sub_add_cancel h5le]
  simp only [threePrimeHeight, oddHeightSuffix235]
  change
    2 ^ Nat.log 2 (2 ^ (a + 1)) *
          3 ^ Nat.log 3 (2 ^ (a + 1)) * 5 ^ Nat.log 5 (2 ^ (a + 1)) =
      2 *
          (3 ^ (Nat.log 3 (2 ^ (a + 1)) - Nat.log 3 x) *
            5 ^ (Nat.log 5 (2 ^ (a + 1)) - Nat.log 5 x)) *
        (2 ^ Nat.log 2 x * 3 ^ Nat.log 3 x * 5 ^ Nat.log 5 x)
  rw [Nat.log_pow (by norm_num : 1 < 2), hlog2, h3pow, h5pow, pow_succ]
  ring

/-- Half of the height-cleared mass when a block contains no odd jump. -/
def halfClearedMassZero (c₀ : ℕ) : ℕ := c₀

/-- Half of the height-cleared mass when the internal jump is `p`.
`c₀` counts shell points before the jump and `c₁` those after it. -/
def halfClearedMassOne (p c₀ c₁ : ℕ) : ℕ := p * c₀ + c₁

/-- Half of the height-cleared mass for ordered internal jumps `p`, then `q`.
The three cell counts lie before `p`, between the jumps, and after `q`. -/
def halfClearedMassTwo (p q c₀ c₁ c₂ : ℕ) : ℕ :=
  p * q * c₀ + q * c₁ + c₂

/-- The one-jump digit formula used by the exact checker. -/
def blockDigitOne (p c₀ c₁ : ℕ) : ℕ :=
  c₀ + c₁ + (p - 1) * c₀

/-- The two-jump digit formula used by the exact checker.  The second
correction sees every point before the second jump. -/
def blockDigitTwo (p q c₀ c₁ c₂ : ℕ) : ℕ :=
  c₀ + c₁ + c₂ + (p - 1) * q * c₀ + (q - 1) * (c₀ + c₁)

theorem halfClearedMassZero_eq (c₀ : ℕ) :
    halfClearedMassZero c₀ = c₀ := rfl

/-- Exact one-jump suffix-product expansion. -/
theorem halfClearedMassOne_eq_blockDigitOne
    {p c₀ c₁ : ℕ} (hp : 1 ≤ p) :
    halfClearedMassOne p c₀ c₁ = blockDigitOne p c₀ c₁ := by
  unfold halfClearedMassOne blockDigitOne
  have hpEq : (p - 1) + 1 = p := Nat.sub_add_cancel hp
  calc
    p * c₀ + c₁ = ((p - 1) + 1) * c₀ + c₁ := by rw [hpEq]
    _ = c₀ + c₁ + (p - 1) * c₀ := by ring

/-- Exact two-jump suffix-product expansion.  This is the cellwise version of
`List.prod_eq_one_add_suffixCorrection` specialized to the only nontrivial
block shape that can occur for the `{2,3,5}` dyadic compression. -/
theorem halfClearedMassTwo_eq_blockDigitTwo
    {p q c₀ c₁ c₂ : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    halfClearedMassTwo p q c₀ c₁ c₂ = blockDigitTwo p q c₀ c₁ c₂ := by
  unfold halfClearedMassTwo blockDigitTwo
  have hpEq : (p - 1) + 1 = p := Nat.sub_add_cancel hp
  have hqEq : (q - 1) + 1 = q := Nat.sub_add_cancel hq
  have hqC₀ : q * c₀ = c₀ + (q - 1) * c₀ := by
    calc
      q * c₀ = ((q - 1) + 1) * c₀ := by rw [hqEq]
      _ = c₀ + (q - 1) * c₀ := by ring
  have hqC₁ : q * c₁ = c₁ + (q - 1) * c₁ := by
    calc
      q * c₁ = ((q - 1) + 1) * c₁ := by rw [hqEq]
      _ = c₁ + (q - 1) * c₁ := by ring
  calc
    p * q * c₀ + q * c₁ + c₂ =
        ((p - 1) + 1) * ((q - 1) + 1) * c₀ +
          ((q - 1) + 1) * c₁ + c₂ := by rw [hpEq, hqEq]
    _ = (p - 1) * q * c₀ + q * c₀ + q * c₁ + c₂ := by rw [hqEq]; ring
    _ = c₀ + c₁ + c₂ + (p - 1) * q * c₀ + (q - 1) * (c₀ + c₁) := by
      rw [hqC₀, hqC₁]
      ring

/-- Replacing the included right endpoint (weight `1`) by the included left
endpoint (weight `b`) changes a cleared shell mass by exactly `b-1`.  This is
the normalization that distinguished the checker's half-open shell from the
initial right-closed probe. -/
theorem halfOpenMass_eq_rightClosedMass_add
    {halfOpenMass rightClosedMass b : ℕ}
    (h : halfOpenMass + 1 = rightClosedMass + b) :
    halfOpenMass = rightClosedMass + b - 1 := by
  omega

/-- Once the common terminal factor `2` is exposed, the full cleared mass is
twice the checker digit in the two-jump case. -/
theorem clearedMassTwo_eq_two_mul_blockDigitTwo
    {p q c₀ c₁ c₂ : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    2 * halfClearedMassTwo p q c₀ c₁ c₂ =
      2 * blockDigitTwo p q c₀ c₁ c₂ := by
  rw [halfClearedMassTwo_eq_blockDigitTwo hp hq]

end ErdosProblems.Erdos269
