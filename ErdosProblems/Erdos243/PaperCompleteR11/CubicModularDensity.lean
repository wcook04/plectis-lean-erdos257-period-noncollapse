import ErdosProblems.Erdos243.PaperCompleteR11.CubicDivisorObstruction

/-!
# Single-prime cubic obstructions without the window-length loss

Authored, UNRUN. A fixed prime p >= 3 supplies disjoint three-windows with
lower exceptional density 1/p, rather than 1/(3*p). A concrete modulo-five
corollary constructs the prime, root, and nonsquare witness. This corollary
is unconditional; it does not postulate a good-prime family.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- Exact clearing of the integer-valued binomial profile over the rationals. -/
theorem integral_binomial_profile_clearing (m c : ℤ) (n : ℕ) :
    (6 : ℚ) * (((m * risingBinomial n + c : ℤ)) : ℚ) =
      (m : ℚ) * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + ((6 * c : ℤ) : ℚ) := by
  have hB : (6 : ℚ) * (risingBinomial n : ℚ) =
      (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) := by
    exact_mod_cast six_mul_risingBinomial n
  push_cast
  linear_combination (m : ℚ) * hB

/-- A supplied finite-field witness gives a sharp disjoint-period lower bound.
Unlike the CRT theorem, this counts one selected residue per period p and does
not charge overlapping windows. -/
theorem integral_cubic_single_prime_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ZMod p)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hfactor : 3 * (m : ZMod p) * r ≠ 0) (hns : ¬ IsSquare (r ^ 2 - 1)) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / (p : ℝ)) := by
  letI : NeZero p := ⟨by omega⟩
  letI : NeZero p := ⟨by omega⟩
  let start := (r - 2).val + p * T
  apply disjoint_periodic_lowerDensity _ start p 3 (by omega) hp
  intro k
  have hT : T ≤ start + p * k := by
    have hmul := Nat.mul_le_mul_right T (show 1 ≤ p by omega)
    dsimp [start]
    omega
  have hphase : ((start + p * k : ℕ) : ZMod p) = r - 2 := by
    simp [start, ZMod.natCast_zmod_val]
  obtain ⟨j, hj, hne⟩ := rational_cubic_residue_window_hit a u v
    (fun n ↦ ((m * risingBinomial n + c : ℤ) : ℚ)) 6 m (6 * c)
    T (start + p * k) hT (integral_binomial_profile_clearing m c)
    hnum hden p r hroot hfactor hns hphase
  refine ⟨j, hj, ?_⟩
  intro heq
  exact hne (congrArg (fun z : ℤ ↦ (z : ℚ)) heq)

/-- A genuinely produced modular witness at a prime <= 28 settles this branch
of the requested constant, with no divergent-prime assumption. -/
theorem integral_cubic_small_prime_uniform
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hp28 : p ≤ 28)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ZMod p)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hfactor : 3 * (m : ZMod p) * r ≠ 0) (hns : ¬ IsSquare (r ^ 2 - 1)) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 28) := by
  apply (integral_cubic_single_prime_density a u v m c T p hp
    hnum hden r hroot hfactor hns).mono_bound
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hp28R : (p : ℝ) ≤ 28 := by exact_mod_cast hp28
  exact (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 28) hpR).mpr (by nlinarith)

/-- The finite nonsquare certificate is checked by kernel reduction when run,
not by native evaluation and not by an external Python residue table. -/
theorem three_not_isSquare_zmod_five : ¬ IsSquare (3 : ZMod 5) := by
  decide

/-- Explicit arithmetic progression of coefficient pairs. The root is 3 when
c=m modulo 5, and 2 when c=-m modulo 5. Both have r^2-1=3. -/
theorem integral_cubic_mod_five_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 5) ≠ 0)
    (hc : (c : ZMod 5) = (m : ZMod 5) ∨ (c : ZMod 5) = -(m : ZMod 5)) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 5) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases hc with hc | hc
  · apply integral_cubic_single_prime_density a u v m c T 5 (by decide)
      hnum hden (3 : ZMod 5)
    · calc
        (m : ZMod 5) * ((3 : ZMod 5) ^ 3 - 3) + ((6 * c : ℤ) : ZMod 5) =
            (m : ZMod 5) * ((3 : ZMod 5) ^ 3 - 3) + 6 * (m : ZMod 5) := by
              push_cast
              rw [hc]
        _ = (30 : ZMod 5) * (m : ZMod 5) := by ring
        _ = 0 := by
          have h30 : (30 : ZMod 5) = 0 := by decide
          rw [h30, zero_mul]
    · exact mul_ne_zero (mul_ne_zero (by decide) hm) (by decide)
    · convert three_not_isSquare_zmod_five using 1 <;> decide
  · apply integral_cubic_single_prime_density a u v m c T 5 (by decide)
      hnum hden (2 : ZMod 5)
    · push_cast
      rw [hc]
      norm_num <;> ring_nf <;> norm_num
    · exact mul_ne_zero (mul_ne_zero (by decide) hm) (by decide)
    · convert three_not_isSquare_zmod_five using 1 <;> decide

end ErdosProblems.Erdos243.PaperCompleteR11
