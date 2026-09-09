import ErdosProblems.Erdos243.PaperCompleteR11.CubicPrimitiveNormalisation
import ErdosProblems.Erdos243.PaperCompleteR11.DensityTransport

/-!
# Nonunit constants: explicit primitive divisor obstructions

Authored candidate, UNRUN. The old 1/(12*d) loss is unnecessary for a single
periodic family of disjoint two-windows. We obtain 1/(6*d) for every d >= 2,
and 1/d when d is coprime to 6. In particular divisors 2, 3, and any divisor
between 2 and 28 coprime to 6 give the universal 1/28 bound in this branch.
This does not discard constants whose prime factors are all >= 29.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- The two neighbouring binomial values vanish whenever n+1 is a multiple
of 6*d. The integer witnesses are produced explicitly. -/
theorem risingBinomial_pair_dvd_six_multiple (d n k : ℕ)
    (hphase : n + 1 = 6 * d * k) :
    (d : ℤ) ∣ risingBinomial n ∧ (d : ℤ) ∣ risingBinomial (n + 1) := by
  have hp : (n : ℤ) + 1 = 6 * (d : ℤ) * (k : ℤ) := by exact_mod_cast hphase
  constructor
  · refine ⟨(k : ℤ) * (n : ℤ) * ((n : ℤ) + 2), ?_⟩
    have h6 : 6 * risingBinomial n =
        6 * ((d : ℤ) * ((k : ℤ) * (n : ℤ) * ((n : ℤ) + 2))) := by
      rw [six_mul_risingBinomial, hp]
      ring
    omega
  · refine ⟨(k : ℤ) * ((n : ℤ) + 2) * ((n : ℤ) + 3), ?_⟩
    have h6 : 6 * risingBinomial (n + 1) =
        6 * ((d : ℤ) * ((k : ℤ) * ((n : ℤ) + 2) * ((n : ℤ) + 3))) := by
      rw [six_mul_risingBinomial]
      push_cast
      calc
        ((n : ℤ) + 1) * ((n : ℤ) + 1 + 1) * ((n : ℤ) + 1 + 2) =
            ((n : ℤ) + 1) * ((n : ℤ) + 2) * ((n : ℤ) + 3) := by ring
        _ = 6 * ((d : ℤ) * ((k : ℤ) * ((n : ℤ) + 2) * ((n : ℤ) + 3))) := by
          rw [hp]
          ring
    omega

/-- Away from 2 and 3 the period is d, rather than 6*d. -/
theorem risingBinomial_pair_dvd_coprime_six (d n : ℕ)
    (hcop : Nat.Coprime d 6) (hphase : d ∣ n + 1) :
    (d : ℤ) ∣ risingBinomial n ∧ (d : ℤ) ∣ risingBinomial (n + 1) := by
  have h0 : d ∣ 6 * (n + 2).choose 3 := by
    rw [six_mul_rising_choose]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hphase n) (n + 2)
  have h1 : d ∣ 6 * (n + 1 + 2).choose 3 := by
    rw [six_mul_rising_choose]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hphase (n + 1 + 1)) (n + 1 + 2)
  have hd0 := hcop.dvd_of_dvd_mul_left h0
  have hd1 := hcop.dvd_of_dvd_mul_left h1
  constructor
  · unfold risingBinomial
    exact_mod_cast hd0
  · unfold risingBinomial
    exact_mod_cast hd1

/-- A common nonunit divisor cannot divide both members of a primitive pair. -/
theorem primitive_pair_profile_hit (u : ℕ → ℕ) (P : ℕ → ℤ) (n d : ℕ)
    (hd : 2 ≤ d) (hcop : Nat.Coprime (u n) (u (n + 1)))
    (h0 : (d : ℤ) ∣ P n) (h1 : (d : ℤ) ∣ P (n + 1)) :
    ∃ i : ℕ, i < 2 ∧ (u (n + i) : ℤ) ≠ P (n + i) := by
  by_contra hbad
  have ha : ∀ i : ℕ, i < 2 → (u (n + i) : ℤ) = P (n + i) := by
    intro i hi
    by_contra hh
    exact hbad ⟨i, hi, hh⟩
  have ha0 : (u n : ℤ) = P n := by simpa using ha 0 (by decide)
  rw [← ha0] at h0
  rw [← ha 1 (by decide)] at h1
  have hu0 : d ∣ u n := by exact_mod_cast h0
  have hu1 : d ∣ u (n + 1) := by exact_mod_cast h1
  have hdu : d ∣ 1 := by
    simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hu0 hu1
  have := Nat.dvd_one.mp hdu
  omega

/-- Construct and count the disjoint two-window witnesses on the original
tail. Only the elementary profile divisibility lemma is parametrised. -/
theorem primitive_periodic_pair_density (u : ℕ → ℕ) (P : ℕ → ℤ)
    (T d s : ℕ) (hd : 2 ≤ d) (hs : 2 ≤ s)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1)))
    (hdiv : ∀ n k : ℕ, n + 1 = s * k →
      (d : ℤ) ∣ P n ∧ (d : ℤ) ∣ P (n + 1)) :
    LowerDensityAtLeast {n : ℕ | (u n : ℤ) ≠ P n} (1 / (s : ℝ)) := by
  let r := s * T + (s - 1)
  apply disjoint_periodic_lowerDensity _ r s 2 (by omega) hs
  intro k
  let n := r + s * k
  have hs1 : s - 1 + 1 = s := by omega
  have hphase : n + 1 = s * (T + k + 1) := by
    dsimp [n, r]
    nlinarith
  have hnT : T ≤ n := by
    have hh := Nat.mul_le_mul_right T (show 1 ≤ s by omega)
    dsimp [n, r]
    nlinarith
  obtain ⟨h0, h1⟩ := hdiv n (T + k + 1) hphase
  exact primitive_pair_profile_hit u P n d hd (hcop n hnT) h0 h1

/-- Every nonunit divisor of c gives a literal lower-density bound 1/(6*d). -/
theorem primitive_cubic_constant_divisor_density (u : ℕ → ℕ) (m c : ℤ)
    (T d : ℕ) (hd : 2 ≤ d) (hdc : (d : ℤ) ∣ c)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1))) :
    LowerDensityAtLeast {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}
      (1 / ((6 * d : ℕ) : ℝ)) := by
  apply primitive_periodic_pair_density u (fun n ↦ m * risingBinomial n + c)
    T d (6 * d) hd (by omega) hcop
  intro n k hphase
  obtain ⟨h0, h1⟩ := risingBinomial_pair_dvd_six_multiple d n k hphase
  exact ⟨dvd_add (dvd_mul_of_dvd_right h0 m) hdc,
    dvd_add (dvd_mul_of_dvd_right h1 m) hdc⟩

/-- When the divisor is coprime to 6, the stronger bound is 1/d. -/
theorem primitive_cubic_coprime_six_divisor_density (u : ℕ → ℕ) (m c : ℤ)
    (T d : ℕ) (hd : 2 ≤ d) (hdc : (d : ℤ) ∣ c) (hd6 : Nat.Coprime d 6)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1))) :
    LowerDensityAtLeast {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}
      (1 / (d : ℝ)) := by
  apply primitive_periodic_pair_density u (fun n ↦ m * risingBinomial n + c)
    T d d hd hd hcop
  intro n k hphase
  obtain ⟨h0, h1⟩ := risingBinomial_pair_dvd_coprime_six d n hd6 ⟨k, hphase⟩
  exact ⟨dvd_add (dvd_mul_of_dvd_right h0 m) hdc,
    dvd_add (dvd_mul_of_dvd_right h1 m) hdc⟩

/-- A constant with a factor 2 or 3 already gives the universal bound. -/
theorem primitive_cubic_two_three_divisor_uniform (u : ℕ → ℕ) (m c : ℤ) (T : ℕ)
    (hdiv : (2 : ℤ) ∣ c ∨ (3 : ℤ) ∣ c)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1))) :
    LowerDensityAtLeast {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c} (1 / 28) := by
  rcases hdiv with hdiv | hdiv
  · exact (primitive_cubic_constant_divisor_density u m c T 2 (by decide) hdiv hcop).mono_bound
      (by norm_num)
  · exact (primitive_cubic_constant_divisor_density u m c T 3 (by decide) hdiv hcop).mono_bound
      (by norm_num)

/-- All small divisors coprime to 6 are also settled without prime production. -/
theorem primitive_cubic_small_divisor_uniform (u : ℕ → ℕ) (m c : ℤ) (T d : ℕ)
    (hd : 2 ≤ d) (hd28 : d ≤ 28) (hdc : (d : ℤ) ∣ c) (hd6 : Nat.Coprime d 6)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1))) :
    LowerDensityAtLeast {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c} (1 / 28) := by
  apply (primitive_cubic_coprime_six_divisor_density u m c T d hd hdc hd6 hcop).mono_bound
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hd28R : (d : ℝ) ≤ 28 := by exact_mod_cast hd28
  exact (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 28) hdR).mpr (by nlinarith)

end ErdosProblems.Erdos243.PaperCompleteR11
