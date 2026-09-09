import ErdosProblems.Erdos243.PaperCompleteR11.CubicModularDensity

/-!
# The complete zero-lower-density primitive-shape reduction

Authored candidate, UNRUN. The manuscript's primitive-shape lemma is stated
under zero lower density, not under the universal positive threshold. Its
unit-constant conclusion is proved here at exactly that hypothesis.
The arbitrary positive-threshold theorem must not reuse that conclusion.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9

/-- Arbitrarily late prefixes have arbitrarily small exceptional proportion.
The strict inequality automatically excludes the zero-length prefix. -/
def ZeroLowerDensity (E : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ X : ℕ,
    N ≤ X ∧ (exceptionCount E X : ℝ) < ε * (X : ℝ)

/-- The zero-lower-density hypothesis excludes every strictly positive lower
bound; no convergence of all prefix proportions is required. -/
theorem ZeroLowerDensity.not_positive_lower_bound {E : Set ℕ}
    (hzero : ZeroLowerDensity E) (d : ℝ) (hd : 0 < d) :
    ¬ LowerDensityAtLeast E d := by
  intro hlower
  obtain ⟨N, hN⟩ := hlower (d / 2) (by positivity)
  obtain ⟨X, hX, hx⟩ := hzero (d / 2) (by positivity) N
  have hh := hN X hX
  nlinarith

/-- Conversely, the absence of a positive eventual-prefix lower bound is
precisely the same zero-lower-density condition. -/
theorem zeroLowerDensity_iff_no_positive_lower_bound (E : Set ℕ) :
    ZeroLowerDensity E ↔ ∀ d : ℝ, 0 < d → ¬ LowerDensityAtLeast E d := by
  constructor
  · exact fun h d hd ↦ h.not_positive_lower_bound d hd
  · intro h ε hε N
    by_contra hbad
    have hprefix : ∀ X : ℕ, N ≤ X → ε * (X : ℝ) ≤ (exceptionCount E X : ℝ) := by
      intro X hX
      apply le_of_not_gt
      intro hh
      exact hbad ⟨X, hX, hh⟩
    apply h ε hε
    intro δ hδ
    refine ⟨N, ?_⟩
    intro X hX
    have hh := hprefix X hX
    have hm := mul_nonneg (le_of_lt hδ) (show (0 : ℝ) ≤ (X : ℝ) by positivity)
    nlinarith

/-- A nonunit integer, including zero, has a natural divisor >= 2. No prime
existence theorem is needed for the unit-constant reduction. -/
theorem integer_nonunit_has_natural_divisor (c : ℤ)
    (hc : c ≠ 1 ∧ c ≠ -1) :
    ∃ d : ℕ, 2 ≤ d ∧ (d : ℤ) ∣ c := by
  cases c with
  | ofNat n =>
      by_cases hn : n = 0
      · subst n
        exact ⟨2, by decide, dvd_zero _⟩
      · have hn1 : n ≠ 1 := by
          intro h
          subst n
          exact hc.1 rfl
        exact ⟨n, by omega, dvd_refl _⟩
  | negSucc n =>
      have hn : n ≠ 0 := by
        intro h
        subst n
        exact hc.2 rfl
      refine ⟨n + 1, by omega, -1, ?_⟩
      rw [Int.negSucc_eq]
      omega

/-- Exact full unit-constant conclusion for a primitive profile at ZERO
lower density. This statement cannot be used with a merely small positive
exceptional density. -/
theorem primitive_cubic_unit_constant_of_zero_lower_density
    (u : ℕ → ℕ) (m c : ℤ) (T : ℕ)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1)))
    (hzero : ZeroLowerDensity {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}) :
    c = 1 ∨ c = -1 := by
  by_contra hc
  obtain ⟨d, hd, hdc⟩ := integer_nonunit_has_natural_divisor c (not_or.mp hc)
  have hlower := primitive_cubic_constant_divisor_density u m c T d hd hdc hcop
  exact (hzero.not_positive_lower_bound (1 / ((6 * d : ℕ) : ℝ))
    (by
      have hdpos : 0 < d := by omega
      positivity)) hlower

/-- A primitive tail identifies the full rational profile, not only the
agreement predicate at selected indices. -/
theorem binomial_profile_of_scaled_coefficients (κ η : ℚ) (g : ℕ) (m c : ℤ)
    (hg : 0 < g) (hm : (m : ℚ) * (g : ℚ) = 6 * κ)
    (hc : (c : ℚ) * (g : ℚ) = η) (n : ℕ) :
    (κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η) / (g : ℚ) =
      ((m * risingBinomial n + c : ℤ) : ℚ) := by
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  apply (div_eq_iff hgQ).mpr
  have hB : (6 : ℚ) * (risingBinomial n : ℚ) =
      (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) := by
    exact_mod_cast six_mul_risingBinomial n
  push_cast
  linear_combination -(risingBinomial n : ℚ) * hm - hc - κ * hB

/-- Full zero-density construction of the unit primitive cubic shape and its
exact original-index tail recurrence. No irreducibility, Chebotarev, signed
series convergence or hidden primitive-tail supplier is assumed. -/
theorem rational_cubic_zero_density_primitive_shape
    (a C D : ℕ → ℕ) (κ η : ℚ) (hκ : 0 < κ)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hzero : ZeroLowerDensity
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}) :
    ∃ (N g : ℕ) (m c : ℤ), 0 < g ∧ 0 < m ∧ (c = 1 ∨ c = -1) ∧
      (m : ℚ) * (g : ℚ) = 6 * κ ∧ (c : ℚ) * (g : ℚ) = η ∧
      (∀ n : ℕ, (κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η) / (g : ℚ) =
        ((m * risingBinomial n + c : ℤ) : ℚ)) ∧
      ∀ n, N ≤ n →
        Nat.gcd (C n) (D n) = g ∧
        0 < C n / g ∧ 0 < D n / g ∧
        Nat.Coprime (C n / g) (D n / g) ∧
        Nat.Coprime (C n / g) (C (n + 1) / g) ∧
        C (n + 1) / g + D n / g = a n * (C n / g) ∧
        D (n + 1) / g = a n * (D n / g) := by
  let E : Set ℕ := {n : ℕ | (C n : ℚ) ≠
    κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
  obtain ⟨N, g, m, c, hg, hm, hmcoeff, hccoeff, _hbez, htail⟩ :=
    rational_cubic_primitive_integral_tail a C D κ η hκ hCpos hDpos hC hD
      (hzero.not_positive_lower_bound (1 / 4) (by norm_num))
  let F : Set ℕ := {n : ℕ | ((C n / g : ℕ) : ℤ) ≠ m * risingBinomial n + c}
  have heq : ∀ n, N ≤ n → (n ∈ E ↔ n ∈ F) := by
    intro n hn
    obtain ⟨_hgcd, _hpC, _hpD, _hcop, _hnum, _hden, hagree⟩ := htail n hn
    exact not_congr hagree
  have hFzero : ZeroLowerDensity F := by
    apply (zeroLowerDensity_iff_no_positive_lower_bound F).mpr
    intro d hd hF
    have hE := (lowerDensityAtLeast_iff_of_eventual_iff E F N d heq).mpr hF
    exact (hzero.not_positive_lower_bound d hd) hE
  have hadj : ∀ n, N ≤ n → Nat.Coprime (C n / g) (C (n + 1) / g) := by
    intro n hn
    obtain ⟨_hgcd, _hpC, _hpD, hcop, hnum, _hden, _ha⟩ := htail n hn
    exact primitive_step_adjacent_coprime (a n) _ _ _ hnum hcop
  have hc := primitive_cubic_unit_constant_of_zero_lower_density
    (fun n ↦ C n / g) m c N hadj hFzero
  refine ⟨N, g, m, c, hg, hm, hc, hmcoeff, hccoeff,
    binomial_profile_of_scaled_coefficients κ η g m c hg hmcoeff hccoeff, ?_⟩
  intro n hn
  obtain ⟨hgcd, hpC, hpD, hcop, hnum, hden, _ha⟩ := htail n hn
  exact ⟨hgcd, hpC, hpD, hcop, hadj n hn, hnum, hden⟩

end ErdosProblems.Erdos243.PaperCompleteR11
