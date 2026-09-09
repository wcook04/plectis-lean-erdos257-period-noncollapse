import ErdosProblems.Erdos243.PaperCompleteR11.FrobeniusDescent
import ErdosProblems.Erdos243.PaperCompleteR11.ReciprocalProductAmplification

/-!
# From actual modular cubic roots to the exceptional-set density

Authored candidate, UNRUN. Rational profile coefficients are cleared over the
integers before reduction. There is deliberately no ring homomorphism from
`ℚ` to `ZMod p`. The final theorem is conditional on an actual divergent family
of good primes; producing that family from a number-field nonsquare remains a
separate global obligation, not a premise silently claimed to have been proved.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators


/-- A common integer denominator for every rational cubic profile is
CONSTRUCTED from the two canonical rational denominators. Nonzero leading
coefficient is preserved; no integrality-of-profile supplier is needed. -/
theorem cubic_profile_integer_clearing (κ η : ℚ) :
    ∃ q A B : ℤ, 0 < q ∧
      (∀ n : ℕ, (q : ℚ) *
        (κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η) =
        (A : ℚ) * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + (B : ℚ)) ∧
      (κ ≠ 0 → A ≠ 0) := by
  have hdκ : (κ.den : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast κ.den_pos)
  have hdη : (η.den : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast η.den_pos)
  have hκ : (κ.den : ℚ) * κ = (κ.num : ℚ) := by
    calc
      (κ.den : ℚ) * κ = (κ.den : ℚ) * ((κ.num : ℚ) / (κ.den : ℚ)) := by
        congr 1
        exact (Rat.num_div_den κ).symm
      _ = (κ.num : ℚ) := by field_simp [hdκ]
  have hη : (η.den : ℚ) * η = (η.num : ℚ) := by
    calc
      (η.den : ℚ) * η = (η.den : ℚ) * ((η.num : ℚ) / (η.den : ℚ)) := by
        congr 1
        exact (Rat.num_div_den η).symm
      _ = (η.num : ℚ) := by field_simp [hdη]
  refine ⟨(κ.den : ℤ) * (η.den : ℤ), κ.num * (η.den : ℤ),
    η.num * (κ.den : ℤ), ?_, ?_, ?_⟩
  · exact_mod_cast Nat.mul_pos κ.den_pos η.den_pos
  · intro n
    push_cast
    linear_combination
      (η.den : ℚ) * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) * hκ +
      (κ.den : ℚ) * hη
  · intro hk hA
    have hAq : (κ.num : ℚ) * (η.den : ℚ) = 0 := by exact_mod_cast hA
    have hn : (κ.num : ℚ) = 0 := (mul_eq_zero.mp hAq).resolve_right hdη
    have hz : (κ.den : ℚ) * κ = 0 := hκ.trans hn
    exact hk ((mul_eq_zero.mp hz).resolve_left hdκ)

/-- A cleared cubic root gives the exact negative-neighbour-product identity. -/
theorem cleared_cubic_neighbour_product {K : Type*} [CommRing K]
    (A B r : K) (hroot : A * (r ^ 3 - r) + B = 0) :
    -(A * ((r - 1) ^ 3 - (r - 1)) + B) *
      (A * ((r + 1) ^ 3 - (r + 1)) + B) =
        (3 * A * r) ^ 2 * (r ^ 2 - 1) := by
  have hl : A * ((r - 1) ^ 3 - (r - 1)) + B = -3 * A * r * (r - 1) := by
    linear_combination hroot
  have hr : A * ((r + 1) ^ 3 - (r + 1)) + B = 3 * A * r * (r + 1) := by
    linear_combination hroot
  rw [hl, hr]
  ring

/-- A root at the middle of a three-point window with nonsquare neighbour
ratio forbids agreement at all three indices. The residue specifies the
START of the window: it is `r-2`, not the middle index `r-1`. -/
theorem cubic_three_window_hit {K : Type*} [Field K]
    (u v a : ℕ → K) (A B r : K) (T n : ℕ) (hn : T ≤ n)
    (hnum : ∀ j, T ≤ j → u (j + 1) = a j * u j - v j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hroot : A * (r ^ 3 - r) + B = 0)
    (hfactor : 3 * A * r ≠ 0) (hns : ¬ IsSquare (r ^ 2 - 1))
    (hphase : (n : K) = r - 2) :
    ∃ j : ℕ, j < 3 ∧ u (n + j) ≠
      A * ((((n + j : ℕ) : K) + 1) ^ 3 - (((n + j : ℕ) : K) + 1)) + B := by
  by_contra hbad
  have hagree : ∀ j : ℕ, j < 3 → u (n + j) =
      A * ((((n + j : ℕ) : K) + 1) ^ 3 - (((n + j : ℕ) : K) + 1)) + B := by
    intro j hj
    by_contra he
    exact hbad ⟨j, hj, he⟩
  have hu0 : u n = A * ((r - 1) ^ 3 - (r - 1)) + B := by
    have h := hagree 0 (by decide)
    simp only [Nat.add_zero, hphase] at h
    convert h using 1 <;> ring
  have hu1 : u (n + 1) = 0 := by
    have h := hagree 1 (by decide)
    simp only [Nat.cast_add, Nat.cast_one, hphase] at h
    calc
      u (n + 1) = A * (r ^ 3 - r) + B := by convert h using 1 <;> ring
      _ = 0 := hroot
  have hu2 : u (n + 2) = A * ((r + 1) ^ 3 - (r + 1)) + B := by
    have h := hagree 2 (by decide)
    simp only [Nat.cast_add, Nat.cast_ofNat, hphase] at h
    convert h using 1 <;> ring
  have hz : a n * u n - v n = 0 := by rw [← hnum n hn, hu1]
  have hnext : u (n + 2) = -(a n * v n) := by
    have h := hnum (n + 1) (by omega)
    simpa only [Nat.add_assoc, hu1, hden n hn, mul_zero, zero_sub] using h
  have hs := zero_middle_neighbour_square (u n) (u (n + 2)) (a n) (v n) hz hnext
  rw [hu0, hu2, cleared_cubic_neighbour_product A B r hroot] at hs
  exact hns ((isSquare_square_mul_iff (3 * A * r) (r ^ 2 - 1) hfactor).mp hs)

/-- Agreement with a rational profile is transferred to the residue field
only after the equality has been cleared over `ℤ`. The profile need not be
integer-valued away from the particular agreement indices. -/
theorem rational_cubic_residue_window_hit
    (a u v : ℕ → ℤ) (P : ℕ → ℚ) (q A B : ℤ) (T n : ℕ) (hn : T ≤ n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (p : ℕ) [Fact p.Prime] (r : ZMod p)
    (hroot : (A : ZMod p) * (r ^ 3 - r) + (B : ZMod p) = 0)
    (hfactor : 3 * (A : ZMod p) * r ≠ 0)
    (hns : ¬ IsSquare (r ^ 2 - 1)) (hphase : (n : ZMod p) = r - 2) :
    ∃ j : ℕ, j < 3 ∧ (u (n + j) : ℚ) ≠ P (n + j) := by
  let U : ℕ → ZMod p := fun k ↦ (q : ZMod p) * (u k : ZMod p)
  let V : ℕ → ZMod p := fun k ↦ (q : ZMod p) * (v k : ZMod p)
  let b : ℕ → ZMod p := fun k ↦ (a k : ZMod p)
  have hU : ∀ j, T ≤ j → U (j + 1) = b j * U j - V j := by
    intro j hj
    have h : (u (j + 1) : ZMod p) + (v j : ZMod p) =
        (a j : ZMod p) * (u j : ZMod p) := by
      simpa using congrArg (Int.castRingHom (ZMod p)) (hnum j hj)
    dsimp [U, V, b]
    linear_combination (q : ZMod p) * h
  have hV : ∀ j, T ≤ j → V (j + 1) = b j * V j := by
    intro j hj
    have h : (v (j + 1) : ZMod p) = (a j : ZMod p) * (v j : ZMod p) := by
      simpa using congrArg (Int.castRingHom (ZMod p)) (hden j hj)
    dsimp [V, b]
    rw [h]
    ring
  obtain ⟨j, hj, hne⟩ := cubic_three_window_hit U V b (A : ZMod p) (B : ZMod p)
    r T n hn hU hV hroot hfactor hns hphase
  refine ⟨j, hj, ?_⟩
  intro hagree
  apply hne
  have hQ : (q : ℚ) * (u (n + j) : ℚ) =
      (A : ℚ) * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) *
        (((n + j : ℕ) : ℚ) + 2) + (B : ℚ) := by
    rw [hagree]
    exact hclear (n + j)
  have hZ : q * u (n + j) = A * ((n + j : ℕ) : ℤ) *
      (((n + j : ℕ) : ℤ) + 1) * (((n + j : ℕ) : ℤ) + 2) + B := by
    exact_mod_cast hQ
  have hF : (q : ZMod p) * (u (n + j) : ZMod p) =
      (A : ZMod p) * ((n + j : ℕ) : ZMod p) * (((n + j : ℕ) : ZMod p) + 1) *
        (((n + j : ℕ) : ZMod p) + 2) + (B : ZMod p) := by
    simpa using congrArg (Int.castRingHom (ZMod p)) hZ
  dsimp [U]
  rw [hF]
  ring

/-- Finite good-prime amplification for an arbitrary denominator-cleared
rational cubic profile and the original integer state transitions. -/
theorem rational_cubic_finite_prime_density {ι : Type*} [Fintype ι]
    (a u v : ℕ → ℤ) (P : ℕ → ℚ) (q A B : ℤ) (T : ℕ)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hc : Pairwise (fun i j ↦ Nat.Coprime (p i) (p j)))
    (r : ∀ i, ZMod (p i))
    (hroot : ∀ i, (A : ZMod (p i)) * ((r i) ^ 3 - r i) + (B : ZMod (p i)) = 0)
    (hfactor : ∀ i, 3 * (A : ZMod (p i)) * r i ≠ 0)
    (hns : ∀ i, ¬ IsSquare ((r i) ^ 2 - 1)) :
    LowerDensityAtLeast {n : ℕ | (u n : ℚ) ≠ P n}
      ((1 - ∏ i, (1 - 1 / (p i : ℝ))) / 3) := by
  letI : ∀ i, Fact (p i).Prime := fun i ↦ ⟨hp i⟩
  apply crt_window_lower_density p (fun i ↦ (hp i).pos) hc
    (fun i ↦ r i - 2) _ 3 T (by decide)
  intro i n hn hr
  exact rational_cubic_residue_window_hit a u v P q A B T n hn hclear hnum hden
    (p i) (r i) (hroot i) (hfactor i) (hns i) hr

/-- The nonsquare good-prime branch has a prime-independent one-third bound
once its actual reciprocal-prime series is divergent. This is NOT the
arbitrary-profile universal theorem: neither prime production nor the other
algebraic branches is asserted by this declaration. -/
theorem rational_cubic_divergent_prime_density
    (a u v : ℕ → ℤ) (P : ℕ → ℚ) (q A B : ℤ) (T : ℕ)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hc : Pairwise (fun i j ↦ Nat.Coprime (p i) (p j)))
    (r : ∀ i, ZMod (p i))
    (hroot : ∀ i, (A : ZMod (p i)) * ((r i) ^ 3 - r i) + (B : ZMod (p i)) = 0)
    (hfactor : ∀ i, 3 * (A : ZMod (p i)) * r i ≠ 0)
    (hns : ∀ i, ¬ IsSquare ((r i) ^ 2 - 1))
    (hdiv : ¬ Summable (fun i ↦ (1 : ℝ) / (p i : ℝ))) :
    LowerDensityAtLeast {n : ℕ | (u n : ℚ) ≠ P n} (1 / 3) := by
  letI : ∀ i, Fact (p i).Prime := fun i ↦ ⟨hp i⟩
  apply divergent_reciprocal_window_density p (fun i ↦ (hp i).pos) hc
    (fun i ↦ r i - 2) _ 3 T (by decide) hdiv
  intro i n hn hr
  exact rational_cubic_residue_window_hit a u v P q A B T n hn hclear hnum hden
    (p i) (r i) (hroot i) (hfactor i) (hns i) hr

end ErdosProblems.Erdos243.PaperCompleteR11
