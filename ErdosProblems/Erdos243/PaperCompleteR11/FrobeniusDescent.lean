import ErdosProblems.Erdos243.CubicNeighbourIdentity

/-!
# The algebraic descent after a good Frobenius prime is supplied

UNRUN. No prime-existence theorem is declared here. The ordinary number-field
specialisation argument, its finite exceptional set, and the missing formal
Chebotarev dependency are stated explicitly in analytic_proofs.md.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- A nonzero square root negated by an automorphism cannot be the square
root of a square in its fixed base field (in characteristic different from two). -/
theorem nonsquare_of_negated_root
    {k E : Type*} [Field k] [Field E]
    (ι : k →+* E) (F : E →+* E)
    (hfix : ∀ x : k, F (ι x) = ι x)
    (β : E) (hβ : β ≠ 0) (h2 : (2 : E) ≠ 0)
    (hneg : F β = -β) (γ : k) (hsquare : ι γ = β ^ 2) :
    ¬ IsSquare γ := by
  rintro ⟨s, hs⟩
  have hsq : β ^ 2 = (ι s) ^ 2 := by
    rw [← hsquare, hs, map_mul, pow_two]
  have hprod : (β - ι s) * (β + ι s) = 0 := by
    calc
      (β - ι s) * (β + ι s) = β ^ 2 - (ι s) ^ 2 := by ring
      _ = 0 := by rw [hsq]; ring
  have hfixed : F β = β := by
    rcases mul_eq_zero.mp hprod with hm | hp
    · have heq : β = ι s := sub_eq_zero.mp hm
      rw [heq, hfix]
    · have heq : β = -(ι s) := eq_neg_of_add_eq_zero_left hp
      rw [heq, map_neg, hfix]
  have heq : β = -β := hfixed.symm.trans hneg
  have htwice : (2 : E) * β = 0 := by
    calc
      (2 : E) * β = β + β := by ring
      _ = β + -β := congrArg (fun z : E ↦ β + z) heq
      _ = 0 := add_neg_cancel β
  rcases mul_eq_zero.mp htwice with h | h
  · exact h2 h
  · exact hβ h

/-- A nonzero square factor does not change the square class. -/
theorem isSquare_square_mul_iff {K : Type*} [Field K]
    (c γ : K) (hc : c ≠ 0) : IsSquare (c ^ 2 * γ) ↔ IsSquare γ := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s / c, ?_⟩
    apply (mul_left_cancel₀ (pow_ne_zero 2 hc))
    calc
      c ^ 2 * γ = s * s := hs
      _ = c ^ 2 * ((s / c) * (s / c)) := by field_simp
  · rintro ⟨s, hs⟩
    refine ⟨c * s, ?_⟩
    rw [hs]
    ring


/-- Eliminating the denominator from two consecutive exact state transitions
produces the manuscript's second-order numerator identity.  This is valid in
any commutative ring and has no positivity or invertibility assumptions. -/
theorem second_order_numerator_identity {R : Type*} [CommRing R]
    (u v a : ℕ → R) (n : ℕ)
    (hnum : ∀ j, u (j + 1) = a j * u j - v j)
    (hden : ∀ j, v (j + 1) = a j * v j) :
    u (n + 2) = (a n + a (n + 1)) * u (n + 1) - (a n) ^ 2 * u n := by
  calc
    u (n + 2) = a (n + 1) * u (n + 1) - v (n + 1) := by
      simpa [Nat.add_assoc] using hnum (n + 1)
    _ = a (n + 1) * u (n + 1) - a n * v n := by rw [hden n]
    _ = (a n + a (n + 1)) * u (n + 1) - (a n) ^ 2 * u n := by
      rw [hnum n]
      ring

/-- The second-order identity immediately yields the forced-neighbour square
when the middle numerator vanishes.  This is the exact algebra used after
reduction modulo a good prime. -/
theorem forced_neighbour_square_of_second_order {R : Type*} [CommRing R]
    (uPrev uMid uNext aPrev aNext : R)
    (hsecond : uNext = (aPrev + aNext) * uMid - aPrev ^ 2 * uPrev)
    (hzero : uMid = 0) :
    IsSquare (-uPrev * uNext) := by
  refine ⟨aPrev * uPrev, ?_⟩
  rw [hsecond, hzero]
  ring

/-- Two exact transitions through a zero numerator force the negative
neighbour product to be a square, with no inversions or residue exclusions. -/
theorem zero_middle_neighbour_square {R : Type*} [CommRing R]
    (w z a d : R) (hzero : a * w - d = 0) (hnext : z = -(a * d)) :
    IsSquare (-w * z) := by
  have hd : d = a * w := (sub_eq_zero.mp hzero).symm
  refine ⟨a * w, ?_⟩
  rw [hnext, hd]
  ring

/-- Depressed-cubic neighbour identities, valid in every commutative ring. -/
theorem depressed_cubic_neighbours {R : Type*} [CommRing R]
    (r η : R) (hroot : r ^ 3 - r + η = 0) :
    ((r - 1) ^ 3 - (r - 1) + η = -3 * r * (r - 1)) ∧
    ((r + 1) ^ 3 - (r + 1) + η = 3 * r * (r + 1)) := by
  constructor
  · calc
      (r - 1) ^ 3 - (r - 1) + η = (r ^ 3 - r + η) - 3 * r * (r - 1) := by ring
      _ = -3 * r * (r - 1) := by rw [hroot]; ring
  · calc
      (r + 1) ^ 3 - (r + 1) + η = (r ^ 3 - r + η) + 3 * r * (r + 1) := by ring
      _ = 3 * r * (r + 1) := by rw [hroot]; ring

/-- This is the exact local cubic composition once a good prime with
nonsquare r²−1 has been produced. It does not assume that prime supplier. -/
theorem depressed_cubic_transport_obstruction {K : Type*} [Field K]
    (r η κ : K) (hroot : r ^ 3 - r + η = 0)
    (hfactor : 3 * κ * r ≠ 0) (hnonsquare : ¬ IsSquare (r ^ 2 - 1)) :
    ¬ ∃ a d : K,
      a * (κ * ((r - 1) ^ 3 - (r - 1) + η)) - d = 0 ∧
      κ * ((r + 1) ^ 3 - (r + 1) + η) = -(a * d) := by
  rintro ⟨a, d, hz, hn⟩
  have hs := zero_middle_neighbour_square _ _ a d hz hn
  have hid : -(κ * ((r - 1) ^ 3 - (r - 1) + η)) *
      (κ * ((r + 1) ^ 3 - (r + 1) + η)) =
      (3 * κ * r) ^ 2 * (r ^ 2 - 1) := by
    obtain ⟨hl, hr⟩ := depressed_cubic_neighbours r η hroot
    rw [hl, hr]
    ring
  rw [hid] at hs
  exact hnonsquare ((isSquare_square_mul_iff (3 * κ * r) (r ^ 2 - 1) hfactor).mp hs)

end ErdosProblems.Erdos243.PaperCompleteR11
