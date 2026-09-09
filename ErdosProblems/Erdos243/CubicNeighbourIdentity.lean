import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Erdős #243: cubic neighbouring-value identity and the two mod-7 words

The Type B r2 cubic argument extracts a primitive rising-factorial cubic
`Q(X) = (m/6) X(X+1)(X+2) + c` with `c = ±1`, then forces a field-square
condition in `ℚ(α)` from neighbouring values at a root `α`.  For an
irreducible cubic there is no rational root, so the previous `α : ℚ`
interface did not instantiate that number-field step.

This module kernel-checks the *denominator-cleared ring identities* over an
arbitrary commutative ring, recovers the old rational divided forms as
corollaries, evaluates the two residue words at `m = 12`, and excludes exact
three-step transport of those words over `ZMod 7`.

It does not formalise Chebotarev, gcd stabilisation, or the density
quantifier.  The integer identity `4 * 7 = 28` records word-period
accounting only (`1/(4·7) = 1/28`); it is not a density theorem.

Erdős #243 remains open.
-/

namespace ErdosProblems.Erdos243

variable {R : Type*} [CommRing R]

/-- Rising-factorial cubic template over a commutative ring.  The coefficient
`k` is the already-cleared leading factor (so `k = m/6` in the rational
normalisation). -/
def cubicProfile (k c x : R) : R :=
  k * x * (x + 1) * (x + 2) + c

/-- Unconditional left neighbour identity, with no division. -/
theorem cubicProfile_left_identity (k c α : R) :
    (α + 2) * cubicProfile k c (α - 1)
      - (α - 1) * cubicProfile k c α = 3 * c := by
  unfold cubicProfile
  ring

/-- Unconditional right neighbour identity, with no division. -/
theorem cubicProfile_right_identity (k c α : R) :
    α * cubicProfile k c (α + 1)
      - (α + 3) * cubicProfile k c α = -3 * c := by
  unfold cubicProfile
  ring

/-- At a root, the left identity clears the neighbour without inverting
`α + 2`. -/
theorem cubicProfile_left_cleared (k c α : R)
    (hroot : cubicProfile k c α = 0) :
    (α + 2) * cubicProfile k c (α - 1) = 3 * c := by
  have h := cubicProfile_left_identity k c α
  rw [hroot, mul_zero, sub_zero] at h
  exact h

/-- At a root, the right identity clears the neighbour without inverting
`α`. -/
theorem cubicProfile_right_cleared (k c α : R)
    (hroot : cubicProfile k c α = 0) :
    α * cubicProfile k c (α + 1) = -3 * c := by
  have h := cubicProfile_right_identity k c α
  rw [hroot, mul_zero, sub_zero] at h
  exact h

/-- Product identity at a root: no division.  Over a field, if
`α(α + 2) ≠ 0`, this recovers `-Q(α-1)Q(α+1) = 9c²/(α(α+2))`. -/
theorem cubicProfile_square_cleared (k c α : R)
    (hroot : cubicProfile k c α = 0) :
    -(α * (α + 2) * cubicProfile k c (α - 1) * cubicProfile k c (α + 1))
      = 9 * c ^ 2 := by
  have hl := cubicProfile_left_cleared k c α hroot
  have hr := cubicProfile_right_cleared k c α hroot
  calc
    -(α * (α + 2) * cubicProfile k c (α - 1) * cubicProfile k c (α + 1))
        = -(((α + 2) * cubicProfile k c (α - 1)) *
            (α * cubicProfile k c (α + 1))) := by ring
    _ = -((3 * c) * (-3 * c)) := by rw [hl, hr]
    _ = 9 * c ^ 2 := by ring

/-- Rising-factorial cubic template over `ℚ`, with the historical `m/6`
normalisation. -/
def cubicQ (m c x : ℚ) : ℚ :=
  cubicProfile (m / 6) c x

lemma cubicQ_root_prod {m c α : ℚ} (hroot : cubicQ m c α = 0) :
    (m / 6) * α * (α + 1) * (α + 2) = -c := by
  simp [cubicQ, cubicProfile] at hroot
  linarith

/-- Left neighbour at a rational root: `Q(α-1) = 3c/(α+2)`.  This does not
instantiate an irreducible cubic. -/
theorem cubicQ_neighbour_left {m c α : ℚ}
    (hα : α + 2 ≠ 0) (hroot : cubicQ m c α = 0) :
    cubicQ m c (α - 1) = 3 * c / (α + 2) := by
  have h := cubicProfile_left_cleared (m / 6) c α hroot
  rw [eq_div_iff hα, mul_comm]
  exact h

/-- Right neighbour at a rational root: `Q(α+1) = -3c/α`. -/
theorem cubicQ_neighbour_right {m c α : ℚ}
    (hα : α ≠ 0) (hroot : cubicQ m c α = 0) :
    cubicQ m c (α + 1) = -3 * c / α := by
  have h := cubicProfile_right_cleared (m / 6) c α hroot
  rw [eq_div_iff hα, mul_comm]
  exact h

/-- Square identity over `ℚ` after inverting `α(α+2)`. -/
theorem cubicQ_square_identity {m c α : ℚ}
    (h0 : α ≠ 0) (h2 : α + 2 ≠ 0) (hroot : cubicQ m c α = 0) :
    -(cubicQ m c (α - 1) * cubicQ m c (α + 1))
      = 9 * c ^ 2 / (α * (α + 2)) := by
  rw [cubicQ_neighbour_left h2 hroot, cubicQ_neighbour_right h0 hroot]
  field_simp [h0, h2]
  ring

/-- Word-period accounting `4 * 7 = 28`, equivalently `1/(4·7) = 1/28`.
This is not a uniform lower density over all original `(A,B)`. -/
theorem two_primitive_profile_mod7_period : 4 * 7 = 28 := by decide

/-- Plus-profile word `(1,6,0,2)` at starts `0 (mod 7)`.  Word evaluation
is not orbit exclusion. -/
theorem cubic_plus_word_mod7 :
    (fun n : ZMod 7 => (2 : ZMod 7) * n * (n + 1) * (n + 2) + 1) 0 = 1 ∧
    (fun n : ZMod 7 => (2 : ZMod 7) * n * (n + 1) * (n + 2) + 1) 1 = 6 ∧
    (fun n : ZMod 7 => (2 : ZMod 7) * n * (n + 1) * (n + 2) + 1) 2 = 0 ∧
    (fun n : ZMod 7 => (2 : ZMod 7) * n * (n + 1) * (n + 2) + 1) 3 = 2 := by
  decide

/-- Minus-profile word `(4,5,0,1)` at starts `1 (mod 7)`.  Word evaluation
is not orbit exclusion. -/
theorem cubic_minus_word_mod7 :
    (fun n : ZMod 7 => (2 : ZMod 7) * n * (n + 1) * (n + 2) - 1) 1 = 4 ∧
    (fun n : ZMod 7 => (2 : ZMod 7) * n * (n + 1) * (n + 2) - 1) 2 = 5 ∧
    (fun n : ZMod 7 => (2 : ZMod 7) * n * (n + 1) * (n + 2) - 1) 3 = 0 ∧
    (fun n : ZMod 7 => (2 : ZMod 7) * n * (n + 1) * (n + 2) - 1) 4 = 1 := by
  decide

/-- Exact three-step transport of the plus word is impossible over `𝔽_7`,
including zero residues. -/
theorem cubic_plus_word_exact_transport_impossible :
    ¬ ∃ a b d : ZMod 7,
      a * (1 : ZMod 7) - d = 6 ∧
      b * (6 : ZMod 7) - a * d = 0 ∧
      -(b * (a * d)) = 2 := by
  decide

/-- Exact three-step transport of the minus word is impossible over `𝔽_7`,
including zero residues. -/
theorem cubic_minus_word_exact_transport_impossible :
    ¬ ∃ a b d : ZMod 7,
      a * (4 : ZMod 7) - d = 5 ∧
      b * (5 : ZMod 7) - a * d = 0 ∧
      -(b * (a * d)) = 1 := by
  decide

#print axioms cubicProfile_left_identity
#print axioms cubicProfile_right_identity
#print axioms cubicProfile_square_cleared
#print axioms cubic_plus_word_exact_transport_impossible
#print axioms cubic_minus_word_exact_transport_impossible
#print axioms cubicQ_neighbour_left
#print axioms cubicQ_neighbour_right
#print axioms cubicQ_square_identity

end ErdosProblems.Erdos243
