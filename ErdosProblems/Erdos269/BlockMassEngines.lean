import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the two exact engines behind the block-digit formula

`HalfHeightDenominatorTransport` proves that cancellation is completely
controlled by the running height and that a rational value produces a reduced
carry coprime to the rough part `B`, but records that identifying the
checker's block digit with a height-cleared block mass "remains analytic".

That identification has two exact algebraic engines, and neither of them is
analytic.  Both are landed here, source-independent.

## 1. The suffix-product telescope

For a block element `x` between two internal prime powers, the height quotient
`Q_{a+1} / H(x)` is the product of the internal primes lying *after* `x`.
Summing such suffix products over a block is what produces the checker's
apparently bespoke formula

```
  m_a = A_2(a+1) + ∑_{(p,e) ∈ I_a} (p-1)·σ_a(p,e)·(C_p(e) - C_2(a)).
```

The mechanism is the exact list identity

```
  ∏ ps = 1 + ∑_r (p_r - 1)·∏_{t > r} p_t
```

(`List.prod_eq_one_add_suffixCorrection`): the constant `1` contributes the
block cardinality, and the `r`-th term contributes `(p_r - 1)` times the suffix
product times the number of block elements below the `r`-th jump.  For two
internal jumps `p < q` it is the three-case expansion
`pq = 1 + (p-1)q + (q-1)`, `q = 1 + (q-1)`, `1 = 1`.

## 2. The Bellman identity behind the constant `27`

The checker's state bound is `9·T_a ≤ J_a² + 10·J_a + 27`, where `J_a` counts
the pure prime powers below `2^a`.  The constant `27` is not fitted.  It is
forced by

```
  2·(J² + 10J + 27) = (J+4)² + ((J+1)² + 10(J+1) + 27)
```

(`tailCap_bellman`): the current shell contributes at most `(J+4)²/9`, the
future tail at most `κ(J+1)`, and every jump multiplier is at least `2`, so
`κ(J)` is exactly the fixed point of that backwards recursion.  Any smaller
constant fails at the first shell.

## Claim ceiling

**Erdős #269 remains open**, and the checker-digit identification is *not*
completed here: that still needs the height-quotient suffix formula and the
smooth-lattice counting `C_p(e) = #{x ∈ S : x < p^e}` wired against the live
`threePrimeHeight` vocabulary.  What is landed is the two exact combinatorial
identities on which that wiring rests.
-/

namespace ErdosProblems.Erdos269

/-! ## The suffix-product telescope -/

/-- The telescoping correction of a list of factors: the `r`-th term is
`(p_r - 1)` times the product of everything after it. -/
def suffixCorrection : List ℤ → ℤ
  | [] => 0
  | p :: ps => (p - 1) * ps.prod + suffixCorrection ps

/-- **The suffix telescope.**  A product is one plus the sum of its suffix
corrections.  Applied to the list of internal primes lying after a block
element, this is exactly the expansion of the height quotient that produces the
checker's block digit. -/
theorem List.prod_eq_one_add_suffixCorrection (ps : List ℤ) :
    ps.prod = 1 + suffixCorrection ps := by
  induction ps with
  | nil => simp [suffixCorrection]
  | cons p ps ih =>
      rw [List.prod_cons, suffixCorrection, ih]
      ring

/-- The two-jump case in closed form: the three possible suffix products of a
block element sitting below both, between, or above the internal jumps. -/
theorem suffixCorrection_pair (p q : ℤ) :
    suffixCorrection [p, q] = (p - 1) * q + (q - 1) := by
  simp [suffixCorrection]

/-! ## The Bellman identity behind the state cap -/

/-- The checker's state cap `9·T_a ≤ κ(J_a)`, in numerator form. -/
def tailCap (J : ℕ) : ℕ := J ^ 2 + 10 * J + 27

/-- **The Bellman identity.**  Doubling the cap at rank `J` splits exactly into
the current shell bound `(J+4)²` and the cap at rank `J+1`.  This is why the
constant is `27` and not something smaller: `κ` is the exact fixed point of the
backwards shell recursion under a jump multiplier of at least `2`. -/
theorem tailCap_bellman (J : ℕ) :
    2 * tailCap J = (J + 4) ^ 2 + tailCap (J + 1) := by
  unfold tailCap
  ring

/-- The cap is strictly increasing, so a later anchor never tightens it. -/
theorem tailCap_lt_succ (J : ℕ) : tailCap J < tailCap (J + 1) := by
  unfold tailCap
  nlinarith

/-- A single shell bound feeds the affine-cylinder cap inequality.  The only
source-specific input is the shell mass estimate `9 * d ≤ (J + 4)²`; every
jump multiplier at least two then has enough Bellman budget to absorb that
mass and advance the rank by one. -/
theorem tailCap_step_of_shellMass {J b d : ℕ}
    (hb : 2 ≤ b) (hd : 9 * d ≤ (J + 4) ^ 2) :
    9 * d + tailCap (J + 1) ≤ b * tailCap J := by
  have hbellman := tailCap_bellman J
  have htwo : 2 * tailCap J ≤ b * tailCap J := by
    exact Nat.mul_le_mul_right (tailCap J) hb
  omega

/-- Consecutive affine cap inequalities compose without loss.  If the first
step has digit `d` and the next has digit `e`, their compressed digit is
`c*d+e`; the resulting cap inequality has radix `c*b`.  Together with
`tailCap_step_of_shellMass`, this is the exact algebra needed to compress the
one, two, or three pure-power jumps in an actual dyadic `{2,3,5}` block. -/
theorem tailCap_step_compose {A A' A'' b c d e : ℕ}
    (h₁ : 9 * d + A' ≤ b * A)
    (h₂ : 9 * e + A'' ≤ c * A') :
    9 * (c * d + e) + A'' ≤ (c * b) * A := by
  calc
    9 * (c * d + e) + A'' = c * (9 * d) + (9 * e + A'') := by ring
    _ ≤ c * (9 * d) + c * A' := Nat.add_le_add_left h₂ _
    _ = c * (9 * d + A') := by ring
    _ ≤ c * (b * A) := Nat.mul_le_mul_left c h₁
    _ = (c * b) * A := by ring

end ErdosProblems.Erdos269
