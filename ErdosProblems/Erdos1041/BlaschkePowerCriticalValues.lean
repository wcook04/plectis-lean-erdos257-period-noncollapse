import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Algebra for Blaschke-power polynomial critical spectra

These declarations supply the exact algebra in the accompanying ordinary
proof. The module has not been compiled in the return environment. It has
no `sorry`, extra axiom, or analytic statement hidden in a hypothesis.

The first lemma eliminates the high power at a critical point of A^N-D^N.
The remaining lemmas identify its quadratic model and its Poisson density.
They do NOT formalise the limiting critical-point distribution, the sharp
critical-value exponent theorem, or a general lemniscate path theorem.
-/

namespace ErdosProblems.Erdos1041.BlaschkePowerCriticalValues

/-- Universal critical-value elimination, over any commutative ring.
`huv` is the algebraic critical equation after cancelling the nonzero degree. -/
theorem critical_value_elimination {R : Type*} [CommRing R]
    (u v du dv : R) (k : ℕ)
    (huv : u ^ k * du = v ^ k * dv) :
    du * (u ^ (k + 1) - v ^ (k + 1)) =
      v ^ k * (u * dv - v * du) := by
  calc
    du * (u ^ (k + 1) - v ^ (k + 1)) =
        u * (u ^ k * du) - v ^ k * (v * du) := by
          simp only [pow_succ]
          ring
    _ = u * (v ^ k * dv) - v ^ k * (v * du) := by rw [huv]
    _ = v ^ k * (u * dv - v * du) := by ring

/-- The Wronskian numerator of A=z(z+b), D=1+bz. -/
theorem quadratic_wronskian {R : Type*} [CommRing R] (z b : R) :
    (z * (z + b)) * b - (1 + b * z) * (2 * z + b) =
      -(b * z ^ 2 + 2 * z + b) := by ring

/-- Exact value identity for the explicit family, without division. -/
theorem quadratic_critical_value_identity {R : Type*} [CommRing R]
    (z b : R) (k : ℕ)
    (hc : (z * (z + b)) ^ k * (2 * z + b) =
      (1 + b * z) ^ k * b) :
    (2 * z + b) *
      ((z * (z + b)) ^ (k + 1) - (1 + b * z) ^ (k + 1)) =
      -(b * z ^ 2 + 2 * z + b) * (1 + b * z) ^ k := by
  have h := critical_value_elimination
    (z * (z + b)) (1 + b * z) (2 * z + b) b k hc
  rw [quadratic_wronskian] at h
  simpa only [mul_comm] using h

/-- The real-coordinate identity proving the disc automorphism factor
has modulus less than one for |z|<1 and |b|<1. -/
theorem blaschke_disc_modulus_identity (x y b : ℝ) :
    ((1 + b * x) ^ 2 + (b * y) ^ 2) -
        ((x + b) ^ 2 + y ^ 2) =
      (1 - b ^ 2) * (1 - (x ^ 2 + y ^ 2)) := by ring

/-- The endpoint density is the average of uniform measure and one
Poisson kernel, after multiplying by its positive denominator. -/
theorem endpoint_density_identity (b x : ℝ) :
    2 * (1 + b * x) = (1 + b ^ 2 + 2 * b * x) + (1 - b ^ 2) := by ring

/-- Circle averaging x=cos(theta), mean x=0, mean x^2=1/2,
turns this identity into the exact eighth-power limit 1+2*b^2. -/
theorem eighth_power_integrand_identity (b x : ℝ) :
    (1 + b ^ 2 + 2 * b * x) * (1 + b * x) =
      1 + b ^ 2 + (3 * b + b ^ 3) * x + 2 * b ^ 2 * x ^ 2 := by ring

/-- Exact slack for the local ball used by the explicit short connector. -/
theorem half_parameter_ball_slack :
    2 * (45 / 64 : ℝ) ^ 2 < 1 := by norm_num

end ErdosProblems.Erdos1041.BlaschkePowerCriticalValues
