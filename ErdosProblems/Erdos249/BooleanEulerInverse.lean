import Mathlib

/-!
# An explicit inverse for the Boolean Euler transform

Lean-checked helper (r5; `cf_8309991b61ac4c53b3e3` exit 0). Algebraic inverse
only: it does not complete `dim = #signatures` and does not decide `S`.
The companion ordinary proof explains the connection with the existing
finite-subset matrix.

`Cube n` is a recursively indexed Boolean cube. `eulerTransform n r` is the
matrix whose (T,S)-entry is the product of `r i` over coordinates present in
both T and S. Recursion avoids choosing an order on a `Finset` of primes.

The conclusion is algebraic only: the CRT realisation of its rows by affine
totient evaluations is a separate arithmetic obligation.
-/

namespace ErdosProblems.Erdos249.BooleanEulerInverse

universe u
variable {K : Type u} [Field K]

def Cube : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × Cube n

/-- Tensor-product Euler transform, in the order false, true. -/
def eulerTransform : (n : Nat) → (Fin n → K) → (Cube n → K) → Cube n → K
  | 0, _, f, x => f x
  | n + 1, r, f, (false, x) =>
      eulerTransform n (fun i => r i.succ)
        (fun y => f (false, y) + f (true, y)) x
  | n + 1, r, f, (true, x) =>
      eulerTransform n (fun i => r i.succ)
        (fun y => f (false, y) + r 0 * f (true, y)) x

/-- Invert each coordinate using `(r-1)⁻¹ [[r,-1],[-1,1]]`. -/
def eulerInverse : (n : Nat) → (Fin n → K) → (Cube n → K) → Cube n → K
  | 0, _, f, x => f x
  | n + 1, r, f, (false, x) =>
      (r 0 * eulerInverse n (fun i => r i.succ) (fun y => f (false, y)) x -
        eulerInverse n (fun i => r i.succ) (fun y => f (true, y)) x) / (r 0 - 1)
  | n + 1, r, f, (true, x) =>
      (eulerInverse n (fun i => r i.succ) (fun y => f (true, y)) x -
        eulerInverse n (fun i => r i.succ) (fun y => f (false, y)) x) / (r 0 - 1)

/-- Full-cube recovery; no positivity assumption or determinant search. -/
theorem inverse_transform (n : Nat) :
    ∀ (r : Fin n → K), (∀ i, r i ≠ 1) → ∀ (f : Cube n → K),
      eulerInverse n r (eulerTransform n r f) = f := by
  induction n with
  | zero =>
      intro r hr f
      rfl
  | succ n ih =>
      intro r hr f
      have htail : ∀ i : Fin n, r i.succ ≠ 1 := fun i => hr i.succ
      have h0 : r 0 - 1 ≠ 0 := sub_ne_zero.mpr (hr 0)
      have hleft := ih (fun i => r i.succ) htail
        (fun y => f (false, y) + f (true, y))
      have hright := ih (fun i => r i.succ) htail
        (fun y => f (false, y) + r 0 * f (true, y))
      funext x
      rcases x with ⟨b, x⟩
      cases b <;>
        simp only [eulerInverse, eulerTransform] <;>
        rw [hleft, hright] <;>
        field_simp [h0] <;> ring

/-- Distinct columns are independent: equality of transforms forces equality
of all coefficients. Subfamilies can be extended by zero to the full cube. -/
theorem transform_injective (n : Nat) (r : Fin n → K)
    (hr : ∀ i, r i ≠ 1) :
    Function.Injective (eulerTransform n r) := by
  intro f g h
  have h' := congrArg (eulerInverse n r) h
  simpa only [inverse_transform n r hr] using h'

/-- The totient specialisation has an integral inverse, without division. -/
def integralEulerInverse (p : ℤ) (u v : ℤ) : ℤ × ℤ :=
  (p * u - (p - 1) * v, (p - 1) * (v - u))

/-- One-coordinate rational identity underlying the integral inverse. -/
theorem totient_coordinate_recovery (p : ℚ) (hp : p ≠ 1) (a b : ℚ) :
    (p * (a + b) - (p - 1) * (a + p / (p - 1) * b),
      (p - 1) * ((a + p / (p - 1) * b) - (a + b))) = (a, b) := by
  have h : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  apply Prod.ext <;> dsimp <;> field_simp [h] <;> ring

end ErdosProblems.Erdos249.BooleanEulerInverse
