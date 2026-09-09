import Mathlib

/-!
# Finite arithmetic and weighted charging for LCM record crossings

These lemmas verify the local arithmetic and charging steps of
`LcmRecordExcess.md`. They do not formalise its analytic divergence theorem,
its canonical-orbit transfer, or unrestricted Erdős 243.
-/

namespace ErdosProblems.Erdos243.LcmRecordExcess

/-- A centred LCM numerator can rise only at overlap one. -/
theorem rise_is_fresh {U U' V rho : ℤ}
    (hU : 0 < U) (hrho : 1 ≤ rho)
    (hcenter : -U ≤ 2 * V) (hstep : rho * U' = U - V)
    (hrise : U < U') : rho = 1 ∧ U' - U = -V := by
  have hsmall : rho < 2 := by
    by_contra h
    have hlarge : 2 ≤ rho := by omega
    have hprod : 2 * U' ≤ rho * U' := by nlinarith
    nlinarith
  have hone : rho = 1 := by omega
  constructor
  · exact hone
  · rw [hone] at hstep
    linarith

/-- Crossing a wall preceded by B covered integers requires an actual jump
larger than B. The source may lie below the previous running maximum. -/
theorem covered_wall_forces_excess {U d L a tau B : ℤ}
    (hd : 0 < d) (hsource : U < tau) (hcross : tau ≤ U + d)
    (hfeedback : d = (a - 1) * U - L)
    (hcover : ∀ z : ℤ, tau - B ≤ z → z < tau →
      ∃ m : ℤ, B < m ∧ m ∣ L ∧ m ∣ z) : B < d := by
  by_contra h
  have hsmall : d ≤ B := by omega
  obtain ⟨m, hm, hmL, hmU⟩ := hcover U (by omega) hsource
  have hmd : m ∣ d := by
    rw [hfeedback]
    exact dvd_sub (dvd_mul_of_dvd_right hmU (a - 1)) hmL
  have hle : m ≤ d := Int.le_of_dvd hd hmd
  omega

/-- A step crosses at most its integer excess many walls, whenever the
spacing estimate `(h-1)P < d` holds and `P > B`. -/
theorem wall_count_le_excess {h P d B : ℕ}
    (hP : B < P) (hd : B < d)
    (hspacing : (h - 1) * P < d) : h ≤ d - B := by
  by_contra hh
  have hge : d - B ≤ h - 1 := by omega
  have hmul : (d - B) * P ≤ (h - 1) * P := Nat.mul_le_mul_right P hge
  have hrem : 1 ≤ d - B := by omega
  have hBP : B + 1 ≤ P := by omega
  have hbound : d ≤ (d - B) * P := by
    have hmul2 := Nat.mul_le_mul_left (d - B) hBP
    have hmul3 := Nat.mul_le_mul_right B hrem
    have hsplit : d - B + B = d := Nat.sub_add_cancel (by omega)
    nlinarith
  omega

/-- Any nonnegative decreasing weight can replace the reciprocal charge.
The wall-count premise is discharged by `wall_count_le_excess` in the note. -/
theorem weighted_wall_charge (walls : Finset ℕ) (f : ℕ → ℝ)
    (U r : ℕ) (hf : Antitone f) (hpos : 0 ≤ f U)
    (hsource : ∀ t ∈ walls, U ≤ t) (hcard : walls.card ≤ r) :
    ∑ t ∈ walls, f t ≤ (r : ℝ) * f U := by
  calc
    ∑ t ∈ walls, f t ≤ ∑ _t ∈ walls, f U :=
      Finset.sum_le_sum (fun t ht => hf (hsource t ht))
    _ = (walls.card : ℝ) * f U := by simp
    _ ≤ (r : ℝ) * f U := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hpos

end ErdosProblems.Erdos243.LcmRecordExcess
