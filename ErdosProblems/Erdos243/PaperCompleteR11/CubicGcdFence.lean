import ErdosProblems.Erdos243.PaperCompleteR11.CubicWindowTransport
import ErdosProblems.Erdos243.ReciprocalTailRigidity

/-!
# A uniform four-window gcd reduction for cubic profiles

Authored candidate, UNRUN. The reduction works below density `1/4`, not only
under density zero. Four agreeing values give the exact third difference;
every earlier common divisor divides that difference. No upper growth estimate,
record restart, denominator reduction, or prime-existence hypothesis is needed.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- Four rational-profile agreements give an integer cleared third difference. -/
theorem cubic_four_agreements_difference (C : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ) (n : ℕ)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) = P (n + j)) :
    q * ((C (n + 3) : ℤ) - 3 * (C (n + 2) : ℤ) +
      3 * (C (n + 1) : ℤ) - (C n : ℤ)) = 6 * A := by
  have h0 := hclear n
  have h1 := hclear (n + 1)
  have h2 := hclear (n + 2)
  have h3 := hclear (n + 3)
  have ha0 : (C n : ℚ) = P n := by simpa using hagree 0 (by decide)
  rw [← ha0] at h0
  rw [← hagree 1 (by decide)] at h1
  rw [← hagree 2 (by decide)] at h2
  rw [← hagree 3 (by decide)] at h3
  have hQ : (q : ℚ) * ((C (n + 3) : ℚ) - 3 * (C (n + 2) : ℚ) +
      3 * (C (n + 1) : ℚ) - (C n : ℚ)) = 6 * (A : ℚ) := by
    push_cast at h1 h2 h3
    linear_combination h3 - 3 * h2 + 3 * h1 - h0
  exact_mod_cast hQ

/-- Divisibility of four agreeing numerators fences the common divisor by
one fixed nonzero integer: the cleared leading coefficient times six. -/
theorem common_divisor_dvd_cubic_third_difference (C : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ) (n d : ℕ)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) = P (n + j))
    (hdiv : ∀ j : ℕ, j < 4 → d ∣ C (n + j)) :
    (d : ℤ) ∣ 6 * A := by
  have hd0 : (d : ℤ) ∣ (C n : ℤ) := by
    have h := hdiv 0 (by decide)
    simp only [Nat.add_zero] at h
    exact_mod_cast h
  have hd1 : (d : ℤ) ∣ (C (n + 1) : ℤ) := by exact_mod_cast hdiv 1 (by decide)
  have hd2 : (d : ℤ) ∣ (C (n + 2) : ℤ) := by exact_mod_cast hdiv 2 (by decide)
  have hd3 : (d : ℤ) ∣ (C (n + 3) : ℤ) := by exact_mod_cast hdiv 3 (by decide)
  have hlin : (d : ℤ) ∣ ((C (n + 3) : ℤ) - 3 * (C (n + 2) : ℤ) +
      3 * (C (n + 1) : ℤ) - (C n : ℤ)) :=
    dvd_sub (dvd_add (dvd_sub hd3 (dvd_mul_of_dvd_right hd2 3))
      (dvd_mul_of_dvd_right hd1 3)) hd0
  have h := dvd_mul_of_dvd_right hlin q
  rwa [cubic_four_agreements_difference C P q A B n hclear hagree] at h

/-- Persistent common divisors for any positive-coordinate natural orbit;
this does not package unrelated growth or unboundedness assumptions. -/
theorem natural_orbit_common_divisor_tail (a C D : ℕ → ℕ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (s d : ℕ) (hdC : d ∣ C s) (hdD : d ∣ D s) :
    ∀ k : ℕ, d ∣ C (s + k) ∧ d ∣ D (s + k) := by
  intro k
  induction k with
  | zero => simpa using And.intro hdC hdD
  | succ k ih =>
      constructor
      · have hs : d ∣ C (s + k + 1) + D (s + k) := by
          rw [hC]
          exact dvd_mul_of_dvd_right ih.1 _
        simpa only [Nat.add_assoc] using (Nat.dvd_add_iff_left ih.2).mpr hs
      · rw [show s + (k + 1) = s + k + 1 by omega, hD]
        exact dvd_mul_of_dvd_right ih.2 _

/-- Below the four-window threshold every state gcd divides the same cleared
third difference. The conclusion applies at EVERY index, not one subsequence. -/
theorem cubic_gcd_dvd_of_not_quarter_density (a C D : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | (C n : ℚ) ≠ P n} (1 / 4)) :
    ∀ s : ℕ, (Nat.gcd (C s) (D s) : ℤ) ∣ 6 * A := by
  intro s
  obtain ⟨n, hsn, hn⟩ := clean_windows_of_not_lower_density
    {n : ℕ | (C n : ℚ) ≠ P n} 4 (by decide) hlow s
  have hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) = P (n + j) := by
    intro j hj
    exact not_ne_iff.mp (hn j hj)
  apply common_divisor_dvd_cubic_third_difference C P q A B n
    (Nat.gcd (C s) (D s)) hclear hagree
  intro j _
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show s ≤ n + j by omega)
  have h := natural_orbit_common_divisor_tail a C D hC hD s
    (Nat.gcd (C s) (D s)) (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) k
  simpa only [← hk] using h.1

/-- A literal bounded-gcd conclusion, with no density-zero premise. -/
theorem cubic_gcd_bound_of_not_quarter_density (a C D : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ) (hA : A ≠ 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | (C n : ℚ) ≠ P n} (1 / 4)) :
    ∀ s : ℕ, Nat.gcd (C s) (D s) ≤ (6 * A).natAbs := by
  intro s
  obtain ⟨k, hk⟩ := cubic_gcd_dvd_of_not_quarter_density a C D P q A B hC hD hclear hlow s
  have hd : Nat.gcd (C s) (D s) ∣ (6 * A).natAbs := by
    refine ⟨k.natAbs, ?_⟩
    rw [hk, Int.natAbs_mul, Int.natAbs_natCast]
  have hpos : 0 < (6 * A).natAbs := Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hA)
  exact Nat.le_of_dvd hpos hd

/-- Actual gcd stabilisation for the exact orbit below lower density `1/4`.
Only positivity of the numerators is required in addition to the equations. -/
theorem cubic_gcd_stabilises_of_not_quarter_density (a C D : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ) (hA : A ≠ 0) (hpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | (C n : ℚ) ≠ P n} (1 / 4)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Nat.gcd (C n) (D n) = Nat.gcd (C N) (D N) := by
  apply dvdChain_eventuallyConstant_of_cofinally_bounded
    (fun n ↦ Nat.gcd (C n) (D n)) (6 * A).natAbs
    (fun n ↦ Nat.gcd_pos_of_pos_left _ (hpos n))
    (fun n ↦ tailGcd_dvd_succ _ _ _ _ _ (hC n) (hD n))
  intro n
  exact ⟨n, le_rfl, cubic_gcd_bound_of_not_quarter_density a C D P q A B hA hC hD
    hclear hlow n⟩


/-- The low-density gcd reduction for a literal arbitrary rational profile.
The common denominator and integer leading coefficient are constructed by
the theorem, rather than supplied as additional hypotheses. -/
theorem rational_cubic_profile_gcd_stabilises
    (a C D : ℕ → ℕ) (κ η : ℚ) (hκ : κ ≠ 0)
    (hpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hlow : ¬ LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
      (1 / 4)) :
    ∃ B N : ℕ, (∀ n, Nat.gcd (C n) (D n) ≤ B) ∧
      ∀ n, N ≤ n → Nat.gcd (C n) (D n) = Nat.gcd (C N) (D N) := by
  obtain ⟨q, A, B, _hq, hclear, hA⟩ := cubic_profile_integer_clearing κ η
  let P : ℕ → ℚ := fun n ↦ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η
  have hbound := cubic_gcd_bound_of_not_quarter_density a C D P q A B (hA hκ)
    hC hD hclear hlow
  obtain ⟨N, hN⟩ := cubic_gcd_stabilises_of_not_quarter_density a C D P q A B
    (hA hκ) hpos hC hD hclear hlow
  exact ⟨(6 * A).natAbs, N, hbound, hN⟩

end ErdosProblems.Erdos243.PaperCompleteR11
