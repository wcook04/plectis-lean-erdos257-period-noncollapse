import ErdosProblems.Erdos243.CubicNeighbourIdentity

/-!
Candidate, UNRUN. Correct phase-specific modulo-seven obstructions, a sharp
one-in-seven disjoint-block counting certificate, and exact counterexamples
to the stronger phase-free statement in the supplied manuscript.
-/
namespace ErdosProblems.Erdos243.PaperCompleteR9

noncomputable def exceptionFinset (E : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n ↦ n ∈ E)

noncomputable def exceptionCount (E : Set ℕ) (X : ℕ) : ℕ :=
  (exceptionFinset E X).card

/-- Disjoint periodic witness blocks lose no factor of the block length. -/
theorem disjoint_periodic_count (E : Set ℕ) (r s L : ℕ)
    (hL : L ≤ s) (hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ r + s * k + i ∈ E)
    (K : ℕ) : K ≤ exceptionCount E (r + s * K) := by
  classical
  choose w hw using hhit
  let F : ℕ → ℕ := fun k ↦ r + s * k + w k
  have hFmono : StrictMono F := by
    intro k l hkl
    have hmul := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hkl)
    have hwk := (hw k).1
    dsimp [F]
    nlinarith
  have hmem : ∀ k ∈ Finset.range K, F k ∈ exceptionFinset E (r + s * K) := by
    intro k hk
    have hkl := Finset.mem_range.mp hk
    have hmul := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hkl)
    have hwk := (hw k).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, (hw k).2⟩
    dsimp [F]
    nlinarith
  have hc := Finset.card_le_card_of_injOn F hmem hFmono.injective.injOn
  simpa [exceptionCount] using hc

/-- Consequently the lower exceptional density is at least 1/s. This finite
inequality is stronger than a zero-lower-density contradiction. -/
theorem disjoint_periodic_linear_bound (E : Set ℕ) (r s L : ℕ)
    (hs : 0 < s) (hL : L ≤ s)
    (hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ r + s * k + i ∈ E) :
    ∀ X : ℕ, X ≤ s * exceptionCount E X + (r + s) := by
  classical
  intro X
  by_cases hr : r ≤ X
  · let K := (X - r) / s
    have hdecomp := Nat.mod_add_div (X - r) s
    change (X - r) % s + s * K = X - r at hdecomp
    have hfloor : s * K ≤ X - r := by omega
    have hend : r + s * K ≤ X := by omega
    have hsub : exceptionFinset E (r + s * K) ⊆ exceptionFinset E X := by
      intro x hx
      obtain ⟨hx, hE⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le hend), hE⟩
    have hc : K ≤ exceptionCount E X :=
      (disjoint_periodic_count E r s L hL hhit K).trans (Finset.card_le_card hsub)
    have hrem := Nat.mod_lt (X - r) hs
    have hmul := Nat.mul_le_mul_left s hc
    omega
  · omega

/-- A generic four-step word test in characteristic seven. -/
theorem bad_four_step_block
    (a u v P : ℕ → ℤ) (T n : ℕ) (hn : T ≤ n)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (c0 c1 c2 c3 : ZMod 7)
    (hc0 : (P n : ZMod 7) = c0)
    (hc1 : (P (n + 1) : ZMod 7) = c1)
    (hc2 : (P (n + 2) : ZMod 7) = c2)
    (hc3 : (P (n + 3) : ZMod 7) = c3)
    (hword : ¬ ∃ a0 a1 a2 d0 : ZMod 7,
      a0 * c0 - d0 = c1 ∧
      a1 * c1 - a0 * d0 = c2 ∧
      a2 * c2 - a1 * (a0 * d0) = c3) :
    ∃ i : ℕ, i < 4 ∧ u (n + i) ≠ P (n + i) := by
  by_contra hbad
  have hagree : ∀ i : ℕ, i < 4 → u (n + i) = P (n + i) := by
    intro i hi
    by_contra hh
    exact hbad ⟨i, hi, hh⟩
  have hu0 : (u n : ZMod 7) = c0 := by simpa using
    (congrArg (Int.castRingHom (ZMod 7)) (hagree 0 (by decide))).trans hc0
  have hu1 : (u (n + 1) : ZMod 7) = c1 :=
    (congrArg (Int.castRingHom (ZMod 7)) (hagree 1 (by decide))).trans hc1
  have hu2 : (u (n + 2) : ZMod 7) = c2 :=
    (congrArg (Int.castRingHom (ZMod 7)) (hagree 2 (by decide))).trans hc2
  have hu3 : (u (n + 3) : ZMod 7) = c3 :=
    (congrArg (Int.castRingHom (ZMod 7)) (hagree 3 (by decide))).trans hc3
  have hs (j : ℕ) (hj : T ≤ j) :
      (u (j + 1) : ZMod 7) + (v j : ZMod 7) = (a j : ZMod 7) * (u j : ZMod 7) := by
    simpa only [map_add, map_mul] using congrArg (Int.castRingHom (ZMod 7)) (hnum j hj)
  have hd (j : ℕ) (hj : T ≤ j) :
      (v (j + 1) : ZMod 7) = (a j : ZMod 7) * (v j : ZMod 7) := by
    simpa only [map_mul] using congrArg (Int.castRingHom (ZMod 7)) (hden j hj)
  have hs0 := hs n hn
  have hs1 := hs (n + 1) (by omega)
  have hs2 := hs (n + 2) (by omega)
  simp only [Nat.add_assoc, hu0, hu1, hu2, hu3, hd n hn,
    hd (n + 1) (by omega)] at hs0 hs1 hs2
  apply hword
  refine ⟨a n, a (n + 1), a (n + 2), v n, ?_, ?_, ?_⟩
  · linear_combination -hs0
  · linear_combination -hs1
  · linear_combination -hs2

def plusCubic (n : ℕ) : ℤ := 2 * (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) + 1

def minusCubic (n : ℕ) : ℤ := 2 * (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) - 1

theorem plus_phase_hit (a u v : ℕ → ℤ) (T k : ℕ) (hT : T ≤ 7 * k)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    ∃ i : ℕ, i < 4 ∧ u (7 * k + i) ≠ plusCubic (7 * k + i) := by
  have hseven : (7 : ZMod 7) = 0 := by decide
  apply bad_four_step_block a u v plusCubic T (7 * k) hT hnum hden 1 6 0 2
  · norm_num [plusCubic, Int.cast_add, Int.cast_mul, Int.cast_sub, Nat.cast_add, Nat.cast_mul, hseven]
    simp only [hseven, zero_mul, zero_add, add_zero]
    norm_num <;> decide
  · norm_num [plusCubic, Int.cast_add, Int.cast_mul, Int.cast_sub, Nat.cast_add, Nat.cast_mul, hseven]
    simp only [hseven, zero_mul, zero_add, add_zero]
    norm_num <;> decide
  · norm_num [plusCubic, Int.cast_add, Int.cast_mul, Int.cast_sub, Nat.cast_add, Nat.cast_mul, hseven]
    simp only [hseven, zero_mul, zero_add, add_zero]
    norm_num <;> decide
  · norm_num [plusCubic, Int.cast_add, Int.cast_mul, Int.cast_sub, Nat.cast_add, Nat.cast_mul, hseven]
    simp only [hseven, zero_mul, zero_add, add_zero]
    norm_num <;> decide
  · rintro ⟨a0, a1, a2, d0, h0, h1, h2⟩
    apply cubic_plus_word_exact_transport_impossible
    refine ⟨a0, a1, d0, ?_, h1, ?_⟩
    · simpa only [mul_one] using h0
    · simpa only [mul_zero, zero_sub] using h2

theorem minus_phase_hit (a u v : ℕ → ℤ) (T k : ℕ) (hT : T ≤ 1 + 7 * k)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    ∃ i : ℕ, i < 4 ∧ u (1 + 7 * k + i) ≠ minusCubic (1 + 7 * k + i) := by
  have hseven : (7 : ZMod 7) = 0 := by decide
  apply bad_four_step_block a u v minusCubic T (1 + 7 * k) hT hnum hden 4 5 0 1
  · norm_num [minusCubic, Int.cast_add, Int.cast_mul, Int.cast_sub, Nat.cast_add, Nat.cast_mul, hseven]
    simp only [hseven, zero_mul, zero_add, add_zero]
    norm_num <;> decide
  · norm_num [minusCubic, Int.cast_add, Int.cast_mul, Int.cast_sub, Nat.cast_add, Nat.cast_mul, hseven]
    simp only [hseven, zero_mul, zero_add, add_zero]
    norm_num <;> decide
  · norm_num [minusCubic, Int.cast_add, Int.cast_mul, Int.cast_sub, Nat.cast_add, Nat.cast_mul, hseven]
    simp only [hseven, zero_mul, zero_add, add_zero]
    norm_num <;> decide
  · norm_num [minusCubic, Int.cast_add, Int.cast_mul, Int.cast_sub, Nat.cast_add, Nat.cast_mul, hseven]
    simp only [hseven, zero_mul, zero_add, add_zero]
    norm_num <;> decide
  · rintro ⟨a0, a1, a2, d0, h0, h1, h2⟩
    apply cubic_minus_word_exact_transport_impossible
    refine ⟨a0, a1, d0, h0, h1, ?_⟩
    simpa only [mul_zero, zero_sub] using h2

/-- Correct one-seventh bound, for the PLUS terminal profile only. -/
theorem plus_profile_one_seventh (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    ∀ X : ℕ, X ≤ 7 * exceptionCount {n | u n ≠ plusCubic n} X + (7 * T + 7) := by
  apply disjoint_periodic_linear_bound _ (7 * T) 7 4 (by decide) (by decide)
  intro k
  obtain ⟨i, hi, hb⟩ := plus_phase_hit a u v T (T + k) (by omega) hnum hden
  exact ⟨i, hi, by simpa [Nat.mul_add, Nat.add_assoc] using hb⟩

/-- Correct one-seventh bound, for the MINUS terminal profile only. -/
theorem minus_profile_one_seventh (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    ∀ X : ℕ, X ≤ 7 * exceptionCount {n | u n ≠ minusCubic n} X + (7 * T + 8) := by
  have h := disjoint_periodic_linear_bound {n | u n ≠ minusCubic n}
    (1 + 7 * T) 7 4 (by decide) (by decide) (fun k ↦ by
      obtain ⟨i, hi, hb⟩ := minus_phase_hit a u v T (T + k) (by omega) hnum hden
      exact ⟨i, hi, by simpa [Nat.mul_add, Nat.add_assoc] using hb⟩)
  intro X
  have hx := h X
  omega

/-- Exact primitive positive fragment refuting the phase-free plus clause. -/
theorem plus_phase_free_counterexample :
    plusCubic 1 = 13 ∧
    plusCubic 2 = 49 ∧
    plusCubic 3 = 121 ∧
    plusCubic 4 = 241 ∧
    (49 : ℤ) + 44411 = 3420 * 13 ∧
    (151885620 : ℤ) = 3420 * 44411 ∧
    (121 : ℤ) + 151885620 = 3099709 * 49 ∧
    (470801223284580 : ℤ) = 3099709 * 151885620 ∧
    (241 : ℤ) + 470801223284580 = 3890919200701 * 121 ∧
    (1831849519391491043458490580 : ℤ) = 3890919200701 * 470801223284580 ∧
    Nat.Coprime 13 44411 ∧
    Nat.Coprime 49 151885620 ∧
    Nat.Coprime 121 470801223284580 ∧
    Nat.Coprime 241 1831849519391491043458490580 ∧
    3420 < (3099709 : ℕ) ∧
    3099709 < (3890919200701 : ℕ) := by
  norm_num [plusCubic, Nat.Coprime]

/-- Exact primitive positive fragment refuting the phase-free minus clause. -/
theorem minus_phase_free_counterexample :
    minusCubic 6 = 671 ∧
    minusCubic 7 = 1007 ∧
    minusCubic 8 = 1439 ∧
    minusCubic 9 = 1979 ∧
    (1007 : ℤ) + 32408293 = 48300 * 671 ∧
    (1565320551900 : ℤ) = 48300 * 32408293 ∧
    (1439 : ℤ) + 1565320551900 = 1554439477 * 1007 ∧
    (2433196060032787356300 : ℤ) = 1554439477 * 1565320551900 ∧
    (1979 : ℤ) + 2433196060032787356300 = 1690893717882409561 * 1439 ∧
    (4114275932285670421925171903779033584300 : ℤ) = 1690893717882409561 * 2433196060032787356300 ∧
    Nat.Coprime 671 32408293 ∧
    Nat.Coprime 1007 1565320551900 ∧
    Nat.Coprime 1439 2433196060032787356300 ∧
    Nat.Coprime 1979 4114275932285670421925171903779033584300 ∧
    48300 < (1554439477 : ℕ) ∧
    1554439477 < (1690893717882409561 : ℕ) := by
  norm_num [minusCubic, Nat.Coprime]

/-- Every positive primitive finite frame can be continued indefinitely.
The chosen next multiplier is v+1; this is not merely a congruence example. -/
theorem primitive_extension (u v : ℤ) (hu : 0 < u) (hv : 0 < v)
    (hcop : IsCoprime u v) :
    0 < (v + 1) * u - v ∧ 0 < (v + 1) * v ∧
    IsCoprime ((v + 1) * u - v) ((v + 1) * v) := by
  obtain ⟨r, s, hrs⟩ := hcop
  refine ⟨by nlinarith, by positivity, ?_⟩
  refine ⟨r + (s - r * (u - 1)) * v, -(s - r * (u - 1)) * (u - 1), ?_⟩
  calc
    (r + (s - r * (u - 1)) * v) * ((v + 1) * u - v) +
        (-(s - r * (u - 1)) * (u - 1)) * ((v + 1) * v)
        = r * u + s * v := by ring
    _ = 1 := hrs

end ErdosProblems.Erdos243.PaperCompleteR9
