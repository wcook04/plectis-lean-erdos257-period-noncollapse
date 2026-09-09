import ErdosProblems.Erdos243.PaperCompleteR9.PolynomialCorrections
import Mathlib

/-!
# Window incidences and quantitative exceptional density

Authored candidate, UNRUN. Every hit is charged to an exceptional index together
with its offset. Overlapping windows therefore cost at most their length, not
the number of residue classes. No density assumption is hidden in the counting
lemmas. `LowerDensityAtLeast` uses the usual epsilon / eventual-prefix definition
of a lower bound for the lower asymptotic density (prefixes start at zero).
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9

/-- Literal eventual-prefix formulation of a lower asymptotic density bound. -/
def LowerDensityAtLeast (E : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    (d - ε) * (X : ℝ) ≤ (exceptionCount E X : ℝ)

/-- Charge each centre to a hit and its offset. This remains valid when the
windows overlap arbitrarily. The target prefix is supplied explicitly. -/
theorem window_incidence_bound (A : Finset ℕ) (E : Set ℕ) (L X : ℕ)
    (hhit : ∀ n ∈ A, ∃ i : ℕ, i < L ∧ n + i < X ∧ n + i ∈ E) :
    A.card ≤ L * exceptionCount E X := by
  classical
  have h : ∀ n : ↥A, ∃ i : ℕ, i < L ∧ (n : ℕ) + i < X ∧ (n : ℕ) + i ∈ E :=
    fun n ↦ hhit n n.property
  choose w hw using h
  let f : ↥A → (↥(exceptionFinset E X)) × Fin L := fun n ↦
    (⟨(n : ℕ) + w n, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hw n).2.1, (hw n).2.2⟩⟩,
     ⟨w n, (hw n).1⟩)
  have hf : Function.Injective f := by
    intro n m hnm
    have he := congrArg (fun z : (↥(exceptionFinset E X)) × Fin L ↦
      ((z.1 : ℕ), (z.2 : ℕ))) hnm
    have hv := congrArg Prod.fst he
    have hi := congrArg Prod.snd he
    change (n : ℕ) + w n = (m : ℕ) + w m at hv
    change w n = w m at hi
    apply Subtype.ext
    omega
  have hc := Fintype.card_le_of_injective f hf
  simpa [exceptionCount, Nat.mul_comm] using hc

/-- A whole rectangle of residue centres has exactly the expected cardinality.
The proof uses the quotient and remainder, not an informal independence claim. -/
theorem residue_rectangle_card (M T K : ℕ) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r < M) :
    ((Finset.range K ×ˢ R).image (fun kr ↦ (T + kr.1) * M + kr.2)).card =
      K * R.card := by
  classical
  have hinj : Set.InjOn (fun kr : ℕ × ℕ ↦ (T + kr.1) * M + kr.2)
      ↑(Finset.range K ×ˢ R) := by
    intro x hx y hy he
    obtain ⟨hxK, hxR⟩ := Finset.mem_product.mp hx
    obtain ⟨hyK, hyR⟩ := Finset.mem_product.mp hy
    have hxr := hR x.2 hxR
    have hyr := hR y.2 hyR
    have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hxr
    have hr : x.2 = y.2 := by
      have := congrArg (fun z : ℕ ↦ z % M) he
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hxr, Nat.mod_eq_of_lt hyr] using this
    have hk : x.1 = y.1 := by
      have he' : (T + x.1) * M + x.2 = (T + y.1) * M + y.2 := by
        simpa using he
      rw [hr] at he'
      have hm : (T + x.1) * M = (T + y.1) * M := Nat.add_right_cancel he'
      have ht := Nat.eq_of_mul_eq_mul_right hM hm
      omega
    exact Prod.ext hk hr
  rw [Finset.card_image_iff.mpr hinj, Finset.card_product, Finset.card_range]

/-- Simultaneous residue obstructions give a finite quantitative inequality.
Each residue starts one length-`L` obstruction per period `M`. The constant
accounts for the initial segment, an incomplete period, and the right edge. -/
theorem residue_window_linear_bound (E : Set ℕ) (M L T : ℕ)
    (hM : 0 < M) (R : Finset ℕ) (hR : ∀ r ∈ R, r < M)
    (hhit : ∀ n : ℕ, T ≤ n → n % M ∈ R →
      ∃ i : ℕ, i < L ∧ n + i ∈ E) :
    ∀ X : ℕ, R.card * X ≤ M * L * exceptionCount E X +
      R.card * (M * T + M + L) := by
  classical
  intro X
  by_cases hsmall : X < M * T + L
  · have h1 := Nat.mul_le_mul_left R.card (Nat.le_of_lt hsmall)
    have h2 := Nat.mul_le_mul_left R.card
      (show M * T + L ≤ M * T + M + L by omega)
    omega
  let K := (X - L) / M - T
  have hL : L ≤ X := by omega
  have hsub := Nat.sub_add_cancel hL
  have hT : T ≤ (X - L) / M := by
    apply (Nat.le_div_iff_mul_le hM).mpr
    nlinarith
  have hq : T + K = (X - L) / M := by dsimp [K]; omega
  have hmod := Nat.mod_add_div (X - L) M
  rw [← hq] at hmod
  have hrem := Nat.mod_lt (X - L) hM
  have hbase : (T + K) * M ≤ X - L := by
    rw [Nat.mul_comm]
    omega
  have hend : (T + K) * M + L ≤ X := by omega
  have hX : X ≤ M * K + (M * T + M + L) := by nlinarith
  let A := ((Finset.range K ×ˢ R).image (fun kr ↦ (T + kr.1) * M + kr.2))
  have hc : A.card = K * R.card := residue_rectangle_card M T K R hR
  have hhitA : ∀ n ∈ A, ∃ i : ℕ, i < L ∧ n + i < X ∧ n + i ∈ E := by
    intro n hn
    obtain ⟨⟨k, r⟩, hkr, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hk, hr⟩ := Finset.mem_product.mp hkr
    have hk' := Finset.mem_range.mp hk
    have hr' := hR r hr
    have hmul := Nat.mul_le_mul_left (T + k) (show 1 ≤ M by omega)
    have hnT : T ≤ (T + k) * M + r := by nlinarith
    have hnR : ((T + k) * M + r) % M ∈ R := by
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hr'] using hr
    obtain ⟨i, hi, he⟩ := hhit _ hnT hnR
    refine ⟨i, hi, ?_, he⟩
    have hkm := Nat.mul_le_mul_right M (Nat.succ_le_of_lt hk')
    nlinarith
  have hinc := window_incidence_bound A E L X hhitA
  rw [hc] at hinc
  have hincM := Nat.mul_le_mul_left M hinc
  have hXR := Nat.mul_le_mul_left R.card hX
  nlinarith

/-- Convert an explicit real linear counting inequality into lower density. -/
theorem lowerDensityAtLeast_of_linear_bound (E : Set ℕ) (a b c : ℝ)
    (hb : 0 < b)
    (h : ∀ X : ℕ, a * (X : ℝ) ≤ b * (exceptionCount E X : ℝ) + c) :
    LowerDensityAtLeast E (a / b) := by
  intro ε hε
  have hbε : 0 < b * ε := mul_pos hb hε
  obtain ⟨N, hN⟩ := exists_nat_gt (c / (b * ε))
  refine ⟨N, ?_⟩
  intro X hNX
  have hNX' : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hNX
  have hcN : c < (N : ℝ) * (b * ε) := (div_lt_iff₀ hbε).mp hN
  have hcX : c ≤ (b * ε) * (X : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hNX' (le_of_lt hbε)
    nlinarith
  have hX := h X
  have hab : b * (a / b) = a := by field_simp [ne_of_gt hb]
  apply le_of_mul_le_mul_left (a := b) (b := (a / b - ε) * (X : ℝ))
      (c := exceptionCount E X) (by
    calc
    b * ((a / b - ε) * (X : ℝ)) = a * (X : ℝ) - (b * ε) * (X : ℝ) := by
      rw [← mul_assoc, mul_sub, hab]
      ring
    _ ≤ b * (exceptionCount E X : ℝ) := by linarith
    ) hb

/-- Uniform density of a union of residue obstructions; all overlaps have
already been accounted for by the incidence injection. -/
theorem residue_window_lower_density (E : Set ℕ) (M L T : ℕ)
    (hM : 0 < M) (hL : 0 < L) (R : Finset ℕ) (hR : ∀ r ∈ R, r < M)
    (hhit : ∀ n : ℕ, T ≤ n → n % M ∈ R →
      ∃ i : ℕ, i < L ∧ n + i ∈ E) :
    LowerDensityAtLeast E ((R.card : ℝ) / ((M : ℝ) * (L : ℝ))) := by
  apply lowerDensityAtLeast_of_linear_bound E (R.card : ℝ)
    ((M : ℝ) * (L : ℝ)) ((R.card * (M * T + M + L) : ℕ) : ℝ)
  · positivity
  · intro X
    exact_mod_cast residue_window_linear_bound E M L T hM R hR hhit X

/-- Lower density bounds are closed under limits of the numerical bounds. -/
theorem lowerDensityAtLeast_of_approximations (E : Set ℕ) (d : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ,
      d - ε < c ∧ LowerDensityAtLeast E c) :
    LowerDensityAtLeast E d := by
  intro ε hε
  obtain ⟨c, hc, hE⟩ := h (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := hE (ε / 2) (by linarith)
  refine ⟨N, ?_⟩
  intro X hX
  have hn := hN X hX
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  exact (mul_le_mul_of_nonneg_right (by linarith : d - ε ≤ c - ε / 2) hX0).trans hn

/-- Failure of the `1/L` lower density bound forces arbitrarily late wholly
non-exceptional windows. This is useful before stabilising an arithmetic gcd. -/
theorem clean_windows_of_not_lower_density (E : Set ℕ) (L : ℕ) (hL : 0 < L)
    (hnot : ¬ LowerDensityAtLeast E (1 / (L : ℝ))) :
    ∀ T : ℕ, ∃ n : ℕ, T ≤ n ∧ ∀ i : ℕ, i < L → n + i ∉ E := by
  classical
  intro T
  by_contra hn
  have hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ T + L * k + i ∈ E := by
    intro k
    by_contra hk
    apply hn
    refine ⟨T + L * k, by omega, ?_⟩
    intro i hi he
    exact hk ⟨i, hi, he⟩
  apply hnot
  apply lowerDensityAtLeast_of_linear_bound E 1 (L : ℝ) ((T + L : ℕ) : ℝ)
  · exact_mod_cast hL
  · intro X
    have h := disjoint_periodic_linear_bound E T L L hL (le_refl L) hhit X
    have hr : (X : ℝ) ≤ (L : ℝ) * (exceptionCount E X : ℝ) + ((T + L : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa only [one_mul] using hr

end ErdosProblems.Erdos243.PaperCompleteR11
