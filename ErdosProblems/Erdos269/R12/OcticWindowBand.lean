import ErdosProblems.Erdos269.R12.ExactModulus
import ErdosProblems.Erdos269.LongWindowCapR11

/-!
# Enlarged equivalence band: little-o(8^a), rather than little-o(2^a)

For the actual 2,3,5 height word, 8^len/15 < W. Keeping this exact scale
strictly enlarges the sufficient decay condition in the long paper. The
carry-dominating lower bound is still required. No irrationality producer
is assumed or proved unconditionally. All Lean execution UNRUN.
-/
namespace ErdosProblems.Erdos269.PaperR12
open PaperR7 PaperR8 PaperR10 PaperR11 Filter
open scoped Topology

theorem octic_cap_is_exactly_beaten (G : ℕ → ℕ → ℕ)
    (hsmall : ∀ B, 0 < B →
      Tendsto (fun n : ℕ => (G B n : ℝ) / (8 : ℝ) ^ n) atTop (𝓝 0)) :
    ∀ B lo : ℕ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ len : ℕ, 0 < len ∧
        ((max (G B (lo + len)) (B * bridgeWidth (lo + len)) : ℕ) : ℝ) /
          (actualWindowBase lo len : ℝ) < ε := by
  intro B lo hB ε hε
  have hlo : 0 < (8 : ℝ) ^ lo := by positivity
  have hev : ∀ᶠ n : ℕ in atTop,
      (G B n : ℝ) / (8 : ℝ) ^ n < ε / (15 * (8 : ℝ) ^ lo) :=
    (tendsto_order.1 (hsmall B hB)).2 _ (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨k, hk, hquad⟩ := exists_len_quadratic_div_lt (B * 90) (lo + N) hε
  have hlen : 0 < N + k := by omega
  have h8 : 0 < (8 : ℝ) ^ (N + k) := by positivity
  have h2 : 0 < (2 : ℝ) ^ k := by positivity
  have hW : (0 : ℝ) < (actualWindowBase lo (N + k) : ℝ) := by
    exact_mod_cast windowBase235_pos lo (N + k)
  have hW8 := (long_window_growth lo (N + k) (by omega)).2.1
  have hgshift : (G B (lo + (N + k)) : ℝ) / (8 : ℝ) ^ (N + k) < ε / 15 := by
    calc
      _ = (8 : ℝ) ^ lo *
          ((G B (lo + (N + k)) : ℝ) / (8 : ℝ) ^ (lo + (N + k))) := by
        rw [pow_add (8 : ℝ) lo (N + k)]
        field_simp
      _ < (8 : ℝ) ^ lo * (ε / (15 * (8 : ℝ) ^ lo)) :=
        mul_lt_mul_of_pos_left (hN _ (by omega)) hlo
      _ = ε / 15 := by field_simp
  have hg : (G B (lo + (N + k)) : ℝ) <
      ε * (actualWindowBase lo (N + k) : ℝ) := by
    have h1 := (div_lt_iff₀ h8).1 hgshift
    have h2 := mul_lt_mul_of_pos_left hW8 hε
    nlinarith only [h1, h2]
  have hden : (2 : ℝ) ^ k ≤ (actualWindowBase lo (N + k) : ℝ) := by
    have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (N + k) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
        (by omega : k ≤ N + k)
    have hbase : (2 : ℝ) ^ (N + k) ≤ (actualWindowBase lo (N + k) : ℝ) := by
      exact_mod_cast two_pow_le_windowBase235 lo (N + k)
    exact hpow.trans hbase
  have hb : ((B * bridgeWidth (lo + (N + k)) : ℕ) : ℝ) <
      ε * (actualWindowBase lo (N + k) : ℝ) := by
    calc
      _ = ((B * 90 * ((lo + N) + k + 1) ^ 2 : ℕ) : ℝ) := by
        unfold bridgeWidth
        push_cast
        ring
      _ < ε * (2 : ℝ) ^ k := (div_lt_iff₀ h2).1 hquad
      _ ≤ ε * (actualWindowBase lo (N + k) : ℝ) :=
        mul_le_mul_of_nonneg_left hden hε.le
  refine ⟨N + k, hlen, (div_lt_iff₀ hW).2 ?_⟩
  rw [Nat.cast_max]
  exact max_lt_iff.2 ⟨hg, hb⟩

/-- A genuine strengthening of the long-paper band. The universal cap and
limit hypotheses are explicit; the conclusion is an equivalence, not an
unconditional proof of either side. -/
theorem octic_window_band (G : ℕ → ℕ → ℕ)
    (hdom : ∀ B a, 0 < B → longPaperCap B a ≤ G B a)
    (hsmall : ∀ B, 0 < B →
      Tendsto (fun n : ℕ => (G B n : ℝ) / (8 : ℝ) ^ n) atTop (𝓝 0)) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G ↔
      Irrational paperSeries235 := by
  constructor
  · exact irrational_of_escape_dominating_sharp_cap G
      (fun B a hB => (sharpPaperCap_le_longR11 B a).trans (hdom B a hB))
  · intro h
    exact escape_of_irrational_of_exact_beating
      (irrational_tail_one_of_paperSeries h) G (octic_cap_is_exactly_beaten G hsmall)

end ErdosProblems.Erdos269.PaperR12
