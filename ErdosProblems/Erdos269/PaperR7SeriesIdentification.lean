import ErdosProblems.Erdos269.PaperR7ActualOrbit
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Round 7: identify the original smooth-number series with the shell tsum

The distinction is material: a theorem about `dyadicShellTsumTailR235 0` is
not an end-to-end theorem about the paper's `S` until reindexing has been
proved. We build the exponent/smooth-number and shell/exponent equivalences,
prove summability, and identify the literal running-LCM series.

Validation: authored, not compiled. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators

abbrev Exponent235 := ℕ × ℕ × ℕ

def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2

noncomputable def exponentKernel235 (e : Exponent235) : ℝ :=
  (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ)⁻¹

theorem exponentValue235_pos (e : Exponent235) : 0 < exponentValue235 e := by
  unfold exponentValue235 smooth3Val
  positivity

/-- Unique factorisation, with the three exponent coordinates retained. -/
theorem exponentValue235_factorization (e : Exponent235) :
    (exponentValue235 e).factorization =
      Finsupp.single 2 e.1 + Finsupp.single 3 e.2.1 + Finsupp.single 5 e.2.2 := by
  unfold exponentValue235 smooth3Val
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp [Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2),
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3),
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5)]

theorem exponentValue235_injective : Function.Injective exponentValue235 := by
  intro e f hef
  have h := congrArg Nat.factorization hef
  rw [exponentValue235_factorization, exponentValue235_factorization] at h
  have h2 := congrArg (fun f : ℕ →₀ ℕ => f 2) h
  have h3 := congrArg (fun f : ℕ →₀ ℕ => f 3) h
  have h5 := congrArg (fun f : ℕ →₀ ℕ => f 5) h
  simp at h2 h3 h5
  exact Prod.ext h2 (Prod.ext h3 h5)

/-- Positive smooth integers, counted once as numbers rather than as exponents. -/
def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}

noncomputable def exponentSmoothEquiv235 : Exponent235 ≃ Smooth235 where
  toFun e := ⟨exponentValue235 e, ⟨e, rfl⟩⟩
  invFun x := Classical.choose x.property
  left_inv e := exponentValue235_injective (Classical.choose_spec
    (show exponentValue235 e ∈ Set.range exponentValue235 from ⟨e, rfl⟩))
  right_inv x := Subtype.ext (Classical.choose_spec x.property)

/-- The original running-LCM summand at a smooth integer. -/
noncomputable def smoothReciprocal235 (x : Smooth235) : ℝ :=
  (smoothPrefixLcm 2 3 5 x.val : ℝ)⁻¹

theorem smoothReciprocal235_eq_height (x : Smooth235) :
    smoothReciprocal235 x = (threePrimeHeight 2 3 5 x.val : ℝ)⁻¹ := by
  have hx : x.val ≠ 0 := by
    obtain ⟨e, he⟩ := x.property
    rw [← he]
    exact (exponentValue235_pos e).ne'
  unfold smoothReciprocal235
  rw [smoothPrefixLcm_eq_threePrimeHeight
    (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 3)
    (by norm_num : Nat.Prime 5) (by norm_num) (by norm_num) (by norm_num) hx]

theorem smoothReciprocal235_comp_exponent (e : Exponent235) :
    smoothReciprocal235 (exponentSmoothEquiv235 e) = exponentKernel235 e := by
  rw [smoothReciprocal235_eq_height]
  rfl

/-- The scalar `S` as a sum over actual distinct smooth integers and actual LCMs. -/
noncomputable def paperSeries235 : ℝ := ∑' x : Smooth235, smoothReciprocal235 x

def shellIndex235 (e : Exponent235) : ℕ := Nat.log 2 (exponentValue235 e)

theorem exponent_mem_own_shell235 (e : Exponent235) :
    e ∈ dyadicSmoothShell235 (shellIndex235 e) := by
  apply mem_dyadicSmoothShell235_iff.mpr
  exact ⟨Nat.pow_log_le_self 2 (exponentValue235_pos e).ne',
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (exponentValue235 e)⟩

theorem shellIndex235_eq_of_mem {a : ℕ} {e : Exponent235}
    (he : e ∈ dyadicSmoothShell235 a) : shellIndex235 e = a := by
  obtain ⟨hlo, hhi⟩ := mem_dyadicSmoothShell235_iff.mp he
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi

/-- Each exponent vector belongs to exactly one finite dyadic shell. -/
noncomputable def shellExponentEquiv235 :
    (Σ a : ℕ, {e : Exponent235 // e ∈ dyadicSmoothShell235 a}) ≃ Exponent235 where
  toFun z := z.2.val
  invFun e := ⟨shellIndex235 e, ⟨e, exponent_mem_own_shell235 e⟩⟩
  left_inv z := by
    rcases z with ⟨a, ⟨e, he⟩⟩
    have ha := shellIndex235_eq_of_mem he
    change (⟨shellIndex235 e, ⟨e, exponent_mem_own_shell235 e⟩⟩ :
      Σ a : ℕ, {e : Exponent235 // e ∈ dyadicSmoothShell235 a}) = ⟨a, ⟨e, he⟩⟩
    cases ha
    rfl
  right_inv _ := rfl

/-- The finite fibre sum is literally the pre-existing shell mass. -/
theorem tsum_exponentKernel235_shell (a : ℕ) :
    (∑' e : {e : Exponent235 // e ∈ dyadicSmoothShell235 a},
      exponentKernel235 e.val) = dyadicShellMassR235 a := by
  rw [tsum_fintype]
  simp only [exponentKernel235, exponentValue235, dyadicShellMassR235,
    dyadicShellMassQ235, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact Finset.sum_attach (dyadicSmoothShell235 a)
    (fun e : ℕ × ℕ × ℕ =>
      ((threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℕ) : ℝ)⁻¹)

theorem summable_shellSigma_kernel235 :
    Summable (fun z : Σ a : ℕ, {e : Exponent235 // e ∈ dyadicSmoothShell235 a} =>
      exponentKernel235 z.2.val) := by
  apply (summable_sigma_of_nonneg (fun _ => by
    unfold exponentKernel235
    positivity)).mpr
  constructor
  · intro a
    exact (hasSum_fintype _).summable
  · simpa only [tsum_exponentKernel235_shell] using summable_dyadicShellMassR235

theorem summable_exponentKernel235 : Summable exponentKernel235 := by
  exact shellExponentEquiv235.summable_iff.mp summable_shellSigma_kernel235

theorem exponentKernel235_tsum_eq_shellTsum :
    (∑' e : Exponent235, exponentKernel235 e) = dyadicShellTsumTailR235 0 := by
  calc
    (∑' e : Exponent235, exponentKernel235 e) =
        ∑' z : Σ a : ℕ, {e : Exponent235 // e ∈ dyadicSmoothShell235 a},
          exponentKernel235 z.2.val :=
      (shellExponentEquiv235.tsum_eq exponentKernel235).symm
    _ = ∑' a : ℕ, ∑' e : {e : Exponent235 // e ∈ dyadicSmoothShell235 a},
          exponentKernel235 e.val := summable_shellSigma_kernel235.tsum_sigma
    _ = ∑' a : ℕ, dyadicShellMassR235 a := tsum_congr tsum_exponentKernel235_shell
    _ = dyadicShellTsumTailR235 0 := by simp [dyadicShellTsumTailR235]

/-- Convergence of the paper's original, ungrouped smooth-number series. -/
theorem summable_smoothReciprocal235 : Summable smoothReciprocal235 := by
  apply exponentSmoothEquiv235.summable_iff.mp
  exact summable_exponentKernel235.congr
    fun e => (smoothReciprocal235_comp_exponent e).symm

/-- End-to-end identification of the paper's scalar `S`. -/
theorem paperSeries235_eq_shellTsum : paperSeries235 = dyadicShellTsumTailR235 0 := by
  unfold paperSeries235
  calc
    (∑' x : Smooth235, smoothReciprocal235 x) =
        ∑' e : Exponent235, smoothReciprocal235 (exponentSmoothEquiv235 e) :=
      (exponentSmoothEquiv235.tsum_eq smoothReciprocal235).symm
    _ = ∑' e : Exponent235, exponentKernel235 e :=
      tsum_congr smoothReciprocal235_comp_exponent
    _ = dyadicShellTsumTailR235 0 := exponentKernel235_tsum_eq_shellTsum

/-- All clauses of the short-note actual-orbit proposition, on the literal series. -/
theorem short_actual_orbit :
    Summable smoothReciprocal235 ∧
    (∀ a : ℕ, Summable (fun n : ℕ => dyadicShellMassR235 (a + n))) ∧
    (∀ a : ℕ,
      trueNormalizedState (a + 1) =
        (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
          (dyadicOrderedBlockDigit235 a : ℝ)) ∧
    (∀ a : ℕ, 0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 ∧
      (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 <
        90 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ B : ℤ,
      (∃ a : ℕ, ∀ n, a ≤ n → ∃ z : ℤ,
        (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
      (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
        FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31))) := by
  refine ⟨summable_smoothReciprocal235, ?_, actual_orbit_dynamics_and_bounds⟩
  intro a
  exact summable_dyadicShellMassR235.comp_injective fun _ _ h => Nat.add_left_cancel h

/-- All clauses of the long-record shell recurrence, including the infinite sum. -/
theorem long_actual_orbit :
    Summable dyadicShellMassR235 ∧
    paperSeries235 = (∑' a : ℕ, dyadicShellMassR235 a) ∧
    (∀ a : ℕ,
      0 < dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) =
        (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2 * dyadicShellMassR235 a ∧
      trueNormalizedState (a + 1) =
        (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
          (dyadicOrderedBlockDigit235 a : ℝ) ∧
      trueNormalizedState a =
        ∑' n : ℕ, (dyadicOrderedBlockDigit235 (a + n) : ℝ) /
          ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (a + j) : ℝ)) := by
  refine ⟨summable_dyadicShellMassR235, ?_, ?_⟩
  · simpa [dyadicShellTsumTailR235] using paperSeries235_eq_shellTsum
  · intro a
    exact ⟨orderedDigit235_pos a,
      (half_threePrimeHeight_mul_dyadicShellMassR235 a).symm,
      dyadicNormalizedShellTsumTailR235_succ a,
      trueNormalizedState_eq_digit_tsum a⟩

end ErdosProblems.Erdos269.PaperR7
