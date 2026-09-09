import ErdosProblems.Erdos1041.WeightedGroupedRigidityR10
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperMomentConsumers
import ErdosProblems.Erdos1041.FreePointCentralCompletion
import ErdosProblems.Erdos1041.FreePointUniformRadius

/-! Paper endpoints: weighted equality, centroid loss, Cauchy--Schwarz and
all-degree equal-weight free points. The existing non-strict theorem is reused.
All compilation and axiom audits are UNRUN. -/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
noncomputable section
namespace ErdosProblems.Erdos1041
open Real Complex

/-- This is the exact existing paper target, with no added supplier hypothesis. -/
theorem paper_weighted_free_point : PaperAnalyticTargets.WeightedFreePoint := by
  intro m c w hc hw hsum
  constructor
  · exact weighted_closed_disc_product_bound w c (fun j => (hw j).le) hsum hc
  · exact weighted_equality_iff_all_zero w c hw hsum hc

/-- Stronger support-correct extension of the paper theorem to zero weights. -/
theorem paper_weighted_free_point_nonnegative {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) :
    weightedQuadratic w c ≤ 1 ∧
      (weightedQuadratic w c = 1 ↔ ∀ j, 0 < w j → c j = 0) :=
  ⟨weighted_closed_disc_product_bound w c hw hsum hc,
    weighted_equality_iff_positive_support_zero w c hw hsum hc⟩

/-- The centroid formula following res:fp-weighted-all-degree, including the
closed-disc endpoint and nonnegative weights. -/
theorem weighted_centroid_refinement {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) :
    weightedQuadratic w c ≤ 1 - ‖∑ j, (w j : ℂ) * c j‖ ^ 2 := by
  have h := weighted_closed_disc_single_deficit w c hw hsum hc 1 (by omega)
  rw [weightedTaylorCoeff_one w c hc, norm_neg, Complex.norm_conj] at h
  norm_num at h
  linarith

/-- Weighted Cauchy--Schwarz in the precise probability-weight normalisation.
This also records the quantitative linear consequence of the centroid bound. -/
theorem weighted_cauchy_schwarz_probability {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    (∑ j, w j * x j) ^ 2 ≤ ∑ j, w j * x j ^ 2 := by
  let μ := ∑ j, w j * x j
  have hnonneg : 0 ≤ ∑ j, w j * (x j - μ) ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
  have he : (∑ j, w j * (x j - μ) ^ 2) =
      (∑ j, w j * x j ^ 2) - μ ^ 2 := by
    calc
      _ = ∑ j, (w j * x j ^ 2 - 2 * μ * (w j * x j) + μ ^ 2 * w j) :=
        Finset.sum_congr rfl (fun j _ => by ring)
      _ = (∑ j, w j * x j ^ 2) - 2 * μ * (∑ j, w j * x j) +
          μ ^ 2 * (∑ j, w j) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [hsum]; change _ - 2 * μ * μ + μ ^ 2 * 1 = _; ring
  rw [he] at hnonneg
  dsimp [μ] at *
  linarith

theorem weighted_linear_centroid_refinement {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, w j * weightedGeometric w c (c j)) ^ 2 ≤
      1 - ‖∑ j, (w j : ℂ) * c j‖ ^ 2 :=
  (weighted_cauchy_schwarz_probability w (fun j => weightedGeometric w c (c j)) hw hsum).trans
    (weighted_centroid_refinement w c hw hsum hc)

theorem weighted_linear_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) :
    ∑ j, w j * weightedGeometric w c (c j) ≤ 1 :=
  PaperMomentConsumers.weighted_first_of_second w (fun j => weightedGeometric w c (c j))
    hw hsum (weighted_closed_disc_product_bound w c hw hsum hc)

theorem weighted_linear_equality_iff {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, w j * weightedGeometric w c (c j)) = 1 ↔
      ∀ j, 0 < w j → c j = 0 := by
  constructor
  · intro heq
    have hcs := weighted_cauchy_schwarz_probability w
      (fun j => weightedGeometric w c (c j)) hw hsum
    rw [heq, one_pow] at hcs
    have hQ : weightedQuadratic w c = 1 :=
      le_antisymm (weighted_closed_disc_product_bound w c hw hsum hc) hcs
    exact weighted_positive_support_zero_of_equality w c hw hsum hc hQ
  · intro hs
    simp only [weightedGeometric_eq_one_of_support_zero w c hw hs, mul_one]
    exact hsum

/-- A local finite-product proof avoids imposing positivity on vanishing factors. -/
theorem rpow_finset_prod_nonnegative {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (q : ℝ) :
    (∏ i ∈ s, x i) ^ q = ∏ i ∈ s, (x i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      Real.mul_rpow (hx i (Finset.mem_insert_self i s))
        (Finset.prod_nonneg (fun j hj => hx j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))]

def equalFreePointRow {m : ℕ} (c : Fin m → ℂ) (j : Fin m) : ℝ :=
  (∏ k, ‖1 - conj (c k) * c j‖) ^ (1 / (m : ℝ))

theorem equalWeight_sum {m : ℕ} (hm : 0 < m) :
    (∑ _j : Fin m, (1 / (m : ℝ))) = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [hm0]

theorem equalFreePointRow_eq_weighted {m : ℕ} (c : Fin m → ℂ) (j : Fin m) :
    equalFreePointRow c j = weightedGeometric (fun _ : Fin m => 1 / (m : ℝ)) c (c j) := by
  exact rpow_finset_prod_nonnegative Finset.univ
    (fun k => ‖1 - conj (c k) * c j‖) (fun k _ => norm_nonneg _) _

/-- The quadratic equal-weight theorem, stronger than FP_m itself. -/
theorem equal_free_point_quadratic {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 1) : ∑ j, equalFreePointRow c j ^ 2 ≤ (m : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h := weighted_closed_disc_product_bound (fun _ : Fin m => 1 / (m : ℝ)) c
    (fun _ => by positivity) (equalWeight_sum hm) hc
  change (∑ j, (1 / (m : ℝ)) *
    weightedGeometric (fun _ : Fin m => 1 / (m : ℝ)) c (c j) ^ 2) ≤ 1 at h
  simp only [← equalFreePointRow_eq_weighted] at h
  rw [← Finset.mul_sum] at h
  have h' : (∑ j, equalFreePointRow c j ^ 2) / (m : ℝ) ≤ 1 := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using h
  exact (div_le_one hmpos).mp h'

theorem equal_free_point_linear {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 1) : ∑ j, equalFreePointRow c j ≤ (m : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h := weighted_linear_bound (fun _ : Fin m => 1 / (m : ℝ)) c
    (fun _ => by positivity) (equalWeight_sum hm) hc
  simp only [← equalFreePointRow_eq_weighted] at h
  rw [← Finset.mul_sum] at h
  have h' : (∑ j, equalFreePointRow c j) / (m : ℝ) ≤ 1 := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using h
  exact (div_le_one hmpos).mp h'

theorem reflected_kernel_symmetry (a b : ℂ) :
    ‖1 - conj a * b‖ = ‖1 - conj b * a‖ := by
  calc
    ‖1 - conj a * b‖ = ‖conj (1 - conj a * b)‖ := (Complex.norm_conj _).symm
    _ = _ := by simp [mul_comm]

/-- The orientation and exponent used literally in both papers. -/
theorem geometric_row_mean_closed_disc_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, (∏ k, ‖1 - conj (c j) * c k‖) ^ ((m : ℝ)⁻¹)) ≤ (m : ℝ) := by
  have h := equal_free_point_linear hm c hc
  simpa only [equalFreePointRow, reflected_kernel_symmetry, one_div] using h

/-- Reuse the supplied central-region result, without expanding its old radius. -/
theorem paper_central_region_comparison {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ Real.sqrt (1 - Real.exp (-2))) :
    (∑ j, (∏ k, ‖1 - conj (c j) * c k‖) ^ ((m : ℝ)⁻¹)) ≤ (m : ℝ) :=
  FreePointHilbertCertificate.geometric_row_mean_central_le hm c hc

end ErdosProblems.Erdos1041
end
