import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős #1041: quantitative straight-segment certificates for collinear roots

The analytic collinear-root argument produces adjacent roots `a,b` and an
intervening critical point `c` such that the critical value controls the whole
real segment and has norm below one.  This module isolates the final geometric
consumer: the segment lies in the open lemniscate and its Euclidean length is
strictly below two.  The interface is stated using endpoint distance, so it
also consumes the stronger hypothesis that the collinear root set itself has
diameter below two; the unit-disk version is an immediate corollary.

The polynomial supplier (discriminant/Fekete plus real-root interlacing) is
recorded analytically in `CollinearRootCase.md`; the theorem below is deliberately
stated at the exact interface that supplier emits.
-/

namespace ErdosProblems.Erdos1041

open Set
open Polynomial
open Module
open scoped BigOperators

/-- Hadamard's determinant inequality for real square matrices, stated using
the Euclidean norms of the rows.  The proof is the standard volume-form
argument; it is included because collinearity makes the Vandermonde matrix
real, avoiding any complex determinant detour. -/
theorem abs_det_le_prod_euclidean_rowNorm
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, ‖WithLp.toLp 2 (A i)‖ := by
  classical
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
    ⟨finrank_euclideanSpace_fin⟩
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℝ
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
    b.toBasis.orientation
  let v : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i ↦ WithLp.toLp 2 (A i)
  have hvolume := o.abs_volumeForm_apply_le v
  have hrobust : o.volumeForm = b.toBasis.det :=
    o.volumeForm_robust b rfl
  rw [hrobust, Module.Basis.det_apply] at hvolume
  have hmatrix : b.toBasis.toMatrix v = A.transpose := by
    ext i j
    simp [b, v, Module.Basis.toMatrix_apply]
  rw [hmatrix, Matrix.det_transpose] at hvolume
  exact hvolume

/-- The evaluation matrix of the first `n` Chebyshev polynomials. -/
noncomputable def chebyshevEvalMatrix {n : ℕ}
    (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦
    (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (y i)

/-- Product of the leading coefficients of `T₀,…,Tₙ₋₁`. -/
def chebyshevDetScale (n : ℕ) : ℝ :=
  ∏ j : Fin n, (2 : ℝ) ^ ((j : ℕ) - 1)

private theorem sum_fin_tsub_one (n : ℕ) :
    (∑ j : Fin n, ((j : ℕ) - 1)) = (n - 1) * (n - 2) / 2 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ j - 1) (n + 1),
        Finset.sum_range_succ']
      simp [Finset.sum_range_id]

theorem chebyshevDetScale_eq_pow (n : ℕ) :
    chebyshevDetScale n =
      (2 : ℝ) ^ ((n - 1) * (n - 2) / 2) := by
  rw [chebyshevDetScale]
  calc
    (∏ j : Fin n, (2 : ℝ) ^ ((j : ℕ) - 1)) =
        (2 : ℝ) ^ (∑ j : Fin n, ((j : ℕ) - 1)) := by
      simpa using Finset.prod_pow_eq_pow_sum Finset.univ
        (fun j : Fin n ↦ (j : ℕ) - 1) (2 : ℝ)
    _ = (2 : ℝ) ^ ((n - 1) * (n - 2) / 2) := by
      rw [sum_fin_tsub_one]

theorem chebyshevDetScale_sq_eq_pow (n : ℕ) (hn : 2 ≤ n) :
    chebyshevDetScale n ^ 2 =
      (2 : ℝ) ^ ((n - 1) * (n - 2)) := by
  have hdvd : 2 ∣ (n - 1) * (n - 2) := by
    have hn1 : n - 1 = (n - 2) + 1 := by omega
    rw [hn1, mul_comm]
    exact Nat.two_dvd_mul_add_one (n - 2)
  rw [chebyshevDetScale_eq_pow, ← pow_mul,
    Nat.div_mul_cancel hdvd]

/-- Passing from monomials to Chebyshev polynomials multiplies the evaluation
determinant by the product of their leading coefficients. -/
theorem det_chebyshevEvalMatrix {n : ℕ} (y : Fin n → ℝ) :
    (chebyshevEvalMatrix y).det =
      (Matrix.vandermonde y).det * chebyshevDetScale n := by
  classical
  let p : Fin n → ℝ[X] := fun j ↦ Polynomial.Chebyshev.T ℝ (j : ℤ)
  let C : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j ↦ (p j).coeff i
  have hdeg (j : Fin n) : (p j).natDegree = (j : ℕ) := by
    simp [p]
  have hmatrix : chebyshevEvalMatrix y = Matrix.vandermonde y * C := by
    simpa [chebyshevEvalMatrix, C] using
      Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
        y p (fun j ↦ (hdeg j).le)
  have hdetC : C.det = chebyshevDetScale n := by
    rw [Matrix.det_of_upperTriangular
      (Matrix.matrixOfPolynomials_blockTriangular p (fun j ↦ (hdeg j).le))]
    apply Finset.prod_congr rfl
    intro j _hj
    change (p j).coeff (j : ℕ) = (2 : ℝ) ^ ((j : ℕ) - 1)
    rw [← hdeg j, Polynomial.coeff_natDegree]
    simp [p]
  rw [hmatrix, Matrix.det_mul, hdetC]

/-- Chebyshev–Hadamard interval determinant bound.  Unlike the monomial
version below, this retains the full product of Chebyshev leading
coefficients; simplifying that product gives the factor
`2 ^ ((n - 1) * (n - 2) / 2)`. -/
theorem chebyshevDetScale_sq_mul_sq_abs_det_vandermonde_le_pow_card
    {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    chebyshevDetScale n ^ 2 * |(Matrix.vandermonde y).det| ^ 2 ≤
      (n : ℝ) ^ n := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := chebyshevEvalMatrix y
  let row : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i ↦ WithLp.toLp 2 (B i)
  have hrow (i : Fin n) : ‖row i‖ ^ 2 ≤ (n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ j : Fin n, (row i j) ^ 2) ≤ ∑ _j : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _hj
        have habs :
            |(Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (y i)| ≤ 1 :=
          Polynomial.Chebyshev.abs_eval_T_real_le_one (j : ℤ) (hy i)
        change ((Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (y i)) ^ 2 ≤ 1
        rw [← sq_abs]
        nlinarith [abs_nonneg ((Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (y i))]
      _ = (n : ℝ) := by simp
  have hdet := abs_det_le_prod_euclidean_rowNorm B
  have hprodNonneg : 0 ≤ ∏ i, ‖row i‖ := by positivity
  have hB : |B.det| ^ 2 ≤ (n : ℝ) ^ n := by
    calc
      |B.det| ^ 2 ≤ (∏ i, ‖row i‖) ^ 2 := by
        change |B.det| ≤ ∏ i, ‖row i‖ at hdet
        nlinarith [abs_nonneg B.det, hprodNonneg]
      _ = ∏ i, ‖row i‖ ^ 2 := by rw [Finset.prod_pow]
      _ ≤ ∏ _i : Fin n, (n : ℝ) :=
        Finset.prod_le_prod (fun _ _ ↦ sq_nonneg _) (fun i _ ↦ hrow i)
      _ = (n : ℝ) ^ n := by simp
  have hscale : 0 ≤ chebyshevDetScale n := by
    unfold chebyshevDetScale
    positivity
  rw [show B.det = (Matrix.vandermonde y).det * chebyshevDetScale n by
    simpa [B] using det_chebyshevEvalMatrix y,
    abs_mul, abs_of_nonneg hscale, mul_pow] at hB
  nlinarith

/-- The Chebyshev–Hadamard bound with the leading-coefficient product
simplified. -/
theorem pow_two_mul_sq_abs_det_vandermonde_le_pow_card
    {n : ℕ} (hn : 2 ≤ n) (y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    (2 : ℝ) ^ ((n - 1) * (n - 2)) *
        |(Matrix.vandermonde y).det| ^ 2 ≤
      (n : ℝ) ^ n := by
  rw [← chebyshevDetScale_sq_eq_pow n hn]
  exact chebyshevDetScale_sq_mul_sq_abs_det_vandermonde_le_pow_card y hy

/-- Pairwise-distance form of the Chebyshev-refined interval Fekete bound. -/
theorem pow_two_mul_sq_pairwiseDistanceProduct_le_pow_card
    {n : ℕ} (hn : 2 ≤ n) (y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    (2 : ℝ) ^ ((n - 1) * (n - 2)) *
        (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, |y j - y i|) ^ 2 ≤
      (n : ℝ) ^ n := by
  simpa [Matrix.det_vandermonde, Finset.abs_prod] using
    pow_two_mul_sq_abs_det_vandermonde_le_pow_card hn y hy

/-- Real Fekete/Hadamard bound in the exact squared form needed by the
collinear-root theorem. -/
theorem sq_abs_det_vandermonde_le_pow_card
    {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    |(Matrix.vandermonde y).det| ^ 2 ≤ (n : ℝ) ^ n := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.vandermonde y
  let row : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i ↦ WithLp.toLp 2 (A i)
  have hrow (i : Fin n) : ‖row i‖ ^ 2 ≤ (n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ j : Fin n, (row i j) ^ 2) ≤ ∑ _j : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _hj
        have habs : |y i ^ (j : ℕ)| ≤ 1 := by
          rw [abs_pow]
          exact pow_le_one₀ (abs_nonneg _) (hy i)
        change (y i ^ (j : ℕ)) ^ 2 ≤ 1
        rw [← sq_abs]
        nlinarith [abs_nonneg (y i ^ (j : ℕ))]
      _ = (n : ℝ) := by simp
  have hdet := abs_det_le_prod_euclidean_rowNorm A
  have hprodNonneg : 0 ≤ ∏ i, ‖row i‖ := by positivity
  calc
    |(Matrix.vandermonde y).det| ^ 2 = |A.det| ^ 2 := by rfl
    _ ≤ (∏ i, ‖row i‖) ^ 2 := by
      change |A.det| ≤ ∏ i, ‖row i‖ at hdet
      nlinarith [abs_nonneg A.det, hprodNonneg]
    _ = ∏ i, ‖row i‖ ^ 2 := by rw [Finset.prod_pow]
    _ ≤ ∏ _i : Fin n, (n : ℝ) :=
      Finset.prod_le_prod (fun _ _ ↦ sq_nonneg _) (fun i _ ↦ hrow i)
    _ = (n : ℝ) ^ n := by simp

/-- Pairwise-distance form of the real Fekete bound. -/
theorem sq_pairwiseDistanceProduct_le_pow_card
    {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, |y j - y i|) ^ 2 ≤
      (n : ℝ) ^ n := by
  simpa [Matrix.det_vandermonde, Finset.abs_prod] using
    sq_abs_det_vandermonde_le_pow_card y hy

/-- Exact cubic interval discriminant estimate.  For normalized roots
`-1, t, 1`, the Vandermonde product is `2 (1 - t²)` and its square is at most
four.  This is the algebraic source of the sharp cubic level
`D³ / (12 √3)`. -/
theorem cubic_normalized_vandermonde_sq_le_four
    {t : ℝ} (ht : |t| ≤ 1) :
    ((t + 1) * 2 * (1 - t)) ^ 2 ≤ 4 := by
  have ht2 : t ^ 2 ≤ 1 := by
    calc
      t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      _ ≤ (1 : ℝ) ^ 2 := (sq_le_sq₀ (abs_nonneg t) zero_le_one).2 ht
      _ = 1 := by norm_num
  have hs0 : 0 ≤ 1 - t ^ 2 := by linarith
  have hs1 : 1 - t ^ 2 ≤ 1 := sub_le_self _ (sq_nonneg t)
  have hs2 : (1 - t ^ 2) * (1 - t ^ 2) ≤ 1 * 1 :=
    mul_self_le_mul_self hs0 hs1
  calc
    ((t + 1) * 2 * (1 - t)) ^ 2 =
        4 * ((1 - t ^ 2) * (1 - t ^ 2)) := by ring
    _ ≤ 4 * (1 * 1) := mul_le_mul_of_nonneg_left hs2 (by norm_num)
    _ = 4 := by norm_num

/-- If a finite product of critical-value moduli is below one, at least one
critical value is below one.  This is the order-theoretic last step of the
discriminant/Fekete argument. -/
theorem exists_norm_lt_one_of_prod_norm_lt_one
    {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (hprod : ∏ i, ‖v i‖ < 1) :
    ∃ i, ‖v i‖ < 1 := by
  by_contra hnone
  have hge : ∀ i, (1 : ℝ) ≤ ‖v i‖ := by
    intro i
    exact le_of_not_gt (fun hi ↦ hnone ⟨i, hi⟩)
  have hone : (1 : ℝ) ≤ ∏ i, ‖v i‖ := by
    calc
      (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
      _ ≤ ∏ i, ‖v i‖ :=
        Finset.prod_le_prod (fun _ _ ↦ zero_le_one) (fun i _ ↦ hge i)
  exact (not_lt_of_ge hone) hprod

/-- Finite geometric-mean selection in the exact form used by the quantitative
diameter theorem. -/
theorem exists_le_of_prod_le_pow
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hprod : ∏ i, v i ≤ r ^ Fintype.card ι) :
    ∃ i, v i ≤ r := by
  by_contra hnone
  have hlt : ∀ i, r < v i := by
    intro i
    exact lt_of_not_ge (fun hi ↦ hnone ⟨i, hi⟩)
  have hstrict : r ^ Fintype.card ι < ∏ i, v i := by
    calc
      r ^ Fintype.card ι = ∏ _i : ι, r := by simp
      _ < ∏ i, v i :=
        Finset.prod_lt_prod_of_nonempty
          (fun _ _ ↦ hr) (fun i _ ↦ hlt i) Finset.univ_nonempty
  exact (not_lt_of_ge hprod) hstrict

/-- Interlacing turns an adjacent-root interval into a one-peak interval.
This lemma records the only order-theoretic fact subsequently used: monotone
growth up to `c` and monotone decay after `c` make `c` dominate the interval. -/
theorem norm_le_peak_of_monotone_antitone
    {g : ℝ → ℂ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hleft : MonotoneOn (fun x ↦ ‖g x‖) (Icc a c))
    (hright : AntitoneOn (fun x ↦ ‖g x‖) (Icc c b)) :
    ∀ x ∈ Icc a b, ‖g x‖ ≤ ‖g c‖ := by
  intro x hx
  by_cases hxc : x ≤ c
  · exact hleft ⟨hx.1, hxc⟩ ⟨hac, le_rfl⟩ hxc
  · have hcx : c ≤ x := le_of_lt (lt_of_not_ge hxc)
    exact hright ⟨le_rfl, hcb⟩ ⟨hcx, hx.2⟩ hcx

/-- The affine segment from `a` to `b`, parametrised by the real unit interval. -/
def realSegment (a b : ℂ) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * a + (t : ℂ) * b

/-- The exact certificate emitted by the collinear-root argument: one interior
critical value dominates the modulus on the adjacent-root segment. -/
structure CollinearPeakCertificate (f : ℂ → ℂ) (a b c : ℂ) : Prop where
  endpoint_distance_lt_two : dist a b < 2
  critical_value_lt_one : ‖f c‖ < 1
  segment_control : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (realSegment a b t)‖ ≤ ‖f c‖

/-- Two points in the open unit disk are at distance below two.  This is the
only place the original Erdős disk hypothesis enters the segment consumer. -/
theorem dist_lt_two_of_norm_lt_one {a b : ℂ}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    dist a b < 2 := by
  calc
    dist a b = ‖a - b‖ := by rw [dist_eq_norm]
    _ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    _ < 2 := by linarith

/-- A collinear peak certificate gives the complete Erdős-1041 conclusion for
its two endpoint roots: strict lemniscate containment and length below two. -/
theorem CollinearPeakCertificate.straightSegment_solution
    {f : ℂ → ℂ} {a b c : ℂ}
    (h : CollinearPeakCertificate f a b c) :
    (∀ t ∈ Icc (0 : ℝ) 1, ‖f (realSegment a b t)‖ < 1) ∧
      dist a b < 2 := by
  constructor
  · intro t ht
    exact lt_of_le_of_lt (h.segment_control t ht) h.critical_value_lt_one
  · exact h.endpoint_distance_lt_two

/-- Quantitative peak certificate: the selected chord is controlled by an
arbitrary level `M` and an arbitrary length budget `D`. -/
structure CollinearScalePeakCertificate
    (f : ℂ → ℂ) (a b c : ℂ) (D M : ℝ) : Prop where
  endpoint_distance_le : dist a b ≤ D
  critical_value_le : ‖f c‖ ≤ M
  segment_control : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (realSegment a b t)‖ ≤ ‖f c‖

theorem CollinearScalePeakCertificate.straightSegment_bound
    {f : ℂ → ℂ} {a b c : ℂ} {D M : ℝ}
    (h : CollinearScalePeakCertificate f a b c D M) :
    (∀ t ∈ Icc (0 : ℝ) 1, ‖f (realSegment a b t)‖ ≤ M) ∧
      dist a b ≤ D := by
  constructor
  · intro t ht
    exact (h.segment_control t ht).trans h.critical_value_le
  · exact h.endpoint_distance_le

/-- Polynomial-facing wrapper around `straightSegment_solution`. -/
theorem polynomial_straightSegment_solution_of_collinearPeak
    (p : ℂ[X]) {a b c : ℂ}
    (h : CollinearPeakCertificate p.eval a b c) :
    (∀ t ∈ Icc (0 : ℝ) 1, ‖p.eval (realSegment a b t)‖ < 1) ∧
      dist a b < 2 :=
  h.straightSegment_solution

/-- The full finite fan-in emitted by resultant/Fekete and interlacing: every
critical point is paired with its adjacent roots and controls their segment,
while the product of all critical-value moduli is strictly below one. -/
structure CollinearCriticalFamily
    {ι : Type*} [Fintype ι] (p : ℂ[X]) where
  critical : ι → ℂ
  leftRoot : ι → ℂ
  rightRoot : ι → ℂ
  left_isRoot : ∀ i, p.eval (leftRoot i) = 0
  right_isRoot : ∀ i, p.eval (rightRoot i) = 0
  roots_ne : ∀ i, leftRoot i ≠ rightRoot i
  endpoint_distance_lt_two : ∀ i, dist (leftRoot i) (rightRoot i) < 2
  critical_product_lt_one : ∏ i, ‖p.eval (critical i)‖ < 1
  segment_control : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
    ‖p.eval (realSegment (leftRoot i) (rightRoot i) t)‖ ≤
      ‖p.eval (critical i)‖

/-- Quantitative finite critical-gap data.  For a degree-`n` collinear
polynomial of root diameter `D`, the intended instantiation uses
`M=(D/2)^n / 2^(n-2)` and `ι = Fin (n-1)`. -/
structure CollinearScaleCriticalFamily
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) (D M : ℝ) where
  critical : ι → ℂ
  leftRoot : ι → ℂ
  rightRoot : ι → ℂ
  left_isRoot : ∀ i, p.eval (leftRoot i) = 0
  right_isRoot : ∀ i, p.eval (rightRoot i) = 0
  roots_ne : ∀ i, leftRoot i ≠ rightRoot i
  endpoint_distance_le : ∀ i, dist (leftRoot i) (rightRoot i) ≤ D
  critical_product_le : ∏ i, ‖p.eval (critical i)‖ ≤ M ^ Fintype.card ι
  segment_control : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
    ‖p.eval (realSegment (leftRoot i) (rightRoot i) t)‖ ≤
      ‖p.eval (critical i)‖

/-- Quantitative diameter/level fan-in. -/
theorem CollinearScaleCriticalFamily.exists_straightSegment_bound
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) {D M : ℝ} (hM : 0 < M)
    (h : CollinearScaleCriticalFamily p D M) :
    ∃ i : ι,
      p.eval (h.leftRoot i) = 0 ∧
      p.eval (h.rightRoot i) = 0 ∧
      h.leftRoot i ≠ h.rightRoot i ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
          ‖p.eval (realSegment (h.leftRoot i) (h.rightRoot i) t)‖ ≤ M) ∧
        dist (h.leftRoot i) (h.rightRoot i) ≤ D := by
  obtain ⟨i, hi⟩ := exists_le_of_prod_le_pow
    (fun i ↦ ‖p.eval (h.critical i)‖) hM
    h.critical_product_le
  have hbound := CollinearScalePeakCertificate.straightSegment_bound
    (f := fun z ↦ p.eval z)
    { endpoint_distance_le := h.endpoint_distance_le i
      critical_value_le := hi
      segment_control := fun t ht ↦ h.segment_control i t ht }
  exact ⟨i, h.left_isRoot i, h.right_isRoot i, h.roots_ne i,
    hbound.1, hbound.2⟩

/-- **Chebyshev-refined quantitative chord theorem.**  The interval
Fekete/resultant supplier for a degree-`n` collinear polynomial naturally emits
a `CollinearScaleCriticalFamily` at level
`(D / 2) ^ n / 2 ^ (n - 2)`.  This theorem preserves that exact level in the
selected adjacent-root chord. -/
theorem CollinearScaleCriticalFamily.exists_diameter_chord
    {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) {D : ℝ} (hD : 0 < D)
    (h : CollinearScaleCriticalFamily p D
      ((D / 2) ^ n / (2 : ℝ) ^ (n - 2))) :
    ∃ i : ι,
      p.eval (h.leftRoot i) = 0 ∧
      p.eval (h.rightRoot i) = 0 ∧
      h.leftRoot i ≠ h.rightRoot i ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
          ‖p.eval (realSegment (h.leftRoot i) (h.rightRoot i) t)‖ ≤
            (D / 2) ^ n / (2 : ℝ) ^ (n - 2)) ∧
        dist (h.leftRoot i) (h.rightRoot i) ≤ D := by
  apply h.exists_straightSegment_bound
  exact div_pos (pow_pos (by linarith) n) (pow_pos (by norm_num) (n - 2))

/-- **Strict Erdős-1041 collinear corollary.**  If `0 < D < 2` and
`n ≥ 2`, the Chebyshev-refined level `(D / 2) ^ n / 2 ^ (n - 2)` is
strictly below one, so the quantitative chord lies in the open lemniscate and
has length below two. -/
theorem CollinearScaleCriticalFamily.exists_erdos1041_chord
    {n : ℕ} (hn : 2 ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) {D : ℝ} (hD : 0 < D) (hD2 : D < 2)
    (h : CollinearScaleCriticalFamily p D
      ((D / 2) ^ n / (2 : ℝ) ^ (n - 2))) :
    ∃ i : ι,
      p.eval (h.leftRoot i) = 0 ∧
      p.eval (h.rightRoot i) = 0 ∧
      h.leftRoot i ≠ h.rightRoot i ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
          ‖p.eval (realSegment (h.leftRoot i) (h.rightRoot i) t)‖ < 1) ∧
        dist (h.leftRoot i) (h.rightRoot i) < 2 := by
  obtain ⟨i, hli, hri, hlr, hsegment, hdist⟩ :=
    h.exists_diameter_chord p hD
  have hhalf_nonneg : 0 ≤ D / 2 := by linarith
  have hhalf_lt_one : D / 2 < 1 := by linarith
  have hn0 : n ≠ 0 := by omega
  have hnum : (D / 2) ^ n < 1 :=
    pow_lt_one₀ hhalf_nonneg hhalf_lt_one hn0
  have hden : (1 : ℝ) ≤ 2 ^ (n - 2) := one_le_pow₀ (by norm_num)
  have hlevel : (D / 2) ^ n / (2 : ℝ) ^ (n - 2) < 1 := by
    calc
      (D / 2) ^ n / (2 : ℝ) ^ (n - 2) ≤ (D / 2) ^ n / 1 :=
        div_le_div_of_nonneg_left (pow_nonneg hhalf_nonneg n) (by norm_num) hden
      _ = (D / 2) ^ n := div_one _
      _ < 1 := hnum
  refine ⟨i, hli, hri, hlr, ?_, hdist.trans_lt hD2⟩
  intro t ht
  exact (hsegment t ht).trans_lt hlevel

/-- **Collinear-root fan-in.**  The strict critical-value product and the
interlacing segment controls select two roots joined inside `|p| < 1` by a
straight segment of length below two. -/
theorem CollinearCriticalFamily.exists_straightSegment_solution
    {ι : Type*} [Fintype ι] (p : ℂ[X])
    (h : CollinearCriticalFamily p) :
    ∃ i : ι,
      p.eval (h.leftRoot i) = 0 ∧
      p.eval (h.rightRoot i) = 0 ∧
      h.leftRoot i ≠ h.rightRoot i ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
          ‖p.eval (realSegment (h.leftRoot i) (h.rightRoot i) t)‖ < 1) ∧
        dist (h.leftRoot i) (h.rightRoot i) < 2 := by
  obtain ⟨i, hi⟩ := exists_norm_lt_one_of_prod_norm_lt_one
    (fun i ↦ p.eval (h.critical i)) h.critical_product_lt_one
  have hsolution := polynomial_straightSegment_solution_of_collinearPeak p
    (h :=
      { endpoint_distance_lt_two := h.endpoint_distance_lt_two i
        critical_value_lt_one := hi
        segment_control := fun t ht ↦ h.segment_control i t ht })
  exact ⟨i, h.left_isRoot i, h.right_isRoot i, h.roots_ne i,
    hsolution.1, hsolution.2⟩

/-! ## Exact scope guard

Critical-gap selection is essential: not every adjacent-root segment is safe,
even for a cubic with three real roots in the open unit disk. -/

/-- A rational real-rooted cubic witnessing failure of the all-gaps
strengthening. -/
noncomputable def unsafeAdjacentGapCubic : ℝ[X] :=
  (Polynomial.X - Polynomial.C (-(19 : ℝ) / 20)) *
    (Polynomial.X - Polynomial.C ((9 : ℝ) / 10)) *
      (Polynomial.X - Polynomial.C ((999 : ℝ) / 1000))

/-- The first adjacent-root segment of `unsafeAdjacentGapCubic` contains
`-1/3`, where the polynomial is already strictly above one. -/
theorem unsafeAdjacentGapCubic_value :
    unsafeAdjacentGapCubic.eval (-(1 : ℝ) / 3) =
      (5471893 : ℝ) / 5400000 := by
  norm_num [unsafeAdjacentGapCubic]

theorem unsafeAdjacentGapCubic_not_in_openLemniscate :
    1 < |unsafeAdjacentGapCubic.eval (-(1 : ℝ) / 3)| := by
  rw [unsafeAdjacentGapCubic_value]
  norm_num [abs_of_pos]

end ErdosProblems.Erdos1041
