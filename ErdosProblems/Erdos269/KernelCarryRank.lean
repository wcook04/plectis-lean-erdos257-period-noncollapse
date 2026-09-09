import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import ErdosProblems.Shared.IrrationalRotationStaircase
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Erdős #269: the rank phase transition of the running-LCM kernel

The running-LCM kernel `threePrimeKernelQ p q r i j k` is
`1 / (p ^ log_p N * q ^ log_q N * r ^ log_r N)` with `N = p^i q^j r^k`.

**Two generators.**  With only `p` and `q` the analogous kernel is an outer
product, so every matrix it forms has rank at most one
(`twoPrimeKernelQ_eq_outer_product`).

**Three generators.**  The only new ingredient is the single *binary* carry
`logCarry r (p^i) (q^j) ∈ {0,1}`.  That one bit is enough to destroy every
finite separation: for pairwise-independent generators and every `n`, there
are injective index families `I, J : Fin n → ℕ` whose `n × n` minor is
nonzero **simultaneously in every layer `k`**
(`exists_uniform_nonsingular_threePrimeKernel_minor`).  Hence each fixed-`k`
matrix has infinite rank over `ℚ`, and no finite sum
`∑_{ℓ<d} f_ℓ(i) · G_ℓ(j,k)` can represent the kernel
(`not_finite_separable_threePrimeKernel`).

Nothing here proves irrationality or transcendence of a three-prime value.
The missing producer is still an infinite residue-escape theorem; this module
sharpens the *structural* boundary that any such producer must respect.
-/

namespace ErdosProblems.Erdos269

open ErdosProblems.Shared

/-! ## The two-factor logarithmic carry -/

/-- The binary carry of `Nat.log` across a product. -/
def logCarry (b x y : ℕ) : ℕ :=
  Nat.log b (x * y) - Nat.log b x - Nat.log b y

/-- `Nat.log` is superadditive across a product. -/
theorem add_log_le_log_mul {b : ℕ} (hb : 1 < b) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Nat.log b x + Nat.log b y ≤ Nat.log b (x * y) := by
  apply Nat.le_log_of_pow_le hb
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.pow_log_le_self b hx) (Nat.pow_log_le_self b hy)

/-- `Nat.log` loses at most one unit across a product: the **two-factor
carry law**. -/
theorem log_mul_le_add_log_succ {b : ℕ} (hb : 1 < b) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Nat.log b (x * y) ≤ Nat.log b x + Nat.log b y + 1 := by
  have hlt : x * y < b ^ (Nat.log b x + Nat.log b y + 2) := by
    calc x * y < b ^ (Nat.log b x + 1) * b ^ (Nat.log b y + 1) :=
          Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_pow_succ_log_self hb x)
            (Nat.lt_pow_succ_log_self hb y)
      _ = b ^ (Nat.log b x + Nat.log b y + 2) := by rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (Nat.mul_ne_zero hx hy) hlt
  omega

/-- The carry is a single bit. -/
theorem logCarry_le_one {b : ℕ} (hb : 1 < b) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    logCarry b x y ≤ 1 := by
  have h1 := add_log_le_log_mul hb hx hy
  have h2 := log_mul_le_add_log_succ hb hx hy
  unfold logCarry
  omega

/-- The exact carry decomposition of `Nat.log` across a product. -/
theorem log_mul_eq_add_log_add_logCarry {b : ℕ} (hb : 1 < b) {x y : ℕ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    Nat.log b (x * y) = Nat.log b x + Nat.log b y + logCarry b x y := by
  have h1 := add_log_le_log_mul hb hx hy
  unfold logCarry
  omega

/-- Pulling a pure power of the base out of `Nat.log`. -/
theorem log_pow_mul {b : ℕ} (hb : 1 < b) (i : ℕ) {m : ℕ} (hm : m ≠ 0) :
    Nat.log b (b ^ i * m) = i + Nat.log b m := by
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
  · rw [pow_add]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self b hm)
  · have hbi : 0 < b ^ i := pow_pos (by omega) i
    have hstep : b ^ i * m < b ^ i * b ^ (Nat.log b m + 1) :=
      mul_lt_mul_of_pos_left (Nat.lt_pow_succ_log_self hb m) hbi
    calc b ^ i * m < b ^ i * b ^ (Nat.log b m + 1) := hstep
      _ = b ^ (i + Nat.log b m + 1) := by rw [← pow_add]; ring_nf

/-! ## The real bridge: the carry is a two-dimensional rotation carry -/

/-- `Nat.log` of a pure power, read as a floor of a real logarithm. -/
private theorem natLog_pow_eq_floor {b x : ℕ} (hb : 1 < b) (hx : 0 < x) (i : ℕ) :
    Nat.log b (x ^ i) = ⌊(i : ℝ) * Real.logb b x⌋₊ := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hcast : (((x ^ i : ℕ)) : ℝ) = (x : ℝ) ^ i := by push_cast; ring
  rw [← Real.natFloor_logb_natCast b (x ^ i), hcast, Real.logb_pow]

/-- **The `Nat.log` carry is the two-dimensional rotation carry.**  This is
the only place real logarithms enter. -/
theorem logCarry_pow_eq_floor_fract {p q b : ℕ} (hb : 1 < b) (hp : 0 < p) (hq : 0 < q)
    (i j : ℕ) :
    (logCarry b (p ^ i) (q ^ j) : ℤ)
      = ⌊Int.fract ((i : ℝ) * Real.logb b p) + Int.fract ((j : ℝ) * Real.logb b q)⌋ := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set x : ℝ := (i : ℝ) * Real.logb b p with hx
  set y : ℝ := (j : ℝ) * Real.logb b q with hy
  have hpi : (p ^ i : ℕ) ≠ 0 := pow_ne_zero _ hp.ne'
  have hqj : (q ^ j : ℕ) ≠ 0 := pow_ne_zero _ hq.ne'
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by
    have h1 : 1 ≤ p := hp
    exact_mod_cast h1
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by
    have h1 : 1 ≤ q := hq
    exact_mod_cast h1
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx]
    exact mul_nonneg (Nat.cast_nonneg i) (Real.logb_nonneg hbR hp1R)
  have hy0 : (0 : ℝ) ≤ y := by
    rw [hy]
    exact mul_nonneg (Nat.cast_nonneg j) (Real.logb_nonneg hbR hq1R)
  -- the three `Nat.log` values as floors
  have hLp : Nat.log b (p ^ i) = ⌊x⌋₊ := natLog_pow_eq_floor hb hp i
  have hLq : Nat.log b (q ^ j) = ⌊y⌋₊ := natLog_pow_eq_floor hb hq j
  have hprodR : (((p ^ i * q ^ j : ℕ)) : ℝ) = (p : ℝ) ^ i * (q : ℝ) ^ j := by push_cast; ring
  have hLpq : Nat.log b (p ^ i * q ^ j) = ⌊x + y⌋₊ := by
    rw [← Real.natFloor_logb_natCast b (p ^ i * q ^ j), hprodR,
      Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
  -- the exact `ℤ`-floor split
  have hsplit : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + ⌊Int.fract x + Int.fract y⌋ := by
    have hxy : x + y = ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) + (Int.fract x + Int.fract y) := by
      have hx' := Int.floor_add_fract x
      have hy' := Int.floor_add_fract y
      push_cast
      linarith
    rw [hxy, Int.floor_intCast_add]
  have hsuper := add_log_le_log_mul hb hpi hqj
  have hcarry := log_mul_eq_add_log_add_logCarry hb hpi hqj
  have hzx : ((⌊x⌋₊ : ℕ) : ℤ) = ⌊x⌋ := Int.natCast_floor_eq_floor hx0
  have hzy : ((⌊y⌋₊ : ℕ) : ℤ) = ⌊y⌋ := Int.natCast_floor_eq_floor hy0
  have hzxy : ((⌊x + y⌋₊ : ℕ) : ℤ) = ⌊x + y⌋ :=
    Int.natCast_floor_eq_floor (by linarith)
  have hZ : ((Nat.log b (p ^ i * q ^ j) : ℕ) : ℤ)
      = ((Nat.log b (p ^ i) : ℕ) : ℤ) + ((Nat.log b (q ^ j) : ℕ) : ℤ)
        + (logCarry b (p ^ i) (q ^ j) : ℤ) := by
    rw [hcarry]; push_cast; ring
  rw [hLp, hLq, hLpq] at hZ
  rw [hzx, hzy, hzxy, hsplit] at hZ
  omega

/-! ## Independence of the two generators -/

/-- For distinct primes, no positive multiple of `logb r p` is an integer. -/
theorem noIntegerOrbit_logb_of_prime {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) : NoIntegerOrbit (Real.logb r p) := by
  intro n hn hfract
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  set x : ℝ := (n : ℝ) * Real.logb r p with hx
  set z : ℤ := ⌊x⌋ with hz
  have hxz : x = (z : ℝ) := by
    have := Int.floor_add_fract x
    rw [hfract] at this
    rw [hz]; linarith
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx]
    exact mul_nonneg (Nat.cast_nonneg n) (Real.logb_nonneg hr1 hp1.le)
  have hz0 : 0 ≤ z := by rw [hz]; exact Int.floor_nonneg.2 hx0
  -- `n * log p = z * log r`
  have hkey : (n : ℝ) * Real.log (p : ℝ) = (z : ℝ) * Real.log (r : ℝ) := by
    have hlogb : Real.logb (r : ℝ) (p : ℝ) = Real.log (p : ℝ) / Real.log (r : ℝ) := rfl
    rw [hx, hlogb] at hxz
    field_simp at hxz
    linarith
  -- exponentiate
  have hlogL : Real.log (((p ^ n : ℕ)) : ℝ) = (n : ℝ) * Real.log (p : ℝ) := by
    push_cast; rw [Real.log_pow]
  have hlogR : Real.log (((r ^ z.toNat : ℕ)) : ℝ) = (z : ℝ) * Real.log (r : ℝ) := by
    push_cast
    rw [Real.log_pow]
    congr 1
    exact_mod_cast congrArg (fun m : ℤ => (m : ℝ)) (Int.toNat_of_nonneg hz0)
  have hposL : (0 : ℝ) < ((p ^ n : ℕ) : ℝ) := by
    have hpn : 0 < p ^ n := pow_pos hp.pos n
    exact_mod_cast hpn
  have hposR : (0 : ℝ) < ((r ^ z.toNat : ℕ) : ℝ) := by
    have hrz : 0 < r ^ z.toNat := pow_pos hr.pos _
    exact_mod_cast hrz
  have hlogEq : Real.log (((p ^ n : ℕ)) : ℝ) = Real.log (((r ^ z.toNat : ℕ)) : ℝ) := by
    rw [hlogL, hlogR, hkey]
  have hEqR : ((p ^ n : ℕ) : ℝ) = ((r ^ z.toNat : ℕ) : ℝ) := by
    have h1 := Real.exp_log hposL
    have h2 := Real.exp_log hposR
    rw [← h1, ← h2, hlogEq]
  have hEq : p ^ n = r ^ z.toNat := by exact_mod_cast hEqR
  have hdvd : p ∣ r ^ z.toNat := by
    rw [← hEq]
    exact dvd_pow_self p hn.ne'
  exact hpr (Nat.prime_dvd_prime_iff_eq hp hr |>.1 (hp.dvd_of_dvd_pow hdvd))

/-! ## The kernel factorises through the carry -/

/-- Factor of the running-LCM height that depends only on the first exponent
and the layer. -/
def rowFactor (p q r i k : ℕ) : ℕ :=
  p ^ i * q ^ Nat.log q (p ^ i * r ^ k) * r ^ Nat.log r (p ^ i) * r ^ k

/-- Factor of the running-LCM height that depends only on the second exponent
and the layer. -/
def colFactor (p q r j k : ℕ) : ℕ :=
  p ^ Nat.log p (q ^ j * r ^ k) * q ^ j * r ^ Nat.log r (q ^ j)

/-- **Exact rank-one-plus-carry factorisation of the running-LCM height.**
Everything except the single carry bit splits into a row factor and a column
factor. -/
theorem threePrimeHeight_factorisation {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (i j k : ℕ) :
    threePrimeHeight p q r (smooth3Val p q r i j k)
      = rowFactor p q r i k * colFactor p q r j k * r ^ logCarry r (p ^ i) (q ^ j) := by
  have hp0 : p ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  have hr0 : r ≠ 0 := by omega
  have hpi : (p ^ i : ℕ) ≠ 0 := pow_ne_zero _ hp0
  have hqj : (q ^ j : ℕ) ≠ 0 := pow_ne_zero _ hq0
  have hrk : (r ^ k : ℕ) ≠ 0 := pow_ne_zero _ hr0
  have hLp : Nat.log p (smooth3Val p q r i j k) = i + Nat.log p (q ^ j * r ^ k) := by
    unfold smooth3Val
    rw [mul_assoc]
    exact log_pow_mul hp i (Nat.mul_ne_zero hqj hrk)
  have hLq : Nat.log q (smooth3Val p q r i j k) = j + Nat.log q (p ^ i * r ^ k) := by
    unfold smooth3Val
    have hperm : p ^ i * q ^ j * r ^ k = q ^ j * (p ^ i * r ^ k) := by ring
    rw [hperm]
    exact log_pow_mul hq j (Nat.mul_ne_zero hpi hrk)
  have hLr : Nat.log r (smooth3Val p q r i j k)
      = k + (Nat.log r (p ^ i) + Nat.log r (q ^ j) + logCarry r (p ^ i) (q ^ j)) := by
    unfold smooth3Val
    have hperm : p ^ i * q ^ j * r ^ k = r ^ k * (p ^ i * q ^ j) := by ring
    rw [hperm, log_pow_mul hr k (Nat.mul_ne_zero hpi hqj),
      log_mul_eq_add_log_add_logCarry hr hpi hqj]
  unfold threePrimeHeight rowFactor colFactor
  rw [hLp, hLq, hLr]
  simp only [pow_add]
  ring

/-- The row factor is positive. -/
theorem rowFactor_pos {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (i k : ℕ) :
    0 < rowFactor p q r i k := by
  unfold rowFactor; positivity

/-- The column factor is positive. -/
theorem colFactor_pos {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (j k : ℕ) :
    0 < colFactor p q r j k := by
  unfold colFactor; positivity

/-- The rational kernel splits as (row) × (staircase entry) × (column). -/
theorem threePrimeKernelQ_factorisation {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (i j k : ℕ) :
    threePrimeKernelQ p q r i j k
      = ((rowFactor p q r i k : ℚ))⁻¹ * ((r : ℚ)⁻¹) ^ logCarry r (p ^ i) (q ^ j)
        * ((colFactor p q r j k : ℚ))⁻¹ := by
  unfold threePrimeKernelQ
  rw [threePrimeHeight_factorisation hp hq hr i j k]
  push_cast
  rw [mul_inv, mul_inv, inv_pow]
  ring

/-! ## Two generators: the kernel is an outer product -/

/-- The two-generator running-LCM kernel. -/
def twoPrimeKernelQ (p q i j : ℕ) : ℚ :=
  ((p ^ Nat.log p (p ^ i * q ^ j) * q ^ Nat.log q (p ^ i * q ^ j) : ℕ) : ℚ)⁻¹

/-- **Rank one at two generators.**  The two-generator kernel is literally an
outer product, so every matrix built from it has rank at most one. -/
theorem twoPrimeKernelQ_eq_outer_product {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (i j : ℕ) :
    twoPrimeKernelQ p q i j
      = ((p ^ i * q ^ Nat.log q (p ^ i) : ℕ) : ℚ)⁻¹
        * ((p ^ Nat.log p (q ^ j) * q ^ j : ℕ) : ℚ)⁻¹ := by
  have hpi : (p ^ i : ℕ) ≠ 0 := pow_ne_zero _ (by omega)
  have hqj : (q ^ j : ℕ) ≠ 0 := pow_ne_zero _ (by omega)
  have hLp : Nat.log p (p ^ i * q ^ j) = i + Nat.log p (q ^ j) := log_pow_mul hp i hqj
  have hLq : Nat.log q (p ^ i * q ^ j) = j + Nat.log q (p ^ i) := by
    have hperm : p ^ i * q ^ j = q ^ j * p ^ i := by ring
    rw [hperm]
    exact log_pow_mul hq j hpi
  unfold twoPrimeKernelQ
  rw [hLp, hLq]
  push_cast
  simp only [pow_add]
  rw [← mul_inv]
  congr 1
  ring

/-- Every minor of the two-generator kernel of size at least two vanishes. -/
theorem twoPrimeKernelQ_minor_two_eq_zero {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    (i i' j j' : ℕ) :
    twoPrimeKernelQ p q i j * twoPrimeKernelQ p q i' j'
      - twoPrimeKernelQ p q i j' * twoPrimeKernelQ p q i' j = 0 := by
  rw [twoPrimeKernelQ_eq_outer_product hp hq, twoPrimeKernelQ_eq_outer_product hp hq,
    twoPrimeKernelQ_eq_outer_product hp hq, twoPrimeKernelQ_eq_outer_product hp hq]
  ring

/-! ## Three generators: uniformly nonsingular minors of every order -/

/-- **The rank phase transition.**  For generators whose logarithmic ratios
have no integer return, and for every `n`, there are injective index families
whose `n × n` running-LCM minor is nonzero *simultaneously in every layer*
`k`.  The `n = 2` case already contains the classical non-separation
witness; the content is that the same construction survives to every order. -/
theorem exists_uniform_nonsingular_threePrimeKernel_minor {p q r : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hα : NoIntegerOrbit (Real.logb r p)) (hβ : NoIntegerOrbit (Real.logb r q))
    (n : ℕ) :
    ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
      ∀ k : ℕ,
        (Matrix.det fun a b : Fin n => threePrimeKernelQ p q r (I a) (J b) k) ≠ 0 := by
  obtain ⟨I, J, _hIpos, _hJpos, hIinj, hJinj, hstair⟩ :=
    exists_staircase_indices hα hβ n
  refine ⟨I, J, hIinj, hJinj, ?_⟩
  intro k
  -- the carry is exactly the staircase pattern
  have hcarry : ∀ a b : Fin n,
      logCarry r (p ^ I a) (q ^ J b) = if (b : ℕ) ≤ (a : ℕ) then 1 else 0 := by
    intro a b
    have h := logCarry_pow_eq_floor_fract (b := r) hr (by omega : 0 < p) (by omega : 0 < q)
      (I a) (J b)
    rw [hstair a b] at h
    by_cases hba : (b : ℕ) ≤ (a : ℕ)
    · rw [if_pos hba] at h ⊢
      omega
    · rw [if_neg hba] at h ⊢
      omega
  rcases n with _ | m
  · simp [Matrix.det_fin_zero]
  · have hMat : (fun a b : Fin (m + 1) => threePrimeKernelQ p q r (I a) (J b) k)
        = Matrix.diagonal (fun a : Fin (m + 1) => ((rowFactor p q r (I a) k : ℕ) : ℚ)⁻¹)
          * carryStaircase ((r : ℚ)⁻¹) m
          * Matrix.diagonal (fun b : Fin (m + 1) => ((colFactor p q r (J b) k : ℕ) : ℚ)⁻¹) := by
      funext a b
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
        threePrimeKernelQ_factorisation hp hq hr, hcarry a b]
      by_cases hba : (b : ℕ) ≤ (a : ℕ) <;> simp [carryStaircase, hba]
    rw [hMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
      det_carryStaircase]
    have hrQ : (2 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr
    have hrpos : (0 : ℚ) < (r : ℚ) := by linarith
    have ht0 : (r : ℚ)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hrpos)
    have hthalf : (r : ℚ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hrpos (by norm_num)]
      linarith
    have ht1 : (r : ℚ)⁻¹ - 1 ≠ 0 := by
      intro hzero
      have : (r : ℚ)⁻¹ = 1 := by linarith [sub_eq_zero.1 hzero]
      linarith
    have hprodA :
        (∏ a : Fin (m + 1), ((rowFactor p q r (I a) k : ℕ) : ℚ)⁻¹) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun a _ => inv_ne_zero ?_
      have hpos : (0 : ℚ) < ((rowFactor p q r (I a) k : ℕ) : ℚ) := by
        exact_mod_cast rowFactor_pos (p := p) (q := q) (r := r)
          (by omega) (by omega) (by omega) (I a) k
      exact ne_of_gt hpos
    have hprodB :
        (∏ b : Fin (m + 1), ((colFactor p q r (J b) k : ℕ) : ℚ)⁻¹) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun b _ => inv_ne_zero ?_
      have hpos : (0 : ℚ) < ((colFactor p q r (J b) k : ℕ) : ℚ) := by
        exact_mod_cast colFactor_pos (p := p) (q := q) (r := r)
          (by omega) (by omega) (by omega) (J b) k
      exact ne_of_gt hpos
    exact mul_ne_zero (mul_ne_zero hprodA (mul_ne_zero ht0 (pow_ne_zero _ ht1))) hprodB

/-- **Three distinct primes force infinite rank in every layer.** -/
theorem exists_uniform_nonsingular_threePrimeKernel_minor_of_prime {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) :
    ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
      ∀ k : ℕ,
        (Matrix.det fun a b : Fin n => threePrimeKernelQ p q r (I a) (J b) k) ≠ 0 :=
  exists_uniform_nonsingular_threePrimeKernel_minor hp.one_lt hq.one_lt hr.one_lt
    (noIntegerOrbit_logb_of_prime hp hr hpr) (noIntegerOrbit_logb_of_prime hq hr hqr) n

/-- **No finite separation.**  If the kernel had a finite representation
`∑_{ℓ < d} f ℓ i * G ℓ j k`, every minor of order `d + 1` would vanish; the
theorem above produces a nonzero one. -/
theorem not_finite_separable_threePrimeKernel {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpr : p ≠ r) (hqr : q ≠ r) (d : ℕ) :
    ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
        ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k := by
  rintro ⟨f, G, hrep⟩
  obtain ⟨I, J, _, _, hdet⟩ :=
    exists_uniform_nonsingular_threePrimeKernel_minor_of_prime hp hq hr hpr hqr (d + 1)
  refine hdet 0 ?_
  -- pad the `(d+1) × d` and `d × (d+1)` factors with a zero column / zero row
  set A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ :=
    fun a l => if h : (l : ℕ) < d then f ⟨l, h⟩ (I a) else 0 with hA
  set B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ :=
    fun l b => if h : (l : ℕ) < d then G ⟨l, h⟩ (J b) 0 else 0 with hB
  have hMat : (fun a b : Fin (d + 1) => threePrimeKernelQ p q r (I a) (J b) 0) = A * B := by
    funext a b
    rw [hrep]
    show _ = ∑ l : Fin (d + 1), A a l * B l b
    rw [Fin.sum_univ_castSucc]
    have hlast : A a (Fin.last d) * B (Fin.last d) b = 0 := by
      simp [hA, Fin.last]
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hlt : ((l.castSucc : Fin (d + 1)) : ℕ) < d := by
      simpa using l.2
    simp [hA, hB, hlt]
  rw [hMat, Matrix.det_mul]
  have hAzero : A.det = 0 := by
    refine Matrix.det_eq_zero_of_column_eq_zero (Fin.last d) fun a => ?_
    simp [hA, Fin.last]
  rw [hAzero, zero_mul]

end ErdosProblems.Erdos269

namespace ErdosProblems.Erdos269

/-! ## Exact `{2,3,5}` receipts

The layer `k = 0` of the `{2,3,5}` kernel begins

```
1        1/6      1/360     1/10800
1/2      1/60     1/720     1/21600
1/12     1/360    1/21600   1/129600
1/120    1/720    1/43200   1/1296000
```

The leading `2 x 2` and `3 x 3` minors are nonzero, but the leading `4 x 4`
minor **vanishes**.  So the rank theorem above is genuinely about the
existence of suitable index families, not about leading minors; the
vanishing `4 x 4` is the regression test against overstating it. -/

private theorem kernel235_0_0 : threePrimeKernelQ 2 3 5 0 0 0 = 1 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 1 = 0 from by decide,
    show Nat.log 3 1 = 0 from by decide,
    show Nat.log 5 1 = 0 from by decide]

private theorem kernel235_0_1 : threePrimeKernelQ 2 3 5 0 1 0 = 1 / 6 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 3 = 1 from by decide,
    show Nat.log 3 3 = 1 from by decide,
    show Nat.log 5 3 = 0 from by decide]

private theorem kernel235_0_2 : threePrimeKernelQ 2 3 5 0 2 0 = 1 / 360 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 9 = 3 from by decide,
    show Nat.log 3 9 = 2 from by decide,
    show Nat.log 5 9 = 1 from by decide]

private theorem kernel235_0_3 : threePrimeKernelQ 2 3 5 0 3 0 = 1 / 10800 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 27 = 4 from by decide,
    show Nat.log 3 27 = 3 from by decide,
    show Nat.log 5 27 = 2 from by decide]

private theorem kernel235_0_4 : threePrimeKernelQ 2 3 5 0 4 0 = 1 / 129600 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 81 = 6 from by decide,
    show Nat.log 3 81 = 4 from by decide,
    show Nat.log 5 81 = 2 from by decide]

private theorem kernel235_1_0 : threePrimeKernelQ 2 3 5 1 0 0 = 1 / 2 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 2 = 1 from by decide,
    show Nat.log 3 2 = 0 from by decide,
    show Nat.log 5 2 = 0 from by decide]

private theorem kernel235_1_1 : threePrimeKernelQ 2 3 5 1 1 0 = 1 / 60 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 6 = 2 from by decide,
    show Nat.log 3 6 = 1 from by decide,
    show Nat.log 5 6 = 1 from by decide]

private theorem kernel235_1_2 : threePrimeKernelQ 2 3 5 1 2 0 = 1 / 720 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 18 = 4 from by decide,
    show Nat.log 3 18 = 2 from by decide,
    show Nat.log 5 18 = 1 from by decide]

private theorem kernel235_1_3 : threePrimeKernelQ 2 3 5 1 3 0 = 1 / 21600 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 54 = 5 from by decide,
    show Nat.log 3 54 = 3 from by decide,
    show Nat.log 5 54 = 2 from by decide]

private theorem kernel235_1_4 : threePrimeKernelQ 2 3 5 1 4 0 = 1 / 1296000 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 162 = 7 from by decide,
    show Nat.log 3 162 = 4 from by decide,
    show Nat.log 5 162 = 3 from by decide]

private theorem kernel235_2_0 : threePrimeKernelQ 2 3 5 2 0 0 = 1 / 12 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 4 = 2 from by decide,
    show Nat.log 3 4 = 1 from by decide,
    show Nat.log 5 4 = 0 from by decide]

private theorem kernel235_2_1 : threePrimeKernelQ 2 3 5 2 1 0 = 1 / 360 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 12 = 3 from by decide,
    show Nat.log 3 12 = 2 from by decide,
    show Nat.log 5 12 = 1 from by decide]

private theorem kernel235_2_2 : threePrimeKernelQ 2 3 5 2 2 0 = 1 / 21600 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 36 = 5 from by decide,
    show Nat.log 3 36 = 3 from by decide,
    show Nat.log 5 36 = 2 from by decide]

private theorem kernel235_2_3 : threePrimeKernelQ 2 3 5 2 3 0 = 1 / 129600 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 108 = 6 from by decide,
    show Nat.log 3 108 = 4 from by decide,
    show Nat.log 5 108 = 2 from by decide]

private theorem kernel235_2_4 : threePrimeKernelQ 2 3 5 2 4 0 = 1 / 7776000 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 324 = 8 from by decide,
    show Nat.log 3 324 = 5 from by decide,
    show Nat.log 5 324 = 3 from by decide]

private theorem kernel235_3_0 : threePrimeKernelQ 2 3 5 3 0 0 = 1 / 120 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 8 = 3 from by decide,
    show Nat.log 3 8 = 1 from by decide,
    show Nat.log 5 8 = 1 from by decide]

private theorem kernel235_3_1 : threePrimeKernelQ 2 3 5 3 1 0 = 1 / 720 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 24 = 4 from by decide,
    show Nat.log 3 24 = 2 from by decide,
    show Nat.log 5 24 = 1 from by decide]

private theorem kernel235_3_2 : threePrimeKernelQ 2 3 5 3 2 0 = 1 / 43200 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 72 = 6 from by decide,
    show Nat.log 3 72 = 3 from by decide,
    show Nat.log 5 72 = 2 from by decide]

private theorem kernel235_3_3 : threePrimeKernelQ 2 3 5 3 3 0 = 1 / 1296000 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 216 = 7 from by decide,
    show Nat.log 3 216 = 4 from by decide,
    show Nat.log 5 216 = 3 from by decide]

private theorem kernel235_3_4 : threePrimeKernelQ 2 3 5 3 4 0 = 1 / 77760000 := by
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    show Nat.log 2 648 = 9 from by decide,
    show Nat.log 3 648 = 5 from by decide,
    show Nat.log 5 648 = 4 from by decide]

/-- Matrix-form wrapper for the smallest exact non-separation witness. -/
theorem kernel_235_minor2_eq_neg_one_fifteen :
    (Matrix.det fun a b : Fin 2 => threePrimeKernelQ 2 3 5 a b 0) = -1 / 15 := by
  calc
    (Matrix.det fun a b : Fin 2 => threePrimeKernelQ 2 3 5 a b 0) =
        -(1 / 15 : ℚ) := by
      simpa [Matrix.det_fin_two, mul_comm] using
        kernel_235_minor_eq_neg_one_fifteen
    _ = -1 / 15 := by norm_num

/-- The leading `3 x 3` minor is also nonzero. -/
theorem kernel_235_minor3_eq_one_over_81000 :
    (Matrix.det fun a b : Fin 3 => threePrimeKernelQ 2 3 5 a b 0) = 1 / 81000 := by
  norm_num [Matrix.det_fin_three, kernel235_0_0, kernel235_0_1, kernel235_0_2, kernel235_0_3, kernel235_0_4, kernel235_1_0, kernel235_1_1, kernel235_1_2, kernel235_1_3, kernel235_1_4, kernel235_2_0, kernel235_2_1, kernel235_2_2, kernel235_2_3, kernel235_2_4, kernel235_3_0, kernel235_3_1, kernel235_3_2, kernel235_3_3, kernel235_3_4]

/-- **Falsifier: the leading `4 x 4` minor vanishes, and for a sharp reason.**
On the first four columns, row `3` is an exact rational multiple of row `0`:

`K(3, j, 0) = (1/120) * K(0, j, 0)`  for `j = 0,1,2,3`.

So the leading `4 x 4` minor of the `{2,3,5}` kernel is singular.  Leading
minors are therefore *not* a witness of infinite rank, and index selection in
`exists_uniform_nonsingular_threePrimeKernel_minor` is essential, not
cosmetic. -/
theorem kernel_235_row_three_eq_smul_row_zero :
    (∀ j : Fin 4, threePrimeKernelQ 2 3 5 3 (j : ℕ) 0
        = (1 / 120 : ℚ) * threePrimeKernelQ 2 3 5 0 (j : ℕ) 0) := by
  intro j
  fin_cases j <;> norm_num [kernel235_0_0, kernel235_0_1, kernel235_0_2, kernel235_0_3, kernel235_0_4, kernel235_1_0, kernel235_1_1, kernel235_1_2, kernel235_1_3, kernel235_1_4, kernel235_2_0, kernel235_2_1, kernel235_2_2, kernel235_2_3, kernel235_2_4, kernel235_3_0, kernel235_3_1, kernel235_3_2, kernel235_3_3, kernel235_3_4]

/-- **The coincidence is exactly four columns wide.**  At the fifth column the
proportionality fails, which is why moving one column out of the coincidence
range restores nonsingularity. -/
theorem kernel_235_row_three_ne_smul_row_zero_at_four :
    threePrimeKernelQ 2 3 5 3 4 0 ≠ (1 / 120 : ℚ) * threePrimeKernelQ 2 3 5 0 4 0 := by
  norm_num [kernel235_0_0, kernel235_0_1, kernel235_0_2, kernel235_0_3, kernel235_0_4, kernel235_1_0, kernel235_1_1, kernel235_1_2, kernel235_1_3, kernel235_1_4, kernel235_2_0, kernel235_2_1, kernel235_2_2, kernel235_2_3, kernel235_2_4, kernel235_3_0, kernel235_3_1, kernel235_3_2, kernel235_3_3, kernel235_3_4]

end ErdosProblems.Erdos269
