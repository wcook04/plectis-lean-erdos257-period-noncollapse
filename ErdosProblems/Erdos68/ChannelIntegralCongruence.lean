import ErdosProblems.Erdos68.ChannelBreakpointRigidity
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Integral channel congruence for Erdős problem 68

This module compares a channel numerator with the corresponding factorial
moment modulo `d! - 1`.  The congruence holds for every support index, so
simultaneous cancellation of the channels `2, ..., D` makes their least common
multiple divide the factorial moment.

The second part estimates that least common multiple.  Consecutive numbers
`m! - 1` are compared through their pairwise gcds; this gives an explicit
finite lower bound after the gcd losses are counted.  Consequently, if a
positive integer `M` is divisible by the channel lcm and is smaller than
`(R+1)! - 1`, then `R` must grow at least cubically along `D = 2t^2`.  A later
estimate improves the explicit constant to `R+1 > (3/2)t^3` for `t >= 2^32`.

All conclusions after the congruence theorem retain these stated hypotheses.
In particular, this file does not construct `M` or `R` from the series in
Erdős problem 68, prove that its channels vanish, or decide the rationality of
that series.
-/

namespace Erdos68

/-- The least common multiple of the channel moduli through `D`. -/
def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

/-- Every individual channel coefficient is congruent to its factorial
coefficient modulo `d! - 1`.  Unlike quotient-band rigidity, this statement
has no restriction on the support index. -/
theorem channelCoefficient_sub_factorial_dvd
    {d i : ℕ} (hd : 2 ≤ d) :
    ((d.factorial : ℤ) - 1) ∣
      ((i.factorial : ℤ) -
        (i.factorial / d.factorial ^ (i / d) : ℕ)) := by
  have hdpos : 0 < d := by omega
  have hhi : i < (i / d + 1) * d := by
    rw [← Nat.div_lt_iff_lt_mul hdpos]
    exact Nat.lt_succ_self _
  have hcoeff := channel_coefficient_band
    (d := d) (i := i) (k := i / d) (Nat.div_mul_le_self i d) hhi
  let a : ℕ := i.factorial / d.factorial ^ (i / d)
  have hcast : (i.factorial : ℤ) =
      (d.factorial : ℤ) ^ (i / d) * (a : ℤ) := by
    simpa [a, Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ℤ)) hcoeff.symm
  have hpow : ((d.factorial : ℤ) - 1) ∣
      (d.factorial : ℤ) ^ (i / d) - 1 := by
    simpa using sub_dvd_pow_sub_pow (d.factorial : ℤ) 1 (i / d)
  rcases hpow with ⟨z, hz⟩
  refine ⟨(a : ℤ) * z, ?_⟩
  change (i.factorial : ℤ) - (a : ℤ) =
    ((d.factorial : ℤ) - 1) * ((a : ℤ) * z)
  calc
    (i.factorial : ℤ) - (a : ℤ) =
        (a : ℤ) * ((d.factorial : ℤ) ^ (i / d) - 1) := by
          rw [hcast]
          ring
    _ = (a : ℤ) * (((d.factorial : ℤ) - 1) * z) := by rw [hz]
    _ = ((d.factorial : ℤ) - 1) * ((a : ℤ) * z) := by ring

/-- The factorial moment and every channel numerator have the same residue
modulo `d! - 1`. -/
theorem channelNumerator_mod_factorialMoment
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ)
    {d : ℕ} (hd : 2 ≤ d) :
    ((d.factorial : ℤ) - 1) ∣
      factorialMoment coeff index - channelNumerator coeff index d := by
  unfold factorialMoment channelNumerator
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro j _
  rcases channelCoefficient_sub_factorial_dvd (d := d) (i := index j) hd with
    ⟨z, hz⟩
  refine ⟨coeff j * z, ?_⟩
  calc
    coeff j * (index j).factorial -
        coeff j * ((index j).factorial / d.factorial ^ (index j / d) : ℕ) =
        coeff j * ((index j).factorial -
          ((index j).factorial / d.factorial ^ (index j / d) : ℕ)) := by ring
    _ = coeff j * (((d.factorial : ℤ) - 1) * z) := by rw [hz]
    _ = ((d.factorial : ℤ) - 1) * (coeff j * z) := by ring

/-- An annihilated `d`-channel forces its modulus `d! - 1` to divide the
factorial moment. -/
theorem channelModulus_dvd_factorialMoment_of_channel_zero
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ)
    {d : ℕ} (hd : 2 ≤ d)
    (hzero : channelNumerator coeff index d = 0) :
    ((d.factorial : ℤ) - 1) ∣ factorialMoment coeff index := by
  simpa [hzero] using channelNumerator_mod_factorialMoment coeff index hd

/-- Simultaneous channel annihilation forces the full least-common-multiple
obstruction, independently of the size or geometry of the support. -/
theorem channelLCM_dvd_factorialMoment_of_channels_zero
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ)
    (hzero : ∀ d ∈ Finset.Icc 2 D,
      channelNumerator coeff index d = 0) :
    (channelLCM D : ℤ) ∣ factorialMoment coeff index := by
  rw [Int.natCast_dvd]
  apply Finset.lcm_dvd
  intro d hdmem
  rw [← Int.natCast_dvd]
  have hd : 2 ≤ d := (Finset.mem_Icc.mp hdmem).1
  have hdiv := channelModulus_dvd_factorialMoment_of_channel_zero
    coeff index hd (hzero d hdmem)
  have hfac : 1 ≤ d.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d)
  simpa [channelLCM, Nat.cast_sub hfac] using hdiv

/-- Exact affine normal form for one channel: after subtracting the factorial
moment, the remaining numerator is an integral multiple of `d! - 1`. -/
theorem exists_channelCorrection
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ)
    {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℤ,
      channelNumerator coeff index d =
        factorialMoment coeff index + ((d.factorial : ℤ) - 1) * k := by
  rcases channelNumerator_mod_factorialMoment coeff index hd with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  calc
    channelNumerator coeff index d =
        factorialMoment coeff index -
          (factorialMoment coeff index - channelNumerator coeff index d) := by ring
    _ = factorialMoment coeff index - (((d.factorial : ℤ) - 1) * z) := by rw [hz]
    _ = factorialMoment coeff index + ((d.factorial : ℤ) - 1) * (-z) := by ring

/-- If the factorial moment is zero, the channel numerator is an integral
multiple of `d! - 1`. -/
theorem channelNumerator_eq_modulus_mul_of_moment_zero
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ)
    {d : ℕ} (hd : 2 ≤ d)
    (hmoment : factorialMoment coeff index = 0) :
    ∃ k : ℤ,
      channelNumerator coeff index d = ((d.factorial : ℤ) - 1) * k := by
  rcases exists_channelCorrection coeff index hd with ⟨k, hk⟩
  exact ⟨k, by simpa [hmoment] using hk⟩

/-! ## Product versus lcm with explicit gcd loss -/

/-- Product of all pairwise gcd collision terms in a list, with each
unordered pair counted once. -/
def pairwiseGCDProduct : List ℕ → ℕ
  | [] => 1
  | a :: tail =>
      (tail.map (Nat.gcd a)).prod * pairwiseGCDProduct tail

/-- Recursive lcm of a list, normalized to `1` on the empty list. -/
def listLCM : List ℕ → ℕ
  | [] => 1
  | a :: tail => Nat.lcm a (listLCM tail)

theorem listLCM_dvd_prod (values : List ℕ) :
    listLCM values ∣ values.prod := by
  induction values with
  | nil => simp [listLCM]
  | cons a tail ih =>
      rw [listLCM, List.prod_cons]
      exact Nat.lcm_dvd (dvd_mul_right a tail.prod)
        (ih.trans (dvd_mul_left tail.prod a))

theorem gcd_list_prod_dvd_prod_gcd (a : ℕ) (values : List ℕ) :
    Nat.gcd a values.prod ∣ (values.map (Nat.gcd a)).prod := by
  induction values with
  | nil => simp
  | cons b tail ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons]
      exact (gcd_mul_dvd_mul_gcd a b tail.prod).trans
        (mul_dvd_mul_left (Nat.gcd a b) ih)

/-- The product of a finite list divides its lcm times the product of all
pairwise gcds.  This records precisely the gcd loss used in the
factorial-gap estimate below. -/
theorem list_prod_dvd_lcm_mul_pairwiseGCDProduct (values : List ℕ) :
    values.prod ∣ listLCM values * pairwiseGCDProduct values := by
  induction values with
  | nil => simp [listLCM, pairwiseGCDProduct]
  | cons a tail ih =>
      have hlcm : listLCM tail ∣ tail.prod := listLCM_dvd_prod tail
      have hgcd_lcm :
          Nat.gcd a (listLCM tail) ∣ Nat.gcd a tail.prod :=
        Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
          ((Nat.gcd_dvd_right _ _).trans hlcm)
      have hgcd :
          Nat.gcd a (listLCM tail) ∣
            (tail.map (Nat.gcd a)).prod :=
        hgcd_lcm.trans (gcd_list_prod_dvd_prod_gcd a tail)
      rw [List.prod_cons, listLCM, pairwiseGCDProduct]
      calc
        a * tail.prod ∣ a * (listLCM tail * pairwiseGCDProduct tail) :=
          mul_dvd_mul_left a ih
        _ = (Nat.gcd a (listLCM tail) * Nat.lcm a (listLCM tail)) *
              pairwiseGCDProduct tail := by
                rw [Nat.gcd_mul_lcm]
                ring
        _ = Nat.lcm a (listLCM tail) *
              (Nat.gcd a (listLCM tail) * pairwiseGCDProduct tail) := by
                ring
        _ ∣ Nat.lcm a (listLCM tail) *
              ((tail.map (Nat.gcd a)).prod * pairwiseGCDProduct tail) := by
                exact mul_dvd_mul_left _ (mul_dvd_mul_right hgcd _)

/-! ## Factorial-gap collision bounds -/

theorem dvd_descFactorial_of_pos
    {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    n ∣ n.descFactorial k := by
  cases n with
  | zero => omega
  | succ n =>
      cases k with
      | zero => omega
      | succ k =>
          rw [Nat.succ_descFactorial_succ]
          exact dvd_mul_right _ _

/-- Two factorial gaps can collide only through the intervening descending
factorial: `gcd(m!-1,n!-1)` divides
`n.descFactorial (n-m)-1`. -/
theorem gcd_factorial_sub_one_dvd_descFactorial_sub_one
    {m n : ℕ} (hmn : m < n) :
    Nat.gcd (m.factorial - 1) (n.factorial - 1) ∣
      n.descFactorial (n - m) - 1 := by
  let g := Nat.gcd (m.factorial - 1) (n.factorial - 1)
  have hmfac : 1 ≤ m.factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hnfac : 1 ≤ n.factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hmMod : m.factorial ≡ 1 [MOD g] :=
    ((Nat.modEq_iff_dvd' hmfac).2 (Nat.gcd_dvd_left _ _)).symm
  have hnMod : n.factorial ≡ 1 [MOD g] :=
    ((Nat.modEq_iff_dvd' hnfac).2 (Nat.gcd_dvd_right _ _)).symm
  have hk : n - m ≤ n := Nat.sub_le _ _
  have hfactorial :
      m.factorial * n.descFactorial (n - m) = n.factorial := by
    have h := Nat.factorial_mul_descFactorial hk
    simpa [Nat.sub_sub_self (Nat.le_of_lt hmn)] using h
  have hfactorMod :
      n.factorial ≡ n.descFactorial (n - m) [MOD g] := by
    simpa [hfactorial] using
      hmMod.mul_right (n.descFactorial (n - m))
  have hQMod : n.descFactorial (n - m) ≡ 1 [MOD g] :=
    hfactorMod.symm.trans hnMod
  have hQpos : 1 ≤ n.descFactorial (n - m) := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hk))
  exact (Nat.modEq_iff_dvd' hQpos).1 hQMod.symm

/-- Quantitative pairwise collision cost for factorial gaps. -/
theorem gcd_factorial_sub_one_le_pow_gap
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    Nat.gcd (m.factorial - 1) (n.factorial - 1) ≤ n ^ (n - m) := by
  have hkpos : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hk : n - m ≤ n := Nat.sub_le _ _
  have hndvd :
      n ∣ n.descFactorial (n - m) :=
    dvd_descFactorial_of_pos hkpos hk
  have hnQ : n ≤ n.descFactorial (n - m) :=
    Nat.le_of_dvd (Nat.descFactorial_pos.mpr hk) hndvd
  have hQsubpos : 0 < n.descFactorial (n - m) - 1 := by
    omega
  have hgcdQ :=
    gcd_factorial_sub_one_dvd_descFactorial_sub_one hmn
  calc
    Nat.gcd (m.factorial - 1) (n.factorial - 1) ≤
        n.descFactorial (n - m) - 1 :=
      Nat.le_of_dvd hQsubpos hgcdQ
    _ ≤ n.descFactorial (n - m) := Nat.sub_le _ _
    _ ≤ n ^ (n - m) := Nat.descFactorial_le_pow _ _

/-! ## Consecutive factorial-gap segments -/

/-- The `k` consecutive factorial gaps beginning at `m`. -/
def factorialGapFrom : ℕ → ℕ → List ℕ
  | _, 0 => []
  | m, k + 1 => (m.factorial - 1) :: factorialGapFrom (m + 1) k

/-- Sum `r + (r+1) + ... + (r+k-1)`.  This recursive form keeps the
collision proof free of natural-number division. -/
def intervalExponent : ℕ → ℕ → ℕ
  | _, 0 => 0
  | r, k + 1 => r + intervalExponent (r + 1) k

/-- Triangular collision exponent `1+...+k`. -/
def triangularExponent (k : ℕ) : ℕ :=
  intervalExponent 1 k

/-- Total pair-distance exponent for a segment of length `k`. -/
def pairDistanceExponent : ℕ → ℕ
  | 0 => 0
  | k + 1 => triangularExponent k + pairDistanceExponent k

/-- Collision of one factorial gap with a later consecutive block costs the
sum of the intervening index distances. -/
theorem cross_factorialGap_prod_le_pow_intervalExponent
    {m r k D : ℕ}
    (hm : 2 ≤ m) (hr : 1 ≤ r) (hmax : m + r + k ≤ D + 1) :
    ((factorialGapFrom (m + r) k).map
      (Nat.gcd (m.factorial - 1))).prod ≤
        D ^ intervalExponent r k := by
  induction k generalizing r with
  | zero => simp [factorialGapFrom, intervalExponent]
  | succ k ih =>
      rw [factorialGapFrom, List.map_cons, List.prod_cons, intervalExponent]
      have hmr : m < m + r := by omega
      have hhead0 :=
        gcd_factorial_sub_one_le_pow_gap hm hmr
      have hsub : m + r - m = r := by omega
      have hbase : m + r ≤ D := by omega
      have hhead :
          Nat.gcd (m.factorial - 1) ((m + r).factorial - 1) ≤ D ^ r := by
        calc
          Nat.gcd (m.factorial - 1) ((m + r).factorial - 1) ≤
              (m + r) ^ (m + r - m) := hhead0
          _ = (m + r) ^ r := by rw [hsub]
          _ ≤ D ^ r := Nat.pow_le_pow_left hbase _
      have htail := ih (r := r + 1) (by omega) (by omega)
      calc
        Nat.gcd (m.factorial - 1) ((m + r).factorial - 1) *
            ((factorialGapFrom (m + r + 1) k).map
              (Nat.gcd (m.factorial - 1))).prod ≤
            D ^ r * D ^ intervalExponent (r + 1) k :=
          Nat.mul_le_mul hhead htail
        _ = D ^ (r + intervalExponent (r + 1) k) := by
          rw [pow_add]

/-- The full pairwise gcd collision product for a consecutive factorial-gap
segment is bounded by the exact sum of all pair distances. -/
theorem pairwiseGCDProduct_factorialGapFrom_le
    {m k D : ℕ} (hm : 2 ≤ m) (hmax : m + k ≤ D + 1) :
    pairwiseGCDProduct (factorialGapFrom m k) ≤
      D ^ pairDistanceExponent k := by
  induction k generalizing m with
  | zero => simp [factorialGapFrom, pairwiseGCDProduct, pairDistanceExponent]
  | succ k ih =>
      rw [factorialGapFrom, pairwiseGCDProduct, pairDistanceExponent]
      have hcross :=
        cross_factorialGap_prod_le_pow_intervalExponent
          (m := m) (r := 1) (k := k) (D := D) hm (by omega) (by omega)
      have htail := ih (m := m + 1) (by omega) (by omega)
      calc
        ((factorialGapFrom (m + 1) k).map
              (Nat.gcd (m.factorial - 1))).prod *
            pairwiseGCDProduct (factorialGapFrom (m + 1) k) ≤
          D ^ triangularExponent k * D ^ pairDistanceExponent k :=
            Nat.mul_le_mul hcross htail
        _ = D ^ (triangularExponent k + pairDistanceExponent k) := by
          rw [pow_add]

theorem intervalExponent_eq (r k : ℕ) :
    intervalExponent r k = k * r + k.choose 2 := by
  induction k generalizing r with
  | zero => simp [intervalExponent]
  | succ k ih =>
      rw [intervalExponent, ih, Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      ring

theorem triangularExponent_eq_choose (k : ℕ) :
    triangularExponent k = (k + 1).choose 2 := by
  rw [triangularExponent, intervalExponent_eq, Nat.choose_succ_succ]
  simp

/-- Closed form for the sum of all pair distances in a `k`-term
consecutive segment. -/
theorem pairDistanceExponent_eq_choose (k : ℕ) :
    pairDistanceExponent k = (k + 1).choose 3 := by
  induction k with
  | zero => norm_num [pairDistanceExponent, Nat.choose]
  | succ k ih =>
      rw [pairDistanceExponent, triangularExponent_eq_choose, ih]
      exact (Nat.choose_succ_succ (k + 1) 2).symm

/-- Every consecutive factorial-gap segment lcm divides the ambient
`channelLCM`. -/
theorem listLCM_factorialGapFrom_dvd_channelLCM
    {m k D : ℕ} (hm : 2 ≤ m) (hmax : m + k ≤ D + 1) :
    listLCM (factorialGapFrom m k) ∣ channelLCM D := by
  induction k generalizing m with
  | zero => simp [factorialGapFrom, listLCM]
  | succ k ih =>
      rw [factorialGapFrom, listLCM]
      apply Nat.lcm_dvd
      · apply Finset.dvd_lcm
        rw [Finset.mem_Icc]
        omega
      · exact ih (m := m + 1) (by omega) (by omega)

theorem factorialGapFrom_mem_pos
    {m k x : ℕ} (hm : 2 ≤ m) (hx : x ∈ factorialGapFrom m k) :
    0 < x := by
  induction k generalizing m with
  | zero => simp [factorialGapFrom] at hx
  | succ k ih =>
      simp only [factorialGapFrom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr (by omega))
      · exact ih (m := m + 1) (by omega) hx

theorem factorialGapFrom_prod_pos {m k : ℕ} (hm : 2 ≤ m) :
    0 < (factorialGapFrom m k).prod :=
  List.prod_pos (fun _ hx ↦ factorialGapFrom_mem_pos hm hx)

/-- Every term of a consecutive factorial-gap block is at least its first
term, so the block product dominates the corresponding constant power. -/
theorem pow_factorial_sub_one_le_factorialGapFrom_prod
    (m k : ℕ) :
    (m.factorial - 1) ^ k ≤ (factorialGapFrom m k).prod := by
  induction k generalizing m with
  | zero => simp [factorialGapFrom]
  | succ k ih =>
      rw [factorialGapFrom, List.prod_cons]
      have hfactorial : m.factorial ≤ (m + 1).factorial :=
        Nat.factorial_le (by omega)
      have hgap : m.factorial - 1 ≤ (m + 1).factorial - 1 :=
        Nat.sub_le_sub_right hfactorial 1
      calc
        (m.factorial - 1) ^ (k + 1) =
            (m.factorial - 1) * (m.factorial - 1) ^ k := by
              rw [pow_succ, Nat.mul_comm]
        _ ≤ (m.factorial - 1) * ((m + 1).factorial - 1) ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgap _)
        _ ≤ (m.factorial - 1) * (factorialGapFrom (m + 1) k).prod :=
          Nat.mul_le_mul_left _ (ih (m + 1))

theorem listLCM_factorialGapFrom_pos {m k : ℕ} (hm : 2 ≤ m) :
    0 < listLCM (factorialGapFrom m k) := by
  induction k generalizing m with
  | zero => simp [factorialGapFrom, listLCM]
  | succ k ih =>
      rw [factorialGapFrom, listLCM]
      apply Nat.pos_of_ne_zero
      exact Nat.lcm_ne_zero
        (Nat.ne_of_gt (Nat.sub_pos_of_lt
          (Nat.one_lt_factorial.mpr (by omega))))
        (Nat.ne_of_gt (ih (m := m + 1) (by omega)))

theorem pairwiseGCDProduct_factorialGapFrom_pos
    {m k : ℕ} (hm : 2 ≤ m) :
    0 < pairwiseGCDProduct (factorialGapFrom m k) := by
  induction k generalizing m with
  | zero => simp [factorialGapFrom, pairwiseGCDProduct]
  | succ k ih =>
      rw [factorialGapFrom, pairwiseGCDProduct]
      apply Nat.mul_pos
      · apply List.prod_pos
        intro g hg
        rw [List.mem_map] at hg
        rcases hg with ⟨x, hx, rfl⟩
        exact Nat.gcd_pos_of_pos_left _
          (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr (by omega)))
      · exact ih (m := m + 1) (by omega)

theorem channelLCM_pos (D : ℕ) : 0 < channelLCM D := by
  unfold channelLCM
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro d hd
  have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
  exact Nat.ne_of_gt
    (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr (by omega)))

/-- Exact finite consecutive-segment inequality before rewriting the
pair-distance exponent in closed form. -/
theorem factorialGapFrom_prod_le_channelLCM_mul_pow
    {m k D : ℕ} (hm : 2 ≤ m) (hmax : m + k ≤ D + 1) :
    (factorialGapFrom m k).prod ≤
      channelLCM D * D ^ pairDistanceExponent k := by
  have hdiv :=
    list_prod_dvd_lcm_mul_pairwiseGCDProduct (factorialGapFrom m k)
  have hmidpos :
      0 < listLCM (factorialGapFrom m k) *
        pairwiseGCDProduct (factorialGapFrom m k) :=
    Nat.mul_pos (listLCM_factorialGapFrom_pos hm)
      (pairwiseGCDProduct_factorialGapFrom_pos hm)
  have hlcm :=
    listLCM_factorialGapFrom_dvd_channelLCM hm hmax
  have hlcm_le :
      listLCM (factorialGapFrom m k) ≤ channelLCM D :=
    Nat.le_of_dvd (channelLCM_pos D) hlcm
  have hpairs :=
    pairwiseGCDProduct_factorialGapFrom_le hm hmax
  calc
    (factorialGapFrom m k).prod ≤
        listLCM (factorialGapFrom m k) *
          pairwiseGCDProduct (factorialGapFrom m k) :=
      Nat.le_of_dvd hmidpos hdiv
    _ ≤ channelLCM D * D ^ pairDistanceExponent k :=
      Nat.mul_le_mul hlcm_le hpairs

/-- The final `k` factorial gaps ending at `D`, listed from low to high. -/
def factorialGapSegment (D k : ℕ) : List ℕ :=
  factorialGapFrom (D + 1 - k) k

/-- Exact finite segment inequality with the recursive pair-distance
exponent. -/
theorem factorialGapSegment_prod_le_channelLCM_mul_pow
    {D k : ℕ} (hkD : k < D) :
    (factorialGapSegment D k).prod ≤
      channelLCM D * D ^ pairDistanceExponent k := by
  unfold factorialGapSegment
  apply factorialGapFrom_prod_le_channelLCM_mul_pow
  · omega
  · omega

/-- Exact finite segment inequality in binomial closed form:
`choose (k+1) 3 = k(k^2-1)/6`. -/
theorem factorialGapSegment_prod_le_channelLCM_mul_pow_choose
    {D k : ℕ} (hkD : k < D) :
    (factorialGapSegment D k).prod ≤
      channelLCM D * D ^ ((k + 1).choose 3) := by
  simpa [pairDistanceExponent_eq_choose] using
    factorialGapSegment_prod_le_channelLCM_mul_pow hkD

/-- Exact finite lower constraint on the channel lcm.  It combines the
smallest gap in the final `k`-block with the pairwise-gcd upper bound. -/
theorem factorialGapSegment_base_pow_le_channelLCM_mul_pow_choose
    {D k : ℕ} (hkD : k < D) :
    ((D + 1 - k).factorial - 1) ^ k ≤
      channelLCM D * D ^ ((k + 1).choose 3) := by
  calc
    ((D + 1 - k).factorial - 1) ^ k ≤
        (factorialGapSegment D k).prod := by
      exact pow_factorial_sub_one_le_factorialGapFrom_prod _ _
    _ ≤ channelLCM D * D ^ ((k + 1).choose 3) :=
      factorialGapSegment_prod_le_channelLCM_mul_pow_choose hkD

/-- If a positive integer is a multiple of the channel lcm and is smaller
than the factorial gap at `R+1`, then the channel lcm is smaller than that gap
as well. -/
theorem channelLCM_lt_radiusFactorial_sub_one_of_dvd_of_lt
    {D M R : ℕ}
    (hMpos : 0 < M)
    (hdiv : channelLCM D ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    channelLCM D < (R + 1).factorial - 1 :=
  lt_of_le_of_lt (Nat.le_of_dvd hMpos hdiv) hsmall

/-- Finite radius constraint obtained by combining divisibility by the
channel lcm with the final-block estimate. -/
theorem factorialGapSegment_base_pow_lt_radiusFactorial_mul_pow
    {D k M R : ℕ}
    (hkD : k < D)
    (hMpos : 0 < M)
    (hdiv : channelLCM D ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    ((D + 1 - k).factorial - 1) ^ k <
      ((R + 1).factorial - 1) * D ^ ((k + 1).choose 3) := by
  have hQ :
      channelLCM D < (R + 1).factorial - 1 :=
    channelLCM_lt_radiusFactorial_sub_one_of_dvd_of_lt hMpos hdiv hsmall
  have hDpos : 0 < D ^ ((k + 1).choose 3) :=
    pow_pos (by omega) _
  exact lt_of_le_of_lt
    (factorialGapSegment_base_pow_le_channelLCM_mul_pow_choose hkD)
    (Nat.mul_lt_mul_of_pos_right hQ hDpos)

/-- Logarithmic form of the exact pre-asymptotic radius constraint.  This is
the finite real inequality to which explicit Stirling estimates and the
choice `k = Nat.sqrt (2 * D)` can be applied; it contains no asymptotic
notation. -/
theorem factorialGapSegment_log_radius_constraint
    {D k M R : ℕ}
    (hkD : k < D)
    (hMpos : 0 < M)
    (hdiv : channelLCM D ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    (k : ℝ) * Real.log (((D + 1 - k).factorial - 1 : ℕ) : ℝ) <
      Real.log (((R + 1).factorial - 1 : ℕ) : ℝ) +
        (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ) := by
  have hnat :=
    factorialGapSegment_base_pow_lt_radiusFactorial_mul_pow
      hkD hMpos hdiv hsmall
  have hbasePos : 0 < (D + 1 - k).factorial - 1 := by
    exact Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr (by omega))
  have hradiusPos : 0 < (R + 1).factorial - 1 := by
    omega
  have hDpos : 0 < D := by omega
  have hcast :
      ((((D + 1 - k).factorial - 1) ^ k : ℕ) : ℝ) <
        ((((R + 1).factorial - 1) * D ^ ((k + 1).choose 3) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hlog :=
    Real.log_lt_log
      (by positivity :
        0 < ((((D + 1 - k).factorial - 1) ^ k : ℕ) : ℝ))
      hcast
  simpa [Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul,
    hbasePos.ne', hradiusPos.ne', hDpos.ne'] using hlog

/-- An explicit lower bound for the logarithm of a factorial gap.  It is the
global lower Stirling estimate with only nonnegative secondary terms discarded,
and the elementary loss `n! - 1 ≥ n! / 2`. -/
theorem log_factorial_sub_one_lower_bound
    {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * Real.log (n : ℝ) - n - Real.log 2 ≤
      Real.log ((n.factorial - 1 : ℕ) : ℝ) := by
  have hfac2 : 2 ≤ n.factorial :=
    (Nat.factorial_le hn).trans' (by norm_num)
  have hfacPos : (0 : ℝ) < n.factorial := by positivity
  have hgapPos : (0 : ℝ) < (n.factorial - 1 : ℕ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (by omega : 1 < n.factorial))
  have hhalfNat : n.factorial ≤ 2 * (n.factorial - 1) := by omega
  have hhalf :
      (n.factorial : ℝ) / 2 ≤ (n.factorial - 1 : ℕ) := by
    apply (div_le_iff₀ (by norm_num)).2
    exact_mod_cast (by simpa [Nat.mul_comm] using hhalfNat)
  have hlogHalf :
      Real.log ((n.factorial : ℝ) / 2) ≤
        Real.log ((n.factorial - 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) hhalf
  have hstirling := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  rw [Real.log_div (by positivity) (by norm_num)] at hlogHalf
  nlinarith

/-- Elementary upper bound for a factorial gap: `log(n! - 1) ≤ n log n`. -/
theorem log_factorial_sub_one_upper_bound
    {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n.factorial - 1 : ℕ) : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) := by
  have hgapPos : (0 : ℝ) < (n.factorial - 1 : ℕ) := by
    exact_mod_cast
      (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr (by omega)))
  have hgapFac : n.factorial - 1 ≤ n.factorial := Nat.sub_le _ _
  have hfacPow : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have hcast :
      ((n.factorial - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast hgapFac.trans hfacPow
  have hlog := Real.log_le_log hgapPos hcast
  simpa [Real.log_pow] using hlog

/-- Explicit finite radius constraint after applying the stated Stirling
bounds.  The conclusion contains no factorials or logarithms of factorial
gaps. -/
theorem factorialGapSegment_stirling_radius_constraint
    {D k M R : ℕ}
    (hkD : k < D)
    (hMpos : 0 < M)
    (hdiv : channelLCM D ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    (k : ℝ) *
        (((D + 1 - k : ℕ) : ℝ) *
            Real.log ((D + 1 - k : ℕ) : ℝ) -
          (D + 1 - k : ℕ) - Real.log 2) <
      ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
        (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ) := by
  have hn : 2 ≤ D + 1 - k := by omega
  have hR : 2 ≤ R + 1 := by
    have : 0 < (R + 1).factorial - 1 := by omega
    exact (Nat.one_lt_factorial.mp (by omega))
  have hlower :=
    log_factorial_sub_one_lower_bound (n := D + 1 - k) hn
  have hupper :=
    log_factorial_sub_one_upper_bound (n := R + 1) hR
  have hmiddle :=
    factorialGapSegment_log_radius_constraint hkD hMpos hdiv hsmall
  have hkNonneg : (0 : ℝ) ≤ k := by positivity
  norm_num at hupper ⊢
  calc
    (k : ℝ) *
        ((↑(D + 1 - k) : ℝ) * Real.log (↑(D + 1 - k) : ℝ) -
          ↑(D + 1 - k) - Real.log 2) ≤
        (k : ℝ) *
          Real.log (((D + 1 - k).factorial - 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlower hkNonneg
    _ < Real.log (((R + 1).factorial - 1 : ℕ) : ℝ) +
          (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ) :=
      hmiddle
    _ ≤ (↑R + 1) * Real.log (↑R + 1) +
          (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ) :=
      by
        simpa [add_comm] using
          add_le_add_right hupper
            ((((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ))

/-- Optimizing block length from the elementary lcm argument. -/
def radiusOptimizationWindow (D : ℕ) : ℕ :=
  Nat.sqrt (2 * D)

theorem radiusOptimizationWindow_sq_le (D : ℕ) :
    radiusOptimizationWindow D ^ 2 ≤ 2 * D := by
  exact Nat.sqrt_le' _

theorem two_mul_lt_radiusOptimizationWindow_succ_sq (D : ℕ) :
    2 * D < (radiusOptimizationWindow D + 1) ^ 2 := by
  exact Nat.lt_succ_sqrt' _

theorem radiusOptimizationWindow_lt
    {D : ℕ} (hD : 3 ≤ D) :
    radiusOptimizationWindow D < D := by
  rw [radiusOptimizationWindow, Nat.sqrt_lt']
  nlinarith

/-- The Stirling constraint at the final-block length `⌊√(2D)⌋`. -/
theorem optimized_stirling_radius_constraint
    {D M R : ℕ}
    (hD : 3 ≤ D)
    (hMpos : 0 < M)
    (hdiv : channelLCM D ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    let k := radiusOptimizationWindow D
    (k : ℝ) *
        (((D + 1 - k : ℕ) : ℝ) *
            Real.log ((D + 1 - k : ℕ) : ℝ) -
          (D + 1 - k : ℕ) - Real.log 2) <
      ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
        (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ) := by
  exact factorialGapSegment_stirling_radius_constraint
    (radiusOptimizationWindow_lt hD) hMpos hdiv hsmall

/-- Cubic upper bound for the collision exponent on the exact square
subsequence `D = 2t²`, `k = 2t`. -/
theorem three_mul_choose_two_mul_add_one_le_four_mul_cube (t : ℕ) :
    3 * (2 * t + 1).choose 3 ≤ 4 * t ^ 3 := by
  cases t with
  | zero => norm_num [Nat.choose]
  | succ t =>
      have hdesc :=
        Nat.descFactorial_eq_factorial_mul_choose (2 * (t + 1) + 1) 3
      have hsub : 2 * (t + 1) + 1 - 2 = 2 * t + 1 := by omega
      norm_num [Nat.descFactorial, Nat.factorial, hsub] at hdesc
      nlinarith

/-- Exact cubic formula for the collision exponent on the square-subsequence
window.  The additive form avoids natural-number subtraction. -/
theorem three_mul_choose_two_mul_add_one_add_self_eq_four_mul_cube (t : ℕ) :
    3 * (2 * t + 1).choose 3 + t = 4 * t ^ 3 := by
  cases t with
  | zero => norm_num [Nat.choose]
  | succ t =>
      have hdesc :=
        Nat.descFactorial_eq_factorial_mul_choose (2 * (t + 1) + 1) 3
      have hsub : 2 * (t + 1) + 1 - 2 = 2 * t + 1 := by omega
      norm_num [Nat.descFactorial, Nat.factorial, hsub] at hdesc
      nlinarith

/-- **Sharp-constant boundary of the one-kernel logarithmic constraint.**
If the putative radius lies exactly on the asymptotically optimized boundary
`R+1 = (16/9)t³`, then the existing finite logarithmic constraint is already
satisfied.  Consequently that constraint alone cannot force a strict lower
bound at the sharp constant; only subcritical constants (or a stronger finite
input) remain available. -/
theorem sharp_radius_satisfies_square_log_constraint
    {t R : ℕ} (ht : 4 ≤ t) (hsharp : 9 * (R + 1) = 16 * t ^ 3) :
    (2 * t : ℝ) *
          (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
              Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) -
            (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) <
        ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) := by
  let n : ℕ := 2 * t ^ 2 + 1 - 2 * t
  have htpos : 0 < t := by omega
  have htone : 1 ≤ t := by omega
  have hnpos : 0 < n := by
    dsimp [n]
    have : 2 * t ≤ t ^ 2 := by nlinarith
    omega
  have hnleNat : n ≤ 2 * t ^ 2 := by
    dsimp [n]
    omega
  have hnEq : n + 2 * t = 2 * t ^ 2 + 1 := by
    dsimp [n]
    omega
  have hnCast : (n : ℝ) = 2 * (t : ℝ) ^ 2 - 2 * (t : ℝ) + 1 := by
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnEq
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hcast ⊢
    nlinarith
  have hnMass : 3 * (t : ℝ) ^ 3 ≤ 2 * (t : ℝ) * (n : ℝ) := by
    rw [hnCast]
    have htReal : (4 : ℝ) ≤ t := by exact_mod_cast ht
    nlinarith
  have hnle : (n : ℝ) ≤ ((2 * t ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnleNat
  have hlognle :
      Real.log (n : ℝ) ≤ Real.log ((2 * t ^ 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) hnle
  have hlogDnonneg : 0 ≤ Real.log ((2 * t ^ 2 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have hDone : 1 ≤ 2 * t ^ 2 := by nlinarith
    exact_mod_cast hDone
  have hchooseNat :=
    three_mul_choose_two_mul_add_one_add_self_eq_four_mul_cube t
  have hchoose :
      (3 : ℝ) * (((2 * t + 1).choose 3 : ℕ) : ℝ) + (t : ℝ) =
        4 * (t : ℝ) ^ 3 := by
    exact_mod_cast hchooseNat
  have hcoeff :
      2 * (t : ℝ) * (n : ℝ) - (((2 * t + 1).choose 3 : ℕ) : ℝ) ≤
        (8 : ℝ) / 3 * (t : ℝ) ^ 3 := by
    rw [hnCast]
    nlinarith [show (1 : ℝ) ≤ t by exact_mod_cast htone]
  have hlogD :
      Real.log ((2 * t ^ 2 : ℕ) : ℝ) =
        Real.log 2 + 2 * Real.log (t : ℝ) := by
    norm_num [Nat.cast_mul, Nat.cast_pow, Real.log_mul, Real.log_pow,
      htpos.ne']
  have hR :
      ((R + 1 : ℕ) : ℝ) = (16 : ℝ) / 9 * (t : ℝ) ^ 3 := by
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hsharp
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hcast ⊢
    nlinarith
  have hlogR :
      Real.log (R + 1 : ℝ) =
        Real.log ((16 : ℝ) / 9) + 3 * Real.log (t : ℝ) := by
    have hR' : (R : ℝ) + 1 = (16 : ℝ) / 9 * (t : ℝ) ^ 3 := by
      norm_num at hR ⊢
      exact hR
    rw [hR', Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2hi : Real.log 2 < 1 := by
    nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  have hlogRatioPos : 0 < Real.log ((16 : ℝ) / 9) :=
    Real.log_pos (by norm_num)
  have hconstant :
      (8 : ℝ) / 3 * Real.log 2 - 3 <
        (16 : ℝ) / 9 * Real.log ((16 : ℝ) / 9) := by
    nlinarith
  have htCubePos : 0 < (t : ℝ) ^ 3 := by positivity
  have hconstantScaled := mul_lt_mul_of_pos_right hconstant htCubePos
  have hcore :
      ((8 : ℝ) / 3 * (t : ℝ) ^ 3) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) -
          3 * (t : ℝ) ^ 3 <
        ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) := by
    rw [hlogD, hR, hlogR]
    nlinarith
  have hcoeffLog := mul_le_mul_of_nonneg_right hcoeff hlogDnonneg
  have hupper :
      (2 * t : ℝ) *
          ((n : ℝ) * Real.log ((2 * t ^ 2 : ℕ) : ℝ) - (n : ℝ)) ≤
        (((8 : ℝ) / 3 * (t : ℝ) ^ 3) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) - 3 * (t : ℝ) ^ 3) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) := by
    norm_num [Nat.cast_mul] at hcoeffLog ⊢
    nlinarith
  change
    (2 * t : ℝ) *
          ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) - Real.log 2) < _
  calc
    (2 * t : ℝ) *
          ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) - Real.log 2) <
        (2 * t : ℝ) *
          ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) := by
            have htwoT : 0 < (2 * t : ℝ) := by positivity
            nlinarith [mul_pos htwoT hlog2pos]
    _ ≤ (2 * t : ℝ) *
          ((n : ℝ) * Real.log ((2 * t ^ 2 : ℕ) : ℝ) - (n : ℝ)) := by
            gcongr
    _ ≤ (((8 : ℝ) / 3 * (t : ℝ) ^ 3) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) - 3 * (t : ℝ) ^ 3) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) := hupper
    _ < ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) := by
            linarith

/-- On the exact square subsequence, the finite logarithmic constraint already
forces a cubic radius.  The deliberately coarse constant keeps this implication
fully explicit; no asymptotic notation is used. -/
theorem square_subsequence_radius_cubic_of_log_constraint
    {t R : ℕ} (ht : 4096 ≤ t)
    (hconstraint :
      (2 * t : ℝ) *
          (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
              Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) -
            (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) <
        ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ)) :
    t ^ 3 < 8 * (R + 1) := by
  have htpos : 0 < t := by omega
  have htone : 1 ≤ t := by omega
  have htReal : (1 : ℝ) ≤ t := by exact_mod_cast htone
  have hlogt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htReal
  have hnloNat :
      t ^ 2 ≤ 2 * t ^ 2 + 1 - 2 * t := by
    have : t ^ 2 + 2 * t ≤ 2 * t ^ 2 + 1 := by nlinarith
    omega
  have hnhiNat :
      2 * t ^ 2 + 1 - 2 * t ≤ 2 * t ^ 2 := by omega
  have hnlo :
      ((t ^ 2 : ℕ) : ℝ) ≤
        ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) := by
    exact_mod_cast hnloNat
  have hnhi :
      ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) ≤
        ((2 * t ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnhiNat
  have hlogn :
      2 * Real.log (t : ℝ) ≤
        Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) := by
    have h :=
      Real.log_le_log (by positivity : (0 : ℝ) < (t ^ 2 : ℕ)) hnlo
    simpa [Nat.cast_pow, Real.log_pow] using h
  have hnlogn :
      ((t ^ 2 : ℕ) : ℝ) * (2 * Real.log (t : ℝ)) ≤
        ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
          Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) := by
    exact mul_le_mul hnlo hlogn (by positivity) (by positivity)
  have hchooseNat :=
    three_mul_choose_two_mul_add_one_le_four_mul_cube t
  have hchoose :
      (3 : ℝ) * (((2 * t + 1).choose 3 : ℕ) : ℝ) ≤
        4 * (t : ℝ) ^ 3 := by exact_mod_cast hchooseNat
  have hlogD :
      Real.log ((2 * t ^ 2 : ℕ) : ℝ) =
        Real.log 2 + 2 * Real.log (t : ℝ) := by
    norm_num [Nat.cast_mul, Nat.cast_pow, Real.log_mul, Real.log_pow,
      htpos.ne']
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lo : (2 : ℝ) / 3 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 1 := by
    nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  have hlogtlo : 12 * Real.log 2 ≤ Real.log (t : ℝ) := by
    have hpowNat : 2 ^ 12 ≤ t := by norm_num at ht ⊢; exact ht
    have hpow :
        ((2 : ℝ) ^ 12) ≤ (t : ℝ) := by exact_mod_cast hpowNat
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ 12) hpow
    simpa [Real.log_pow] using h
  by_contra hnot
  have hsmallNat : 8 * (R + 1) ≤ t ^ 3 := by omega
  have hsNat : R + 1 ≤ t ^ 3 := by omega
  have hs :
      ((R + 1 : ℕ) : ℝ) ≤ (t : ℝ) ^ 3 := by exact_mod_cast hsNat
  have hlogs :
      Real.log (R + 1 : ℝ) ≤ 3 * Real.log (t : ℝ) := by
    have h :=
      Real.log_le_log (by positivity : (0 : ℝ) < (R + 1 : ℕ)) hs
    simpa [Real.log_pow] using h
  have hradius :
      ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) ≤
        ((t : ℝ) ^ 3 / 8) * (3 * Real.log (t : ℝ)) := by
    have hs8 :
        ((R + 1 : ℕ) : ℝ) ≤ (t : ℝ) ^ 3 / 8 := by
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
        (by
          have hcast :
              (8 : ℝ) * ((R + 1 : ℕ) : ℝ) ≤ (t : ℝ) ^ 3 := by
            exact_mod_cast hsmallNat
          simpa [mul_comm] using hcast)
    have hRone : (1 : ℝ) ≤ (R + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
    have hlogR : 0 ≤ Real.log (R + 1 : ℝ) :=
      Real.log_nonneg hRone
    exact mul_le_mul hs8 hlogs hlogR (by positivity)
  have hcollision :
      (((2 * t + 1).choose 3 : ℕ) : ℝ) *
          Real.log ((2 * t ^ 2 : ℕ) : ℝ) ≤
        (4 * (t : ℝ) ^ 3 / 3) *
          (Real.log 2 + 2 * Real.log (t : ℝ)) := by
    rw [hlogD]
    have hc :
        (((2 * t + 1).choose 3 : ℕ) : ℝ) ≤
          4 * (t : ℝ) ^ 3 / 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hlhs :
      4 * (t : ℝ) ^ 3 * Real.log (t : ℝ) -
          4 * (t : ℝ) ^ 3 - 2 * (t : ℝ) * Real.log 2 ≤
        (2 * t : ℝ) *
          (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
              Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) -
            (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) := by
    norm_num [Nat.cast_mul, Nat.cast_pow] at hnlogn hnhi ⊢
    nlinarith
  have htCube : (1 : ℝ) ≤ (t : ℝ) ^ 3 :=
    one_le_pow₀ htReal
  have htLeCube : (t : ℝ) ≤ (t : ℝ) ^ 3 := by
    calc
      (t : ℝ) = (t : ℝ) * 1 := by ring
      _ ≤ (t : ℝ) * (t : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ htReal) (by positivity)
      _ = (t : ℝ) ^ 3 := by ring
  rw [hlogD] at hcollision
  nlinarith

/-- On `D = 2t²`, the divisibility and factorial-gap hypotheses force the
explicit lower bound `t³ < 8(R+1)`. -/
theorem square_subsequence_radius_cubic_lower
    {t M R : ℕ} (ht : 4096 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    t ^ 3 < 8 * (R + 1) := by
  apply square_subsequence_radius_cubic_of_log_constraint ht
  have hkD : 2 * t < 2 * t ^ 2 := by
    have htpos : 0 < t := by omega
    nlinarith
  have hconstraint :=
    factorialGapSegment_stirling_radius_constraint
      (D := 2 * t ^ 2) (k := 2 * t) hkD hMpos hdiv hsmall
  simpa [Nat.cast_mul] using hconstraint

/-- Under the channel-lcm and factorial-gap hypotheses for every sufficiently
large `t`, the reverse cubic bound `8(R(t)+1) ≤ t³` cannot hold eventually. -/
theorem no_eventual_square_subsequence_cubic_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 8 * (R t + 1) ≤ t ^ 3 := by
  rintro ⟨T, hupper⟩
  let t := max T 4096
  have htT : T ≤ t := by exact Nat.le_max_left _ _
  have ht : 4096 ≤ t := by exact Nat.le_max_right _ _
  have hlower :=
    square_subsequence_radius_cubic_lower ht
      (hMpos t ht) (hdiv t ht) (hsmall t ht)
  exact (Nat.not_lt_of_ge (hupper t htT)) hlower

/-- Mathlib little-o form of the square-subsequence obstruction.  Thus the
radius sequence cannot be `o(t³)`, equivalently cannot be
`o(D^(3/2))` after the reparameterization `D = 2t²`, under the checked
channel hypotheses. -/
theorem not_isLittleO_square_subsequence_radius
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => ((R t + 1 : ℕ) : ℝ)) =o[Filter.atTop]
        (fun t : ℕ => (t : ℝ) ^ 3) := by
  intro hlittle
  have hreal :=
    hlittle.def (show (0 : ℝ) < 1 / 8 by norm_num)
  have hnat :
      ∀ᶠ t : ℕ in Filter.atTop, 8 * (R t + 1) ≤ t ^ 3 := by
    filter_upwards [hreal] with t ht
    have hleft :
        |(((R t + 1 : ℕ) : ℝ))| = ((R t + 1 : ℕ) : ℝ) :=
      abs_of_nonneg (by positivity)
    have hright :
        |(t : ℝ) ^ 3| = (t : ℝ) ^ 3 :=
      abs_of_nonneg (by positivity)
    simp only [Real.norm_eq_abs, hleft, hright] at ht
    have hcast :
        (8 : ℝ) * ((R t + 1 : ℕ) : ℝ) ≤ ((t ^ 3 : ℕ) : ℝ) := by
      norm_num [Nat.cast_pow] at ht ⊢
      nlinarith
    exact_mod_cast hcast
  exact no_eventual_square_subsequence_cubic_upper M R
    hMpos hdiv hsmall (Filter.eventually_atTop.1 hnat)

set_option maxHeartbeats 800000 in
/-- Retaining most of the terminal factorial index sharpens the first coarse
square-subsequence constant: for `t ≥ 2^32`, the same finite logarithmic
constraint forces `R + 1 > (3/2)t³`. -/
theorem square_subsequence_radius_three_halves_of_log_constraint
    {t R : ℕ} (ht : 2 ^ 32 ≤ t)
    (hconstraint :
      (2 * t : ℝ) *
          (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
              Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) -
            (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) <
        ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ)) :
    3 * t ^ 3 < 2 * (R + 1) := by
  have ht32 : 32 ≤ t := by
    have : (32 : ℕ) ≤ 2 ^ 32 := by norm_num
    omega
  have htpos : 0 < t := by omega
  have htone : 1 ≤ t := by omega
  have htReal : (1 : ℝ) ≤ t := by exact_mod_cast htone
  have hlogt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htReal
  have hnloNat :
      t ^ 2 ≤ 2 * t ^ 2 + 1 - 2 * t := by
    have : t ^ 2 + 2 * t ≤ 2 * t ^ 2 + 1 := by nlinarith
    omega
  have hnstrongNat :
      15 * t ^ 2 ≤ 8 * (2 * t ^ 2 + 1 - 2 * t) := by
    have : 15 * t ^ 2 + 16 * t ≤ 16 * t ^ 2 + 8 := by nlinarith
    omega
  have hnhiNat :
      2 * t ^ 2 + 1 - 2 * t ≤ 2 * t ^ 2 := by omega
  have hnlo :
      ((t ^ 2 : ℕ) : ℝ) ≤
        ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) := by
    exact_mod_cast hnloNat
  have hnstrong :
      (15 : ℝ) / 8 * (t : ℝ) ^ 2 ≤
        ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) := by
    have hcast :
        (15 : ℝ) * (t : ℝ) ^ 2 ≤
          8 * ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) := by
      exact_mod_cast hnstrongNat
    nlinarith
  have hnhi :
      ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) ≤
        2 * (t : ℝ) ^ 2 := by
    exact_mod_cast hnhiNat
  have hlogn :
      2 * Real.log (t : ℝ) ≤
        Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) := by
    have h :=
      Real.log_le_log (by positivity : (0 : ℝ) < (t ^ 2 : ℕ)) hnlo
    simpa [Nat.cast_pow, Real.log_pow] using h
  have hnlogn :
      ((15 : ℝ) / 8 * (t : ℝ) ^ 2) *
          (2 * Real.log (t : ℝ)) ≤
        ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
          Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) := by
    exact mul_le_mul hnstrong hlogn (by positivity) (by positivity)
  have hchooseNat :=
    three_mul_choose_two_mul_add_one_le_four_mul_cube t
  have hchoose :
      (3 : ℝ) * (((2 * t + 1).choose 3 : ℕ) : ℝ) ≤
        4 * (t : ℝ) ^ 3 := by exact_mod_cast hchooseNat
  have hlogD :
      Real.log ((2 * t ^ 2 : ℕ) : ℝ) =
        Real.log 2 + 2 * Real.log (t : ℝ) := by
    norm_num [Nat.cast_mul, Nat.cast_pow, Real.log_mul, Real.log_pow,
      htpos.ne']
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lo : (2 : ℝ) / 3 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 1 := by
    nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  have hlogtlo : 32 * Real.log 2 ≤ Real.log (t : ℝ) := by
    have hpow :
        ((2 : ℝ) ^ 32) ≤ (t : ℝ) := by exact_mod_cast ht
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ 32) hpow
    simpa [Real.log_pow] using h
  by_contra hnot
  have hsmallNat : 2 * (R + 1) ≤ 3 * t ^ 3 := by omega
  have hsNat : R + 1 ≤ 2 * t ^ 3 := by omega
  have hs :
      ((R + 1 : ℕ) : ℝ) ≤ (3 : ℝ) / 2 * (t : ℝ) ^ 3 := by
    have hcast :
        (2 : ℝ) * ((R + 1 : ℕ) : ℝ) ≤
          3 * (t : ℝ) ^ 3 := by exact_mod_cast hsmallNat
    nlinarith
  have hlogs :
      Real.log (R + 1 : ℝ) ≤
        Real.log 2 + 3 * Real.log (t : ℝ) := by
    have hs' :
        ((R + 1 : ℕ) : ℝ) ≤ 2 * (t : ℝ) ^ 3 := by
      exact_mod_cast hsNat
    have h :=
      Real.log_le_log (by positivity : (0 : ℝ) < (R + 1 : ℕ)) hs'
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    norm_num at h ⊢
    exact h
  have hradius :
      ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) ≤
        ((3 : ℝ) / 2 * (t : ℝ) ^ 3) *
          (Real.log 2 + 3 * Real.log (t : ℝ)) := by
    have hRone : (1 : ℝ) ≤ (R + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
    have hlogR : 0 ≤ Real.log (R + 1 : ℝ) :=
      Real.log_nonneg hRone
    exact mul_le_mul hs hlogs hlogR (by positivity)
  have hcollision :
      (((2 * t + 1).choose 3 : ℕ) : ℝ) *
          Real.log ((2 * t ^ 2 : ℕ) : ℝ) ≤
        (4 * (t : ℝ) ^ 3 / 3) *
          (Real.log 2 + 2 * Real.log (t : ℝ)) := by
    rw [hlogD]
    have hc :
        (((2 * t + 1).choose 3 : ℕ) : ℝ) ≤
          4 * (t : ℝ) ^ 3 / 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hlhs :
      (15 : ℝ) / 2 * (t : ℝ) ^ 3 * Real.log (t : ℝ) -
          4 * (t : ℝ) ^ 3 - 2 * (t : ℝ) * Real.log 2 ≤
        (2 * t : ℝ) *
          (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
              Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) -
            (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) := by
    norm_num [Nat.cast_mul, Nat.cast_pow] at hnlogn hnhi ⊢
    nlinarith
  have htLeCube : (t : ℝ) ≤ (t : ℝ) ^ 3 := by
    nlinarith [show (1 : ℝ) ≤ t by exact_mod_cast htone]
  have hlogscaled :
      32 * Real.log 2 * (t : ℝ) ^ 3 ≤
        Real.log (t : ℝ) * (t : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right hlogtlo (by positivity)
  have hlog2scaled :
      ((2 : ℝ) / 3) * (t : ℝ) ^ 3 <
        Real.log 2 * (t : ℝ) ^ 3 :=
    mul_lt_mul_of_pos_right hlog2lo (by positivity)
  have hlinear :
      (t : ℝ) * Real.log 2 ≤ (t : ℝ) ^ 3 := by
    have := mul_le_mul htLeCube (le_of_lt hlog2hi)
      (le_of_lt hlog2pos) (by positivity : (0 : ℝ) ≤ (t : ℝ) ^ 3)
    nlinarith
  rw [hlogD] at hcollision
  nlinarith

/-- The channel hypotheses force the explicit bound
`R + 1 > (3/2)t³` on `D = 2t²`. -/
theorem square_subsequence_radius_three_halves_lower
    {t M R : ℕ} (ht : 2 ^ 32 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := by
  apply square_subsequence_radius_three_halves_of_log_constraint ht
  have hkD : 2 * t < 2 * t ^ 2 := by
    have htpos : 0 < t := by
      have : (0 : ℕ) < 2 ^ 32 := by positivity
      omega
    nlinarith
  have hconstraint :=
    factorialGapSegment_stirling_radius_constraint
      (D := 2 * t ^ 2) (k := 2 * t) hkD hMpos hdiv hsmall
  simpa [Nat.cast_mul] using hconstraint

/-- Sequence form of the improved constant: the competing upper bound
`R(t)+1 ≤ (3/2)t³` cannot hold eventually. -/
theorem no_eventual_square_subsequence_three_halves_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 2 ^ 32 ≤ t → 0 < M t)
    (hdiv : ∀ t, 2 ^ 32 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 2 ^ 32 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 2 * (R t + 1) ≤ 3 * t ^ 3 := by
  rintro ⟨T, hupper⟩
  let t := max T (2 ^ 32)
  have htT : T ≤ t := by exact Nat.le_max_left _ _
  have ht : 2 ^ 32 ≤ t := by exact Nat.le_max_right _ _
  have hlower :=
    square_subsequence_radius_three_halves_lower ht
      (hMpos t ht) (hdiv t ht) (hsmall t ht)
  exact (Nat.not_lt_of_ge (hupper t htT)) hlower

#print axioms list_prod_dvd_lcm_mul_pairwiseGCDProduct
#print axioms gcd_factorial_sub_one_dvd_descFactorial_sub_one
#print axioms pairDistanceExponent_eq_choose
#print axioms factorialGapSegment_prod_le_channelLCM_mul_pow_choose
#print axioms factorialGapSegment_base_pow_lt_radiusFactorial_mul_pow
#print axioms factorialGapSegment_log_radius_constraint
#print axioms factorialGapSegment_stirling_radius_constraint
#print axioms optimized_stirling_radius_constraint
#print axioms three_mul_choose_two_mul_add_one_add_self_eq_four_mul_cube
#print axioms sharp_radius_satisfies_square_log_constraint
#print axioms square_subsequence_radius_cubic_lower
#print axioms no_eventual_square_subsequence_cubic_upper
#print axioms not_isLittleO_square_subsequence_radius
#print axioms square_subsequence_radius_three_halves_lower
#print axioms no_eventual_square_subsequence_three_halves_upper

end Erdos68
