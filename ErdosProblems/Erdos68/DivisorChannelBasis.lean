import ErdosProblems.Erdos68.FactorialChannelCertificate
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Divisor-coordinate channel basis for Erdős problem 68

The adjacent difference `T_n = n e_{n-1} - e_n` hits exactly the divisor
channels of index `n`.  Subtracting proper-divisor copies produces an
integral family `U_n` with a single nonzero channel.  On the manuscript
support `n ≥ 2`, the second channel forces an extra factor of `12` in the
moment, so annihilating channels through `D` yields `12 L_D ∣ M`.

No declaration here constructs a cofinal nonintegrality family or decides
rationality of the factorial-gap series.
-/

namespace ErdosProblems.Erdos68

open Finsupp

/-! ## Linearity of the Finsupp channel presentation -/

theorem channelNumerator_add (f g : ℕ →₀ ℤ) (d : ℕ) :
    channelNumerator (f + g) d =
      channelNumerator f d + channelNumerator g d := by
  unfold channelNumerator
  exact sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem channelNumerator_zero (d : ℕ) : channelNumerator 0 d = 0 := by
  simp [channelNumerator]

theorem channelNumerator_smul (z : ℤ) (f : ℕ →₀ ℤ) (d : ℕ) :
    channelNumerator (z • f) d = z * channelNumerator f d := by
  classical
  unfold channelNumerator
  rw [sum_smul_index' (fun _ => by simp)]
  simp only [smul_eq_mul]
  simp_rw [mul_assoc]
  unfold Finsupp.sum
  rw [← Finset.mul_sum]

theorem channelNumerator_neg (f : ℕ →₀ ℤ) (d : ℕ) :
    channelNumerator (-f) d = -channelNumerator f d := by
  rw [← neg_one_smul ℤ f, channelNumerator_smul]
  ring

theorem channelNumerator_sub (f g : ℕ →₀ ℤ) (d : ℕ) :
    channelNumerator (f - g) d =
      channelNumerator f d - channelNumerator g d := by
  simp [sub_eq_add_neg, channelNumerator_add, channelNumerator_neg]

theorem channelNumerator_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ →₀ ℤ)
    (d : ℕ) :
    channelNumerator (∑ i ∈ s, f i) d =
      ∑ i ∈ s, channelNumerator (f i) d := by
  classical
  induction s using Finset.induction with
  | empty => simp [channelNumerator_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, channelNumerator_add, ih]

theorem factorialMoment_add (f g : ℕ →₀ ℤ) :
    factorialMoment (f + g) = factorialMoment f + factorialMoment g := by
  unfold factorialMoment
  exact sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem factorialMoment_smul (z : ℤ) (f : ℕ →₀ ℤ) :
    factorialMoment (z • f) = z * factorialMoment f := by
  classical
  unfold factorialMoment
  rw [sum_smul_index' (fun _ => by simp)]
  simp only [smul_eq_mul]
  simp_rw [mul_assoc]
  unfold Finsupp.sum
  rw [← Finset.mul_sum]

theorem factorialMoment_neg (f : ℕ →₀ ℤ) :
    factorialMoment (-f) = -factorialMoment f := by
  rw [← neg_one_smul ℤ f, factorialMoment_smul]
  ring

theorem factorialMoment_sub (f g : ℕ →₀ ℤ) :
    factorialMoment (f - g) = factorialMoment f - factorialMoment g := by
  simp [sub_eq_add_neg, factorialMoment_add, factorialMoment_neg]

theorem factorialMoment_zero : factorialMoment (0 : ℕ →₀ ℤ) = 0 := by
  simp [factorialMoment]

theorem factorialMoment_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ →₀ ℤ) :
    factorialMoment (∑ i ∈ s, f i) = ∑ i ∈ s, factorialMoment (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [factorialMoment_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, factorialMoment_add, ih]

theorem channelNumerator_single (i : ℕ) (z : ℤ) (d : ℕ) :
    channelNumerator (single i z) d = z * (channelWeight i d : ℤ) := by
  unfold channelNumerator
  exact sum_single_index (by simp)

theorem factorialMoment_single (i : ℕ) (z : ℤ) :
    factorialMoment (single i z) = z * (i.factorial : ℤ) := by
  unfold factorialMoment
  exact sum_single_index (by simp)

/-! ## Adjacent differences `T_n` -/

/-- Adjacent difference `T_n = n e_{n-1} - e_n`. -/
noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1

theorem channelNumerator_adjacentDifference
    {n d : ℕ} (_hn : 1 ≤ n) :
    channelNumerator (adjacentDifference n) d = channelEvent d n := by
  unfold adjacentDifference channelEvent
  rw [channelNumerator_sub, channelNumerator_single, channelNumerator_single]
  ring

theorem factorialMoment_adjacentDifference {n : ℕ} (hn : 1 ≤ n) :
    factorialMoment (adjacentDifference n) = 0 := by
  have hsucc : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  have hfac : n.factorial = n * (n - 1).factorial := by
    simpa [hsucc] using Nat.factorial_succ (n - 1)
  unfold adjacentDifference
  rw [factorialMoment_sub, factorialMoment_single, factorialMoment_single]
  simp [hfac]

lemma pred_div_eq_of_dvd
    {d n : ℕ} (hdpos : 0 < d) (hn : 0 < n) (hnd : d ∣ n) :
    (n - 1) / d = n / d - 1 := by
  have heq : d * (n / d) = n := Nat.mul_div_cancel' hnd
  have hq : 1 ≤ n / d :=
    Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hn hnd) hdpos)
  have hsucc : n / d - 1 + 1 = n / d := Nat.sub_add_cancel hq
  have hdecomp : n - 1 = d * (n / d - 1) + (d - 1) := by
    calc
      n - 1 = d * (n / d) - 1 := by rw [heq]
      _ = d * (n / d - 1 + 1) - 1 := by rw [hsucc]
      _ = d * (n / d - 1) + d - 1 := by rw [mul_add, mul_one]
      _ = d * (n / d - 1) + (d - 1) :=
        Nat.add_sub_assoc (Nat.succ_le_of_lt hdpos) _
  rw [hdecomp, Nat.mul_add_div hdpos]
  have : (d - 1) / d = 0 :=
    Nat.div_eq_of_lt (Nat.sub_lt hdpos (by omega))
  rw [this, Nat.add_zero]

/-- On a divisor event, `T_n` contributes exactly `(d! - 1) W_{d,n}`. -/
theorem channelEvent_eq_of_dvd
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) (hnd : d ∣ n) :
    channelEvent d n =
      ((d.factorial : ℤ) - 1) * (channelWeight n d : ℤ) := by
  have hdpos : 0 < d := by omega
  have hle : d ≤ n := Nat.le_of_dvd hn hnd
  have hfloor : (n - 1) / d = n / d - 1 := pred_div_eq_of_dvd hdpos hn hnd
  have hq : n / d = (n - 1) / d + 1 := by
    have : 1 ≤ n / d := Nat.div_pos hle hdpos
    omega
  have hsucc : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  have hfac : n.factorial = n * (n - 1).factorial := by
    simpa [hsucc] using Nat.factorial_succ (n - 1)
  have hnW := channelWeight_mul_denominator n d hdpos
  have hpredW := channelWeight_mul_denominator (n - 1) d hdpos
  have hpow :
      d.factorial ^ (n / d) =
        d.factorial ^ ((n - 1) / d) * d.factorial := by
    rw [hq, pow_succ]
  have hmul :
      d.factorial ^ ((n - 1) / d) * (d.factorial * channelWeight n d) =
        d.factorial ^ ((n - 1) / d) *
          (n * channelWeight (n - 1) d) := by
    calc
      d.factorial ^ ((n - 1) / d) * (d.factorial * channelWeight n d)
          = d.factorial ^ (n / d) * channelWeight n d := by
            rw [hpow, mul_assoc]
      _ = n.factorial := hnW
      _ = n * (n - 1).factorial := hfac
      _ = n * (d.factorial ^ ((n - 1) / d) * channelWeight (n - 1) d) := by
            rw [hpredW]
      _ = d.factorial ^ ((n - 1) / d) * (n * channelWeight (n - 1) d) := by
            ring
  have hpowpos : 0 < d.factorial ^ ((n - 1) / d) :=
    Nat.pow_pos (Nat.factorial_pos d)
  have hNW :
      d.factorial * channelWeight n d = n * channelWeight (n - 1) d :=
    Nat.eq_of_mul_eq_mul_left hpowpos hmul
  have hNWZ :
      (d.factorial : ℤ) * (channelWeight n d : ℤ) =
        (n : ℤ) * (channelWeight (n - 1) d : ℤ) := by
    exact_mod_cast hNW
  unfold channelEvent
  rw [← hNWZ]
  ring

theorem channelEvent_eq_indicator
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    channelEvent d n =
      (if d ∣ n then ((d.factorial : ℤ) - 1) * (channelWeight n d : ℤ)
        else 0) := by
  by_cases hnd : d ∣ n
  · simp [hnd, channelEvent_eq_of_dvd hd hn hnd]
  · simp [hnd, channelEvent_eq_zero_of_not_dvd hd hnd]

/-- `V_d(T_n) = (d! - 1) W_{d,n} 1_{d | n}`. -/
theorem channelNumerator_adjacentDifference_eq
    {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) :
    channelNumerator (adjacentDifference n) d =
      (if d ∣ n then ((d.factorial : ℤ) - 1) * (channelWeight n d : ℤ)
        else 0) := by
  have hn0 : 0 < n := by omega
  rw [channelNumerator_adjacentDifference (by omega),
    channelEvent_eq_indicator hd hn0]

theorem channelWeight_self {n : ℕ} (hn : 0 < n) :
    channelWeight n n = 1 := by
  have hn1 : n / n = 1 := Nat.div_self hn
  rw [channelWeight, hn1, pow_one, Nat.div_self (Nat.factorial_pos n)]

/-! ## Support-sensitive factor of `12` -/

lemma channelWeight_two_mul_pow (n : ℕ) :
    2 ^ (n / 2) * channelWeight n 2 = n.factorial := by
  simpa [Nat.factorial_two] using channelWeight_mul_denominator n 2 (by omega)

lemma channelWeight_two_even (k : ℕ) :
    channelWeight (2 * k) 2 =
      k.factorial * ∏ i ∈ Finset.range k, (2 * i + 1) := by
  induction k with
  | zero => simp [channelWeight]
  | succ k ih =>
      have hfloor : (2 * (k + 1)) / 2 = k + 1 := by omega
      have hfloor' : (2 * k) / 2 = k := by omega
      have hfac :
          (2 * (k + 1)).factorial =
            (2 * (k + 1)) * (2 * k + 1) * (2 * k).factorial := by
        have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
        have h0 : 2 * k + 1 = (2 * k) + 1 := by omega
        rw [h1, Nat.factorial_succ, h0, Nat.factorial_succ]
        ring
      have hW := channelWeight_two_mul_pow (2 * (k + 1))
      have hW' := channelWeight_two_mul_pow (2 * k)
      apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
      calc
        2 ^ (k + 1) * channelWeight (2 * (k + 1)) 2
            = (2 * (k + 1)).factorial := by
              simpa [hfloor, Nat.factorial_two] using hW
        _ = (2 * (k + 1)) * (2 * k + 1) * (2 * k).factorial := hfac
        _ = 2 * (k + 1) * (2 * k + 1) * (2 ^ k * channelWeight (2 * k) 2) := by
              simpa [hfloor', Nat.factorial_two] using congrArg
                (fun t => (2 * (k + 1)) * (2 * k + 1) * t) hW'.symm
        _ = 2 ^ (k + 1) *
              ((k + 1) * (2 * k + 1) * channelWeight (2 * k) 2) := by
              ring
        _ = 2 ^ (k + 1) *
              ((k + 1) * (2 * k + 1) *
                (k.factorial * ∏ i ∈ Finset.range k, (2 * i + 1))) := by
              simp [ih]
        _ = 2 ^ (k + 1) *
              ((k + 1).factorial *
                ∏ i ∈ Finset.range (k + 1), (2 * i + 1)) := by
              simp [Nat.factorial_succ, Finset.prod_range_succ]
              ring

lemma channelWeight_two_odd (k : ℕ) :
    channelWeight (2 * k + 1) 2 =
      (2 * k + 1) * channelWeight (2 * k) 2 := by
  have hfloor : (2 * k + 1) / 2 = k := by omega
  have hfloor' : (2 * k) / 2 = k := by omega
  have hW := channelWeight_two_mul_pow (2 * k + 1)
  have hW' := channelWeight_two_mul_pow (2 * k)
  have hfac : (2 * k + 1).factorial = (2 * k + 1) * (2 * k).factorial :=
    Nat.factorial_succ (2 * k)
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
  calc
    2 ^ k * channelWeight (2 * k + 1) 2 = (2 * k + 1).factorial := by
      simpa [hfloor, Nat.factorial_two] using hW
    _ = (2 * k + 1) * (2 * k).factorial := hfac
    _ = (2 * k + 1) * (2 ^ k * channelWeight (2 * k) 2) := by
          simpa [hfloor', Nat.factorial_two] using
            congrArg (fun t => (2 * k + 1) * t) hW'.symm
    _ = 2 ^ k * ((2 * k + 1) * channelWeight (2 * k) 2) := by ring

lemma two_dvd_channelWeight_two_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    2 ∣ channelWeight n 2 := by
  rcases Nat.even_or_odd' n with ⟨k, h | h⟩
  · have hk : 2 ≤ k := by omega
    rw [h, channelWeight_two_even]
    exact dvd_mul_of_dvd_left (Nat.dvd_factorial (by omega) hk) _
  · have hk : 2 ≤ k := by omega
    rw [h, channelWeight_two_odd, channelWeight_two_even]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (Nat.dvd_factorial (by omega) hk) _) _

lemma three_dvd_channelWeight_two_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ channelWeight n 2 := by
  have hmul := channelWeight_two_mul_pow n
  have h3 : 3 ∣ n.factorial :=
    (show 3 ∣ (3 : ℕ).factorial by decide).trans
      (Nat.factorial_dvd_factorial hn)
  have hcop : Nat.Coprime 3 (2 ^ (n / 2)) :=
    Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
  have : 3 ∣ 2 ^ (n / 2) * channelWeight n 2 := by
    rw [hmul]; exact h3
  exact hcop.dvd_of_dvd_mul_left this

lemma six_dvd_channelWeight_two_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    6 ∣ channelWeight n 2 :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3)
    (two_dvd_channelWeight_two_of_four_le hn)
    (three_dvd_channelWeight_two_of_three_le (by omega))

/-- Pointwise `12 ∣ n! - 2 W_{2,n}` on the manuscript support `n ≥ 2`. -/
theorem twelve_dvd_factorial_sub_two_channelWeight
    {n : ℕ} (hn : 2 ≤ n) :
    (12 : ℤ) ∣ (n.factorial : ℤ) - 2 * (channelWeight n 2 : ℤ) := by
  rcases le_or_gt n 3 with hn3 | hn4
  · have : n = 2 ∨ n = 3 := by omega
    rcases this with rfl | rfl <;> native_decide
  · have hn4' : 4 ≤ n := by omega
    have h24 : 24 ∣ n.factorial :=
      (show 24 ∣ (4 : ℕ).factorial by decide).trans
        (Nat.factorial_dvd_factorial hn4')
    have h12n : 12 ∣ n.factorial :=
      dvd_trans (by decide : 12 ∣ 24) h24
    have h6 : 6 ∣ channelWeight n 2 := six_dvd_channelWeight_two_of_four_le hn4'
    have h12W : 12 ∣ 2 * channelWeight n 2 := by
      obtain ⟨k, hk⟩ := h6
      refine ⟨k, ?_⟩
      rw [hk]; ring
    have h12W' : (12 : ℤ) ∣ 2 * (channelWeight n 2 : ℤ) := by
      exact_mod_cast h12W
    have h12n' : (12 : ℤ) ∣ (n.factorial : ℤ) := by
      exact_mod_cast h12n
    exact dvd_sub h12n' h12W'

/-- `M(λ) - 2 V_2(λ) ≡ 0 (mod 12)` for finite integer vectors supported on
`n ≥ 2`. -/
theorem twelve_dvd_moment_sub_two_channelTwo
    (lam : ℕ →₀ ℤ) (hsupp : ∀ n ∈ lam.support, 2 ≤ n) :
    (12 : ℤ) ∣ factorialMoment lam - 2 * channelNumerator lam 2 := by
  classical
  unfold factorialMoment channelNumerator
  have hfun :
      (lam.sum fun i z =>
          z * (i.factorial : ℤ) - 2 * (z * (channelWeight i 2 : ℤ))) =
        lam.sum (fun i z => z * (i.factorial : ℤ)) -
          2 * lam.sum (fun i z => z * (channelWeight i 2 : ℤ)) := by
    rw [sum_sub]
    simp [Finsupp.sum, Finset.mul_sum]
  change (12 : ℤ) ∣
      lam.sum (fun i z => z * (i.factorial : ℤ)) -
        2 * lam.sum (fun i z => z * (channelWeight i 2 : ℤ))
  rw [← hfun]
  unfold Finsupp.sum
  apply Finset.dvd_sum
  intro i hi
  have hi2 : 2 ≤ i := hsupp i hi
  have hpt := twelve_dvd_factorial_sub_two_channelWeight hi2
  have hterm :
      (fun i z => z * (i.factorial : ℤ) - 2 * (z * (channelWeight i 2 : ℤ)))
          i (lam i) =
        lam i * ((i.factorial : ℤ) - 2 * (channelWeight i 2 : ℤ)) := by
    ring
  rw [hterm]
  exact dvd_mul_of_dvd_right hpt _

/-! ## Channel moduli and `12 L_D` -/

theorem channelWeight_sub_factorial_dvd {d i : ℕ} (hd : 2 ≤ d) :
    ((d.factorial : ℤ) - 1) ∣
      (i.factorial : ℤ) - (channelWeight i d : ℤ) := by
  have hdpos : 0 < d := by omega
  have hmul := channelWeight_mul_denominator i d hdpos
  have hcast :
      (i.factorial : ℤ) =
        (d.factorial : ℤ) ^ (i / d) * (channelWeight i d : ℤ) := by
    exact_mod_cast hmul.symm
  have hpow : ∀ k : ℕ, ((d.factorial : ℤ) - 1) ∣
      (d.factorial : ℤ) ^ k - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hsplit :
            (d.factorial : ℤ) ^ (k + 1) - 1 =
              (d.factorial : ℤ) * ((d.factorial : ℤ) ^ k - 1) +
                ((d.factorial : ℤ) - 1) := by ring
        rw [hsplit]
        exact dvd_add (dvd_mul_of_dvd_right ih _) dvd_rfl
  have hpow := hpow (i / d)
  rcases hpow with ⟨z, hz⟩
  refine ⟨(channelWeight i d : ℤ) * z, ?_⟩
  calc
    (i.factorial : ℤ) - (channelWeight i d : ℤ) =
        (channelWeight i d : ℤ) * ((d.factorial : ℤ) ^ (i / d) - 1) := by
          rw [hcast]; ring
    _ = (channelWeight i d : ℤ) * (((d.factorial : ℤ) - 1) * z) := by rw [hz]
    _ = ((d.factorial : ℤ) - 1) * ((channelWeight i d : ℤ) * z) := by ring

theorem channelModulus_dvd_moment_sub_channel
    (lam : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ((d.factorial : ℤ) - 1) ∣
      factorialMoment lam - channelNumerator lam d := by
  classical
  unfold factorialMoment channelNumerator Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  have hpt := channelWeight_sub_factorial_dvd (d := d) (i := i) hd
  change ((d.factorial : ℤ) - 1) ∣
    lam i * (i.factorial : ℤ) - lam i * (channelWeight i d : ℤ)
  have :
      lam i * (i.factorial : ℤ) - lam i * (channelWeight i d : ℤ) =
        lam i * ((i.factorial : ℤ) - (channelWeight i d : ℤ)) := by ring
  rw [this]
  exact dvd_mul_of_dvd_right hpt _

theorem channelModulus_dvd_factorialMoment_of_channel_zero
    (lam : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d)
    (hzero : channelNumerator lam d = 0) :
    ((d.factorial : ℤ) - 1) ∣ factorialMoment lam := by
  simpa [hzero] using channelModulus_dvd_moment_sub_channel lam hd

/-- Least common multiple of the channel moduli through `D`. -/
def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

theorem channelLCM_dvd_factorialMoment_of_channels_zero
    (D : ℕ) (lam : ℕ →₀ ℤ)
    (hzero : ∀ d ∈ Finset.Icc 2 D, channelNumerator lam d = 0) :
    (channelLCM D : ℤ) ∣ factorialMoment lam := by
  rw [Int.natCast_dvd]
  apply Finset.lcm_dvd
  intro d hdmem
  rw [← Int.natCast_dvd]
  have hd : 2 ≤ d := (Finset.mem_Icc.mp hdmem).1
  have hdiv := channelModulus_dvd_factorialMoment_of_channel_zero lam hd
    (hzero d hdmem)
  have hfac : 1 ≤ d.factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d)
  simpa [channelLCM, Nat.cast_sub hfac] using hdiv

lemma coprime_twelve_factorial_sub_one {d : ℕ} (hd : 2 ≤ d) :
    Nat.Coprime 12 (d.factorial - 1) := by
  rcases le_or_gt d 3 with hle | hgt
  · have : d = 2 ∨ d = 3 := by omega
    rcases this with rfl | rfl <;> decide
  · have h24 : 24 ∣ d.factorial :=
      (show 24 ∣ (4 : ℕ).factorial by decide).trans
        (Nat.factorial_dvd_factorial (by omega : 4 ≤ d))
    have h12 : 12 ∣ d.factorial := dvd_trans (by decide : 12 ∣ 24) h24
    obtain ⟨k, hk⟩ := h12
    have hkpos : 1 ≤ k := by
      have : 12 ≤ d.factorial := Nat.le_of_dvd (Nat.factorial_pos d) ⟨k, hk⟩
      have : 1 ≤ 12 * k := by omega
      omega
    have hdecomp : 12 * k - 1 = 12 * (k - 1) + 11 := by omega
    rw [Nat.coprime_iff_gcd_eq_one, hk, hdecomp, Nat.gcd_mul_left_add_right]
    decide

lemma coprime_lcm_of_coprime {x a b : ℕ}
    (ha : Nat.Coprime x a) (hb : Nat.Coprime x b) :
    Nat.Coprime x (Nat.lcm a b) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  have hxpos : 0 < x := Nat.pos_of_ne_zero fun hx => by
    subst hx
    have ha' : a = 1 := by
      have : Nat.gcd 0 a = 1 := ha
      simpa [Nat.gcd_zero_left] using this
    have hb' : b = 1 := by
      have : Nat.gcd 0 b = 1 := hb
      simpa [Nat.gcd_zero_left] using this
    simp [ha', hb'] at hne
  have hpos : 0 < Nat.gcd x (Nat.lcm a b) := Nat.gcd_pos_of_pos_left _ hxpos
  have hgt : 1 < Nat.gcd x (Nat.lcm a b) := by omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
  have hpx : p ∣ x := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpL : p ∣ Nat.lcm a b := hpdvd.trans (Nat.gcd_dvd_right _ _)
  rcases hp.dvd_lcm.mp hpL with hpa | hpb
  · have : p ∣ 1 :=
      (Nat.coprime_iff_gcd_eq_one.mp ha) ▸ Nat.dvd_gcd hpx hpa
    exact Nat.Prime.not_dvd_one hp this
  · have : p ∣ 1 :=
      (Nat.coprime_iff_gcd_eq_one.mp hb) ▸ Nat.dvd_gcd hpx hpb
    exact Nat.Prime.not_dvd_one hp this

lemma coprime_twelve_finset_lcm (s : Finset ℕ) (hs : ∀ d ∈ s, 2 ≤ d) :
    Nat.Coprime 12 (s.lcm fun d => d.factorial - 1) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert d s _hd ih =>
      rw [Finset.lcm_insert]
      exact coprime_lcm_of_coprime
        (coprime_twelve_factorial_sub_one (hs d (Finset.mem_insert_self d s)))
        (ih fun x hx => hs x (Finset.mem_insert_of_mem hx))

lemma coprime_twelve_channelLCM (D : ℕ) : Nat.Coprime 12 (channelLCM D) :=
  coprime_twelve_finset_lcm _ fun _d hd => (Finset.mem_Icc.mp hd).1

/-- On support `n ≥ 2`, annihilating channels `2, …, D` with `D ≥ 2` forces
`12 L_D ∣ M`. -/
theorem twelve_channelLCM_dvd_factorialMoment_of_channels_zero
    {D : ℕ} (hD : 2 ≤ D) (lam : ℕ →₀ ℤ)
    (hsupp : ∀ n ∈ lam.support, 2 ≤ n)
    (hzero : ∀ d ∈ Finset.Icc 2 D, channelNumerator lam d = 0) :
    ((12 : ℤ) * channelLCM D) ∣ factorialMoment lam := by
  have hV2 : channelNumerator lam 2 = 0 :=
    hzero 2 (by simp [Finset.mem_Icc, hD])
  have h12 : (12 : ℤ) ∣ factorialMoment lam := by
    simpa [hV2] using twelve_dvd_moment_sub_two_channelTwo lam hsupp
  have hL := channelLCM_dvd_factorialMoment_of_channels_zero D lam hzero
  have hcop : IsCoprime (12 : ℤ) (channelLCM D : ℤ) :=
    (coprime_twelve_channelLCM D).isCoprime
  simpa [mul_comm] using hcop.mul_dvd h12 hL

/-! ## Isolated channel units `U_n` -/

/-- Isolated one-channel basis vector, `U_n = T_n - ∑_{d | n, 2 ≤ d < n} W_{d,n} U_d`. -/
noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ :=
  n.strongRecOn' fun n rec =>
    if n ≤ 1 then 0
    else
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2
          else 0

theorem isolatedChannelUnit_eq (n : ℕ) :
    isolatedChannelUnit n =
      if n ≤ 1 then 0
      else
        adjacentDifference n -
          ∑ d ∈ (Finset.Ico 2 n).attach,
            if d.1 ∣ n then
              (channelWeight n d.1 : ℤ) • isolatedChannelUnit d.1
            else 0 := by
  unfold isolatedChannelUnit
  rw [Nat.strongRecOn'_beta]

theorem isolatedChannelUnit_of_le_one {n : ℕ} (hn : n ≤ 1) :
    isolatedChannelUnit n = 0 := by
  rw [isolatedChannelUnit_eq, if_pos hn]

theorem isolatedChannelUnit_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    isolatedChannelUnit n =
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • isolatedChannelUnit d.1
          else 0 := by
  rw [isolatedChannelUnit_eq, if_neg (by omega)]

theorem factorialMoment_isolatedChannelUnit
    {n : ℕ} (hn : 2 ≤ n) :
    factorialMoment (isolatedChannelUnit n) = 0 := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      rw [isolatedChannelUnit_of_two_le hn, factorialMoment_sub,
        factorialMoment_adjacentDifference (by omega),
        factorialMoment_sum]
      simp only [zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro d _
      split_ifs with hdiv
      · have hdlt : d.1 < n := (Finset.mem_Ico.mp d.2).2
        have hd2 : 2 ≤ d.1 := (Finset.mem_Ico.mp d.2).1
        rw [factorialMoment_smul, ih d.1 hdlt hd2, mul_zero]
      · simp [factorialMoment_zero]

/-- `V_d(U_n) = (d! - 1) 1_{d = n}` for `d ≥ 2`. -/
theorem channelNumerator_isolatedChannelUnit
    {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) :
    channelNumerator (isolatedChannelUnit n) d =
      if d = n then ((n.factorial : ℤ) - 1) else 0 := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      have hn0 : 0 < n := by omega
      rw [isolatedChannelUnit_of_two_le hn, channelNumerator_sub,
        channelNumerator_adjacentDifference_eq hn hd, channelNumerator_sum]
      have hsummand :
          ∀ e ∈ Finset.Ico 2 n,
            channelNumerator
              (if e ∣ n then
                (channelWeight n e : ℤ) • isolatedChannelUnit e else 0) d =
              if e ∣ n ∧ e = d then
                (channelWeight n d : ℤ) * ((d.factorial : ℤ) - 1) else 0 := by
        intro e he
        have he2 : 2 ≤ e := (Finset.mem_Ico.mp he).1
        have helt : e < n := (Finset.mem_Ico.mp he).2
        by_cases hdiv : e ∣ n
        · rw [if_pos hdiv, channelNumerator_smul, ih e helt he2]
          by_cases hde : e = d
          · subst hde
            simp [hdiv]
          · rw [if_neg (Ne.symm hde)]
            simp [hde]
        · simp [hdiv, channelNumerator_zero]
      have hsum :
          ∑ e ∈ (Finset.Ico 2 n).attach,
              channelNumerator
                (if e.1 ∣ n then
                  (channelWeight n e.1 : ℤ) • isolatedChannelUnit e.1
                  else 0) d =
            if d ∣ n ∧ d < n then
              ((d.factorial : ℤ) - 1) * (channelWeight n d : ℤ)
            else 0 := by
        classical
        have := Finset.sum_attach (s := Finset.Ico 2 n)
          (f := fun e =>
            channelNumerator
              (if e ∣ n then
                (channelWeight n e : ℤ) • isolatedChannelUnit e else 0) d)
        rw [this, Finset.sum_congr rfl hsummand]
        by_cases hdn : d ∣ n ∧ d < n
        · have hdI : d ∈ Finset.Ico 2 n := by
            simp [Finset.mem_Ico, hd, hdn.2]
          rw [if_pos hdn, Finset.sum_eq_single d]
          · rw [if_pos ⟨hdn.1, rfl⟩]
            ring
          · intro e _he hne
            rw [if_neg fun h => hne h.2]
          · intro hnot
            exact (hnot hdI).elim
        · rw [if_neg hdn]
          apply Finset.sum_eq_zero
          intro e he
          by_cases hdiv : e ∣ n
          · have helt : e < n := (Finset.mem_Ico.mp he).2
            have hne : e ≠ d := fun h => hdn ⟨h ▸ hdiv, h ▸ helt⟩
            rw [if_neg fun h => hne h.2]
          · simp [hdiv]
      rw [hsum]
      by_cases hdn : d ∣ n
      · by_cases hlt : d < n
        · have hne : d ≠ n := ne_of_lt hlt
          simp [hdn, hlt, hne]
        · have hge : n ≤ d := Nat.le_of_not_gt hlt
          have heq : d = n :=
            le_antisymm (Nat.le_of_dvd hn0 hdn) hge
          subst heq
          simp [channelWeight_self hn0]
      · have hne : d ≠ n := fun h => hdn (h ▸ dvd_refl n)
        simp [hdn, hne]

theorem isolatedChannelUnit_two :
    isolatedChannelUnit 2 = adjacentDifference 2 := by
  rw [isolatedChannelUnit_of_two_le (by decide)]
  have hA : (Finset.Ico 2 2).attach = ∅ := by simp
  rw [hA, Finset.sum_empty, sub_zero]

/-- Odd isolated units have vanishing index-`1` coordinate. -/
theorem isolatedChannelUnit_apply_one_of_odd
    {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) :
    isolatedChannelUnit n 1 = 0 := by
  suffices ∀ m, 2 ≤ m → Odd m → isolatedChannelUnit m 1 = 0 from
    this n hn hodd
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm hodd
      rw [isolatedChannelUnit_of_two_le hm]
      have hne2 : m ≠ 2 := fun h =>
        (h ▸ Nat.not_odd_iff_even.2 even_two) hodd
      have hne1 : m ≠ 1 := by omega
      have hT : adjacentDifference m 1 = 0 := by
        unfold adjacentDifference
        have hpred : m - 1 ≠ 1 := fun h => hne2 (by omega)
        simp [Finsupp.sub_apply, hpred, hne1]
      have hsum :
          (∑ d ∈ (Finset.Ico 2 m).attach,
              if d.1 ∣ m then
                (channelWeight m d.1 : ℤ) • isolatedChannelUnit d.1
              else 0) 1 = 0 := by
        rw [Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro d hd
        split_ifs with hdiv
        · have hd2 : 2 ≤ d.1 := (Finset.mem_Ico.mp d.2).1
          have hlt : d.1 < m := (Finset.mem_Ico.mp d.2).2
          have hodd' : Odd d.1 := Odd.of_dvd_nat hodd hdiv
          rw [Finsupp.smul_apply, ih d.1 hlt hd2 hodd', smul_zero]
        · simp
      rw [Finsupp.sub_apply, hT, zero_sub, neg_eq_zero]
      exact hsum

/-- Sharp `D = 2` moment: `-6 e_2 + e_4` has vanishing channel `2` and moment `12`. -/
noncomputable def lambda24 : ℕ →₀ ℤ :=
  single 2 (-6) + single 4 1

theorem lambda24_channel_two : channelNumerator lambda24 2 = 0 := by
  unfold lambda24
  rw [channelNumerator_add, channelNumerator_single, channelNumerator_single]
  native_decide

theorem lambda24_factorialMoment : factorialMoment lambda24 = 12 := by
  unfold lambda24
  rw [factorialMoment_add, factorialMoment_single, factorialMoment_single]
  native_decide

/-- Sharp `D = 3` moment: `-6 e_2 - 8 e_3 + 5 e_4` has vanishing channels `2,3`
and moment `60 = 12 L_3`. -/
noncomputable def lambda234 : ℕ →₀ ℤ :=
  single 2 (-6) + single 3 (-8) + single 4 5

theorem lambda234_channel_two : channelNumerator lambda234 2 = 0 := by
  unfold lambda234
  rw [channelNumerator_add, channelNumerator_add, channelNumerator_single,
    channelNumerator_single, channelNumerator_single]
  native_decide

theorem lambda234_channel_three : channelNumerator lambda234 3 = 0 := by
  unfold lambda234
  rw [channelNumerator_add, channelNumerator_add, channelNumerator_single,
    channelNumerator_single, channelNumerator_single]
  native_decide

theorem lambda234_factorialMoment : factorialMoment lambda234 = 60 := by
  unfold lambda234
  rw [factorialMoment_add, factorialMoment_add, factorialMoment_single,
    factorialMoment_single, factorialMoment_single]
  native_decide

theorem channelLCM_three : channelLCM 3 = 5 := by
  native_decide

end ErdosProblems.Erdos68
