import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos243.ReciprocalTailRigidity

/-!
# Erdős #243: the slow-rise barrier by common-divisor persistence

`ReciprocalTailRigidity.lean` excludes a *bounded* negative part by stabilising
the tail gcd, reducing the orbit, and running a CRT block against the
pairwise-coprime reduced multipliers.  Gcd stabilisation needs bounded negative
magnitudes, so that route stops exactly at the bounded regime.

This module replaces gcd stabilisation by *persistence*: a common divisor of
one tail state `Cₙ` and denominator state `Dₙ` divides every later `Cₜ`, `Dₜ`,
and therefore every later centred error `Eₜ = Dₜ - (aₜ - 1) Cₜ`.  A landing on a
CRT block therefore locks a whole block modulus into every later error, and the
next negative error is at least that modulus.  The CRT block is placed in
`[P, 2P)` for `P` the block product, so the rise bound is only needed below `2P`.

Consequences kernel-checked here:

* `exists_consecutiveMultiples_between`: the bounded CRT block.
* `commonDivisor_persists`, `multiplierOverlap_persists`,
  `multiplierOverlap_dvd_laterCenteredState`: persistence, and the unconditional
  fact that `gcd(aₙ, Dₙ)` divides every later centred error.
* `slowRise_landing`: a tail state starting below the block product that rises
  by at most `B` while below `2P` lands on a block modulus, which then divides
  every later state.
* `no_slowNegative_of_coprimeBlock`: with cofinal negativity and every negative
  error below `2P + B` smaller than every block modulus, contradiction.
* `no_slowRise_reducedTail`: the reduced-tail form, generalising
  `no_boundedRise_reducedTail` from a uniform rise bound to a rise bound that is
  only required below twice the product of `B` consecutive multipliers.

No hypothesis of periodicity, bounded negative part, or stable gcd appears.
The analytic transfer (which moduli to choose on the canonical orbit, and that
`(1 - δ) log₂ log₂ Cₙ` is an admissible rise bound) is an ordinary proof in
`SlowNegativePartRigidity.md`; it is not formalised.  Nothing here settles
Erdős #243.
-/

namespace ErdosProblems.Erdos243

/-! ## The bounded CRT block -/

/-- Pairwise-coprime moduli `m₀, …, m_{k-1}` (each `> 1`) can be assigned to
consecutive integers `x, x+1, …` with the block start `x` in `[P, 2P)`, where
`P` is the product of the moduli. -/
theorem exists_consecutiveMultiples_between
    {k : ℕ}
    (m : Fin k → ℕ)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) :
    ∃ x, (∏ i, m i) ≤ x ∧ x < 2 * ∏ i, m i ∧ ∀ i : Fin k, m i ∣ x + i.1 := by
  classical
  let residue : Fin k → ℕ := fun i ↦ m i - i.1 % m i
  have hm0 : ∀ i ∈ (Finset.univ : Finset (Fin k)), m i ≠ 0 := by
    intro i _
    have := hm i
    omega
  have hpairSet : Set.Pairwise
      (↑(Finset.univ : Finset (Fin k)) : Set (Fin k))
      (fun i j ↦ Nat.Coprime (m i) (m j)) := by
    intro i _ j _ hij
    exact hpair i j hij
  let y := Nat.chineseRemainderOfFinset residue m Finset.univ hm0 hpairSet
  let P := ∏ i : Fin k, m i
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun i _ ↦ by have := hm i; omega
  let x := (y : ℕ) % P + P
  have hmodLt : (y : ℕ) % P < P := Nat.mod_lt _ hPpos
  refine ⟨x, ?_, ?_, fun i ↦ ?_⟩
  · dsimp [x, P]
    omega
  · dsimp [x, P] at hmodLt ⊢
    omega
  · have hy : (y : ℕ) ≡ residue i [MOD m i] :=
      y.property i (Finset.mem_univ i)
    have hmP : m i ∣ P := by
      dsimp [P]
      simpa using Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    have hyP : (y : ℕ) % P ≡ (y : ℕ) [MOD m i] :=
      (Nat.mod_modEq (y : ℕ) P).of_dvd hmP
    have hremLt : i.1 % m i < m i := Nat.mod_lt _ (by have := hm i; omega)
    have hresidueDvd : m i ∣ residue i + i.1 := by
      refine ⟨i.1 / m i + 1, ?_⟩
      dsimp [residue]
      calc
        m i - i.1 % m i + i.1 =
            m i - i.1 % m i + (i.1 % m i + m i * (i.1 / m i)) := by
              rw [Nat.mod_add_div]
        _ = m i + m i * (i.1 / m i) := by omega
        _ = m i * (i.1 / m i + 1) := by ring
    have hcong : (y : ℕ) % P + i.1 ≡ residue i + i.1 [MOD m i] :=
      (hyP.trans hy).add_right i.1
    have hyDvd : m i ∣ (y : ℕ) % P + i.1 :=
      Nat.modEq_zero_iff_dvd.mp
        (hcong.trans (Nat.modEq_zero_iff_dvd.mpr hresidueDvd))
    have hx : x + i.1 = ((y : ℕ) % P + i.1) + P := by
      dsimp [x]
      omega
    rw [hx]
    exact dvd_add hyDvd hmP

/-! ## Persistence of common divisors -/

/-- A common divisor of `Cₙ` and `Dₙ` divides every later `Cₜ` and `Dₜ`. -/
theorem commonDivisor_persists
    (a C D : ℕ → ℕ) (N d n : ℕ)
    (hC : ∀ k, N ≤ k → C (k + 1) + D k = a k * C k)
    (hD : ∀ k, N ≤ k → D (k + 1) = a k * D k)
    (hNn : N ≤ n)
    (hdC : d ∣ C n) (hdD : d ∣ D n) :
    ∀ t, n ≤ t → d ∣ C t ∧ d ∣ D t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ⟨hdC, hdD⟩
  | succ k hk ih =>
      obtain ⟨ihC, ihD⟩ := ih
      have hNk : N ≤ k := le_trans hNn hk
      refine ⟨?_, ?_⟩
      · have h1 : d ∣ a k * C k := dvd_mul_of_dvd_right ihC (a k)
        rw [← hC k hNk] at h1
        exact (Nat.dvd_add_iff_left ihD).mpr h1
      · rw [hD k hNk]
        exact dvd_mul_of_dvd_right ihD (a k)

/-- The overlap `gcd(aₙ, Dₙ)` of a multiplier with the accumulated denominator
state divides every strictly later `Cₜ` and `Dₜ`. -/
theorem multiplierOverlap_persists
    (a C D : ℕ → ℕ) (N n : ℕ)
    (hC : ∀ k, N ≤ k → C (k + 1) + D k = a k * C k)
    (hD : ∀ k, N ≤ k → D (k + 1) = a k * D k)
    (hNn : N ≤ n) :
    ∀ t, n < t → Nat.gcd (a n) (D n) ∣ C t ∧ Nat.gcd (a n) (D n) ∣ D t := by
  intro t ht
  apply commonDivisor_persists a C D N (Nat.gcd (a n) (D n)) (n + 1) hC hD
    (by omega) _ _ t ht
  · have h1 : Nat.gcd (a n) (D n) ∣ a n * C n :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_left (a n) (D n)) (C n)
    rw [← hC n hNn] at h1
    exact (Nat.dvd_add_iff_left (Nat.gcd_dvd_right (a n) (D n))).mpr h1
  · rw [hD n hNn]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right (a n) (D n)) (a n)

/-- A common natural divisor of `C` and `D` divides the centred state. -/
theorem dvd_centeredState_of_dvd
    (a C D d : ℕ) (hdC : d ∣ C) (hdD : d ∣ D) :
    (d : ℤ) ∣ centeredState (a : ℤ) (D : ℤ) (C : ℤ) := by
  unfold centeredState
  exact dvd_sub (Int.natCast_dvd_natCast.mpr hdD)
    (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hdC) _)

/-- Unconditional profile fact: the multiplier overlap `gcd(aₙ, Dₙ)` divides
every strictly later centred error.  On a counterexample, where the errors are
eventually nonzero, the old part of every multiplier is therefore at most the
absolute value of every later error, and in particular at most the next
negative magnitude. -/
theorem multiplierOverlap_dvd_laterCenteredState
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (N n : ℕ)
    (hC : ∀ k, N ≤ k → C (k + 1) + D k = a k * C k)
    (hD : ∀ k, N ≤ k → D (k + 1) = a k * D k)
    (hE : ∀ k, E k = centeredState (a k : ℤ) (D k : ℤ) (C k : ℤ))
    (hNn : N ≤ n) :
    ∀ t, n < t → ((Nat.gcd (a n) (D n) : ℕ) : ℤ) ∣ E t := by
  intro t ht
  obtain ⟨hCt, hDt⟩ := multiplierOverlap_persists a C D N n hC hD hNn t ht
  rw [hE t]
  exact dvd_centeredState_of_dvd (a t) (C t) (D t) _ hCt hDt

/-- A divisor of `D T` divides every later denominator state. -/
theorem dvd_denState_of_le
    (a D : ℕ → ℕ) (N d T : ℕ)
    (hD : ∀ k, N ≤ k → D (k + 1) = a k * D k)
    (hNT : N ≤ T) (hdT : d ∣ D T) :
    ∀ t, T ≤ t → d ∣ D t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hdT
  | succ k hk ih =>
      rw [hD k (le_trans hNT hk)]
      exact dvd_mul_of_dvd_right ih (a k)

/-! ## The landing theorem -/

/-- Slow-rise landing.  Let `m` be `B` pairwise-coprime moduli, each `> 1` and
each dividing `D T`, with product `P`.  If `C T < P`, if the tail state rises
by at most `B` at every index `n ≥ T` with `C n < 2P`, and if `C` tends to
infinity, then at some index `s ≥ T` the state `C (s+1) < 2P + B` is divisible
by a block modulus `m i`, which then divides every later `Cₜ` and `Dₜ`. -/
theorem slowRise_landing
    (a C D : ℕ → ℕ) (N : ℕ) {B : ℕ} (m : Fin B → ℕ) (T : ℕ)
    (hC : ∀ k, N ≤ k → C (k + 1) + D k = a k * C k)
    (hD : ∀ k, N ≤ k → D (k + 1) = a k * D k)
    (hNT : N ≤ T)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (hmD : ∀ i, m i ∣ D T)
    (hstart : C T < ∏ i, m i)
    (hrise : ∀ n, T ≤ n → C n < 2 * ∏ i, m i → C (n + 1) ≤ C n + B)
    (hCTop : Filter.Tendsto C Filter.atTop Filter.atTop) :
    ∃ s, T ≤ s ∧ C (s + 1) < 2 * (∏ i, m i) + B ∧
      ∃ i : Fin B, ∀ t, s + 1 ≤ t → m i ∣ C t ∧ m i ∣ D t := by
  classical
  obtain ⟨x, hPx, hx2P, hxDiv⟩ := exists_consecutiveMultiples_between m hm hpair
  obtain ⟨K, hK⟩ := (Filter.tendsto_atTop_atTop.mp hCTop) x
  let Q : ℕ → Prop := fun t ↦ T < t ∧ x ≤ C t
  have hQ : ∃ t, Q t := ⟨max K (T + 1), by
    refine ⟨?_, hK _ (le_max_left _ _)⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self T) (le_max_right _ _)⟩
  let t := Nat.find hQ
  have htQ : Q t := Nat.find_spec hQ
  have hTt : T < t := htQ.1
  have hxt : x ≤ C t := htQ.2
  let s := t - 1
  have hsT : T ≤ s := by dsimp [s]; omega
  have hst : s + 1 = t := by dsimp [s]; omega
  have hCs : C s < x := by
    by_contra hnot
    have hxs : x ≤ C s := by omega
    by_cases hsT' : s = T
    · rw [hsT'] at hxs
      omega
    · have hTs : T < s := lt_of_le_of_ne hsT (Ne.symm hsT')
      have hmin : t ≤ s := Nat.find_min' hQ ⟨hTs, hxs⟩
      omega
  have hCsBelow : C s < 2 * ∏ i, m i := by omega
  have hRise := hrise s hsT hCsBelow
  rw [hst] at hRise
  let r : ℕ := C t - x
  have hrB : r < B := by dsimp [r]; omega
  let i : Fin B := ⟨r, hrB⟩
  have hxr : x + i.1 = C t := by dsimp [i, r]; omega
  have hmiC : m i ∣ C t := by
    rw [← hxr]
    exact hxDiv i
  have hmiD : m i ∣ D t :=
    dvd_denState_of_le a D N (m i) T hD hNT (hmD i) t (le_of_lt hTt)
  refine ⟨s, hsT, ?_, i, ?_⟩
  · rw [hst]
    omega
  · rw [hst]
    exact commonDivisor_persists a C D N (m i) t hC hD (le_trans hNT (le_of_lt hTt))
      hmiC hmiD

/-! ## The slow-negative contradiction -/

/-- Between two indices with no negative error the tail state does not rise. -/
theorem tailState_antitone_of_nonnegative
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (N s : ℕ)
    (hC : ∀ k, N ≤ k → C (k + 1) + D k = a k * C k)
    (hE : ∀ k, E k = centeredState (a k : ℤ) (D k : ℤ) (C k : ℤ))
    (hNs : N ≤ s) :
    ∀ t, s ≤ t → (∀ j, s ≤ j → j < t → 0 ≤ E j) → C t ≤ C s := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hk ih =>
      intro hnonneg
      have hprev : C k ≤ C s := ih (fun j hj hjk ↦ hnonneg j hj (by omega))
      have hEk : 0 ≤ E k := hnonneg k hk (by omega)
      have hstep : (C (k + 1) : ℤ) = (C k : ℤ) - E k := by
        have hCk := hC k (le_trans hNs hk)
        have hCast := congrArg (fun x : ℕ ↦ (x : ℤ)) hCk
        simp only [Nat.cast_add, Nat.cast_mul] at hCast
        rw [hE k]
        simp only [centeredState]
        linarith
      have hle : (C (k + 1) : ℤ) ≤ (C k : ℤ) := by omega
      exact le_trans (by exact_mod_cast hle) hprev

/-- Slow negative part, block form.  Under the hypotheses of `slowRise_landing`,
if negative errors occur cofinally and every negative error at an index `≥ T`
with `C t < 2P + B` is smaller in absolute value than every block modulus, then
there is a contradiction.  The landing modulus divides every later error, so
the next negative error after the landing is at least that modulus. -/
theorem no_slowNegative_of_coprimeBlock
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (N : ℕ) {B : ℕ} (m : Fin B → ℕ) (T : ℕ)
    (hC : ∀ k, N ≤ k → C (k + 1) + D k = a k * C k)
    (hD : ∀ k, N ≤ k → D (k + 1) = a k * D k)
    (hE : ∀ k, E k = centeredState (a k : ℤ) (D k : ℤ) (C k : ℤ))
    (hNT : N ≤ T)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (hmD : ∀ i, m i ∣ D T)
    (hstart : C T < ∏ i, m i)
    (hrise : ∀ n, T ≤ n → C n < 2 * ∏ i, m i → C (n + 1) ≤ C n + B)
    (hCTop : Filter.Tendsto C Filter.atTop Filter.atTop)
    (hnegative : ∀ n, ∃ t, n ≤ t ∧ E t < 0)
    (hslow : ∀ t, T ≤ t → E t < 0 → C t < 2 * (∏ i, m i) + B →
      ∀ i, -E t < (m i : ℤ)) :
    False := by
  classical
  obtain ⟨s, hsT, hCs, i, hpersist⟩ :=
    slowRise_landing a C D N m T hC hD hNT hm hpair hmD hstart hrise hCTop
  let Q : ℕ → Prop := fun t ↦ s + 1 ≤ t ∧ E t < 0
  have hQ : ∃ t, Q t := hnegative (s + 1)
  let t := Nat.find hQ
  have htQ : Q t := Nat.find_spec hQ
  have hst : s + 1 ≤ t := htQ.1
  have hEt : E t < 0 := htQ.2
  have hnonneg : ∀ j, s + 1 ≤ j → j < t → 0 ≤ E j := by
    intro j hj hjt
    by_contra hneg
    have hjQ : Q j := ⟨hj, by omega⟩
    have := Nat.find_min' hQ hjQ
    omega
  have hCt : C t ≤ C (s + 1) :=
    tailState_antitone_of_nonnegative a C D E N (s + 1) hC hE (by omega) t hst hnonneg
  have hCtBelow : C t < 2 * (∏ i, m i) + B := lt_of_le_of_lt hCt hCs
  obtain ⟨hmC, hmD'⟩ := hpersist t hst
  have hdvdE : ((m i : ℕ) : ℤ) ∣ E t := by
    rw [hE t]
    exact dvd_centeredState_of_dvd (a t) (C t) (D t) (m i) hmC hmD'
  have hdvdNeg : ((m i : ℕ) : ℤ) ∣ -E t := (dvd_neg).mpr hdvdE
  have hle : ((m i : ℕ) : ℤ) ≤ -E t := Int.le_of_dvd (by omega) hdvdNeg
  have hlt := hslow t (by omega) hEt hCtBelow i
  omega

/-! ## The reduced-tail form -/

/-- Reduced-tail slow-rise exclusion.  No reduced exact tail whose numerator
tends to infinity can, for some `B > 0` and some index `T = N + B`, start
below the product `P` of the multipliers `a N, …, a (N+B-1)` and rise by at most
`B` at every index `n ≥ T` with `u n < 2P`.  This generalises
`no_boundedRise_reducedTail`: a uniform rise bound `B` gives the block
hypothesis for that `B` once `u (N+B) < P`, which holds for large `N` when the
multipliers exceed `1`. -/
theorem no_slowRise_reducedTail
    (a u v : ℕ → ℕ) (N B : ℕ)
    (ha : ∀ n, N ≤ n → 1 < a n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n)
    (hv : ∀ n, N ≤ n → v (n + 1) = a n * v n)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop)
    (hstart : u (N + B) < ∏ i : Fin B, a (N + i.1))
    (hrise : ∀ n, N + B ≤ n → u n < 2 * ∏ i : Fin B, a (N + i.1) →
      u (n + 1) ≤ u n + B) :
    False := by
  classical
  let m : Fin B → ℕ := fun i ↦ a (N + i.1)
  have hm : ∀ i, 1 < m i := fun i ↦ ha (N + i.1) (by omega)
  have hvDvd : ∀ n, N ≤ n → v n ∣ v (n + 1) := by
    intro n hn
    rw [hv n hn]
    exact dvd_mul_left (v n) (a n)
  have hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j) := by
    intro i j hij
    have hcurrent : ∀ n, N ≤ n → Nat.Coprime (a n) (v n) := by
      intro n hn
      exact reducedStep_coprime_currentFactor (hred (n + 1) (by omega)) (hu n hn) (hv n hn)
    have hlater : ∀ {p q : ℕ}, N ≤ p → p < q → a p ∣ v q := by
      intro p q hNp hpq
      have h1 : a p ∣ v (p + 1) := by
        rw [hv p hNp]
        exact dvd_mul_right (a p) (v p)
      have hchain : ∀ q, p + 1 ≤ q → a p ∣ v q := by
        intro q hq
        induction q, hq using Nat.le_induction with
        | base => exact h1
        | succ k hk ih => exact dvd_trans ih (hvDvd k (by omega))
      exact hchain q hpq
    rcases lt_or_gt_of_ne (fun h : i.1 = j.1 ↦ hij (Fin.ext h)) with hlt | hgt
    · have hdiv : a (N + i.1) ∣ v (N + j.1) := hlater (by omega) (by omega)
      exact ((hcurrent (N + j.1) (by omega)).of_dvd_right hdiv).symm
    · have hdiv : a (N + j.1) ∣ v (N + i.1) := hlater (by omega) (by omega)
      exact (hcurrent (N + i.1) (by omega)).of_dvd_right hdiv
  have hmD : ∀ i, m i ∣ v (N + B) := by
    intro i
    have h1 : a (N + i.1) ∣ v (N + i.1 + 1) := by
      rw [hv (N + i.1) (by omega)]
      exact dvd_mul_right _ _
    have hchain : ∀ q, N + i.1 + 1 ≤ q → a (N + i.1) ∣ v q := by
      intro q hq
      induction q, hq using Nat.le_induction with
      | base => exact h1
      | succ k hk ih => exact dvd_trans ih (hvDvd k (by omega))
    exact hchain (N + B) (by have := i.2; omega)
  obtain ⟨s, hsT, _, i, hpersist⟩ :=
    slowRise_landing a u v N m (N + B) hu hv (by omega) hm hpair hmD hstart hrise huTop
  obtain ⟨hmu, hmv⟩ := hpersist (s + 1) le_rfl
  have hone : m i = 1 :=
    Nat.eq_one_of_dvd_coprimes (hred (s + 1) (by omega)) hmu hmv
  have := hm i
  omega

end ErdosProblems.Erdos243
