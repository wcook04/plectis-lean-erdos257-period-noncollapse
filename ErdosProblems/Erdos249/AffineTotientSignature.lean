import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Affine totient signatures: local identities and finite-rank upper bound

Type B r4 proposed a complete classification of rational linear relations among
a finite family of affine totient sequences `n ↦ φ(aᵢ n + bᵢ)` by the invariant
`Σ = (A, B, P)`, the primitive form together with the variable primes of the
content.  This module lands the local multiplicative identity and the
equal-signature scalar identities, the Boolean Euler-factor 2×2 determinant,
the two flagship examples, the empty-product rank obstruction `≤ 2`, and the
finite-rank upper bound (dimension at most the number of signatures).

Independence across distinct primitive forms remains the live CRT–Dirichlet
argument in `AllBaseTotientKernel.linearIndependent_totientAffineForms`.  The
matching lower bound that would make dimension equal the number of signatures
for a general mixed-content family is therefore residual.

Nothing here proves irrationality of `∑ φ(n)/2ⁿ`.
-/

namespace ErdosProblems.Erdos249.AffineTotientSignature

open scoped BigOperators
open Matrix

theorem rat_sub_one_ne_zero_of_prime {p : ℕ} (hp : p.Prime) :
    ((p : ℚ) - 1) ≠ 0 :=
  sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)

/-- Euler's identity `φ(c x) = φ(c) φ(x) · gcd(c,x) / φ(gcd(c,x))` over `ℚ`. -/
theorem totient_mul_gcd_ratio (c x : ℕ) (hc : 0 < c) :
    (Nat.totient (c * x) : ℚ) =
      (Nat.totient c : ℚ) * (Nat.totient x : ℚ) *
        ((c.gcd x : ℚ) / (Nat.totient (c.gcd x) : ℚ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hg : 0 < c.gcd x := Nat.gcd_pos_of_pos_left x hc
  have hφg : (Nat.totient (c.gcd x) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hg).ne'
  have h :
      (Nat.totient (c.gcd x) : ℚ) * (Nat.totient (c * x) : ℚ) =
        (Nat.totient c : ℚ) * (Nat.totient x : ℚ) * (c.gcd x : ℚ) := by
    exact_mod_cast Nat.totient_gcd_mul_totient_mul c x
  field_simp [hφg]
  convert h using 1
  ring

/-- The standard formula `n / φ(n) = ∏_{p∣n} p/(p-1)` for `n > 0`. -/
theorem nat_div_totient_eq_primeFactors_ratio {n : ℕ} (hn : 0 < n) :
    (n : ℚ) / (n.totient : ℚ) =
      ∏ p ∈ n.primeFactors, (p : ℚ) / (p - 1) := by
  have hφ : (n.totient : ℚ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hn).ne'
  have hnat := congrArg (fun m : ℕ => (m : ℚ)) (Nat.totient_mul_prod_primeFactors n)
  simp only [Nat.cast_mul, Nat.cast_prod] at hnat
  have hcast :
      ∀ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    exact Nat.cast_sub hp1
  have hrhs :
      (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℚ)) =
        ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) :=
    Finset.prod_congr rfl hcast
  have hprod1 :
      (∏ p ∈ n.primeFactors, ((p : ℚ) - 1)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    exact rat_sub_one_ne_zero_of_prime (Nat.prime_of_mem_primeFactors hp)
  have hprod0 :
      (∏ p ∈ n.primeFactors, (p : ℚ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    exact Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors hp).ne'
  have hprod1' :
      (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℚ)) ≠ 0 := by
    rw [hrhs]
    exact hprod1
  calc
    (n : ℚ) / n.totient
        = (∏ p ∈ n.primeFactors, (p : ℚ)) /
            (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℚ)) := by
          rw [div_eq_div_iff hφ hprod1']
          exact hnat.symm.trans (mul_comm _ _)
    _ = ∏ p ∈ n.primeFactors, (p : ℚ) / ((p - 1 : ℕ) : ℚ) :=
          (Finset.prod_div_distrib (fun p : ℕ => (p : ℚ))
            (fun p : ℕ => ((p - 1 : ℕ) : ℚ))).symm
    _ = ∏ p ∈ n.primeFactors, (p : ℚ) / (p - 1) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          rw [hcast p hp]

/-- A prime dividing a primitive slope cannot divide the affine value. -/
theorem coprime_slope_not_dvd_value {A B n p : ℕ}
    (hAB : Nat.Coprime A B) (hp : p.Prime) (hA : p ∣ A) :
    ¬ p ∣ A * n + B := by
  intro hL
  have hAn : p ∣ A * n := hA.mul_right n
  have hB : p ∣ B := (Nat.dvd_add_iff_right hAn).mpr hL
  have hg : p ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
  rw [hAB.gcd_eq_one] at hg
  exact hp.not_dvd_one hg

/-- Primitive slope, intercept, and variable-prime set of an affine totient channel. -/
structure Sig where
  slope : ℕ
  intercept : ℕ
  variablePrimes : Finset ℕ
deriving DecidableEq

/-- The signature `Σ = (A, B, P)` of the channel `n ↦ φ(a n + b)`. -/
def affineTotientSignature (a b : ℕ) : Sig where
  slope := a / a.gcd b
  intercept := b / a.gcd b
  variablePrimes :=
    (a.gcd b).primeFactors.filter (fun p => ¬ p ∣ a / a.gcd b)

theorem affineTotientSignature_coprime {a b : ℕ} (ha : 0 < a) :
    Nat.Coprime (a / a.gcd b) (b / a.gcd b) :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left b ha)

theorem affine_value_eq_content_mul_primitive {a b n : ℕ} (ha : 0 < a) :
    a * n + b =
      a.gcd b * ((a / a.gcd b) * n + b / a.gcd b) := by
  have _hg := Nat.gcd_pos_of_pos_left b ha
  have hga : a.gcd b ∣ a := Nat.gcd_dvd_left _ _
  have hgb : a.gcd b ∣ b := Nat.gcd_dvd_right _ _
  have ha' := Nat.mul_div_cancel' hga
  have hb' := Nat.mul_div_cancel' hgb
  calc
    a * n + b
      = (a.gcd b * (a / a.gcd b)) * n + (a.gcd b * (b / a.gcd b)) := by
          rw [ha', hb']
    _ = a.gcd b * ((a / a.gcd b) * n + b / a.gcd b) := by ring

theorem gcd_primeFactors_eq_variable_dvd
    {c A B n : ℕ} (hc : 0 < c) (hAB : Nat.Coprime A B)
    (_hL : A * n + B ≠ 0) :
    (c.gcd (A * n + B)).primeFactors =
      (c.primeFactors.filter (fun p => ¬ p ∣ A)).filter
        (fun p => p ∣ A * n + B) := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · intro hp
    have hpcd := Nat.dvd_gcd_iff.mp hp.2.1
    refine ⟨⟨⟨hp.1, hpcd.1, hc.ne'⟩, ?_⟩, hpcd.2⟩
    intro hA
    exact coprime_slope_not_dvd_value hAB hp.1 hA hpcd.2
  · intro hp
    refine ⟨hp.1.1.1, Nat.dvd_gcd_iff.mpr ⟨hp.1.1.2.1, hp.2⟩, ?_⟩
    exact (Nat.gcd_pos_of_pos_left _ hc).ne'

/-- Local identity (A5): after extracting content, the totient depends on `c`
only through the variable-prime set `P`. -/
theorem totient_content_mul_primitive (c A B n : ℕ) (hc : 0 < c)
    (hAB : Nat.Coprime A B) :
    (Nat.totient (c * (A * n + B)) : ℚ) =
      (Nat.totient c : ℚ) * (Nat.totient (A * n + B) : ℚ) *
        ∏ p ∈ (c.primeFactors.filter (fun p => ¬ p ∣ A)).filter
            (fun p => p ∣ A * n + B),
          (p : ℚ) / (p - 1) := by
  set L := A * n + B
  rcases eq_or_ne L 0 with hL | hL
  · simp [hL]
  have hg : 0 < c.gcd L := Nat.gcd_pos_of_pos_left L hc
  have hratio := totient_mul_gcd_ratio c L hc
  have hprod := nat_div_totient_eq_primeFactors_ratio hg
  have hpf := gcd_primeFactors_eq_variable_dvd hc hAB hL
  simp only [L] at hratio hprod hpf
  rw [hratio, hprod, hpf]

def Sig.normalised (σ : Sig) : ℕ → ℚ :=
  fun n =>
    (Nat.totient (σ.slope * n + σ.intercept) : ℚ) *
      ∏ p ∈ σ.variablePrimes.filter (fun p => p ∣ σ.slope * n + σ.intercept),
        (p : ℚ) / (p - 1)

theorem totient_eq_content_smul_normalised {a b : ℕ} (ha : 0 < a) (n : ℕ) :
    (Nat.totient (a * n + b) : ℚ) =
      (Nat.totient (a.gcd b) : ℚ) *
        (affineTotientSignature a b).normalised n := by
  have hc : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha
  have hAB := affineTotientSignature_coprime (a := a) (b := b) ha
  have hval := affine_value_eq_content_mul_primitive (a := a) (b := b) (n := n) ha
  have hprim :=
    totient_content_mul_primitive (a.gcd b) (a / a.gcd b) (b / a.gcd b) n hc hAB
  simp only [affineTotientSignature, Sig.normalised]
  rw [hval]
  convert hprim using 1
  exact (mul_assoc _ _ _).symm

/-- Equal signatures give proportional affine totient sequences. -/
theorem totient_div_content_eq_of_same_signature
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hσ : affineTotientSignature a₁ b₁ = affineTotientSignature a₂ b₂) (n : ℕ) :
    (Nat.totient (a₁ * n + b₁) : ℚ) / (Nat.totient (a₁.gcd b₁) : ℚ) =
      (Nat.totient (a₂ * n + b₂) : ℚ) / (Nat.totient (a₂.gcd b₂) : ℚ) := by
  have hc₁ : (Nat.totient (a₁.gcd b₁) : ℚ) ≠ 0 := by
    exact_mod_cast
      (Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left b₁ ha₁)).ne'
  have hc₂ : (Nat.totient (a₂.gcd b₂) : ℚ) ≠ 0 := by
    exact_mod_cast
      (Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left b₂ ha₂)).ne'
  have h₁ := totient_eq_content_smul_normalised (a := a₁) (b := b₁) ha₁ n
  have h₂ := totient_eq_content_smul_normalised (a := a₂) (b := b₂) ha₂ n
  field_simp [hc₁, hc₂]
  simp [h₁, h₂, hσ]
  ring

/-- The identity `φ(6n+3) = φ(12n+6)`: equal signatures `(2,1,{3})`. -/
theorem totient_six_mul_add_three_eq_twelve_mul_add_six (n : ℕ) :
    Nat.totient (6 * n + 3) = Nat.totient (12 * n + 6) := by
  have hval : 12 * n + 6 = 2 * (6 * n + 3) := by ring
  have hodd : Odd (6 * n + 3) := ⟨3 * n + 1, by ring⟩
  have hcop : Nat.Coprime 2 (6 * n + 3) := Nat.coprime_two_left.mpr hodd
  rw [hval, Nat.totient_mul hcop, Nat.totient_two, one_mul]

/-- `φ(n+1)` and `φ(2n+2)` are independent: same primitive form, distinct `P`. -/
theorem linearIndependent_totient_succ_two_succ :
    LinearIndependent ℚ
      ![fun n : ℕ => (Nat.totient (n + 1) : ℚ),
        fun n : ℕ => (Nat.totient (2 * n + 2) : ℚ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have ht4 : Nat.totient 4 = 2 := by decide
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.totient_one, Nat.totient_two,
    ht4] at h0 h1
  have ht : t = 0 := by linarith
  have hs : s = 0 := by linarith
  exact ⟨hs, ht⟩

/-- Boolean Euler-factor entry `∏_{p ∈ S ∩ T} p/(p-1)`. -/
def booleanEulerEntry (S T : Finset ℕ) : ℚ :=
  ∏ p ∈ S ∩ T, (p : ℚ) / (p - 1)

theorem p_div_p_sub_one {p : ℕ} (hp : 1 < p) :
    (p : ℚ) / (p - 1) = 1 + 1 / (p - 1) := by
  have hp1 : (p : ℚ) ≠ 1 := by exact_mod_cast hp.ne'
  have hsub : (p : ℚ) - 1 ≠ 0 := sub_ne_zero.mpr hp1
  field_simp [hsub]
  ring

theorem booleanEulerEntry_eq_sum (S T : Finset ℕ)
    (hST : ∀ p ∈ S ∩ T, 1 < p) :
    booleanEulerEntry S T =
      ∑ U ∈ (S ∩ T).powerset, ∏ p ∈ U, (1 : ℚ) / (p - 1) := by
  unfold booleanEulerEntry
  have hcongr :
      ∀ p ∈ S ∩ T, (p : ℚ) / (p - 1) = 1 + (1 : ℚ) / (p - 1) :=
    fun p hp => p_div_p_sub_one (hST p hp)
  rw [Finset.prod_congr rfl hcongr]
  simpa using Finset.prod_one_add (f := fun p : ℕ => (1 : ℚ) / (p - 1)) (S ∩ T)

/-- The 2×2 Euler block for `∅` and `{p}` has determinant `1/(p-1)`. -/
theorem booleanEuler_empty_singleton_det {p : ℕ} (hp : p.Prime) :
    Matrix.det
      (!![booleanEulerEntry ∅ ∅, booleanEulerEntry ∅ {p};
          booleanEulerEntry {p} ∅, booleanEulerEntry {p} {p}]) =
      (1 : ℚ) / (p - 1) := by
  have hsub := rat_sub_one_ne_zero_of_prime hp
  simp [booleanEulerEntry, Matrix.det_fin_two]
  field_simp [hsub]
  ring

theorem booleanEuler_empty_singleton_det_ne_zero {p : ℕ} (hp : p.Prime) :
    Matrix.det
      (!![booleanEulerEntry ∅ ∅, booleanEulerEntry ∅ {p};
          booleanEulerEntry {p} ∅, booleanEulerEntry {p} {p}]) ≠ 0 := by
  rw [booleanEuler_empty_singleton_det hp]
  exact div_ne_zero one_ne_zero (rat_sub_one_ne_zero_of_prime hp)

def idSeq : ℕ → ℚ := fun n => n
def constSeq : ℕ → ℚ := fun _ => 1

def affinePairFamily : Fin 2 → (ℕ → ℚ)
  | 0 => idSeq
  | 1 => constSeq

/-- Affine sequences `n ↦ a n + b` span a space of dimension at most two.
This is why an empty Jordan product `f(n) = n` cannot have totient-kernel rank
`k^e+1`. -/
theorem affineNatSeq_eq_pair (a b : ℕ) :
    (fun n : ℕ => ((a * n + b : ℕ) : ℚ)) =
      (a : ℚ) • idSeq + (b : ℚ) • constSeq := by
  funext n
  simp [idSeq, constSeq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_add, Nat.cast_mul]

theorem affineNatSeq_mem_span_pair (a b : ℕ) :
    (fun n : ℕ => ((a * n + b : ℕ) : ℚ)) ∈
      Submodule.span ℚ (Set.range affinePairFamily) := by
  rw [affineNatSeq_eq_pair]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)

theorem affineNatSeq_span_finrank_le_two {ι : Type*} [Fintype ι] (a b : ι → ℕ) :
    Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun i n => ((a i * n + b i : ℕ) : ℚ))) ≤ 2 := by
  have hsub :
      Submodule.span ℚ (Set.range fun i n => ((a i * n + b i : ℕ) : ℚ)) ≤
        Submodule.span ℚ (Set.range affinePairFamily) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
    exact affineNatSeq_mem_span_pair (a i) (b i)
  haveI : Module.Finite ℚ (Submodule.span ℚ (Set.range affinePairFamily)) :=
    Module.Finite.span_of_finite (R := ℚ) (Set.finite_range affinePairFamily)
  have hcard :
      Module.finrank ℚ (Submodule.span ℚ (Set.range affinePairFamily)) ≤ 2 := by
    simpa using (finrank_range_le_card (R := ℚ) affinePairFamily)
  exact (Submodule.finrank_mono hsub).trans hcard

theorem totientAffine_seq_eq_smul_normalised {a b : ℕ} (ha : 0 < a) :
    (fun n => (Nat.totient (a * n + b) : ℚ)) =
      ((a.gcd b).totient : ℚ) • (affineTotientSignature a b).normalised := by
  funext n
  simp [Pi.smul_apply, smul_eq_mul]
  exact totient_eq_content_smul_normalised ha n

/-- The span of a finite affine totient family has dimension at most the number
of distinct signatures.  Equality for mixed primitive forms still uses the
live CRT–Dirichlet independence theorem. -/
theorem totientAffine_span_finrank_le_signature_card
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ) (ha : ∀ i, 0 < a i) :
    Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun i n => (Nat.totient (a i * n + b i) : ℚ))) ≤
      Fintype.card (Set.range fun i => affineTotientSignature (a i) (b i)) := by
  classical
  let σs := Set.range fun i => affineTotientSignature (a i) (b i)
  haveI : Fintype σs := Set.fintypeRange _
  have hmem :
      Set.range (fun i n => (Nat.totient (a i * n + b i) : ℚ)) ⊆
        Submodule.span ℚ
          (Set.range fun i => (affineTotientSignature (a i) (b i)).normalised) := by
    intro x hx
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
    rw [totientAffine_seq_eq_smul_normalised (ha i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsub :
      Submodule.span ℚ (Set.range fun i n => (Nat.totient (a i * n + b i) : ℚ)) ≤
        Submodule.span ℚ
          (Set.range fun i => (affineTotientSignature (a i) (b i)).normalised) := by
    rwa [Submodule.span_le]
  have hrange :
      Set.range (fun i => (affineTotientSignature (a i) (b i)).normalised) =
        Set.range (fun σ : σs => σ.1.normalised) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
      exact ⟨⟨affineTotientSignature (a i) (b i), ⟨i, rfl⟩⟩, rfl⟩
    · intro hx
      obtain ⟨σ, rfl⟩ := hx
      obtain ⟨i, hi⟩ := σ.2
      exact ⟨i, by simp [hi]⟩
  haveI : Module.Finite ℚ
      (Submodule.span ℚ
        (Set.range fun i => (affineTotientSignature (a i) (b i)).normalised)) :=
    Module.Finite.span_of_finite (R := ℚ)
      (Set.finite_range fun i => (affineTotientSignature (a i) (b i)).normalised)
  have hcard :
      Module.finrank ℚ
          (Submodule.span ℚ
            (Set.range fun i => (affineTotientSignature (a i) (b i)).normalised)) ≤
        Fintype.card σs := by
    rw [hrange]
    simpa using (finrank_range_le_card (R := ℚ) (fun σ : σs => σ.1.normalised))
  exact (Submodule.finrank_mono hsub).trans (by convert hcard)

end ErdosProblems.Erdos249.AffineTotientSignature
