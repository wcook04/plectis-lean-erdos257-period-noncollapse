import ErdosProblems.Erdos243.ReciprocalTailRigidity

open scoped BigOperators

/-!
# Erdős 243: exact dynamic cancellation

This module isolates the primitive arithmetic of one or two dynamically
reduced reciprocal-tail steps.  It strengthens the cancellation sandwich in
`ReciprocalTailRigidity` and records exact falsifiers for purely local descent
arguments.  It does not claim termination of the unrestricted orbit.
-/

namespace ErdosProblems.Erdos243

/-- The raw next numerator is coprime to the current reduced numerator. -/
theorem rawNext_coprime_currentNumerator
    {a u v q : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : q + v = a * u) :
    Nat.Coprime u q := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  apply Nat.dvd_one.mp
  have hgu : Nat.gcd u q ∣ u := Nat.gcd_dvd_left u q
  have hgq : Nat.gcd u q ∣ q := Nat.gcd_dvd_right u q
  have hgsum : Nat.gcd u q ∣ q + v := by
    rw [hq]
    exact dvd_mul_of_dvd_right hgu a
  have hgv : Nat.gcd u q ∣ v :=
    (Nat.dvd_add_iff_right hgq).mpr hgsum
  simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hgu hgv

/-- For a primitive input pair, the content removed from the raw next pair is
controlled exactly by the square of the current multiplier. -/
theorem rawNext_gcd_eq_gcd_sq
    {a u v q : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : q + v = a * u) :
    Nat.gcd q (a * v) = Nat.gcd q (a ^ 2) := by
  have hqu : Nat.Coprime q u :=
    (rawNext_coprime_currentNumerator hcop hq).symm
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left q (a * v))
    let d := Nat.gcd q (a * v)
    have hdq : d ∣ q := Nat.gcd_dvd_left q (a * v)
    have hdav : d ∣ a * v := Nat.gcd_dvd_right q (a * v)
    have hdaqu : d ∣ a * q := dvd_mul_of_dvd_right hdq a
    have hdsum : d ∣ a * v + a * q := Nat.dvd_add hdav hdaqu
    have hdsqMul : d ∣ a ^ 2 * u := by
      calc
        d ∣ a * v + a * q := hdsum
        _ = a ^ 2 * u := by rw [← Nat.mul_add, Nat.add_comm v q, hq]; ring
    have hdu : Nat.Coprime d u :=
      hqu.of_dvd_left (Nat.gcd_dvd_left q (a * v))
    exact hdu.dvd_mul_right.mp hdsqMul
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left q (a ^ 2))
    let d := Nat.gcd q (a ^ 2)
    have hdq : d ∣ q := Nat.gcd_dvd_left q (a ^ 2)
    have hdsq : d ∣ a ^ 2 := Nat.gcd_dvd_right q (a ^ 2)
    have hdaqu : d ∣ a * q := dvd_mul_of_dvd_right hdq a
    have hdsum : d ∣ a * q + a * v := by
      calc
        d ∣ a ^ 2 * u := dvd_mul_of_dvd_left hdsq u
        _ = a * q + a * v := by rw [← Nat.mul_add, hq]; ring
    exact (Nat.dvd_add_iff_right hdaqu).mpr hdsum

/-- Quotient-level overlap formula for the removed content.  The first copy
of `d = gcd(a,v)` is forced, while the second copy is precisely the overlap
between `d` and the residual raw numerator `q/d`. -/
theorem rawNext_gcd_exact_overlap
    {a u v q : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : q + v = a * u) :
    let d := Nat.gcd a v
    Nat.gcd q (a * v) = d * Nat.gcd (q / d) d := by
  let d := Nat.gcd a v
  change Nat.gcd q (a * v) = d * Nat.gcd (q / d) d
  have hdA : d ∣ a := by
    dsimp [d]
    exact Nat.gcd_dvd_left a v
  have hdV : d ∣ v := by
    dsimp [d]
    exact Nat.gcd_dvd_right a v
  have hdSum : d ∣ q + v := by
    rw [hq]
    exact dvd_mul_of_dvd_left hdA u
  have hdQ : d ∣ q := (Nat.dvd_add_iff_left hdV).mpr hdSum
  have hdaq : Nat.gcd a q = d := by
    apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd (Nat.gcd_dvd_left a q)
      let k := Nat.gcd a q
      have hkA : k ∣ a := Nat.gcd_dvd_left a q
      have hkQ : k ∣ q := Nat.gcd_dvd_right a q
      have hkSum : k ∣ q + v := by
        rw [hq]
        exact dvd_mul_of_dvd_left hkA u
      exact (Nat.dvd_add_iff_right hkQ).mpr hkSum
    · exact Nat.dvd_gcd hdA hdQ
  by_cases hdZero : d = 0
  · have haZero : a = 0 := by simpa [hdZero] using hdA
    have hqZero : q = 0 := by simpa [hdZero] using hdQ
    simp [haZero, hqZero, hdZero]
  · have hdPos : 0 < d := Nat.pos_of_ne_zero hdZero
    let A := a / d
    let Q := q / d
    change Nat.gcd q (a * v) = d * Nat.gcd Q d
    have haEq : a = d * A := (Nat.mul_div_cancel' hdA).symm
    have hqEq : q = d * Q := (Nat.mul_div_cancel' hdQ).symm
    have hred : Nat.Coprime A Q := by
      dsimp [A, Q]
      have hgPos : 0 < Nat.gcd a q := by simpa [hdaq] using hdPos
      have h : Nat.Coprime (a / Nat.gcd a q) (q / Nat.gcd a q) :=
        Nat.coprime_div_gcd_div_gcd hgPos
      simpa [hdaq] using h
    have hgcdReduced : Nat.gcd Q (d * A ^ 2) = Nat.gcd Q d := by
      apply Nat.dvd_antisymm
      · apply Nat.dvd_gcd (Nat.gcd_dvd_left Q (d * A ^ 2))
        let k := Nat.gcd Q (d * A ^ 2)
        have hkQ : k ∣ Q := Nat.gcd_dvd_left Q (d * A ^ 2)
        have hkProd : k ∣ d * A ^ 2 := Nat.gcd_dvd_right Q (d * A ^ 2)
        have hkCop : Nat.Coprime k (A ^ 2) :=
          ((hred.pow_left 2).of_dvd_right hkQ).symm
        exact hkCop.dvd_mul_right.mp hkProd
      · apply Nat.dvd_gcd (Nat.gcd_dvd_left Q d)
        exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right Q d) (A ^ 2)
    rw [rawNext_gcd_eq_gcd_sq hcop hq]
    calc
      Nat.gcd q (a ^ 2) = Nat.gcd (d * Q) ((d * A) ^ 2) := by rw [hqEq, haEq]
      _ = d * Nat.gcd Q (d * A ^ 2) := by
        rw [show (d * A) ^ 2 = d * (d * A ^ 2) by ring,
          Nat.gcd_mul_left]
      _ = d * Nat.gcd Q d := by rw [hgcdReduced]

/-- The algebraic heart of the square-overlap normal form.  Once common
content `d` has been factored from both the multiplier and raw numerator,
coprimality of their primitive parts leaves only the overlap of `ω` with
`d` available for a second copy in the square. -/
theorem gcd_scaled_square_eq
    {d α ω c : ℕ}
    (hαω : Nat.Coprime α ω)
    (hc : c = Nat.gcd ω d) :
    Nat.gcd (d * ω) ((d * α) ^ 2) = d * c := by
  have hgcdReduced : Nat.gcd ω (d * α ^ 2) = Nat.gcd ω d := by
    apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd (Nat.gcd_dvd_left ω (d * α ^ 2))
      let k := Nat.gcd ω (d * α ^ 2)
      have hkω : k ∣ ω := Nat.gcd_dvd_left ω (d * α ^ 2)
      have hkProd : k ∣ d * α ^ 2 := Nat.gcd_dvd_right ω (d * α ^ 2)
      have hkCop : Nat.Coprime k (α ^ 2) :=
        ((hαω.pow_left 2).of_dvd_right hkω).symm
      exact hkCop.dvd_mul_right.mp hkProd
    · apply Nat.dvd_gcd (Nat.gcd_dvd_left ω d)
      exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right ω d) (α ^ 2)
  rw [show (d * α) ^ 2 = d * (d * α ^ 2) by ring, Nat.gcd_mul_left,
    hgcdReduced, ← hc]

/-- Explicit-factor version of the exact square-cancellation normal form.
It deliberately separates quotient bookkeeping from its reusable algebraic
core: if `d = b*c`, then the removed content is `b*c^2`, and the overlap
factor `c` is coprime to the surviving primitive multiplier `α`. -/
theorem cancellationOverlap_normalForm_explicit
    {a w h d α ω c b : ℕ}
    (ha : a = d * α)
    (hw : w = d * ω)
    (hαω : Nat.Coprime α ω)
    (hc : c = Nat.gcd ω d)
    (hd : d = b * c)
    (hh : h = Nat.gcd w (a ^ 2)) :
    h = b * c ^ 2 ∧ a = b * c * α ∧ Nat.Coprime c α := by
  have hcontent : h = d * c := by
    rw [hh, hw, ha]
    exact gcd_scaled_square_eq hαω hc
  constructor
  · rw [hcontent, hd]
    ring
  constructor
  · rw [ha, hd]
  · have hcω : c ∣ ω := by
      rw [hc]
      exact Nat.gcd_dvd_left ω d
    exact (hαω.of_dvd_right hcω).symm

/-- Transport of the reduced denominator through the exact overlap factors.
When `h=d*c`, the overlap factor is deleted and only the primitive multiplier
`α` survives. -/
theorem cancellation_denominator_transport_explicit
    {a h v vNext d α c t : ℕ}
    (hdPos : 0 < d)
    (hcPos : 0 < c)
    (ha : a = d * α)
    (hh : h = d * c)
    (hv : v = c * t)
    (hstep : h * vNext = a * v) :
    vNext = α * (v / c) := by
  have hcancelD : c * vNext = α * (c * t) := by
    apply Nat.eq_of_mul_eq_mul_left hdPos
    calc
      d * (c * vNext) = (d * c) * vNext := by ring
      _ = h * vNext := by rw [← hh]
      _ = a * v := hstep
      _ = (d * α) * (c * t) := by rw [ha, hv]
      _ = d * (α * (c * t)) := by ring
  have hvNext : vNext = α * t := by
    apply Nat.eq_of_mul_eq_mul_left hcPos
    calc
      c * vNext = α * (c * t) := hcancelD
      _ = c * (α * t) := by ring
  have hquot : v / c = t := by
    rw [hv, Nat.mul_div_cancel_left t hcPos]
  rw [hquot, hvNext]

/-- The overlap factor is exactly the part deleted from the old primitive
denominator. -/
theorem deletedFactor_eq_oldDenominator_div_gcd
    {c α t v vNext : ℕ}
    (htPos : 0 < t)
    (hcop : Nat.Coprime c α)
    (hv : v = c * t)
    (hvNext : vNext = α * t) :
    c = v / Nat.gcd v vNext := by
  rw [hv, hvNext, Nat.gcd_mul_right, hcop.gcd_eq_one, Nat.one_mul,
    Nat.mul_div_left c htPos]

/-- Equivalent lcm form of exact denominator deletion: the lcm of the
current multiplier and reduced denominator is the overlap factor times the
next reduced denominator. -/
theorem lcm_eq_overlap_mul_nextDenominator
    {a v vNext d α c t : ℕ}
    (hdPos : 0 < d)
    (hd : d = Nat.gcd a v)
    (ha : a = d * α)
    (hv : v = c * t)
    (hvNext : vNext = α * t) :
    Nat.lcm a v = c * vNext := by
  apply Nat.eq_of_mul_eq_mul_left hdPos
  calc
    d * Nat.lcm a v = Nat.gcd a v * Nat.lcm a v := by rw [hd]
    _ = a * v := Nat.gcd_mul_lcm a v
    _ = (d * α) * (c * t) := by rw [ha, hv]
    _ = d * (c * (α * t)) := by ring
    _ = d * (c * vNext) := by rw [hvNext]

/-- Dividing a primitive raw next pair by its full common content leaves
consecutive reduced numerators coprime. -/
theorem reducedStep_consecutiveNumerator_coprime
    {a u v q h uNext : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : q + v = a * u)
    (hqu : q = h * uNext) :
    Nat.Coprime u uNext := by
  have huq : Nat.Coprime u q := rawNext_coprime_currentNumerator hcop hq
  exact huq.of_dvd_right ⟨h, by simpa [Nat.mul_comm] using hqu⟩

/-- If `h` is the full common content removed from the raw next pair, then it
is exactly `gcd q (a^2)`. -/
theorem reducedStep_cancellationFactor_eq_square
    {a u v q h uNext vNext : ℕ}
    (hcop : Nat.Coprime u v)
    (hcopNext : Nat.Coprime uNext vNext)
    (hq : q + v = a * u)
    (hqu : q = h * uNext)
    (hav : a * v = h * vNext) :
    h = Nat.gcd q (a ^ 2) := by
  have hraw : Nat.gcd q (a * v) = h := by
    rw [hqu, hav, Nat.gcd_mul_left, hcopNext.gcd_eq_one, Nat.mul_one]
  rw [← rawNext_gcd_eq_gcd_sq hcop hq, hraw]

/-- Two consecutive dynamically reduced steps satisfy an exact non-autonomous
second-order recurrence for their primitive numerators. -/
theorem reducedStep_secondOrder
    {a aNext u uNext uNextNext v vNext h hNext : ℕ}
    (hu : h * uNext + v = a * u)
    (hv : h * vNext = a * v)
    (huNext : hNext * uNextNext + vNext = aNext * uNext) :
    a ^ 2 * u + h * hNext * uNextNext =
      h * (a + aNext) * uNext := by
  calc
    a ^ 2 * u + h * hNext * uNextNext =
        a * (h * uNext + v) + h * hNext * uNextNext := by
          rw [hu]
          ring
    _ = a * h * uNext + h * vNext + h * hNext * uNextNext := by
      rw [hv]
      ring
    _ = a * h * uNext + h * (hNext * uNextNext + vNext) := by ring
    _ = a * h * uNext + h * (aNext * uNext) := by rw [huNext]
    _ = h * (a + aNext) * uNext := by ring

/-- On a cancellation-free step, the centered error satisfies the dual
nearest-remainder identity.  This integer form avoids all sign side
conditions and exposes the changing modulus used by the anti-shadowing
problem. -/
theorem cancellationFree_dualRemainder
    {a Δ p pNext e eNext s : ℤ}
    (hpNext : pNext = p - e)
    (hdefect : Δ * pNext = a ^ 2 * e - eNext)
    (hs : s = a ^ 2 - 1 + Δ) :
    s * e - Δ * p = eNext - e := by
  calc
    s * e - Δ * p =
        (a ^ 2 * e - eNext) - Δ * pNext + (eNext - e) := by
          rw [hs, hpNext]
          ring
    _ = eNext - e := by rw [← hdefect]; ring

/-- Exact square/curvature identity on a cancellation-free pair of steps.
It packages the primitive second-order cocycle as a changing quadratic norm,
without asserting the still-open global anti-shadowing conclusion. -/
theorem cancellationFree_curvature_square
    {a aNext p pNext pNextNext q : ℤ}
    (hq : q = a * p - pNext)
    (hrec : pNextNext + a ^ 2 * p = (a + aNext) * pNext) :
    q ^ 2 + (p * pNextNext - pNext ^ 2) =
      (aNext - a) * p * pNext := by
  rw [hq]
  calc
    (a * p - pNext) ^ 2 + (p * pNextNext - pNext ^ 2) =
        p * (pNextNext + a ^ 2 * p - 2 * a * pNext) := by ring
    _ = (aNext - a) * p * pNext := by rw [hrec]; ring

/-- The centered-state transfer matrix attached to an excursion has square
determinant.  The theorem is stated as its scalar algebraic interface so that
later block producers can choose their preferred matrix representation. -/
theorem excursionMatrix_det_square
    {A B aStart aStop K α β : ℤ}
    (hK : K = A - (aStart - 1) * B)
    (hα : α = A + (aStop - 1) * B)
    (hβ : β = A * (aStart - 1) - (aStop - 1) * K) :
    α * K + β * B = A ^ 2 := by
  rw [hα, hβ, hK]
  ring

/-- Primitive matrix gcd lemma.  If both the input vector and the second
matrix row are primitive, then the common content of the output is exactly
the gcd of the determinant with the second output coordinate.  This is the
generic arithmetic consumer behind the exact block-cancellation payment. -/
theorem primitiveMatrix_gcd_eq_det_gcd
    {p q r s x y : ℤ}
    (hrow : Int.gcd r s = 1)
    (hinput : Int.gcd x y = 1) :
    Int.gcd (p * x + q * y) (r * x + s * y) =
      Int.gcd (p * s - q * r) (r * x + s * y) := by
  let U := p * x + q * y
  let V := r * x + s * y
  let det := p * s - q * r
  change Int.gcd U V = Int.gcd det V
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd
    · have hdU : (Int.gcd U V : ℤ) ∣ U := Int.gcd_dvd_left U V
      have hdV : (Int.gcd U V : ℤ) ∣ V := Int.gcd_dvd_right U V
      have hdDetX : (Int.gcd U V : ℤ) ∣ det * x := by
        have hlin : s * U - q * V = det * x := by
          dsimp [U, V, det]
          ring
        rw [← hlin]
        exact Int.dvd_sub (dvd_mul_of_dvd_right hdU s)
          (dvd_mul_of_dvd_right hdV q)
      have hdDetY : (Int.gcd U V : ℤ) ∣ det * y := by
        have hlin : p * V - r * U = det * y := by
          dsimp [U, V, det]
          ring
        rw [← hlin]
        exact Int.dvd_sub (dvd_mul_of_dvd_right hdV p)
          (dvd_mul_of_dvd_right hdU r)
      have hone : Int.gcd x y ∣ 1 := by rw [hinput]
      rcases Int.gcd_dvd_iff.mp hone with ⟨X, Y, hbez⟩
      calc
        (Int.gcd U V : ℤ) ∣ (det * x) * X + (det * y) * Y :=
          Int.dvd_add (dvd_mul_of_dvd_left hdDetX X)
            (dvd_mul_of_dvd_left hdDetY Y)
        _ = det * (x * X + y * Y) := by ring
        _ = det := by rw [← hbez]; ring
    · exact Int.gcd_dvd_right U V
  · apply Int.dvd_gcd
    · have hdDet : (Int.gcd det V : ℤ) ∣ det := Int.gcd_dvd_left det V
      have hdV : (Int.gcd det V : ℤ) ∣ V := Int.gcd_dvd_right det V
      have hdSX : (Int.gcd det V : ℤ) ∣ s * U := by
        have hlin : s * U = det * x + q * V := by
          dsimp [U, V, det]
          ring
        rw [hlin]
        exact Int.dvd_add (dvd_mul_of_dvd_left hdDet x)
          (dvd_mul_of_dvd_right hdV q)
      have hdRU : (Int.gcd det V : ℤ) ∣ r * U := by
        have hlin : r * U = p * V - det * y := by
          dsimp [U, V, det]
          ring
        rw [hlin]
        exact Int.dvd_sub (dvd_mul_of_dvd_right hdV p)
          (dvd_mul_of_dvd_left hdDet y)
      have hone : Int.gcd r s ∣ 1 := by rw [hrow]
      rcases Int.gcd_dvd_iff.mp hone with ⟨R, S, hbez⟩
      calc
        (Int.gcd det V : ℤ) ∣ (r * U) * R + (s * U) * S :=
          Int.dvd_add (dvd_mul_of_dvd_left hdRU R)
            (dvd_mul_of_dvd_left hdSX S)
        _ = U * (r * R + s * S) := by ring
        _ = U := by rw [← hbez]; ring
    · exact Int.gcd_dvd_right det V

/-- Exact cancellation payment for a normalized excursion block.  After the
common matrix content `σ` is removed, primitivity of the second row and of
both endpoint states turns the transfer scale into the square-determinant gcd
predicted by `primitiveMatrix_gcd_eq_det_gcd`.  The signed coordinate
`K0 * u - B0 * e` is the reduced terminal tail state. -/
theorem blockCancellationPayment_explicit
    {σ : ℕ} {Λ A0 B0 K0 α0 β0 e u eStop uStop : ℤ}
    (hinput : Int.gcd e u = 1)
    (houtput : Int.gcd eStop uStop = 1)
    (hrow : Int.gcd (-B0) K0 = 1)
    (hdet : α0 * K0 + β0 * B0 = A0 ^ 2)
    (he : Λ * eStop = (σ : ℤ) * (α0 * e + β0 * u))
    (hu : Λ * uStop = (σ : ℤ) * ((-B0) * e + K0 * u)) :
    Λ.natAbs = σ * Int.gcd (A0 ^ 2) (K0 * u - B0 * e) := by
  have hdet' : α0 * K0 - β0 * (-B0) = A0 ^ 2 := by
    calc
      α0 * K0 - β0 * (-B0) = α0 * K0 + β0 * B0 := by ring
      _ = A0 ^ 2 := hdet
  have hmatrix :
      Int.gcd (α0 * e + β0 * u) ((-B0) * e + K0 * u) =
        Int.gcd (A0 ^ 2) ((-B0) * e + K0 * u) := by
    calc
      Int.gcd (α0 * e + β0 * u) ((-B0) * e + K0 * u) =
          Int.gcd (α0 * K0 - β0 * (-B0)) ((-B0) * e + K0 * u) :=
        primitiveMatrix_gcd_eq_det_gcd hrow hinput
      _ = Int.gcd (A0 ^ 2) ((-B0) * e + K0 * u) := by rw [hdet']
  calc
    Λ.natAbs = Int.gcd (Λ * eStop) (Λ * uStop) := by
      rw [Int.gcd_mul_left, houtput, mul_one]
    _ = Int.gcd ((σ : ℤ) * (α0 * e + β0 * u))
          ((σ : ℤ) * ((-B0) * e + K0 * u)) := by rw [he, hu]
    _ = σ * Int.gcd (α0 * e + β0 * u) ((-B0) * e + K0 * u) := by
      simpa using Int.gcd_mul_left (σ : ℤ) (α0 * e + β0 * u)
        ((-B0) * e + K0 * u)
    _ = σ * Int.gcd (A0 ^ 2) ((-B0) * e + K0 * u) := by rw [hmatrix]
    _ = σ * Int.gcd (A0 ^ 2) (K0 * u - B0 * e) := by ring_nf

/-- Quotient form of the exact excursion payment.  Here `σ = gcd(A,B)` is
constructed from the unnormalised block data.  The excursion formulas imply
`gcd(B,K)=σ`, so dividing the second row by `σ` makes it primitive; the
square determinant then gives the literal payment
`|Λ| = σ * gcd((A/σ)^2, (K*u-B*e)/σ)`. -/
theorem excursionCancellationPayment
    {σ : ℕ} {Λ A B aStart aStop K α β e u eStop uStop : ℤ}
    (hσ : σ = Int.gcd A B) (hσpos : 0 < σ)
    (hK : K = A - (aStart - 1) * B)
    (hα : α = A + (aStop - 1) * B)
    (hβ : β = A * (aStart - 1) - (aStop - 1) * K)
    (hinput : Int.gcd e u = 1)
    (houtput : Int.gcd eStop uStop = 1)
    (he : Λ * eStop = α * e + β * u)
    (hu : Λ * uStop = (-B) * e + K * u) :
    Λ.natAbs = σ * Int.gcd ((A / (σ : ℤ)) ^ 2)
      ((K * u - B * e) / (σ : ℤ)) := by
  let A0 := A / (σ : ℤ)
  let B0 := B / (σ : ℤ)
  let K0 := K / (σ : ℤ)
  let α0 := α / (σ : ℤ)
  let β0 := β / (σ : ℤ)
  have hσne : (σ : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hσpos)
  have hAdiv : (σ : ℤ) ∣ A := by
    rw [hσ]
    exact Int.gcd_dvd_left A B
  have hBdiv : (σ : ℤ) ∣ B := by
    rw [hσ]
    exact Int.gcd_dvd_right A B
  have hKdiv : (σ : ℤ) ∣ K := by
    rw [hK]
    exact Int.dvd_sub hAdiv
      (dvd_mul_of_dvd_right hBdiv (aStart - 1))
  have hαdiv : (σ : ℤ) ∣ α := by
    rw [hα]
    exact Int.dvd_add hAdiv
      (dvd_mul_of_dvd_right hBdiv (aStop - 1))
  have hβdiv : (σ : ℤ) ∣ β := by
    rw [hβ]
    exact Int.dvd_sub (dvd_mul_of_dvd_left hAdiv (aStart - 1))
      (dvd_mul_of_dvd_right hKdiv (aStop - 1))
  have hBK : Int.gcd B K = Int.gcd A B := by
    apply Nat.dvd_antisymm
    · apply Int.dvd_gcd
      · have hA : A = K + (aStart - 1) * B := by rw [hK]; ring
        rw [hA]
        exact Int.dvd_add (Int.gcd_dvd_right B K)
          (dvd_mul_of_dvd_right (Int.gcd_dvd_left B K) (aStart - 1))
      · exact Int.gcd_dvd_left B K
    · apply Int.dvd_gcd
      · exact Int.gcd_dvd_right A B
      · rw [hK]
        exact Int.dvd_sub (Int.gcd_dvd_left A B)
          (dvd_mul_of_dvd_right (Int.gcd_dvd_right A B) (aStart - 1))
  have hBKσ : Int.gcd B K = σ := hBK.trans hσ.symm
  have hBKpos : 0 < Int.gcd B K := by rw [hBKσ]; exact hσpos
  have hrowPos : Int.gcd B0 K0 = 1 := by
    dsimp [B0, K0]
    simpa [hBKσ] using
      (Int.gcd_div_gcd_div_gcd (i := B) (j := K) hBKpos)
  have hrow : Int.gcd (-B0) K0 = 1 := by simpa using hrowPos
  have hAfac : A = (σ : ℤ) * A0 := by
    dsimp [A0]
    rw [mul_comm]
    exact (Int.ediv_mul_cancel hAdiv).symm
  have hBfac : B = (σ : ℤ) * B0 := by
    dsimp [B0]
    rw [mul_comm]
    exact (Int.ediv_mul_cancel hBdiv).symm
  have hKfac : K = (σ : ℤ) * K0 := by
    dsimp [K0]
    rw [mul_comm]
    exact (Int.ediv_mul_cancel hKdiv).symm
  have hαfac : α = (σ : ℤ) * α0 := by
    dsimp [α0]
    rw [mul_comm]
    exact (Int.ediv_mul_cancel hαdiv).symm
  have hβfac : β = (σ : ℤ) * β0 := by
    dsimp [β0]
    rw [mul_comm]
    exact (Int.ediv_mul_cancel hβdiv).symm
  have hdetFull : α * K + β * B = A ^ 2 :=
    excursionMatrix_det_square hK hα hβ
  have hdet : α0 * K0 + β0 * B0 = A0 ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hσne)
    calc
      (σ : ℤ) ^ 2 * (α0 * K0 + β0 * B0) = α * K + β * B := by
        rw [hαfac, hKfac, hβfac, hBfac]
        ring
      _ = A ^ 2 := hdetFull
      _ = (σ : ℤ) ^ 2 * A0 ^ 2 := by rw [hAfac]; ring
  have he0 : Λ * eStop = (σ : ℤ) * (α0 * e + β0 * u) := by
    rw [he, hαfac, hβfac]
    ring
  have hu0 : Λ * uStop = (σ : ℤ) * ((-B0) * e + K0 * u) := by
    rw [hu, hBfac, hKfac]
    ring
  have hpayment := blockCancellationPayment_explicit
    (σ := σ) (Λ := Λ) (A0 := A0) (B0 := B0) (K0 := K0)
    (α0 := α0) (β0 := β0) hinput houtput hrow hdet he0 hu0
  have hcoord :
      (K * u - B * e) / (σ : ℤ) = K0 * u - B0 * e := by
    calc
      (K * u - B * e) / (σ : ℤ) =
          ((σ : ℤ) * (K0 * u - B0 * e)) / (σ : ℤ) := by
            rw [hKfac, hBfac]
            ring
      _ = K0 * u - B0 * e := Int.mul_ediv_cancel_left _ hσne
  dsimp [A0, K0, B0] at hpayment ⊢
  rw [hcoord]
  exact hpayment

/-- Exact telescoping for a sequence of excursion scales.  The endpoint
equations alone force the product of all block payments to be the total gcd
scale growth; no independence assumption on the intervening prime factors is
needed. -/
theorem blockScale_product_telescopes
    (G t Λ : ℕ → ℕ)
    (hscale : ∀ i, Λ i * G (t i) = G (t (i + 1))) :
    ∀ m, (∏ i ∈ Finset.range m, Λ i) * G (t 0) = G (t m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ]
      calc
        ((∏ i ∈ Finset.range m, Λ i) * Λ m) * G (t 0) =
            Λ m * ((∏ i ∈ Finset.range m, Λ i) * G (t 0)) := by ring
        _ = Λ m * G (t m) := by rw [ih]
        _ = G (t (m + 1)) := hscale m

/-- Multiplicative form of the logarithmic cancellation-mass budget.  If the
ambient tail state is subexponential in physical time, then the product of
all exact excursion payments is subexponential at the corresponding endpoint.
This is the honest global accumulation supplied by the gcd budget; it does
not by itself exclude arbitrarily sparse large payments. -/
theorem blockScale_product_subexponential
    (G C t Λ : ℕ → ℕ)
    (hGpos : ∀ n, 0 < G n)
    (hGleC : ∀ n, G n ≤ C n)
    (hscale : ∀ i, Λ i * G (t i) = G (t (i + 1)))
    (hCsubexp : ∀ K, 0 < K → ∃ N, ∀ n, N ≤ n → C n ^ K < 2 ^ n) :
    ∀ K, 0 < K → ∃ N, ∀ m, N ≤ t m →
      (∏ i ∈ Finset.range m, Λ i) ^ K < 2 ^ (t m) := by
  intro K hK
  obtain ⟨N, hN⟩ := hCsubexp K hK
  refine ⟨N, fun m hm ↦ ?_⟩
  have htel := blockScale_product_telescopes G t Λ hscale m
  have hprodLeG : (∏ i ∈ Finset.range m, Λ i) ≤ G (t m) := by
    have hbase : (∏ i ∈ Finset.range m, Λ i) ≤
        (∏ i ∈ Finset.range m, Λ i) * G (t 0) :=
      Nat.le_mul_of_pos_right _ (hGpos (t 0))
    rw [htel] at hbase
    exact hbase
  exact (Nat.pow_le_pow_left (hprodLeG.trans (hGleC (t m))) K).trans_lt
    (hN (t m) hm)

/-- A new scale-weighted record must be paid for by the intervening gcd scale.
This is the order-theoretic half of the record-payment corollary, separated
from the determinantal computation of that scale. -/
theorem scaledRecord_forces_payment
    {GStart GStop Λ mStart mStop : ℕ}
    (hGStart : 0 < GStart)
    (hscale : GStop = Λ * GStart)
    (hrecord : GStart * mStart < GStop * mStop) :
    mStart < Λ * mStop := by
  apply (Nat.mul_lt_mul_left hGStart).mp
  calc
    GStart * mStart < GStop * mStop := hrecord
    _ = GStart * (Λ * mStop) := by rw [hscale]; ring

/-- Record-payment corollary in the square-residue coordinates supplied by
`excursionCancellationPayment`.  If the primitive magnitude does not itself
account for a new scale-weighted record, the exact `σ * gcd(A0²,z)` payment
does. -/
theorem squareResiduePayment_of_scaledRecord
    {GStart GStop Λ mStart mStop σ : ℕ} {A0 z : ℤ}
    (hGStart : 0 < GStart)
    (hscale : GStop = Λ * GStart)
    (hrecord : GStart * mStart < GStop * mStop)
    (hpayment : Λ = σ * Int.gcd (A0 ^ 2) z) :
    mStart < σ * Int.gcd (A0 ^ 2) z * mStop := by
  have hpaid := scaledRecord_forces_payment hGStart hscale hrecord
  rw [hpayment] at hpaid
  exact hpaid

end ErdosProblems.Erdos243
