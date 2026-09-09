import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-!
# Erdős #1041: the attachment-aware Reeb kernel

`AttachmentAwareReeb.md` closes the topology producer and shows the closure is
metrically inert.  This module checks the algebraic and combinatorial steps the
ordinary proof leans on.

* `rayDist_sq_identity` — the one completed square behind everything:
  `ρ² - 2ρtc + t² - ρ²s² = (t - ρc)²`.  It gives the exact distance from a point
  to a ray through the origin, and (with a sign flip) the exact closest approach
  on the extremal family.
* `attachment_window_sin`, `attachment_window_cos_pos` — Theorem 2: a Newton
  trajectory meeting a saddle neighbourhood of value radius `δ` has value
  argument confined to `ρ|sin Δ| < δ` on the `cos Δ > 0` side.
* `extremal_closest_approach_lower`, `extremal_closest_approach_attained`,
  `extremal_window` — Theorem 5 on `z^n - r^n`, whose window is `(ε/r)^n`.
* `isTree_of_connected_of_card_eq` — the `k` vertices / `k-1` edges count of
  (1c).
* `exists_le_of_sum_le_card_mul` — the averaging of Corollary 3a.
* `rootStar_tangent_sum`, `cassini_endpoint_deficit_zero` — Theorem 4's
  evaluation, and its exact vanishing on the Cassini witness.

Riemann–Hurwitz, the monodromy transposition argument, the strip
diffeomorphism, and the skeleton limits of Theorem 3 are carried by the ordinary
proof and are not encoded here.

This is a standalone focused kernel: `ErdosProblems.Root` does not import it.
Successful Lean replay validates only the algebraic and combinatorial lemmas
listed above; it does not formalize the ordinary Reeb decomposition or the
metric conclusion stated in `AttachmentAwareReeb.md`.
-/

namespace ErdosProblems.Erdos1041.AttachmentAwareReeb

open Finset

/-! ## 1. The completed square -/

/-- Squared distance from `ρ e^{iθ_c}` to the point at parameter `t` on the ray
of angle `θ`, split into its minimum `ρ²s²` and an exact square.  Here
`c = cos Δ`, `s = sin Δ` with `Δ = θ - θ_c`. -/
theorem rayDist_sq_identity (ρ t c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ρ ^ 2 - 2 * ρ * t * c + t ^ 2 - ρ ^ 2 * s ^ 2 = (t - ρ * c) ^ 2 := by
  nlinarith [hcs]

/-! ## 2. Attachment rigidity -/

/-- Theorem 2, angular half: meeting the saddle neighbourhood forces
`ρ|sin Δ| < δ`. -/
theorem attachment_window_sin {ρ t c s δ : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (hmeet : ρ ^ 2 - 2 * ρ * t * c + t ^ 2 < δ ^ 2) :
    (ρ * s) ^ 2 < δ ^ 2 := by
  have hid := rayDist_sq_identity ρ t c s hcs
  nlinarith [sq_nonneg (t - ρ * c)]

/-- Theorem 2, side half: for `δ ≤ ρ` the far side of the ray is excluded, so an
attachable trajectory has `cos Δ > 0`. -/
theorem attachment_window_cos_pos {ρ t c δ : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hmeet : ρ ^ 2 - 2 * ρ * t * c + t ^ 2 < δ ^ 2) :
    0 < c := by
  by_contra hc
  rw [not_lt] at hc
  nlinarith [sq_nonneg t, mul_nonneg (mul_nonneg hρ.le ht) (neg_nonneg.mpr hc)]

/-! ## 3. The extremal family `z^n - r^n` -/

/-- Theorem 5, lower bound: with `Rho = r^n`, every value on the ray of angle
`θ` has `|z|^{2n} ≥ Rho² sin²θ`. -/
theorem extremal_closest_approach_lower {Rho t c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    Rho ^ 2 * s ^ 2 ≤ Rho ^ 2 + 2 * Rho * t * c + t ^ 2 := by
  nlinarith [sq_nonneg (t + Rho * c), hcs]

/-- On the `cos θ ≥ 0` side the minimum is `Rho²`, attained at `t = 0`. -/
theorem extremal_closest_approach_cos_nonneg {Rho t c : ℝ} (hRho : 0 ≤ Rho)
    (ht : 0 ≤ t) (hc : 0 ≤ c) :
    Rho ^ 2 ≤ Rho ^ 2 + 2 * Rho * t * c + t ^ 2 := by
  nlinarith [sq_nonneg t, mul_nonneg (mul_nonneg hRho ht) hc]

/-- On the `cos θ < 0` side the lower bound is attained at `t = -Rho cos θ`,
which is admissible because it is nonnegative. -/
theorem extremal_closest_approach_attained {Rho c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    Rho ^ 2 + 2 * Rho * (-(Rho * c)) * c + (-(Rho * c)) ^ 2 = Rho ^ 2 * s ^ 2 := by
  nlinarith [hcs]

/-- Theorem 5's window: entering the ball of physical radius `ε` forces
`|sin θ| < (ε/r)^n`, since `Rho = r^n` and the value bound is `ε^{2n}`. -/
theorem extremal_window {r eps s : ℝ} {n : ℕ} (hr : 0 < r) (heps : 0 < eps)
    (hbound : (r ^ n) ^ 2 * s ^ 2 < (eps ^ n) ^ 2) :
    s < (eps / r) ^ n := by
  have hrn : 0 < r ^ n := pow_pos hr n
  have hen : 0 < eps ^ n := pow_pos heps n
  have hlt : r ^ n * s < eps ^ n := by nlinarith
  rw [div_pow, lt_div_iff₀ hrn]
  linarith [hlt]

/-! ## 4. The tree count of (1c) -/

/-- A connected graph on `k` vertices with `k - 1` edges is a tree.  In (1c) the
vertices are the `k` roots and the edges are the `k - 1` simple critical
points. -/
theorem isTree_of_connected_of_card_eq {V : Type*} [Finite V] {G : SimpleGraph V}
    (hconn : G.Connected) (hcard : Nat.card G.edgeSet + 1 = Nat.card V) :
    G.IsTree :=
  SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, hcard⟩

/-! ## 5. Averaging: the aggregate implies the hub statement -/

/-- Corollary 3a's averaging step: if the canonical arc lengths sum to at most
`2R` times their number, one of them is at most `2R`. -/
theorem exists_le_of_sum_le_card_mul {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (L : ι → ℝ) (B : ℝ) (h : ∑ i ∈ s, L i ≤ B * s.card) :
    ∃ i ∈ s, L i ≤ B := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hlt : B * s.card < ∑ i ∈ s, L i := by
    have : ∑ _i ∈ s, B < ∑ i ∈ s, L i :=
      Finset.sum_lt_sum_of_nonempty hs fun i hi => hcon i hi
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  linarith

/-! ## 6. The root-star tangent law -/

/-- Theorem 4: the incident tangents at a root are one common rotation applied
to the critical-value directions, so the endpoint sum factors.  Here
`w = exp(-i arg f'(a))` and `u i = exp(i θ_{c_i})`. -/
theorem rootStar_tangent_sum {d : ℕ} (a w : ℂ) (u : Fin d → ℂ) :
    ∑ i, (a * (starRingEnd ℂ) (w * u i)).re
      = (a * (starRingEnd ℂ) w * ∑ i, (starRingEnd ℂ) (u i)).re := by
  rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  ring_nf

/-- The Cassini witness: at the root `a` of `z² - a²` the incident tangent is
`-1`, so the endpoint deficit `R + ⟪a, U_a⟫` vanishes exactly.  With zero edge
curvature, the budget identity (D) then reads `L = 2R = 2a`. -/
theorem cassini_endpoint_deficit_zero (a : ℝ) :
    a + ((a : ℂ) * (starRingEnd ℂ) (-1 : ℂ)).re = 0 := by
  simp

end ErdosProblems.Erdos1041.AttachmentAwareReeb
