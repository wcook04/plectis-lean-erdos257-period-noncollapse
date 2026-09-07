# Blaschke-power critical spectra

Ordinary note, 2026-09-07, Type B r5 return. Type A checked the algebraic
interface and the two rational certificates. The analytic limit theorems,
high-critical path theorem, and metric degeneration law remain ordinary
advisory proofs: novelty is not established, and they are not Lean-checked.
They are not inserted as the short-note flagship. Erdős #1041 remains open.

Replay:

```sh
./repo-python Erdos1041/scripts/blaschke_power/check_degree8.py
./repo-python Erdos1041/scripts/blaschke_power/check_high_critical.py
```

Complete ordinary proofs of the advisory analytic statements live in
[BlaschkePowerCriticalSpectra_r5_source.md](BlaschkePowerCriticalSpectra_r5_source.md).
Algebra: [BlaschkePowerCriticalValues.lean](BlaschkePowerCriticalValues.lean).
The free-point `4s` hierarchy remains
[SharpPowerDiscProducts.md](SharpPowerDiscProducts.md).

## Construction

For `0<b<1` and integer `N≥1`,

```text
A(z)=z(z+b),  D(z)=1+bz,  F_N = A^N - D^N.
```

`F_N` is monic of degree `2N`. Roots are simple and lie on the unit circle
as the preimages of the `N`th roots of unity under the degree-two Blaschke
product `A/D`. The quadratic critical-value identity is division-free:

```text
(2c+b) F_N(c) = -(bc^2+2c+b) (1+bc)^{N-1}
```

at critical points, under the algebraic critical equation. That identity is
the intended Lean interface. It does not prove weak convergence, Poisson
integration, exponent optimality, or a path theorem.

Radial contraction `G(z)=r^{2N} F_N(z/r)` with `0<r<1` produces simple
open-disc roots and scales critical values by `r^{2N}`.

## Checked certificates

Both checkers use only `fractions.Fraction`. Rational disc centres are
certificate inputs. The Rouché interpretation and the circle-root
construction are ordinary, not formalised by the arithmetic.

**Degree 8.** `N=4`, `b=1/2`, `r=999/1000`. Seven disjoint derivative-root
discs. Mean `|G(c)|^{8/7} > 3763187/3500000 > 1.075`. This violates a
proposed numerator `8` in degree `8`; it does not violate the proved
numerator `4`.

**Degree 24.** `N=12`, `b=1/120`, `r=999999999/10^9`. Twenty-three disjoint
discs. Every critical value of `G` lies in `|v+1|<1/12`, hence
`μ>11/12>13/25`, every pair satisfies `|v_i/v_j-1|<2/11`, and no selected
critical value passes the radius-`4/3` test at any centre in `[0,1]`. Mean
`|G(c)|^{8/23} > 46001266667/46000000000 > 40001/40000`. This is not a
counterexample to the parent path problem.

## Advisory ordinary theorems

The source note proposes, with complete ordinary proofs not independently
reviewed here:

1. **Joint spectral law.** Critical points of `A^N-D^N` and the normalised
   moduli `|F_N(c)|^{1/deg}` converge jointly to the Poisson/Blaschke
   measure of `A/D`. The `b=0` case collapses all critical points to the
   origin and is excluded.
2. **Polynomial-class sharpness of the numerator `4s`.** For every `s≥1`
   and `p>4s` there are monic open-disc polynomials whose first `s-1`
   critical-point power sums vanish but whose mean `|f(c)|^{p/(n-1)}`
   exceeds `1`. The same holds with `μ` bounded below by any fixed
   `τ<1`, and with failure of every radius-`4/3` centre test. This
   sharpens the *class* of the r4 free-point hierarchy; it does not
   change the proved upper exponent, and it is not a path selector.
3. **High-critical short connectors.** For fixed small `λ>0` and
   `b=λ/N`, `μ(F_N)→e^{-λ}` while a radial-plus-circular connector has
   length `O((log(1/λ))/N)`. The proof supplies no numerical `N_0`.
   Radial contraction preserves containment and decreases length.
4. **Metric degeneration.** With `λ_N=e^{-α N}`,
   `Λ(F_N)→2(1-e^{-α/2})`. Coefficients approach `z^{2N}-1`
   exponentially, so no modulus of continuity for `Λ` can be uniform
   across degrees in coefficient `ℓ^1` or closed-disc uniform norm.
   This is compatible with registered fixed-degree lower semicontinuity
   in [GenericSufficiencyClosure.md](GenericSufficiencyClosure.md).

## Lead judgement

These results do not replace the trinomial flagship or the paper title.
The trinomial theorem is a complete all-degree parent-length family with
Lean-checked radial inequalities. The Blaschke-power path theorem is an
asymptotic family with an unspecified threshold; the spectral sharpness
and degeneration laws are not parent solutions. They belong in this
ordinary note, with a short pointer in the live paper's remaining-problem
section, not as Theorem 1.

## Boundary

Keep `71/10`, `13/25`, and disk-family `S=4/3`. Do not raise the parent.
The geometric question remains `Λ(f)≤2` on the closed class.
