# Sharp power inequalities for disc products

Ordinary analytic note, 2026-09-07. Type B r4 research return, independently
checked at the identity and rigidity level below. Not Lean-checked. Not
inserted into the short note: the flagship records only the already
registered weighted quadratic theorem
(`weighted_quadratic_free_point_all_degrees` in
[FreePointQuadraticAllDegrees.md](FreePointQuadraticAllDegrees.md)). The
`4s` hierarchy is not a parent path theorem. Erdős #1041 remains open.

## Collision

The quadratic case `p=2` is already in the corpus. Polar comparison on the
circle is already registered as
`polar_derivative_schur_pointwise_critical_certificate_2026_09_05`. This
note records the power-parameter identity and the moment hierarchy proposed
in the r4 return; it does not re-announce the quadratic theorem.

## Identity

For `c_j` in the closed disc, positive weights summing to one, and
`g(z)=exp(sum w_j log(1-conj(c_j)z))` with `g(0)=1`, set
`h_p=g^{p/2}` and write `h_p=1+sum_{ν≥1} b_ν z^ν`. On the open disc the
Poisson mixture of the points is

```text
P(ζ) = 1 - 2 Re(ζ g'(ζ)/g(ζ)) = 1 - (4/p) Re(ζ h_p'(ζ)/h_p(ζ)).
```

The finite-coefficient Taylor combination
`∑ |a_j|² - 2 ∑ j |a_j|² = |a₀|² - ∑_{j≥1} (2j-1)|a_j|²` is
Lean-checked in `PoissonTaylorFiniteIdentity.lean`, together with the
local r3 remainder `m²/(2m-1) ≤ m`. Polar comparison on the circle is
Lean-checked in `PolarDerivativeCircle.lean`. The analytic circle
integral, the 4s hierarchy, and the disc Schur certificate remain ordinary.

## Hierarchy (ordinary)

If `M_k=∑ w_j c_j^k` vanishes for `1 ≤ k ≤ s-1`, then `h_p=1+O(z^s)` and,
for `0 < p ≤ 4s`,

```text
∑ w_j G(c_j)^p ≤ 1,     in particular ∑ w_j G(c_j)^{4s} ≤ 1.
```

Finite equality at the endpoint holds only at the origin configuration.
The exponent `4s` is sharp uniformly in cardinality: an endpoint density
and finite equal-weight approximants exceed one for every `p>4s`. Critical
values inherit the same exponents after the registered polar comparison
and a radial contraction, under the moment hypotheses on the critical
configuration. Selected-critical-value statements that claim a unit
lemniscate connector still require `|v|<1`.

## Boundary

The geometric question remains `Λ(f)≤2` on the closed class. This note
does not select a pair, does not bound a canonical arc, and does not
replace `71/10`, `13/25`, or disk-family `S=4/3`.

## Polynomial realisation (r5)

Free-point sharpness of the numerator `4s` does not by itself prove
sharpness for polynomial critical values. The r5 ordinary note
[BlaschkePowerCriticalSpectra.md](BlaschkePowerCriticalSpectra.md) records
Blaschke-power realisations `F_N=A^N-D^N` with exact degree-8 / degree-24
rational certificates. Complete ordinary proofs of the advisory analytic
theorems sit in
[BlaschkePowerCriticalSpectra_r5_source.md](BlaschkePowerCriticalSpectra_r5_source.md).
That development stays out of the short-note flagship. It does not solve
the parent path problem.
