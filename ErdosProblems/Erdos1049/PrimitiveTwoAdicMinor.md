# Erdős #1049: all-`n` 2-adic valuation of a three-row primitive minor

Status: ordinary complete proofs of a 2-adic identity and, after the small-p
unit identity, of the matching 3-adic formula `v₃(g_n)=2(n-1)²` on the same
*2004* three-row deformation.  Lean checks the degree arithmetic, the 2-adic
calculus, the primitive 3-adic subtraction, and the `D_s` minor formula in
`PrimitiveTwoAdicMinor.lean`.  The finite q-binomial identity isolating the
small-p unit is `QBinomialUnitIdentity.lean` (focused Lake exit 0).  The 3-adic
lemmas in `PrimitiveTwoAdicMinor.lean` are source-landed; their focused rebuild
was occupancy-deferred (exit 75).  This family is not the 2016 Hankel family.
Neither identity decides `F(3/2)`.

## 1. The family

For `n≥1` and `s∈{0,1,2}` take Zudilin 2004 parameters

```
a₀ = 14n+2,   a₁ = 12n+1,   a₂ = 14n+1-s,   β = 27n+2.
```

The deformation varies `a₂`; it is not an `a₀`-shift of the region-theorem
direction `(14n+1, 12n+1, 14n+1; 27n+2)`.  All three rows satisfy
`a₁ ≤ a₂` and `a₁+a₂ ≤ β ≤ a₀+a₂`.

Evaluate the source pair `(A,B)` of (8)–(11) at `p=3/2`, clear denominators,
divide by the integer gcd, and take the first coordinate positive.  Write
`(A_{n,s}, B_{n,s})` for the primitive pair, and

```
g_n = gcd_{0≤i<j≤2} |A_{n,i} B_{n,j} - A_{n,j} B_{n,i}|.
```

## 2. Finite table (exact arithmetic)

Computed from the source coefficients as exact rationals
(`scripts/check_primitive_two_adic_minor.py`):

| n | v₂(g_n) | v₃(g_n) | minors nonzero | (1091n²+83n-2)/2 |
|--:|--------:|--------:|:--------------:|-----------------:|
| 1 | 586 | 0 | yes | 586 |
| 2 | 2264 | 2 | yes | 2264 |
| 3 | 5033 | 8 | yes | 5033 |
| 4 | 8893 | 18 | yes | 8893 |
| 5 | 13844 | 32 | yes | 13844 |
| 6 | 19886 | 50 | yes | 19886 |

The values `v₃(g_n) = 2(n-1)²` match this table.  Type B r4 supplies an
ordinary all-`n` proof of that formula from the small-p unit identity
(Theorem R4.1 / (2.3)); Lean checks the finite q-binomial algebra and the
primitive valuation subtraction.  First coordinates are odd; every second
coordinate has `v₂ = 1`.  The 2-adic minor divisibility is therefore not
rowwise content.

## 3. Theorem D

For the family above, `v₂(g_n) = (1091 n² + 83 n - 2)/2` for every `n≥1`.
More precisely, for `i<j` the valuation of the `(i,j)`-minor equals

```
K_j = (1091 n²)/2 - 13 n j + (135 n)/2 - (j²+j)/2 + 2.
```

**Degree.**  The summand `c_k(p) p^{a₀ k}` has `p`-degree
`e_k + a₀ k + (a₁-1)(k-a₁) + (β-k-1)(k-a₂)` with the source exponent `e_k`.
The increment in `k` is `a₀+a₁+a₂-k-2 = 40n+2-s-k`, strictly positive on the
summation range `a₂ ≤ k ≤ β-2` (Lean: `zudilinDefSummandDegree_step_pos`).
The unique top-degree term is therefore `k=β-1`.  Its leading coefficient is
`±1` (Gaussian binomials are monic in the leading monomial; the remaining
powers are monomials).  Substitution gives `deg A = K_s`, and
`2 K_2 = 1091 n² + 83 n - 2` (Lean: `twoMul_topDegree_s_two`, proved on
twice the degree so that no truncating integer division appears).

**Valuation of A.**  All terms are integral Laurent polynomials in `p`.  At
`p=3/2` the unique leading monomial of degree `K_s` with unit coefficient
implies `v₂(A) = -K_s`, because `v₂((3/2)^K) = -K`
(Lean: `padicValRat_two_three_halves_pow`).

**The series `F₂`.**  Work in `ℚ₂` and set `F₂ = ∑_{m≥1} τ(m) (2/3)^m`.  This
is a 2-adic value, not the real number `F(3/2)`.  The first term has valuation
`1`; every later term has valuation at least `2`, so `v₂(F₂)=1`.

**The remainder `H`.**  The source identity `A F₂ - B = H` holds by the formal
power-series identity at `q=0`.  The source expression for `H` lies in
`1 + q ℤ[[q]]`: the `t=0` term has constant coefficient `1`, denominator
products are units, and `t>0` starts at positive order.  Thus `v₂(H)=0`, so
`v₂(B) = 1-K_s`.

**Primitivity.**  The common scalar of the rational pair has 2-adic valuation
`K_s`.  After clearing, the first coordinate is a 2-adic unit and the second
has valuation `1`.  The primitive error `L_s = A_{n,s} F₂ - B_{n,s}` has
valuation `K_s`.

**Minors.**  For `i<j`,

```
A_{n,i} B_{n,j} - A_{n,j} B_{n,i} = A_{n,j} L_i - A_{n,i} L_j.
```

(Lean: `minor_eq_error_cross`.)  The first coordinates are units and
`K_0 > K_1 > K_2`, so the two terms have unequal valuations and the difference
has valuation `K_j` (Lean: `padicValRat_two_error_cross`).  The minimum over
the three minors is `K_2`, which is the displayed formula.  All three minors
are nonzero for every `n`.

## 4. Boundary

This proves a quadratic 2-adic divisibility for one three-row 2004
deformation, and (ordinarily) the matching 3-adic gcd.  It does not produce
a growing-rank selector family that meets `E_n < D_n/n`, and it does not
prove irrationality at `3/2`.

## 5. R3 / R4.5 wide rectangle (2004 family only; not mixed with 2016 Hankel)

Type B r3/r4 supplies a two-parameter rectangle `a_0=14m+2+t`, `a_1=12m+1`,
`a_2=14m+1-s`, `β=27m+2` for even `m` with `27m+1` prime, `0≤t<12m`,
`m/2≤s≤m+1`, hence `M=6m²+24m` rows.  Distinct 2-adic valuations of the
primitive errors give signed algebraic noncollapse; pigeonhole after
normalisation gives a simultaneous local collision in `6^{m²}ℤ²`.  Heights
are `O(m²)`.  The family is **not defined in Lean**; the pigeonhole consumer
is the existing unimodular theorem
`BezoutPluckerJets.zmod_binary_tail_collision_of_adjacent_det_zero_of_isCoprime`
(ordinary application, no new wrapper).  The remaining target is still the
real inequality `E_n < D_n/n` for selected errors (Type B (8.1)–(8.2)).
Covering every large scale uses the prime-number theorem in the progression
`1 mod 27`.  Degree uniqueness on this rectangle is checked by
`Erdos1049/scripts/check_r3_assimilation_probes.py --mode degrees --quick`.
This is not inserted in the live short note and does not prove `F(3/2)`.

## 6. R4.1–R4.3: small-p unit and the 3-adic formula

After the published integrality exponent `M` is removed, the second source
coefficient is a 3-adic unit and `v₃(A_*)=dη`, `v₃(B_*)=0` on the cone.
The three-row gcd is then `v₃(g_n)=2(n-1)²` because
`D_s=(2n-s)(n+1-s)` is strictly decreasing in `s∈{0,1,2}` and
`D_2=2(n-1)²`.  Lean: `QBinomialUnitIdentity` for the finite q-binomial
identity (2.3); `PrimitiveTwoAdicMinor` for `padicValRat_scale_min`,
`padicValRat_minor_of_unequal_A`, and `zudilinThreeAdicD_min_s_two`.

## 7. R4.9–R4.10: narrower family fails the approximation test

Type B constructs a polynomial-lift family with quadratic rank, simultaneous
local collisions, and eventual real nonvanishing of every nonzero signed
row sum.  On the specified regular scale, the smallest divided real collision
error has infinite limsup.  That is an ordinary **failure** theorem for the
requested approximation inequality on this family.  It does not refute a
lacunary-subsequence strategy or the wider rectangle of §5.  It is not a
theorem about `F(3/2)`, and it is not inserted in the live short note.

The integer core `p^{v_p(Δ)} ≤ |Δ|` for a nonzero determinant is Lean
(`natAbs_ge_pow_padicValInt`); the Archimedean limsup remains ordinary.

## 8. Lattice index (already r2)

A primitive anchor extends to a unimodular basis of `ℤ²`.  After dividing
by `D=6^{m²}`, the residual lattice index is not `g/D²`; the intersection
with `Dℤ²` is taken first.  Already recorded in r2; not re-litigated.
