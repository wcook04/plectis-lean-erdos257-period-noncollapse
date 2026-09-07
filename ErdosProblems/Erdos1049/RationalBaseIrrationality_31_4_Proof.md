# Erdős #1049: irrationality of `F(a/b)` on the region `b^μ < a`, `μ = 2.46497868…`, with `31/4` the first new base

Status: ordinary complete proof citing published lemmas (Zudilin 2004 Lemma 7, with its inputs
Lemma 3, Lemma 4's exponent (16), Lemma 5, and the identity (9)–(11)).  Not kernel-checked; the
finite part is Lean-checked in `RationalBaseContour.lean`.  Independently attacked 2026-09-02
(`state/public-source-redacted://erdos1049_region_adversary/REPORT.md`, commit `b7a2783559`): Theorems A and B survived all eight attacks, with an exact
reconstruction at `n = 4`; Theorem C's first printed form lacked a coefficient-height
hypothesis and is restated below in the corrected form (§1, §5).
Priority: extends Bundschuh–Väänänen 1994 Theorem 2; the rational-base extension of this
kind of result was announced without a constant in Zudilin 2016 (see §7).

## 0. Notation and the object

For real `t > 1`,

```
F(t) := Σ_{m≥1} 1/(t^m − 1) = Σ_{n≥1} τ(n) t^{−n}      (τ = number of divisors),
```

the Lambert value of Erdős #1049 (`F(t) = h_p(1)` in Zudilin's notation, `p = t`,
`q = 1/p`).  A rational base is written `a/b` with `a > b ≥ 1` coprime integers, and
its height parameter is `θ := log b / log a ∈ [0, 1)`.  In Zudilin 2016's notation
`p = r/s`, so `r = a`, `s = b`, and `log|r| > c log|s|` means `θ < 1/c`.

Constants of Zudilin 2004, Section 5, direction `(α₀, α₁, α₂; β) = (14, 12, 14; 27)`:

```
C₁ = (α₀+α₁+α₂)β − (α₁² + α₂² + β²)/2 = 1091/2 = 545.5                         (paper (25))
C₀ = α₁²/2 + α₀α₁ + (β−α₂)(α₂−α₁) − (3/π²)(m² − J) = 266 − (3/π²)(225 − J)     (paper (26))
J  = ∫₀¹ ω(x) d(−ψ'(x)) = Σ_{i=1}^{13} (ψ₁(uᵢ) − ψ₁(vᵢ)),  ψ₁(x) = Σ_{k≥0} 1/(k+x)²
μ  := C₁/C₀ = 2.464978683574975037454488275535521581878…   (Zudilin's Theorem 1 bound)
θ* := C₀/C₁ = 1/μ = 0.40568302138406054101566030557693017464819107867787…
```

with the thirteen intervals `[uᵢ, vᵢ)` = `[1/14,1/12) [1/7,1/6) [3/14,1/4) [2/7,1/3)
[5/14,2/5) [3/7,7/15) [1/2,8/15) [4/7,3/5) [9/14,2/3) [5/7,11/15) [11/14,4/5)
[6/7,13/15) [13/14,14/15)` (recomputed from `ω`, equal to the paper's printed list).
Numerics: `J = 77.943184475009095922589567023992110449…`,
`C₀ = 221.300088165005025124042696692215410…`; mpmath at 60 digits, `J` cross-checked
by direct series summation to `1e−59` (`formal_math/probes/erdos1049_zudilin_region.py`,
receipt `state/public-source-redacted://erdos1049_zudilin_region/region_receipt.json`).

## 1. Statements

**Theorem A (region).** Let `a > b ≥ 1` be coprime integers with

```
b^μ < a,   equivalently   log b / log a < θ* = 0.405683021384…,   μ = 2.464978683574975…
```

Then `F(a/b)` is irrational.  In the normalisation of Zudilin 2016, §2 ("the results can be
given for non-integer `p = r/s`, `|p| > 1`, under `log|r| > c log|s|` for some computable
constant `c > 0`"): the constant is

```
c = μ = C₁/C₀ = 2.46497868357497503745…,
```

the irrationality-exponent bound of Zudilin 2004 Theorem 1 itself, and the region is
`|r| > |s|^μ` for positive `r/s` (negative bases are not treated here, see §4 Step 5).

**Theorem B (first new base).** `F(31/4)` is irrational, and so is `F((31/4)^r)` for every
integer `r ≥ 1`.  Here `log 4 / log 31 = 0.4036981731… < 81/200 < θ*`, and
`4^μ = 30.4835… < 31 < 4^{μ_BV} = 32.3696…` with `μ_BV = 2π²/(π² − 2) = 2.508284761994…`
the Bundschuh–Väänänen exponent, so `31/4` lies outside their region
`log b/log a < 1/2 − 1/π² = 0.398678816357…` and inside Theorem A's.

**Theorem C (degree-budget cap and exact-degree obstruction at `3/2`; corrected 2026-09-05).**
Let `(U_n, V_n) ∈ ℤ[x]²` be any sequence such that, for constants `σ, δ > 0` and `h ≥ 0`
independent of `n` and of the base,

1. `Λ_n(x) := U_n(x) F(x) − V_n(x) ≠ 0` for every real `x > 1`;
2. `deg U_n, deg V_n ≤ δ n² (1+o(1))`;
3. `log max(H(U_n), H(V_n)) ≤ h n² (1+o(1))`, where `H(P)` is the ℓ¹ coefficient
   norm. Intermediate Laurent expressions may be used only to estimate that
   norm; the final pair `(U_n, V_n)` lies in `ℤ[x]²`. A printed Laurent-polynomial
   domain is false: `U_n = X^{-n²}`, `V_n = 0`, `σ = 1`, `δ = 1/4` and height `1`
   meet those hypotheses and give `σ/(σ+δ) = 4/5 > 1/2`.
4. `log|Λ_n(x)| = −σ n² log x (1+o(1))` for every real `x > 1`.

Put `d_n := max(deg U_n, deg V_n)` (with the zero polynomial assigned degree zero).
Then `σ ≤ δ`, and for every fixed rational base `a/b > 1`,

```
limsup n→∞ n^(−2) log |b^{d_n} Λ_n(a/b)|
  ≤ δ log b − σ log(a/b).
```

Consequently the homogenised forms tend to zero whenever
`log b/log a < σ/(σ+δ)`. This is a sufficient region, not an exact decay
criterion under a degree upper bound. Its cutoff is at most `1/2`.

If the actual degrees additionally satisfy `d_n/n² → d`, then `d ≥ σ` and

```
lim n→∞ n^(−2) log |b^{d_n} Λ_n(a/b)| = d log b − σ log(a/b).
```

Thus the forms tend to zero below `log b/log a = σ/(σ+d)` and their absolute
values tend to infinity above it. At equality the normalized logarithm is
zero and these hypotheses alone decide neither behavior. Since `d ≥ σ`,
this exact-degree case cannot have decaying homogenised forms at `3/2`.

**Degree correction (2026-09-05).** The earlier statement inferred an exact
rate from `deg U_n,deg V_n ≤ δn²(1+o(1))` and used `deg U_n` to clear both
polynomials. An upper bound cannot give an exact threshold: increasing `δ`
preserves all four hypotheses but changes the asserted threshold. Both
coordinates must be cleared at their maximum degree. The separate claim
`σ ≤ δ` survives. Theorem A uses its explicitly proved exact degrees and is
unaffected. Even with exact degree convergence, a zero limiting rate does not
settle decay at the boundary.

Hypothesis 3 is the one missing from the first printed form of this theorem (found by the
adversary, attack 7): without it the exponent lemma's bound on `|U_n(p)|` does not follow from
the degree bound, and the printed statement is undecided as a claim, its proof invalid.
For Zudilin's family, §4 directly proves the exact degree and remainder
asymptotics. The published value bound (25), after multiplication by the
explicit normalizing factor, also gives the needed integer-base bound
`|U_n(p)| ≤ p^{(C₁−C₀)n²+o(n²)}`. This suffices for the exponent argument
below, without inferring a coefficient-height asymptotic from the recorded
finite coefficient computations. The theorem applies only to families
satisfying its stated hypotheses; these hypotheses do not define every
possible Padé construction.

Theorem A is the headline; Theorem B is its first consequence beyond the published
region; Theorem C says why the same mechanism cannot reach the problem's target base.

## 2. The published inputs, quoted as printed

Consumed by Theorem A: **Lemma 7** in its polynomial reading, together with the inputs of its
own proof (Lemma 3, Lemma 4's exponent `M(a;b)` of (16), Lemma 5 = Heine's transform, and the
identity (9)–(11)).  **Lemmas 1 and 2 are quoted below for orientation only**: the two
`φ(l)`-sum limits they encode have an elementary proof, given in (E6), so they are not part of
the citation set (adversary §3).  All from W. Zudilin, *Heine's basic transform and a permutation group for q-harmonic
series*, Acta Arith. 111.2 (2004) 153–164 (annex
`annexes/zudilin-2004-heine-q-harmonic-series/`, `extracted.md` line numbers in brackets).
Standing hypothesis of the paper (p. 154, Section 2): "Throughout the paper
`p = 1/q ∈ ℤ ∖ {0, ±1}`."  `D_n(p) := Π_{l=1}^{n} Φ_l(p)`, `Φ_l` the cyclotomic
polynomials.

**Lemma 1** (p. 155 [132–136], attributed to [BV, Section 2] and [Ass, Lemma 2]).
`lim_{n→∞} log|D_n(p)| / (n² log|p|) = 3/π²`.

**Lemma 2** (p. 155 [137–148], attributed to [Zu1, Lemma 1]). For each demi-interval
`[u, v) ⊂ (0, 1)` with `u, v ∈ ℚ`,
`lim_{n→∞} (1/(n² log|p|)) Σ_{l : {n/l} ∈ [u,v)} log|Φ_l(p)| = (3/π²)(ψ'(u) − ψ'(v)) = (3/π²) ∫_u^v d(−ψ'(x))`,
where `{a} = a − ⌊a⌋` and `ψ` is the logarithmic derivative of Euler's gamma function.

**Lemma 7** (p. 161 [451–462]). With `c = (c₀₀, c₀₁, c₁₁, c₂₁, c₁₂, c₂₂)`,
`c₀₀ = a₀+a₁+a₂−b−1, c₀₁ = a₀−1, c₁₁ = a₁−1, c₂₁ = a₂−1, c₁₂ = b−a₁−1, c₂₂ = b−a₂−1`,
`m(c) = max c`, `s(c) = b − a₁ − a₂`, `H(c) = F(a; b)` the series (9),
`M(c) = M(a; b)` the integer of (16) when (14) holds, and

```
ν_l := max{0, ⌊c₂₁/l⌋+⌊c₂₂/l⌋−⌊c₁₁/l⌋−⌊c₁₂/l⌋, ⌊c₀₁/l⌋+⌊c₂₁/l⌋−⌊c₀₀/l⌋−⌊c₁₂/l⌋},   (22)
Ω(p) := Π_{l=2}^{m(c)} Φ_l(p)^{ν_l} ∈ ℤ[p],
```

"We have `p^{−M(c)} D_{m(c)}(p) Ω^{−1}(p) H(c) ∈ ℤ[p] h_p(1) + ℤ[p]`, provided that
`s(c) > 0`."  Its proof (p. 161) is a computation in the polynomial ring: it combines the
inclusion (21) for the six images `gc`, `g ∈ G⁺`, with the Heine-transform stability
(Lemma 5) and the cyclotomic order formula (5), and ends "these polynomials are coprime to
the polynomial `p ∈ ℤ[p]`, we arrive at (23)."  The paper's own display (24),
`p^{−M} D_{mn}(p) Ω^{−1}(p) H_n ∈ ℤ[p]h_p(1) + ℤ[p] ⊂ ℤh_p(1) + ℤ`, distinguishes the
polynomial ring `ℤ[p]` from its evaluation `ℤ`, so `ℤ[p]` in Lemma 7 is the polynomial ring
in the symbol `p`.  This is the reading used below, and it is the only reading under which
the paper's own proof of Theorem 1 goes through.

Also used from the paper: the linear-form identity (9)–(11), `H_n = A_n h_p(1) − B_{1,n} − B_{2,n}`,
with `A_k` from (8) and `A, B₁, B₂ ∈ ℚ(p)` given by (10), (11); and the parameter
conventions of Section 5: `a_j = α_j n + 1`, `b = βn + 2`, `c_{00} = α₀+α₁+α₂−β`,
`c_{j1} = α_j`, `c_{j2} = β − α_j`, `m = m(c)`, so that for `(14,12,14;27)`:
`c = (13, 14, 12, 14, 15, 13)`, `m = 15`, `N := mn = 15n`, `M_n = 266n² + 34n + 1`
(from (16); Lean: `two_mul_zudilinM`), `s(c) = n > 0`, and (14) holds
(`12n+1 ≤ 14n+1`, `26n+2 ≤ 27n+2 ≤ 28n+2`).

Other literature: P. Bundschuh, K. Väänänen, *Arithmetical investigations of a certain
infinite product*, Compositio Math. 91 (1994) 175–199, Theorem 2 second half (p. 177):
for `α = −1` (the case `L_q(−1) = h_p(1)`) the hypothesis is
`λ < (1/2 + 1/π²)^{−1}` with `λ = log h(q)/log|q|_v`; for `q = a/b ∈ ℚ` this is
`log a / log(a/b) < (1/2 + 1/π²)^{−1}`, i.e. `log b/log a < 1/2 − 1/π²`.  This is the only
published rational-base criterion for `F` located; it is used here only for comparison.

## 3. Elementary facts with complete proofs

**(E1) `F(x) ∉ ℚ(x)`.** Use the Lambert representation `F(e^h)=∑_{m≥1}(e^{hm}-1)^{-1}`
and put `T=⌊1/h⌋`.  For `m≤T` one has `hm ≤ e^{hm}-1 ≤ (e-1)hm`, so the initial
sum has order `h^{-1} log(1/h)`.  For `m>T` one has
`(e^{hm}-1)^{-1} ≤ e^{-hm}/(1-e^{-1})`, whose sum is `O(h^{-1})`.  (The same
cutoff applied to `∑_m τ(m) e^{-hm}` does *not* give an `O(h^{-1})` tail: that
divisor-series tail is of order `h^{-1} log(1/h)`.)  Consequently
`(X-1)F(X)→∞` and `(X-1)² F(X)→0` as `X↓1`.  These two limits exclude every
possible pole order of a rational function.
∎

**(E2) Transfer of Lemma 7 to explicit polynomials.** Write
`Λ_n(x) := x^{−M_n} D_N(x) Ω_n(x)^{−1} H_n(x)` where `H_n = A_n F − B_n`, `B_n := B_{1,n} + B_{2,n}`,
`A_n, B_n ∈ ℚ(x)`.  Lemma 7 gives `U_n, V_n ∈ ℤ[x]` with `Λ_n = U_n F − V_n` as functions of
`x > 1`.  Then `(x^{−M_n} D_N Ω_n^{−1} A_n − U_n) F = x^{−M_n} D_N Ω_n^{−1} B_n − V_n` with
both coefficients in `ℚ(x)`; by (E1) the left coefficient vanishes identically, hence

```
U_n = x^{−M_n} D_N(x) A_n(x)/Ω_n(x),    V_n = x^{−M_n} D_N(x) B_n(x)/Ω_n(x)     in ℚ(x),
```

and Lemma 7 says these two rational functions are polynomials with integer coefficients.
∎  (Verified exactly, as an identity in `ℤ[x]`, for `n = 1, 2, 3`: `Ω_n | D_N A_n` and
`Ω_n | D_N B_n` with zero remainder, then `x^{M_n}` divides both quotients;
`formal_math/probes/erdos1049_zudilin_exact_forms.py`, and independently
`state/…/erdos1049_contour_adversary/zud_recon.py`, logs `n1.log, n2.log, n3.log`.)

**(E3) Degrees.** The `k`-th summand of `A_n(x) = Σ_{k=a₂}^{b−1} A_k x^{a₀k}` (from (8), with
`[m; j]_x` of degree `j(m−j)`) has `x`-degree
`d_k = a₀k + E_k + (a₁−1)(k−a₁) + (b−k−1)(k−a₂)`,
`E_k = a₁(a₁−1)/2 − (b−a₂)(b−a₂−1)/2 + (b−k)(b−k−1)/2`, and
`d_{k+1} − d_k = a₀+a₁+a₂−k−2 = 40n+1−k > 0` for `k ≤ b−2`.  So the degrees are strictly
increasing, no cancellation at the top is possible, and

```
K_n := deg A_n = d_{b−1} = (1091n² + 81n + 2)/2,     K_n/n² → 1091/2 = C₁.
```

(Lean: `twoMulZudilinSummandDegree_succ_sub`, `twoMulZudilinSummandDegree_top`,
`twoMulZudilinSummandDegree_step_pos`.)  Since `deg D_N = Σ_{l≤N} φ(l)`,
`deg Ω_n = Σ_{l=2}^{N} ν_l φ(l)`, and `deg B_n D_N ≤ K_n + deg D_N − 1` (each
`D_N/(x^l − 1)` has degree `deg D_N − l`), (E2) gives

```
deg U_n = W_n := K_n − M_n + Σ_{l≤N} φ(l) − Σ_{l≤N} ν_l φ(l),    deg V_n ≤ W_n − 1.
```

(Exact values `W₁, W₂, W₃ = 333, 1315, 2944`, leading coefficients `±1`, `V_n(0) = 1`,
`ord₀ U_n = 2n²`; both probes.)

**(E4) Positivity.** For real `x > 1`, `q = 1/x ∈ (0,1)`, every factor of
`R(q^t) = [(q^{t+1};q)_{a₁−1}/(q;q)_{a₁−1}] · [(q;q)_{b−a₂−1}/(q^{a₂+t};q)_{b−a₂−1}] · q^{a₀t}`
is positive for `t ≥ 0`, so `H_n(x) = Σ_{t≥0} R(q^t) > 0`; also `D_N(x) > 0`, `Ω_n(x) > 0`.
Hence `Λ_n(x) > 0`, in particular `Λ_n(x) ≠ 0`.  No determinant or Nesterenko-type
nonvanishing criterion is needed. ∎

**(E5) Archimedean size, uniform in the real base.** Each `q`-Pochhammer factor in `R(q^t)`
lies in `[(q;q)_∞, 1]`, so `(q;q)_∞² q^{a₀t} ≤ R(q^t) ≤ (q;q)_∞^{−2} q^{a₀t}` and

```
(q;q)_∞² ≤ H_n(x) ≤ (q;q)_∞^{−2}/(1 − q^{a₀}),    i.e.  log H_n(x) = O_x(1).
```

For `l ≥ 1`, `log Φ_l(x) = φ(l) log x + Σ_{d|l} μ(l/d) log(1 − x^{−d})`, and the correction is
at most `τ(l)·|log(1 − 1/x)|` in absolute value; summing over `l ≤ N` costs `O_x(N log N)`.
Therefore

```
log Λ_n(x) = −(K_n − W_n) log x + O_x(n log n) + O_x(1) = −(K_n − W_n) log x + o(n²).
```

(Checked numerically: residual `log Λ̂_n − (K log b − (K−W) log a)` equals `−0.257, +0.241, +0.117`
at `31/4` for `n = 1,2,3`, bounded as predicted; both probes.) ∎

**(E6) The limit `(K_n − W_n)/n² → C₀`, elementary.**
`K_n − W_n = M_n − Σ_{l≤N} φ(l) + Σ_{l≤N} ν_l φ(l)` with `N = 15n`.  Let
`Φ(y) := Σ_{l≤y} φ(l) = (3/π²) y² + O(y log y)` (Mertens' classical theorem).  Then
`Σ_{l≤N} φ(l) = (3/π²)·225 n² (1+o(1))`.  For the second sum, `ν_l = ω(n/l)` with the
1-periodic `ω(x) = max{0, ⌊14x⌋+⌊13x⌋−⌊12x⌋−⌊15x⌋, 2⌊14x⌋−⌊13x⌋−⌊15x⌋}` (Section 5 of the
paper; `ω ∈ {0,1}` for all `x`, since `⌊14x⌋+⌊13x⌋ ≤ ⌊27x⌋ ≤ ⌊12x⌋+⌊15x⌋+1` and
`2⌊14x⌋ ≤ ⌊28x⌋ ≤ ⌊13x⌋+⌊15x⌋+1`, and `ω = 1` exactly on the thirteen intervals), so
`Σ_{l=2}^{N} ν_l φ(l) = Σ_i Σ_{l : {n/l} ∈ [uᵢ, vᵢ)} φ(l)`; the constraint `l ≤ N` is automatic
since `{n/l} = n/l < 1/15 < 1/14 ≤ uᵢ` for `l > 15n`, and `l = 1` never contributes.  For one
interval `[u, v)`: `{n/l} ∈ [u, v)` iff `l ∈ (n/(k+v), n/(k+u)]` for some integer `k ≥ 0`.  The
block `k` contributes `Φ(n/(k+u)) − Φ(n/(k+v)) = (3/π²) n² (1/(k+u)² − 1/(k+v)²) + O(n log n)`;
the blocks with `k > K₀` all lie in `l ≤ n/(K₀+u)` and together contribute at most
`Φ(n/K₀) ≤ (3/π²) n²/K₀² (1+o(1))`.  Letting `K₀ → ∞` slowly with `n`,

```
Σ_{l : {n/l} ∈ [u,v)} φ(l) / n² → (3/π²) Σ_{k≥0} (1/(k+u)² − 1/(k+v)²) = (3/π²)(ψ₁(u) − ψ₁(v)),
```

and summing over the thirteen intervals,

```
(K_n − W_n)/n² → 266 − (3/π²)(225 − J) = C₀,     J = Σ_i (ψ₁(uᵢ) − ψ₁(vᵢ)).
```

This is the content of Zudilin's Lemma 2 (and Lemma 1), which is why the constant is the
paper's `C₀`; the lemmas themselves are not needed.  (If one prefers to cite them, their
integer instance `p = 2` implies the `φ`-statements via `log Φ_l(2) = φ(l) log 2 + O(τ(l))`,
`Σ_{l≤N} τ(l) = O(N log N)`.)  Numerically, `(K_n − W_n)/n² = 254.0, 237.25, 232.0, 229.44,
224.85, 221.63, 221.334, 221.309, 221.3017` at `n = 1, 2, 3, 4, 10, 100, 1000, 4000, 20000`
against `C₀ = 221.30009` (adversary, `adv_constants_region.log`). ∎

## 4. Proof of Theorem A

Fix coprime `a > b ≥ 1` with `θ = log b/log a < θ*`, set `x = a/b`.

*Step 1 (forms).* By (E2)–(E3), for each `n ≥ 1` there are `U_n, V_n ∈ ℤ[x]` with
`deg U_n = W_n`, `deg V_n ≤ W_n − 1`, and `Λ_n(a/b) = U_n(a/b) F(a/b) − V_n(a/b)`.

*Step 2 (homogenisation; the only non-Archimedean step).* Since `deg U_n, deg V_n ≤ W_n`,
`Û_n := b^{W_n} U_n(a/b)` and `V̂_n := b^{W_n} V_n(a/b)` are integers, and
`Λ̂_n := b^{W_n} Λ_n(a/b) = Û_n F(a/b) − V̂_n ∈ ℤ F(a/b) + ℤ`.
(`b^{W_n − 1} U_n(a/b) ∉ ℤ` at `31/4`, `7/2`: the degree is exactly `W_n`; probes.)

*Step 3 (nonvanishing).* `Λ̂_n > 0` by (E4).

*Step 4 (size).* By (E5), `log Λ̂_n = W_n log b − (K_n − W_n) log(a/b) + o(n²) = K_n log b − (K_n − W_n) log a + o(n²)`,
and by (E3), (E6), `log Λ̂_n / n² → C₁ log b − C₀ log a`, which is negative exactly when
`log b/log a < C₀/C₁ = θ*`.  So `Λ̂_n → 0`.

*Step 5 (conclusion).* If `F(a/b) = P/Q` with integers `Q ≥ 1`, then
`Q Λ̂_n = P Û_n − Q V̂_n` is a positive integer for every `n`, yet tends to `0`.
Contradiction. ∎

Every use of a real base `x = a/b` is in (E1), (E4), (E5), which hold for all real `x > 1`;
positivity (E4) is why only positive bases are treated.  The paper's hypothesis `p ∈ ℤ`
enters nowhere: Lemma 7 is a polynomial identity, and the `φ`-sum limits (E6) are elementary.
Exact reconstruction of the forms and of every degree/exponent claim above for `n = 1, 2, 3, 4`
(`M_n, deg D_N, deg Ω_n, K_n, W_n` = `(4393, 1102, 380, 8891, 5220)` at `n = 4`; identity to
relative `1e−97` at `31/4`): `state/public-source-redacted://erdos1049_region_adversary/REPORT.md`, attack 2.

*Proof of Theorem B.* `log 4/log 31 < 81/200` is `4^{200} < 31^{81}`
(`ZudilinHeightRegion.thirtyoneFour_power_certificate`), and `81/200 < θ*` is
`RationalBaseContour.eightyOne_twoHundredths_lt_zudilinContour`; the ratio is invariant under
`(a, b) ↦ (a^r, b^r)` (`zudilinContourRegion_pow`), and `(31^r, 4^r)` are coprime. ∎

## 5. Proof of Theorem C (the cap `b² < a`)

*Rational-base estimate.* Put `d_n = max(deg U_n,deg V_n)`. The exact identity

```
n^(−2) log |b^{d_n} Λ_n(a/b)|
 = (d_n/n²) log b − σ log(a/b) + o(1)
```

gives the asserted upper-limsup inequality and sufficient region. If
`d_n/n² → d`, it gives the exact limiting rate with `d` in place of `δ`.
A negative limit forces decay, a positive limit forces growth, and a zero
limit provides neither conclusion. The degree bound ensures that
`b^{d_n}U_n(a/b)` and `b^{d_n}V_n(a/b)` are both integers.

*Size of the forms at an integer base.* Fix an integer `p ≥ 2` and set `h_p := F(p)`,
`q_n := |U_n(p)|`, and `p_n := sign(U_n(p)) V_n(p)`. For all sufficiently large
`n`, `U_n(p) ≠ 0`: otherwise the nonzero integer `V_n(p)` would have absolute
value tending to zero. Thus `|q_n h_p − p_n| = |Λ_n(p)|` eventually.  By hypotheses 2 and 3,
`q_n ≤ (δn² + 1) H(U_n) p^{δn²} = e^{(h + δ log p) n² (1+o(1))}`; by hypothesis 4 the smallness
`|q_n h_p − p_n| = e^{−σ' n² (1+o(1))}`, `σ' := σ log p`, is two-sided.  Write
`δ' := h + δ log p`.  This is the step the first printed form lacked: `deg U_n ≤ δn²` alone
bounds `|U_n(p)|` only through `H(U_n)`, which was unconstrained.

*Exponent lemma.* Let `P/Q` be any rational with `Q` large and choose `n` minimal with
`|q_n h_p − p_n| < 1/(2Q)`; minimality gives `e^{σ' n²(1+o(1))} ≤ (2Q)^{1+o(1)}`.  If
`Q p_n − P q_n ≠ 0` then `|q_n Q (h_p − P/Q)| ≥ 1 − 1/2`, so
`|h_p − P/Q| ≥ 1/(2 Q q_n) ≥ Q^{−1−δ'/σ'−o(1)}`.  If `Q p_n = P q_n` then
`|h_p − P/Q| = |q_n h_p − p_n|/q_n ≥ e^{−(σ'+δ') n²(1+o(1))} ≥ (2Q)^{−(1+δ'/σ')(1+o(1))}`.
Hence `μ(F(p)) ≤ 1 + δ'/σ' = 1 + (h + δ log p)/(σ log p)`.

*Cap.*  An adjacent-integer argument, not requiring the integer-base irrationality of `F(p)` or Dirichlet, also yields `σ ≤ δ`. If `σ > δ`, choose an integer `p ≥ 2` with `(σ-δ) log p > h`. The values `a_n = U_n(p)`, `b_n = V_n(p)` are integers, `|a_n| ≤ exp((h+δ log p)n²+o(n²))`, and `|L_n| = |a_n F(p)-b_n| = exp(-σ log p n²+o(n²))`. The adjacent determinant `a_n b_{n+1}-a_{n+1} b_n = a_{n+1} L_n - a_n L_{n+1}` is then an integer tending to zero, hence eventually zero. Also `a_n ≠ 0` eventually. Thus `b_n/a_n` is a fixed rational `r`, and both `F(p) ≠ r` and `F(p) = r` contradict the hypotheses. The older exponent-lemma proof remains: `F(p)` is irrational for every integer `p ≥ 2` (Erdős 1948 for `p = 2`; Bézivin 1988, Borwein 1991 in general), so `μ(F(p)) ≥ 2` by Dirichlet, hence `(σ − δ) log p ≤ h` for every integer `p ≥ 2`.  Since `σ, δ, h` do not depend on `p` (hypotheses 3–4), letting `p → ∞` gives `σ ≤ δ`, i.e. `σ/(σ+δ) ≤ 1/2`.  For `3/2`, `θ = log 2/log 3 = 0.6309 > 1/2`. ∎

(When the coefficient heights satisfy `log max(H(U_n),H(V_n)) = o(n²)`, a
single integer `p` already gives `σ ≤ δ`; the limit `p → ∞` is what makes the
theorem hold for a fixed positive coefficient-height exponent `h`.)

*Actual-degree corollary.* If `d_n/n² → d`, the same argument applies with
the degree bound `d+ε` for every `ε>0`; hence `σ ≤ d+ε` for every `ε>0`
and `σ ≤ d`. This proves the exact-degree statement above without identifying
an arbitrary upper bound with the actual degree growth.

For Zudilin's family, (E3) gives the actual degree limit `d = C₁ − C₀`
and (E5)–(E6) give `σ = C₀`. Thus `σ/(σ+d) = θ*` and
`(σ+d)/σ = μ`. In this family, the rational-base threshold is the reciprocal
of the integer-base irrationality-exponent bound. The generic upper-bound
statement alone does not identify the exact threshold of an arbitrary family
or exclude every possible use of that family beyond its sufficient region.

Quantitative gap at `3/2` for this family: `C₁ log 2 − C₀ log 3 = +134.98879065… > 0` per `n²`,
against `log|Û_n| ≈ (C₁ − C₀) log 3 · n² = 356.18 n²`.  So an Archimedean-only argument would
need to remove a `2,3`-smooth content of logarithmic size `≥ 134.99 n²`, i.e. `37.9%` of the
height of `Û_n`, from the pair `(Û_n, V̂_n)`; the packet's measured content on the q-Apéry
diagonal is `gcd = 1` (`HomogenisationCeilingProof.md`).  Reaching `3/2` therefore needs a
family whose exponents are *not* uniform in the base (content imposed while the combination is
chosen: producer `congruence_constrained_adelic_hermite_pade`), or a higher-rank system with
full linear independence, not a different direction in the exact-degree, base-uniform class just proved.

*Direction search (falsifier for "a different `(a,b,c;d)` reaches further").* For every
primitive direction on Zudilin's cone `α₁ ≤ α₂`, `α₁+α₂ < β ≤ α₀+α₂` with all entries `≤ 30`
(37,533 directions), `θ*(dir) = C₀/C₁` computed from (25)–(26) is maximised by `(14,12,14;27)`
and its group image `(15,12,13;26)`, value `0.405683021384`; the next values are
`0.405639` (`(16,13,14;28)`), `0.405583`, `0.405521`.  Larger boxes were not scanned
(`formal_math/probes/erdos1049_zudilin_direction_search.py`, receipt
`…/erdos1049_zudilin_region/direction_search_bound30.json`; the bound-22 scan is also there).

## 6. The region, explicitly

`θ* = 0.40568302138406054101566030557693017464819107867787`; rational bracket from the
`k < 1000` partial sums of the trigamma series with the integral tail bound:
`0.4056830213 < θ* < 0.4056830214`; Lean: `81/200 < θ* < 1/2`.

Coprime `a/b` with `a ≤ 60` in the region: 137 bases, of which the non-integer ones are
`7/2, 9/2, …, 59/2` (all `b = 2`, `a ≥ 7` odd), `16/3, 17/3, 19/3, 20/3, 22/3, …, 59/3`
(`a ≥ 16`, `3 ∤ a`), `31/4, 33/4, 35/4, …, 59/4` (`a ≥ 31` odd), and
`53/5, 54/5, 56/5, 57/5, 58/5, 59/5`.  Closest misses: `52/5` (`θ = 0.407324`, short by
`0.00164`), `51/5`, `29/4` (`0.411694`, short by `0.00601`), `49/5`, `48/5`, `14/3`.
Tightest members: `53/5` (margin `0.000313`), `31/4` (margin `0.001985`), `54/5`.

Bases new relative to Bundschuh–Väänänen, i.e. in the strip `s^μ < r < s^{μ_BV}`,
`(s^μ, s^{μ_BV})`:

```
s=2: (5.52, 5.69) none      s=3: (15.00, 15.73) none      s=4: (30.48, 32.37) 31
s=5: (52.84, 56.65) 53, 54, 56          s=6: (82.82, 89.50) 83, 85, 89
s=7: (121.10, 131.75) 122,123,124,125,127,128,129,130,131
s=8: (168.31, 184.16) 169,171,…,183 (odd)   s=9: (225.00, 247.46) 15 bases   s=10: 12 bases
s=11: 37 bases   s=12: 17 bases
```

So `31/4` is the new base of smallest denominator and smallest numerator; the strip is
infinite: its width `s^{μ_BV} − s^μ` eventually exceeds `s`, so the strip
contains an integer congruent to `1 mod s` for every sufficiently large denominator.  The base `3/2` is at `θ = 0.630929753571…`,
a gap of `0.225247` above `θ*`. The exact-degree corollary of Theorem C
excludes decay at this base for families satisfying all of its hypotheses;
the generic degree-upper-bound conclusion alone is not a universal no-go.

## 7. Prior art and attribution

* Zudilin 2004 proves `μ(F(p)) ≤ 2.46497868…` for integer `p`; it states no rational-base
  result.  Theorem A is its forms placed in the Bundschuh–Väänänen height framework; the
  identity `θ* = 1/μ` (Theorem C) makes the relation exact.
* Bundschuh–Väänänen 1994 Theorem 2 (α = −1) gives the region `θ < 1/2 − 1/π² = 0.398679`
  (`= 1/μ_BV`) over number fields; `7/2` and all `b = 2, 3` members of the region above are
  already theirs.  Duverney 1996 Theorem 2 (per `prior_art_adjudication_2026_09_02.md`) is
  weaker (`0.23201`).
* Zudilin 2016, *On the irrationality of generalized q-logarithm*, Res. Number Theory 2
  (2016), Art. 15, §2 (annex `arxiv-1601-02688`, source lines 200–204): "the results can be
  given for non-integer `p = r/s`, `|p| > 1`, as well under a customary in such situations
  assumption `log|r| > c log|s|` for some computable constant `c > 0`" — for the generalized
  `q`-logarithm of that paper, no `c` computed.  The contribution here is the explicit
  constant for `F` itself, `c = μ_{Zudilin 2004} = 2.46497868…`, its consequences (the strip,
  `31/4`), and the observation that any such `c` equals the integer-base exponent bound.
* Matala-aho, Väänänen, Zudilin, *New irrationality measures for q-logarithms*, Math. Comp.
  75 (2006) 879–889, DOI 10.1090/S0025-5718-05-01812-0 (read in full by the prior-art pass,
  `prior_art_adjudication_2026_09_02.md` addendum, commit `dea7d99cff`): it treats only
  `p = 1/q ∈ ℤ ∖ {0, ±1}` (abstract p. 879; Theorems 1–2; the §3 convention), for
  `ln_q(1−z) = Σ z^ν q^ν/(1−q^ν)` with `z ∈ ℚ`, so it prints no rational-base region and
  cannot beat Bundschuh–Väänänen's `0.398679`.  On p. 880 it says: "Another special case,
  `z = 1` in (1), of the q-harmonic series, is considered in [Z2]. Our present methods do not
  allow us to sharpen the result in [Z2]", where [Z2] is Zudilin, Acta Arith. 111 (2004),
  the result homogenised here.  So the integer-base exponent `μ = 2.46497868…` remained the
  best printed bound for `F(p)` after 2006, and by Theorem C's identity `θ* = 1/μ` the
  region of Theorem A is the one this family of methods yields.  (Any future improvement of
  `μ(F(p))` by forms with `ℤ[p]`-integrality of Lemma-7 type and `p`-uniform size would
  enlarge the region to `1/μ_new` by the same proof; a bound `2.4234` would give `0.4126`
  and admit `29/4`.)
* Krattenthaler–Rochev–Väänänen–Zudilin 2009 (Acta Arith. 136) uses the same normalisation
  `γ = log|ρ|/log|σ| > c` for the `q`-exponential, not for `F`.

## 8. Classification of every step

| step | content | class |
|---|---|---|
| (9)–(11) identity `H_n = A_n F − B_n` | partial fractions, `|q| < 1` | (a) literature, valid for all real `x > 1` |
| Lemma 7 | `x^{−M} D_N Ω^{−1} H_n ∈ ℤ[x]F + ℤ[x]` | (a) literature, polynomial reading fixed by the paper's (24); (b) exact check `n ≤ 3` |
| (E1) `F ∉ ℚ(x)` | log singularity at `x → 1⁺` | (c) new, complete |
| (E2) transfer to explicit `U_n, V_n` | uniqueness from (E1) | (c) new, complete; (b) exact `n ≤ 3` |
| (E3) degrees, `K_n`, `W_n` | integer identities | (b) Lean `RationalBaseContour` + probes |
| (E4) positivity | product of positive factors | (c) new, complete |
| (E5) Archimedean size | Pochhammer bounds, cyclotomic tail | (c) new, complete; (b) numerics |
| (E6) `(K_n − W_n)/n² → C₀` | Mertens plus the block decomposition of `{n/l} ∈ [u,v)` | (c) elementary, complete (Lemmas 1–2 not needed; adversary §3) |
| Steps 1–5 | homogenisation and contradiction | (c) new, complete |
| `81/200 < θ* < 1/2`, `31/4`, powers, `3/2` excluded | finite trigamma sums, `π` bounds | (b) Lean, axioms `propext, Classical.choice, Quot.sound` |
| Theorem C (corrected form) | exponent lemma, coefficient-height bound, Dirichlet, and `p → ∞`; exact-degree corollary separate | (c) ordinary proof corrected 2026-09-05: upper-limsup sufficient region, `σ ≤ δ`, exact rate only under degree convergence, boundary undecided. The published (25) supplies a value bound, not a proof of a coefficient-height asymptotic. |

Every step is (a), (b), or (c) with a complete proof.  The evidence class of Theorems A–C is
therefore **ordinary complete proof citing published lemmas**, an unconditional theorem in the
usual mathematical sense; the citation set is Zudilin 2004 Lemma 7 with Lemma 3, Lemma 4's
(16), Lemma 5 and the identity (9)–(11).  What is not kernel-checked: Lemma 7 and its inputs
(published; re-derived at the UFD level and verified exactly for `n ≤ 4` by the adversary),
the identity (9)–(11), (E1), (E2), (E4), (E5), (E6), the exponent lemma, and the limit passage
in Step 4.
What is kernel-checked: the finite part listed in `RationalBaseContour.lean` (build rc 0,
2778 jobs, no warnings; `#print axioms` on the fourteen named declarations shows only
`propext, Classical.choice, Quot.sound`, the integer identities only `propext, Quot.sound`).

## 9. Receipts

* `formal_math/probes/erdos1049_zudilin_region.py` → `state/public-source-redacted://erdos1049_zudilin_region/region_receipt.json`
* `formal_math/probes/erdos1049_zudilin_direction_search.py 30` → `…/direction_search_bound30.json` (and `bound22`)
* `formal_math/probes/erdos1049_zudilin_c0_c1_check.py`, `formal_math/probes/erdos1049_zudilin_exact_forms.py`, and the adversarial reconstruction `state/…/erdos1049_contour_adversary/` (constants, exact forms `n ≤ 3`)
* Lean: `ErdosProblems/Erdos1049/RationalBaseContour.lean`, build via `scripts/lean_fast_build.py --jobs 2 ErdosProblems.Erdos1049.RationalBaseContour`
* Derivation history: `ZudilinRationalHomogenisationDerivation.md` (2026-09-02), Type B attachment `attachments/typeb_return_8a7ad785.txt`
* Independent adversary (commit `b7a2783559`): `state/public-source-redacted://erdos1049_region_adversary/REPORT.md` with `adv_constants_region.py`, `adv_exact_forms.py` (exact `n ≤ 4`), `adv_theorem_c_heights.py` (coefficient heights); Theorems A, B survived all eight attacks, Theorem C corrected as above

## 10. Correction block, 2026-09-06 (appended; nothing above is rewritten)

Corrective-integration pass for #1049. Every item below was read this pass from the file named
in it. The mathematics of Theorems A and B is unchanged; what changes is the evidence status of
two sentences in §8 and the scope wording of one sentence in §5.

**(C1) The `#print axioms` sentence in §8 is not reproducible from the audited surface.**
§8 says "What is kernel-checked: the finite part listed in `RationalBaseContour.lean` (build rc 0,
2778 jobs, no warnings; `#print axioms` on the fourteen named declarations shows only
`propext, Classical.choice, Quot.sound`, the integer identities only `propext, Quot.sound`)."
Read this pass: `ErdosProblems/Root.lean` imports eleven `Erdos1049` modules
(`RationalBaseLambert`, `RationalPadeArithmetic`, `ZudilinHeightRegion`, `HermitePadeNoGo`,
`ZudilinConeArithmetic`, `AdelicHeightBridge`, `BezoutPluckerJets`, `TwoSelectorRemainderEscape`,
`QAperyTailDenominator`, `SoutheastBlockDeterminant`, `FixedDiagonalRationalClearing`) and does
not import `RationalBaseContour`; `ErdosProblems/AxiomAudit.lean` names no declaration from it;
and the build receipt itself was not located on disk. The declarations of
`RationalBaseContour.lean` are real and were read this pass at lines 159, 180, 201, 214, 232, 251,
266, 270, 279, 296, 317, 337, 344 and 350. The axiom statement is therefore `reported_prior`
until the module is added to `Root.lean`, its declarations are named in `AxiomAudit.lean`, and a
build receipt is on disk. No build was run this pass.

**(C2) The evidence class of Theorems A and B is unchanged and is restated for the record.**
Ordinary complete proof citing published lemmas. The citation set is Zudilin 2004 Lemma 7 in its
polynomial reading, together with the inputs of that lemma's own proof: Lemma 3, the exponent
`M(a;b)` of (16) supplied by Lemma 4, Heine's transform as Lemma 5, and the identity (9)–(11).
Lemmas 1 and 2 are not in the citation set, since (E6) replaces them. Two other surfaces disagreed
with this and are corrected by the companion patch
`docs/strategy/staging/rapid_breakout/audit/patches/frontier_1049.json`: the claim-frontier row
`erdos1049.f_31_over_4_irrational_conditional` carried evidence class
`conditional_on_named_lemmas` and the citation set "Lemma 7 and Lemma 2", and
`docs/formal_math/palomar/longitudinal_truth_2026_09_01.md` line 69 carried "Lemma 7 and Lemma 2".
This file is the authority for the citation set.

**(C3) §5's `3/2` sentence is a statement about this family, not a universal no-go.**
§5 ends "Reaching `3/2` therefore needs a family whose exponents are *not* uniform in the base …,
or a higher-rank system with full linear independence, not a different direction in the
exact-degree, base-uniform class just proved." That is correct as written, and it is worth stating
the boundary once more in the terms of the corrected Theorem C: under the degree upper bound alone
the conclusion is a **sufficient** decay region with cutoff at most `1/2`, and the statement that
there are no decaying homogenised forms at `3/2` belongs to the **exact-degree** case
`d_n/n² → d`. Neither form excludes every possible Padé construction. The precise negative label
for this result is `proved_class_obstruction` scoped to families satisfying hypotheses (1)–(4).

**(C4) Numbers re-verified against receipts this pass.** From
`state/public-source-redacted://erdos1049_zudilin_region/region_receipt.json`:
`theta_star = 0.40568302138406054101566030557693017464819107867787`,
`mu = 2.464978683574975037454488275535521581878`,
`C0 = 221.3000881650050251240426966922154102706`,
`J = 77.94318447500909592258956702399211044972`,
`theta_31_4 = 0.4036981731641997014370328005878493650194`,
`theta_3_2 = 0.6309297535714574370995271143427608542996`,
`gap_3_2 = 0.225246732187396896083866808766`,
`bv_threshold = 0.3986788163576622285561205367902723610956`,
`c_bv_normalisation = 2.508284761994681157505052751018958770537`,
`s = 4` strip `(30.483515, 32.369642)` with the single new numerator `31`,
`137` members with `a ≤ 60` of which `78` are non-integral, tightest members `53/5` and `31/4`,
closest miss `52/5` at `0.40732438367834206972`. From `direction_search_bound30.json`:
`37533` directions scanned, best `0.40568302138406054` at `(14,12,14;27)` and `(15,12,13;26)`,
next `0.4056394327738419` at `(16,13,14;28)`. The bound-30 scan is a bounded-box falsifier,
not an optimality theorem among all admissible directions. Every figure printed in §§1, 5 and 6 above agrees
with these receipts. No number required correction.

**(C5) The adversary verdict is now first-hand.**
`state/public-source-redacted://erdos1049_region_adversary/REPORT.md` was opened
this pass. Its §0 verdict table reads SURVIVES for attacks 1–6 and 8; attack 7 is against
Theorem C's hypotheses alone and is the correction already carried in §1 above. The header
sentence "Theorems A and B survived all eight attacks" is therefore `verified_current` rather than
`reported_prior`.
