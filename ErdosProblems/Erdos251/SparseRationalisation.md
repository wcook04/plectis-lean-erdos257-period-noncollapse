# Erdős #251: sparse congruence-preserving rationalisation (ordinary, unreviewed)

Type B r5 mathematics. The live flagship still opens with the polynomial
complete-tail countermodel, and Theorem~1 remains the lcm-diagonal classifier:
those are the checked parent-problem statements. The sparse existence result
is now a displayed proposition `\ref{res:sparserationalisation}` in the short
note, not a title or Theorem~1 swap. Pair/buffer identities and
variable-alphabet filling are Lean-checked in `SparseRationalisationCore.lean`
(focused Lake exit 0, job `cf_a250f39dc0044c22abdf`); the location schedule
and block-law transfer remain ordinary. Palomar remains
`ExternalVerification251PolynomialShiftCountermodel` with the polynomial word
`a_n=2(n^2+4n+2)`, `U_N=2(N+4)^2`, series `32`. Parent (actual prime-gap
series) remains open.

Source of the ordinary proofs:
`public-source-redacted://state/type_b_return_batches/erdos_revision_packets_r5_20260907/work/erdos_251/erdos_251_revision_packet_r5/02_research_memorandum.md`.
Finite algebra: `scripts/test_sparse_core.py` (integers and `Fraction` only;
no prime data). Lean core (variable-alphabet greedy filling and pair/buffer
identities, **not** the full schedule): `SparseRationalisationCore.lean`.

## Claim boundary

Does **not** prove:

- irrationality or rationality of the unmodified prime-gap series;
- a new prime-gap distribution law;
- the missing prime-specific circular-arc / dispersion lower bound;
- growing-block nonconcentration (Kuperberg remains `blocked_external`);
- a Lean existence theorem for the sparse location schedule.

The theorems concern arbitrary summable nonnegative integer words, then a
quantitative specialisation to prime gaps that *preserves* short-block
empirical laws under a sparse perturbation. Preservation is not a theorem
that those laws hold.

## Mechanism

Constraint separation:

1. neighbouring corrections with a digit-independent unweighted total
   `M d + M(D-d) = M D` and a free weighted digit
   `M(D+d)/2^{n+2}`;
2. a buffer `c = (-C) mod M` that repairs the new cumulative modulus without
   knowing the free digits, and that preserves earlier moduli because
   `M_{j-1} | M_j`;
3. variable digit capacity `D_j = 2^{\ell_{j-1}}-1` using the *preceding*
   spacing, so the capacity telescope supplies the Kakeya overlap
   `w_j \le \sum_{i>j} D_i w_i` without assuming decreasing weights;
4. greedy interval filling for a variable alphabet.

This generalises the r4 elementary pair core (`PairedCongruenceRationalisation.lean`,
fixed `D=3`) rather than repeating it.

## Theorem 2.1 (sparse congruence-preserving rationalisation)

Let `a_n` be nonnegative integers with `S(a)=A<\infty`, `K∈ℕ`, and
`f:ℕ→ℝ` tending to `+∞`. There exist a set `S⊆[K,∞)` of upper Banach
density zero and a nondegenerate interval `I⊂(A,∞)` such that every
`r∈I` is realised by a nonnegative correction `e` with
`supp(e)⊆S`, `0≤e_n≤f(n)` eventually, `S(a+e)=r`, and, for every fixed
`q≥1`, eventually `q | e_n` and `q | ∑_{i<n} e_i`. The same `S` and
correction-value interval work for every input sequence `a`. The
construction can also satisfy `e_n=o(log(n+3))`.

## Lemma 2.2 (variable-alphabet interval filling)

If `w_j>0`, `D_j∈ℕ_{>0}`, `V=∑ D_j w_j <∞`, and `w_j ≤ ∑_{i>j} D_i w_i`,
then `{∑ d_j w_j : 0≤d_j≤D_j} = [0,V]`.

Lean names the greedy core as `exists_digits_hasSum_of_capacity` under
explicit capacity/overlap/vanishing hypotheses. The sparse *schedule* that
produces those hypotheses is ordinary, not Lean.

## Theorem 3.1 (unnormalised block-law preservation)

For `0<ε<1` the actual prime gaps admit a nonnegative perturbation `b`
with rational dyadic sum, prescribed prefix, `b_n-g_n ≤ (log(n+3))^ε`
eventually, evenness for `n≥1`, eventual preservation of every fixed
modulus for coefficients and cumulative sums, and
`|S∩[X,2X)| = O_ε(X/log log X)` where `S={n:b_n≠g_n}`. For block length
`m=o(log log X)` the empirical laws of unnormalised `m`-blocks on
`[X,2X)` have total-variation distance `o(1)`, uniformly over bounded
tests. No limiting gap law is assumed or proved.

Section 3.3: the same construction also preserves every modulus
`q ≤ c log log n / log log log n` at each sufficiently large `n`, for an
explicit allowed `c`. Growing moduli in that range are not a qualitative
escape.

## Propositions 4.1–4.2 (entropy)

Fixed support of size `o(N/log log N)` with polylog amplitude yields a
correction-value set of Hausdorff dimension zero. Adaptive support with
density parameter `δ` and amplitude exponent `α` satisfies
`dim_H E_δ ≤ min{1, α δ / log 2}`. Bounded alphabets on density-zero
supports cannot fill an interval. The construction of Theorem 3.1 matches
the *order* of this trade-off, not an optimal constant.

## Residual

The circular-arc statistic `E_t(X,L,K)` remains a sufficient ordinary
criterion (r4); its actual-prime lower bound is unproved. Subcritical
local laws are preserved by the rational model; a distinguishing estimate
must exceed the block-change error or use a longer window / different
invariant.

## Long-record destinations (labels only; no R-checkout mutation this wave)

- `sec:sparse-rationalisation` after the perturbation discussion in
  `sec:obstructions`; owner is Theorem 2.1 here.
- Block-law transfer and adaptive-support entropy beside it, before the
  actual-prime sufficient inequality.
- Density-zero inference after `res:sparse`: keep the density-zero theorem;
  replace the false “excludes every average” sentence by sparse-averaging
  language already landed in the short note at r4.
- `family_catalogue.tex` actual-tail row: bridge occupied; supply open.
- `extended_record.tex` `sec:xr-divisorhit` / `xr:divisor-hit`: equivalent
  quantifiers, not a strict implication gain.
- Statistical comparison next to `sec:xr-compression` and the mean-tail
  laboratory.
