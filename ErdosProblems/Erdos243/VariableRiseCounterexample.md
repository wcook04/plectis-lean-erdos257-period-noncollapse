# Unrestricted variable-rise envelopes fail (ordinary, not a parent theorem)

Type B r4, 7 September 2026.  This is an ordinary complete proof that the
candidate little-o envelope in the live `res:variablerise` (any unbounded
nondecreasing `ω`) does not force a CRT contradiction, even under a stronger
coprimality condition than old-modulus avoidance.  It is not a reciprocal-tail
orbit, not a parent counterexample to Erdős #243, and not a Lean theorem this
wave.

The bounded-rise theorem `bounded_rise_reduced_tail_excluded` is unchanged.

## Theorem A

Let `ω : [1, ∞) → (0, ∞)` be nondecreasing with `ω(x) → ∞`.  There are
distinct increasing primes `p_j` and a strictly increasing sequence of
positive integers `u_n → ∞` such that

```
gcd(u_n, p_j) = 1  for every n, j,
u_{n+1} − u_n = o(ω(u_n)).
```

The gaps `u_{n+1} − u_n` are nevertheless unbounded.

## Proof

Choose the primes successively so that

```
p_j ≥ 2^{j+3},     ω(p_j / 2) ≥ j²,
```

with indices starting at one.  Both requirements are eventually satisfied as
a prime tends to infinity.  Put

```
σ₀ = ∑_{j≥1} p_j^{-1} < 1/4,
A = { m ≥ 1 : p_j ∤ m for every j }.
```

For every `X`, the union bound gives

```
#(A ∩ [1, X]) ≥ ⌊X⌋ − ∑_{p_j ≤ X} ⌊X / p_j⌋ ≥ ⌊X⌋ − σ₀ X.
```

Thus `A` is infinite; enumerate it as `u_1 < u_2 < ⋯`.

Fix a sufficiently large member `u` and write

```
k = k(u) = #{ j : p_j ≤ 2u },     H = 2k + 2.
```

The exponential lower bound on `p_j` gives `k = O(log u)`, hence `H ≤ u` for
large `u`.  Every number in the integer interval `(u, u+H]` is at most `2u`,
so only the first `k` primes can exclude it.  The number excluded is at most

```
∑_{j≤k} (H / p_j + 1) ≤ H σ₀ + k < H.
```

At least one member of `A` therefore lies in that interval.  Consequently the
next gap is at most `2k+2`.  Since `p_k ≤ 2u`, monotonicity gives
`ω(u) ≥ ω(p_k / 2) ≥ k²`.  As `u → ∞`, also `k(u) → ∞`, and

```
0 < (u_{n+1} − u_n) / ω(u_n) ≤ (2k(u_n) + 2) / k(u_n)² → 0.
```

Finally, for every fixed integer `L`, CRT supplies arbitrarily late blocks of
`L` consecutive integers with the `i`-th integer divisible by a different
selected prime.  Such a block contains no member of `A`, so the gaps are
unbounded.

## Consequence

Take `ω(x) = log log(x+3)`.  The proposed little-o condition fails to exclude
an unbounded avoidance sequence even when every numerator is coprime to every
modulus, including future moduli.  Old-modulus coprimality
`gcd(m_i, u_t) = 1` for `i < t` follows by taking `m_i = p_i`.

The primes constructed here can be enormously sparse.  They have no imposed
relation to the multipliers of an exact reciprocal-tail orbit.  No
denominators `v_n`, multipliers `a_n`, or exact cancellation factors have
been constructed.  A useful variable-rise barrier must therefore retain
quantitative modulus-growth or activation information (canonical orbits supply
`log a_n ≍ 2^n`).

Finite checks live in `scripts/check_erdos243_r4_revision_claims.py` (gap
counting for a constructed prime prefix; CRT blocks; the identity `σ₀ < 1/4`
on that prefix).  The universal quantifier over `ω` is not Lean this wave.
