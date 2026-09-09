# Erdős #249: the all-base totient kernel — dimension, basis and relation module

Fix an integer base `k ≥ 2` and write

\[
F_{j,r}(n)=\varphi\!\left(k^{j}n+r\right),\qquad 0\le r<k^{j}.
\]

The *`k`-kernel through level `e`* is the family `{F_{j,r} : j ≤ e, r < k^j}`.  It
has `1+k+\cdots+k^{e}` members.  The compared structure theorem determines its
linear algebra completely, for every base at once:

- the canonical subfamily — the two zero-residue channels `F_{0,0}`, `F_{1,0}`
  together with one channel per residue `1 ≤ r < k^{j}` with `k \nmid r` at each
  level `1 ≤ j ≤ e` — is linearly independent over `ℚ`;
- it spans the whole level-`e` kernel;
- it therefore indexes a basis of that span;
- the span has dimension exactly `k^{e}+1`;
- the relation module — the kernel of the evaluation map from the free module on
  the `1+k+\cdots+k^{e}` formal symbols — has dimension exactly
  `k+k^{2}+\cdots+k^{e-1}`.

The residue condition is `k \nmid r`, **not** `\gcd(k,r)=1`.  At a composite base
a canonical residue may share a proper prime factor with `k`, and the
composite-residue reduction carries the scalar
`\varphi(k)\gcd(k,u)/\varphi(\gcd(k,u))` rather than `\varphi(k)`.  That scalar is
where a coprimality-shaped index would be wrong.

Two reductions give the spanning half: `F_{j+1,0}=k^{j}F_{1,0}`, and a residue
divisible by `k` drops one level with the scalar above.  Independence is proved
by restricting to the progression `n=km+1`, where every canonical channel becomes
a positive affine totient form and `k \nmid r` is exactly pairwise
non-proportionality, and then applying the all-slope auxiliary-prime row: for
pairwise non-proportional positive affine forms there is an odd prime `ℓ` and
evaluation rows making the totient matrix diagonal and nonsingular mod `ℓ`, with
no odd-slope and no primitivity hypothesis.  The relation dimension is
rank–nullity against the exact rank.

The second compared declaration states that all-slope affine independence on its
own, in pure Mathlib vocabulary.

## Mathematical boundary

Nothing here bears on Erdős #249.  The problem asks for irrationality of
`\sum \varphi(n)/2^{n}`; this is a rank, basis and relation statement about the
`k`-kernel span.  Reading it as parent progress is the error this section exists
to block.

Two attributions must be kept straight.

- **Independence is Martin's.**  Greg Martin, *Simultaneous inequalities among
  values of the Euler phi-function* (arXiv:math/0603053), Theorem 1 already
  subsumes the affine-forms conclusion.  The declaration here is a Lean-checked
  restatement of a consequence of that theorem, and it is labelled as such in
  `formalization.yaml`.
- **Non-`k`-regularity is Coons's.**  Michael Coons, *(Non)Automaticity of number
  theoretic functions*, J. Théor. Nombres Bordeaux 22 (2010) 339–352, Theorem 3.2
  owns the statement that `\varphi` is not `k`-regular, equivalently that the full
  kernel span is infinite-dimensional.  That must never be claimed here.

What has no located antecedent is the exact bounded-depth dimension `k^{e}+1`,
the canonical index, the explicit basis and the relation-module dimension.  The
search was not exhaustive, so the novelty of those is recorded as unassessed.

The integral extension constructs a basis of elementary two-term reduction
relations: each omitted channel contributes `E_i - a E_j`, with a retained
channel `j` and a natural scalar `a`. Its rank is `k+⋯+k^(e-1)`.
The canonical channels also form an integral basis of the channel span.

## Package

`Challenge.lean` imports only Mathlib and redefines the kernel channel, the
canonical index and residue, the through-level family and the relation map in its
own vocabulary.  `../Solutions/ExternalVerification249TotientKernelBasis.lean` identifies each definition with its counterpart
in `Erdos249257/AllBaseTotientKernel.lean` and applies the checked
source theorems. The deliberate negative fixture in
`../NegativeSolutions/ExternalVerification249TotientKernelBasis.lean` gives each
selected declaration the statement `True`, so it must fail statement comparison.

## Verification state

The source integral-basis theorem is compiled and axiom-audited. This exported
package relocates the supplier outside the protected Challenge directory.
Its public Linux Comparator replay, including the deliberate mismatch, remains
pending. No Comparator verdict, Palomar outcome, novelty ruling, or submission
is claimed. The CI receipt binds any eventual result to the exact public commit,
configuration, tool revisions, and binary hashes.
