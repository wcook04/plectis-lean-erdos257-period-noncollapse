# Cover-independent first logarithmic moment, exact cube cost, and \(A_W\)

Ordinary proofs from Type B r4. Historical novelty unassessed. None of
this replaces the Lean-checked reciprocal-summable theorem, which remains
the paper lead and the Palomar flagship. None of it closes universal
#257, membership of \(1/2\), or membership of \(1/21\).

Notation collision: the r3 squarefree support outside every *old* cover
is \(A^\star\) (cover class \(V\), not weighted \(W\)). The new support
below is \(A_W\) (weighted class \(W\), not cover \(V\)). Do not rename
\(A_W\) to a second \(A^\star\); the long record already overloads that
star. r3 leftover \(A^\star\) / variable-exponent cost stays ordinary.

## B.0. Optimised cover cost

For finite \(G\) set \(f_G(n)=\#\{a\in G:a\mid n\}\). A positive cover
consists of finite sets \(G_j\), exponents \(0<\alpha_j\le 1\), weights
\(\eta_j>0\) with \(\sum\eta_j=1\), and coefficients \(c_{j,d}\ge 0\)
satisfying
\[
f_{G_j}(n)^{\alpha_j}\le\sum_{d\mid n}c_{j,d},\qquad
C_j=\sum_d c_{j,d}/d.
\]
It covers \(A\) if \(A\subseteq\bigcup_j G_j\). Its strengthened cost is
\[
K=\sum_j\frac{C_j\eta_j^{-\alpha_j}}{2^{\alpha_j}-1}.
\]
Write \(K_*(F)\) for the infimum of \(K\) over covers of a finite \(F\).
The existing strengthened irrationality theorem applies when \(K\) is
finite. Its special \(\eta_j=2^{-j}\) version is the registered r3
statement.

## B.1. Cover-independent first-logarithmic-moment obstruction

Define \(\Psi(0)=0\) and, for \(t\ge 1\),
\[
\Psi(t)=\inf_{0<\alpha\le 1}\frac{t^\alpha}{2^\alpha-1}.
\]
Every cover of \(A\) with cost \(K\) satisfies, for every finite
\(F\subseteq A\),
\[
K\ge\mathbb E_F\Psi(f_F)\ge e\,\mathbb E_F\log^+ f_F.
\]
Unbounded periodic first logarithmic moments over finite subsets exclude
every strengthened cover, including every choice of \(\eta_j\),
\(\alpha_j\), ordering, and overlaps.

**Proof.** For \(t=f_F(n)>0\), coverage gives \(\sum_j f_{G_j}(n)\ge t\),
so some \(j\) has \(f_{G_j}(n)\ge\eta_j t\). At this \(n\), the majorant
and nonnegativity give a lower bound \(\Psi(t)\). Average over
\(1\le n\le X\); Tonelli and \(\lfloor X/d\rfloor/X\le 1/d\) bound the
left by \(K\). The right is periodic, so the limit is
\(\mathbb E_F\Psi(f_F)\). Convexity \(2^\alpha-1\le\alpha\) on
\([0,1]\) yields \(\Psi(t)\ge e\log t\) for \(t>1\). ∎

**Exact gauge.** Differentiating \(\alpha\log t-\log(2^\alpha-1)\) yields
\[
\Psi(t)=
\begin{cases}
t,&1\le t\le 4,\\
\dfrac{u^u}{(u-1)^{u-1}},&t\ge 4,\quad u=\log_2 t.
\end{cases}
\]
For \(t\le 4\) the minimum is at \(\alpha=1\); for \(t>4\) one has
\(2^\alpha=u/(u-1)\). Thus \(\Psi(t)\) is asymptotic to \(e\log_2 t\),
not to a square of a logarithm. This is a different obstruction from the
r3 logarithmic-square bound on *old* covers.

## B.2. Asymptotically exact divisor-cube cost

Let \(q\ge 2\), let \(P\) be a finite set of primes none dividing \(q\),
let \(M=\prod_{p\in P}p\), and set
\[
F(q,P)=\{qd:d\mid M\},\qquad S=\sum_{p\in P}1/p.
\]
If \(S\ge 1\), then
\[
\frac{e(S-1)}{q}\le K_*(F(q,P))\le\frac{eS}{q}.
\]
In particular \(K_*(F(q,P))=(e+o(1))S/q\) as \(S\to\infty\). The relative
error bound is uniform in \(q\) and in the particular prime set \(P\).

**Lower bound.** On the event \(q\mid n\), which has density \(1/q\), one
has \(f_F(n)=2^Z\) with \(\mathbb EZ=S\). For integers \(z\ge 2\),
\(\Psi(2^z)>e(z-1)\), and the inequality also holds at \(z=0,1\). Apply
B.1.

**Upper bound.** Cover \(F\) by itself with \(\eta=1\) and
\(\alpha=\log_2(1+1/S)\). The exact expansion of \(f_F(n)^\alpha\) is a
divisor majorant of cost at most \(eS/q\).

This is a quantified scale for the cover method on these frames. It does
not prove optimality of the general irrationality method, and it does
not close the parent.

## B.3. A weighted support outside every strengthened cover

There is an infinite support \(A_W\) such that:

1. the finite-prime weighted criterion with \(P=\{2\}\) holds, hence
   every infinite subset of \(A_W\) has irrational subseries at every
   integer base;
2. the reciprocal sum over \(A_W\) diverges;
3. no strengthened positive cover of \(A_W\) has finite cost, even with
   arbitrary \(\eta_j\).

**Construction.** Choose pairwise disjoint finite blocks \(P_k\) of odd
primes, \(k\ge 2\), with \(2^{k-2}\le S_k:=\sum_{p\in P_k}1/p\le 2^{k-2}+1\).
Set \(M_k=\prod_{p\in P_k}p\), \(F_k=\{2^k d:d\mid M_k\}\), and
\(A_W=\bigcup_{k\ge 2}F_k\). Distinct frames have distinct exact
\(2\)-adic valuations, so they are disjoint.

**Weighted summability.** The base-\(2\) weighted sum over \(P=\{2\}\) is
\[
W_{2,\{2\}}(A_W)
=\sum_{k\ge 2}\frac{\prod_{p\in P_k}(1+1/p)}{2^{2^k}-1}
\le 2e\sum_{k\ge 2}\exp\bigl[-(\log 2-1/4)2^k\bigr]<\infty.
\]
The existing weighted theorem and monotonicity under thinning give
hereditary all-base irrationality.

**Failure of every strengthened cover.** On the disjoint events
\(v_2(n)=k\) of density \(2^{-k-1}\), the first logarithmic moment of a
finite union of frames tends to infinity. Apply B.1.

**Reciprocal divergence.** Frame \(k\) has mass
\(2^{-k}\prod(1+1/p)\), which tends to infinity by
\(\log(1+t)\ge t-t^2/2\) and \(\sum p^{-2}<\infty\).

This applies the already established weighted theorem. It is not a new
irrationality endpoint, and it does not close the parent.

## B.4. Incomparability of cover class \(V\) and weighted class \(W\)

Let \(W\) be the union of support classes admitted by all finite-prime
weighted criteria, and \(V\) the class admitted by the strengthened
positive-cover criterion. The registered r3 support \(A^\star\) belongs
to \(V\) but not \(W\). The new \(A_W\) belongs to \(W\) but not \(V\).
Thus \(W\not\subseteq V\) and \(V\not\subseteq W\).

Neither method replaces the other.

**r4 open union (chronological).** A union \(A_W\cup A^\star\) is not
proved irrational merely because both summands are; that would need
synchronised small positive displacements
\(\Delta_{2,A_W}(N)+\Delta_{2,A^\star}(N)\), which r4 did not supply.

**r5 mixed theorem (ordinary).** The finite dyadic-shell estimate
\(\mathscr D_{L;R,M}w_{B,d}\le(1+4L/M)/(d(B-1))\) supplies a common
finite averaging scheme. Every infinite \(A\subseteq E\cup V\) is then
irrational at every integer base, where \(E\) has finite finite-prime
weighted mass and \(V\) admits a strengthened positive cover. In
particular every infinite subset of \(A_W\cup A^\star\) is covered,
although that mixed host lies in neither individual class. The generated
finite-union ideal \(\mathcal H\) strictly contains \(W\cup V\). Proof:
`MixedSupportSynchronisation.md`, Theorems 2.1 and 5.1. Finite checks:
`scripts/check_synchronisation.py --quick`. This does not decide \(1/2\)
or \(1/21\), and does not replace the reciprocal-summable flagship.

## C.1. Base monotonicity of displacements (ordinary)

For integers \(0\le r<d\) and real \(1<x\le y\),
\[
0\le\frac{y^r-1}{y^d-1}\le\frac{x^r-1}{x^d-1}.
\]
Consequently, for any support \(A\) and any integer \(N\ge 0\),
\[
0\le\Delta_{b,A}(N)\le\Delta_{2,A}(N)\qquad(b\ge 2).
\]
The factor two in the supplied formal transfer theorem can be replaced,
in ordinary mathematics, by one. This was not Lean-checked in this wave.

## D.2. Cyclotomic lower bounds do not close rational targets

Saturated cyclotomic divisibility (Type B A.3) strengthens *lower*
bounds on \(D_F\). For a rational difference \(|p/q-S_F|\ge 1/(q D_F)\),
a larger lower bound on \(D_F\) makes the error lower bound *smaller*,
not larger. The actual remaining inequality is the selector condition
\[
\forall K\ \exists N\ge K:\qquad c_x(N+1)\ge Q_N+\beta_N.
\]
A.3 does not prove this, and does not decide \(1/2\) or \(1/21\).

Finite checks live in
`scripts/check_signed_finite_period_r4.py --quick`.
