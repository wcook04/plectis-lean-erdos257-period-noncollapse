# The support word, the hole at one half, and the run criterion

> **Scope correction, added after the fact.**  This note was written from the
> `erdos257_period_noncollapse` closeout without consulting the second Erdos-257
> programme in this repository, `public-source-redacted://erdos257`.  That
> programme had already proved, independently and earlier, a substantial part
> of what is derived below.  Specifically, its `notes/ProgrammeSpine.md`
> contains:
>
> * uniqueness of the representation and the Cantor property (here Section 0);
> * **L1**, $2T_{n-1}=c_n+T_n$ exactly, hence death at rank $n$ is exactly
>   $2u_{n-1}\in(T_n,c_n)$ --- one hole, no other failure mode (here Section 2);
> * **L2**, $\lvert C\rvert=1$ exactly, as a one-line consequence of L1
>   (here Section 1);
> * the constants $2^n(c_n-T_n)\to\tfrac23$, hole density $\to\tfrac13 2^{-n}$,
>   $4^n\gamma_n\to\tfrac23$, survival probability $1/E=0.62239$
>   (here Sections 0.1, 2, 4);
> * the normalised coordinate $v_n=u_n/T_n$ with the hole **centred at $1/2$**
>   of width $\sim\tfrac13 2^{-n}$ (here Section 2's $\psi$, the complementary
>   coordinate);
> * the summed carry identity
>   $\sum_{n\le X}\tau_A(n)=\sum_{n<X}Q_n+2Q_0-Q_X+\sum_{n\le X}t_n$
>   (here derived in Section 0's set-up);
> * the $\Psi$ decomposition and its reindexing by
>   $c_A(n,r)=\#\{k\in A:k\mid n+r\}$ (here Section 5b's first-multiple form);
> * the calibration that a measured deepest death rank matching
>   $\log_2(q/3)$ **is** the random prediction and is therefore *not* evidence
>   of an arithmetic mechanism (here Sections 4, 4b);
> * the $1/(2^d-a)$ neighbour family and its second-order dichotomy, with the
>   witness $1/7=\sum_{d\in A}1/(2^d+1)$ (`notes/CoveringBoundary.md` §4--5);
> * a refutation of "prime forcing" resting on exactly the observation that the
>   greedy is *not* "take whenever the carry stays non-negative" --- the same
>   correction recorded here as Section 6, with 82 counterexamples across eight
>   targets.
>
> Those sections should be read as independent re-derivations, not as new
> results, and the earlier programme has priority.
>
> **Cross-check completed.**  Two further duplications, and four sections that
> survive:
>
> * **Section 5b is also duplicated.**  `ProgrammeSpine.md` carries the same
>   criterion as its integer invariant: $f_P(d)=(2^{P\bmod d}-1)/(2^{d}-1)\in[0,1)$,
>   zero exactly when $d\mid P$, with "Erdos 257 restricted to denominators
>   dividing $2^P-1$ is exactly: no infinite $A$ has $\sum_{d\in A}f_P(d)$ an
>   integer", verified on 11 targets to rank 260 --- and with the same honest
>   label that it is equivalent to 257 and settles nothing.
> * **Bang's theorem is already in use** there (`ElementaryCriterionBoundary.md`
>   §5.3, `JLadderNoGo.md`), for an $\ell$-adic irrationality route which that
>   note then refutes twice.  The use in Section 4g is different --- counting
>   finite Mersenne sums by reduced denominator, not proving irrationality ---
>   so the refutation does not touch it, and the count itself does not appear
>   there.
> * **Section 4e is duplicated too --- retracted.**  `notes/CoveringBoundary.md`
>   §4--5 carries the same family in its own notation, $x_d=1/(2^{d}-a)$, with the
>   same table of second-order coefficients $+\tfrac23$ / $0$ / $-\tfrac23$ for
>   $a=+1,0,-1$, the same "the boundary is second-order, not first-order"
>   statement, and a *better* witness: $1/7=\sum_{d\in A}1/(2^{d}+1)$ for infinite
>   $A$, because $2^{d}\bmod 7$ cycles $2,4,1$ so $7$ divides no $2^{d}+1$ ---
>   certified over 200 ranks with the support prefix listed.  My $1/2$ witness and
>   the $a=\pm2$ rows add nothing of substance.  My iteration-8 grep missed it
>   because they write $a$ where I wrote $c$.  **Section 4e claims no novelty.**
> * **Sections 4d, 4g, 4h and 5d show no occurrence across all nine
>   `hole_geometry` notes**, now read in full: base-$b$ *target* survival, the
>   finite-sum count by denominator via Bang primitive divisors, the identity
>   $b^{n}z_{n+k}=1/(b^{k}-b^{-n})$ with its $c$-independent gap term, and the
>   characteristic-two squarefree witness.  (`ProgrammeSpine.md` mentions
>   "squarefree" only as one of 17 real-valued *support* families, not the
>   $\mathbb F_2((1/t))$ statement.)  These four are the session's residue.
> * A fourth item has since been superseded: `notes/OrbitStationarity.md` largely
>   duplicates `notes/HoleGenericity.md`, which proves the uniform null is *exact*
>   and tests genericity on $1.09\times10^{7}$ targets rather than $510$.  See the
>   banner there.
>
> The durable fix is [`formal_math/ERDOS257_CROSS_INDEX.md`](../../../ERDOS257_CROSS_INDEX.md).
>   `FiniteCertificate.md` §4 does carry a *different* exact self-similarity,
>   $\rho_k(2n)=2\rho_k(n)\bmod k$, with the sharp remark that "the dynamics
>   renormalise; the alphabet does not" --- which is the obstruction Section 4h
>   runs into, and Section 4h should be read against it.
> * Squarefree appears in `ProgrammeSpine.md` only as one of 17 *support*
>   families tested numerically for rationality of $S(A)$ over $\mathbb R$, not
>   as the $\mathbb F_2((1/t))$ statement of Section 5d.
>
> One consequence of reading the other programme is recorded in its own lane:
> `erdos257_hole_geometry/notes/BoundaryFamilySlack.md` settles the
> $\{2^{j}+1\}$ boundary family that `ProgrammeSpine.md` flagged as open.


Date: 2026-08-22.  Executable owners:

* `scripts/support_word_structure_lab.py`
  -> `state/public-source-redacted://support_word_structure_receipt.json`
* `scripts/mersenne_survivor_density_census.py`
  -> `state/public-source-redacted://mersenne_survivor_density_receipt.json`

This note changes the central object.  Every mechanism family in
`Erdos257ResearchFrontierCloseout.md` works in a *derived* coordinate --- an
integer carry, a dyadic cylinder, a reservoir, a corridor.  Here the object
is the Boolean support word itself, and the intrinsic one-dimensional
dynamics it carries.

## 0.  Set-up and the uniqueness that makes greedy forced

Write $z_n = 1/(2^n-1)$, $T_n = \sum_{k>n} z_k$, and

$$C \;=\; \Big\{\, \sum_{a\in A} z_a \;:\; A\subseteq\mathbb N \,\Big\}\subseteq[0,E],
\qquad E=\sum_{k\ge1}z_k=1.6066951524\ldots$$

Both series expansions are exact:

$$z_n=\sum_{j\ge1}2^{-jn},\qquad T_n=\sum_{j\ge1}\frac{2^{-jn}}{2^j-1},$$

so the $j=1$ terms cancel in the difference and

$$\gamma_n \;:=\; z_n-T_n \;=\; \sum_{j\ge2}2^{-jn}\,\frac{2^j-2}{2^j-1}
\;=\;\tfrac23\,4^{-n}\big(1+O(2^{-n})\big) \;>\;0 . \tag{0.1}$$

Strict positivity of $(0.1)$ is the structural fact that governs everything.
Each Mersenne reciprocal strictly dominates its own tail, so **the
representation of a point of $C$ is unique** and the greedy scan
$b_n=\mathbf 1[r_{n-1}\ge z_n]$, $r_n=r_{n-1}-b_nz_n$, is not a heuristic but
the only algorithm: if $r_{n-1}\ge z_n$ and rank $n$ were skipped, the whole
remaining tail $T_n<z_n$ could not reach the target.  Consequently

> $x\in C$ with infinite support $\iff$ $x$ is a counterexample to Erdos 257,
> and there is exactly one candidate support word per target.

Erdos 257 is therefore the single statement: $C\cap\mathbb Q$ contains no
point beyond the countable set of finite Mersenne sums.

## 1.  $C$ has Lebesgue measure exactly one

The depth-$N$ survivor set $C_N$ is a union of $2^N$ intervals of length
$T_N$, so $|C_N| = 2^NT_N = \sum_{j\ge1}2^{-(j-1)N}/(2^j-1) = 1+\tfrac13 2^{-N}+\tfrac172^{-2N}+\cdots$, whence

$$|C| \;=\; \lim_N 2^N T_N \;=\; 1 \qquad\text{exactly.} \tag{1.1}$$

$C$ is a *fat* Cantor set: compact, perfect, nowhere dense, measure $1$
inside an interval of length $E$.  Its thickness $T_n/\gamma_n\sim\tfrac32\,2^{\,n}$
diverges.  So for a Lebesgue-random $\xi\in[0,E]$ the forced greedy survives
with probability $1/E = 0.6223956\ldots$, and the conditional death
probability at rank $n$ is $2^{n-1}\gamma_n/(\text{alive measure}) \approx \tfrac13 2^{-n}$.
This is the null model against which every rational-target statistic below
is read.

## 2.  The intrinsic coordinate: a perturbed doubling map with a hole at $1/2$

Let $\psi_n$ be the fraction of the remaining tail that the support leaves
unused,

$$\psi_n \;=\; \frac{\sum_{a>n}(1-b_a)\,z_a}{T_n}\;=\;1-\frac{r_n}{T_n}\ \in[0,1],
\qquad \psi_0 = 1-\frac{x}{E}. \tag{2.1}$$

Put $\rho_n = T_n/T_{n-1}$.  From $T_{n-1}=z_n+T_n$ one gets, with no
approximation,

$$\boxed{\;\psi_n=\begin{cases}\psi_{n-1}/\rho_n, & \psi_{n-1}\le \rho_n \quad(b_n=1),\\[2pt]
1-(1-\psi_{n-1})/\rho_n, & \psi_{n-1}\ge 1-\rho_n\quad(b_n=0),\end{cases}}\tag{2.2}$$

and the target dies at rank $n$ exactly when $\psi_{n-1}$ falls in the hole

$$H_n=(\rho_n,\,1-\rho_n),\qquad |H_n| \;=\; 1-2\rho_n \;=\; \frac{\gamma_n}{T_{n-1}}
\;=\;\tfrac13 2^{-n}\big(1+O(2^{-n})\big). \tag{2.3}$$

Since $\rho_n=\tfrac12-\tfrac162^{-n}+O(4^{-n})$, both branches of $(2.2)$ are
full and expanding with slope $1/\rho_n = 2+\tfrac232^{-n}+O(4^{-n})$.

Three consequences worth stating plainly.

1.  **The intrinsic dynamics contains no divisor sum.**  $f_A(n)=\sum_{d\mid n}b_d$
    is an artefact of the integer-carry coordinate.  In $(2.2)$ the whole
    problem is a one-dimensional non-autonomous expanding map.  Divisor
    structure re-enters only through the *rationality of the initial point*.
2.  **The perturbation and the hole are the same order, $2^{-n}$.**  That is
    the criticality of the exponent $2$: with $z_n=1/(B^n-1)$, $B\ge3$, one
    gets $T_n/z_n\to 1/(B-1)<1$, $|C|=0$, and holes of order one.  Base $2$ is
    the exact boundary case.
3.  **If $\rho_n$ were $\tfrac12$ the hole would be empty and no target would
    ever die.**  Every death in this problem is paid for by the deviation
    $\tfrac12-\rho_n$.

## 3.  The run criterion: death is an infinite run of takes

Suppose the greedy skips at rank $m$ and survives, and set
$\delta_m := T_m-r_{m-1}\ge 0$.  Since $r_m=r_{m-1}=T_m-\delta_m$ and
$T_m=z_{m+1}+T_{m+1}$,

$$r_m\ge z_{m+1}\iff \delta_m\le T_{m+1},\qquad\text{and then } r_{m+1}=T_{m+1}-\delta_m,$$

which is the same shape one rank later.  Induction gives the exact law

$$\boxed{\;\text{ranks } m+1,\dots,m+L \text{ are all selected and } m+L+1 \text{ is skipped},\quad
L=\max\{i\ge0: T_{m+i}\ge\delta_m\}.\;}\tag{3.1}$$

Equivalently $\delta_m\in(T_{m+L+1},T_{m+L}]$, i.e. $\delta_m\asymp 2^{-(m+L)}$.
Letting $\delta_m<0$ (death) gives $L=\infty$, and indeed once $r>T$ the
greedy provably selects every subsequent rank.  Hence

> **$x\notin C$ if and only if the greedy word ends in an infinite run of $1$s.**

This has a useful computational corollary.  The single integer

$$R_N \;=\; \max\{\text{run of consecutive selected ranks below } N\}$$

records the closest the orbit ever came to death: the smallest survival
margin met before rank $N$ is $\delta\asymp 2^{-(m+R_N)}$ at the rank $m$
where the run starts.  No high-precision margin machinery is needed once the
word is known.  Under the null model of Section 1 the greedy word is
Bernoulli$(1/2)$, so $R_N\approx\log_2 N$, whereas death at rank $m$ requires
a run of length $\approx m$.  **The gap between what death requires and what
the word supplies grows linearly while the word's own fluctuation grows
logarithmically.**

### 3.1  Exact verification of the run law

The law $(3.1)$ predicts that the smallest survival margin met below rank $N$
occurs at the start of the longest take-run, with $L$ equal to
$-\lfloor\log_2\beta\rfloor$ where $\beta=1-r_{m-1}/z_m$.  The lab computes
the two quantities by completely separate routes --- the margin from certified
dyadic enclosures against the gap series $(0.1)$, the run from the word ---
and they coincide on every target at certified depth $4\times10^4$:

| target | tightest-margin rank $m$ | $-\lfloor\log_2\beta_m\rfloor$ | take-run starting at $m+1$ | max take-run |
|---|---:|---:|---:|---:|
| $1/21$ | $688$ | $12$ | $12$ | $15$ |
| $1/5$ | $2472$ | $12$ | $12$ | $12$ |
| $3/11$ | $5050$ | $15$ | $15$ | $15$ |
| $2/21$ | $11123$ | $13$ | $13$ | $13$ |
| $1/465$ | $24092$ | $16$ | $16$ | $16$ |
| $90/511$ | $24994$ | $15$ | $15$ | $15$ |

Maximal take-runs over $4\times10^4$ ranks are $12$--$16$ across eleven
targets, against $\log_2(4\times10^4)=15.3$: the Bernoulli$(1/2)$ value.
Death at rank $m$ would require a run of length $\approx m$.  At the ranks
where these maxima occur ($m\approx 2\times10^3$ to $4\times10^4$) the words
are short of the death threshold by three to four orders of magnitude in the
exponent, and the shortfall widens linearly.

## 4.  Rational targets are statistically indistinguishable from random reals

`mersenne_survivor_density_census.py` runs the certified forced greedy on
every $p/q$ in $(0,E)$ for a list of denominators, with an exact enclosure
of $T_n$ shared across the batch, and certifies each death by the test
$r_n>T_n$.

Null prediction from $(1.1)$: survivor fraction $2^NT_N/E$, already equal to
$1/E=0.6223956$ to six places by depth $20$.  Observed, at depth $400$:

| $q$ | targets | survivor fraction | deepest death |
|---:|---:|---:|---:|
| $997$ | $1601$ | $0.62274$ | $11$ |
| $1009$ | $1621$ | $0.62492$ | $6$ |
| $1024$ | $1645$ | $0.62310$ | $9$ |
| $2047=2^{11}-1$ | $3288$ | $0.62196$ | $10$ |
| $2048$ | $3290$ | $0.62280$ | $9$ |
| $2049$ | $3292$ | $0.62242$ | $8$ |
| $4096$ | $6581$ | $0.62255$ | $9$ |
| $5041=71^2$ | $8099$ | $0.62242$ | $10$ |
| $10007$ (prime) | $16078$ | $0.62191$ | $12$ |

Two facts, both one-way information about which mechanism can exist.

*   Every fraction agrees with $1/E$ inside one standard error, and the
    fraction is **constant from depth $20$ to depth $400$**.  Mersenne
    denominators $2^k-1$, powers of two, primes, and squares are not
    separated.
*   Across all $47{,}000$ targets there is **no death beyond rank $12$**,
    while the null model predicts $\approx 10^{-5}$ deaths beyond rank $30$
    in a sample this size.  Observing none is the null model's own
    prediction, not evidence against it.

Deep single targets agree.  At certified depth $2\times10^4$ the words for
$1/21$, $4/9$, $1/5$, $2/21$, $1/465$, $90/511$, $3/11$, $8/21$, $5/21$ all
survive, have support density $0.493$--$0.508$, divergent
$\sum_{a\in A,a\le N}1/a\approx 3.7$--$5.4$, no eventual period below $720$,
maximal divisor load $36$--$46$, and a smallest relative margin
$\log_2\beta$ between $-10$ and $-15$ over $\approx 7000$ skips --- which is
what the minimum of that many uniform samples is.

**Interpretation, with its own limit stated first.**  Section 5c shows this
census is blind past depth $\log_4 q$, so the table above is *not* evidence
about the deep regime; read on its own it would be an over-claim.  What it
does establish is that the shallow regime contains no anomaly and no
denominator-class effect --- Mersenne $2^k-1$, powers of two, primes and
squares are not separated --- and it calibrates the null model precisely.
The deep-regime evidence is the separate deep-run scan and the single-target
runs, where $N\gg\log_4 q$.

Taken together with those, one mechanism conclusion is supported: a proof
that proceeds by exhibiting a scalar potential, a reservoir sign, a
bounded-window divisor law, or any invariant forcing a cofinal return would
have to make essentially every rational die.  Nothing in the measured margin
distribution --- generic at every depth reached, in both regimes --- offers
such an invariant any slack to act on.  That is an argument about mechanism,
not a probabilistic proof about any particular target.

## 5d.  Characteristic two: the divisor layer alone cannot obstruct

Work in $\mathbb F_2((1/t))$, where $1/(t^a-1)=\sum_{k\ge1}t^{-ak}$ and there
are no carries at all, so

$$\sum_{a\in A}\frac1{t^a-1}=\sum_{n\ge1} f_A(n)\,t^{-n},\qquad f_A(n)=\#\{d\mid n: d\in A\}\bmod 2,$$

and rationality in $\mathbb F_2(t)$ is exactly eventual periodicity of
$(f_A(n)\bmod 2)$.  Over $\mathbb F_2$ the Dirichlet inverse of $1$ is $\mu$,
which reduces to the squarefree indicator, and **every** value of $g\ast\mu$
already lies in $\{0,1\}$.  Hence for *any* eventually periodic
$g:\mathbb N\to\mathbb F_2$ the set

$$A_g=\{\,n:\ (g\ast\mu)(n)=1\ \text{in }\mathbb F_2\,\}\quad\text{satisfies}\quad
\sum_{a\in A_g}\frac1{t^a-1}=\sum_n g(n)t^{-n}\in\mathbb F_2(t).$$

The simplest witness is $g=\delta_1$, giving $A$ = the squarefree numbers,
$f_A(n)=2^{\omega(n)}\equiv 0 \pmod 2$ for every $n\ge2$, and

$$\sum_{a\ \mathrm{squarefree}}\frac{1}{t^a-1}\;=\;\frac1t \qquad\text{in }\mathbb F_2((1/t)),$$

with $A$ infinite.  Verified for all $n\le 2\times10^5$ by the lab.

### 5a.  The dichotomy, and a proof for odd $p$ on a Boolean lattice

Owner: `scripts/characteristic_p_dichotomy_search.py`
-> `state/.../characteristic_p_dichotomy_receipt.json`.

The characteristic-$p$ question is: *does an infinite $A$ exist with
$f_A(n)\bmod p$ eventually periodic?*  Fixing a period $P$ and a preperiod
$L$, the first $L+P$ membership bits are free and thereafter periodicity
forces $b_n\equiv f_A(n-P)-s_n\pmod p$ with
$s_n=\sum_{d\mid n,\,d<n}b_d$; the branch survives only while the forced
residue lands in $\{0,1\}$.  Every eventually periodic residue target with
those parameters is reached by exactly one free prefix, so the enumeration is
complete for each $(p,P,L)$.  For $p=2$ it recovers the squarefree witness
unaided --- the branch $P=1$, $L=1$, prefix $11$ has support
$1,2,3,5,6,7,10,11,13,14,15,17,19,\dots$

Part of the odd case is a theorem, not a search.  Let $p$ be odd and suppose
$f_A\equiv g\pmod p$ for $n>L$ with $g$ of period $P$.  Pick distinct primes
$r_1,\dots,r_m>L$ with $r_i\equiv1\pmod P$, and for $S\subseteq[m]$ write
$r_S=\prod_{i\in S}r_i$.  Every $r_S$ with $S\ne\emptyset$ exceeds $L$ and is
$\equiv1\pmod P$, so

$$\sum_{T\subseteq S}b_{r_T}\;=\;f_A(r_S)\;\equiv\;g(1)=:c \pmod p
\qquad\text{for all }S\ne\emptyset,$$

while the empty set gives $b_{r_\emptyset}=b_1$.  Mobius inversion on the
Boolean lattice yields, for $|S|\ge1$,

$$b_{r_S}\;\equiv\;(-1)^{|S|}\,(b_1-c)\pmod p .$$

Both $b_1-c$ and $c-b_1$ must therefore lie in $\{0,1\}$, which for $p\ge3$
forces $b_1\equiv c$ and hence $b_{r_S}=0$ for every $S\ne\emptyset$.  (For
$p=2$ the two conditions coincide and the obstruction disappears --- exactly
the degeneracy $\mu\equiv|\mu|$.)

> **Proposition.**  Let $p$ be an odd prime and suppose $f_A\bmod p$ is
> eventually periodic with period $P$ and preperiod $L$.  Then
> $g(1)\equiv b_1$, and $A$ contains **no** product of distinct primes
> $r>L$ with $r\equiv1\pmod P$.

Exhaustive enumeration over $P\le5$, $L\le6$, horizon $800$ gives the
dichotomy sharply:

| $p$ | branches enumerated | branches surviving with growing support |
|---:|---:|---:|
| $2$ | $7812$ | $\mathbf{7680}$ |
| $3$ | $7812$ | $0$ |
| $5$ | $7812$ | $0$ |
| $7$ | $7812$ | $0$ |
| $11$ | $7812$ | $0$ |
| $13$ | $7812$ | $0$ |

$39{,}060$ odd-characteristic branches, none surviving; at $p=2$ all but
$132$ survive.

The same lattice argument with an extra coprime factor $M$ gives
$\sum_{d\mid M}b_{d\,r_S}\equiv(-1)^{|S|}\big(f_A(M)-g(M)\big)$, so
consecutive parities sum to $0$ modulo $p$ while lying in $[0,\tau(M)]$;
hence whenever $2\tau(M)<p$ one gets $b_{d r_S}=0$ for every $d\mid M$.  That
extension is $p$-dependent and does not by itself force $A$ finite.

**The obvious way to finish is closed.**  Owner:
`scripts/odd_p_finite_difference_nogo.py` -> `state/.../odd_p_finite_difference_nogo_receipt.json`.
Run the same argument with primes in a general class $\rho$.  Then
$r_S\equiv\rho^{|S|}$, and Mobius inversion gives the finite difference

$$b_{r_S}=(\Delta^{|S|}h)(0),\qquad h=\big(b_1,\,g(\rho),\,g(\rho^2),\dots\big),$$

with $h$ of period $d=\operatorname{ord}_P(\rho)$ from index $1$.  If the only
sequences with every finite difference in $\{0,1\}$ mod $p$ were constant,
the argument would extend to all classes and the dichotomy would follow.
Exhaustive enumeration over $b_1\in\{0,1\}$ and $g\in\mathbb F_p^{d}$ says
otherwise:

| $p$ | $d$ | candidates | survivors | survivors taking the value $1$ |
|---:|---:|---:|---:|---:|
| any of $3,5,7,11,13$ | $1$ | --- | $2$ | $\mathbf 0$ |
| $3$ | $2$ | $18$ | $8$ | $6$ (e.g. $b_1=0$, $g=(0,1)$: differences $0,1,0,1,\dots$) |
| $5$ | $4$ | $1250$ | $32$ | $30$ (e.g. $g=(0,0,0,1)$) |
| $7$ | $3$ | $686$ | $8$ | $6$ (e.g. $g=(0,1,3)$) |

The $d=1$ row recovers the Proposition independently --- no survivor ever
takes the value $1$ --- which is exactly why $\rho=1$ works.  For $d\ge2$ the
constraint is satisfiable with the value $1$ occurring infinitely often, so
**iterating the single-class Boolean-lattice argument over residue classes
cannot force $A$ finite.**  A proof must couple the classes (the constraints
for every $\rho$ coprime to $P$ hold simultaneously, along with the
coprime-factor relations) or use a different mechanism.  The exhaustive
branch search --- $39{,}060$ odd-$p$ branches, zero survivors --- is
unaffected; what is closed is this route to a theorem, and it was the route
this directory had queued.

The odd case is therefore recorded as proven-in-part, exhaustively searched,
and with its most natural completion eliminated --- not as a theorem.

**Consequence.**  The characteristic-two analogue of Erdos 257 is false, and
false with an infinite family of counterexamples.  Therefore no proof of
Erdos 257 can survive reduction of the divisor-count sequence mod $2$: any
valid argument must use the archimedean carry --- the integrality *and
positivity* of $\mathbf 1_A=f_A\ast\mu$ over $\mathbb Z$, together with the
real convergence $\sum f_A(n)2^{-n}=x$.  Purely Dirichlet-combinatorial
obstructions, parity/Mobius sign arguments, and multiplicative normal forms
are excluded as a class, not one at a time.  (Over $\mathbb F_p$ with $p$
odd the naive constant-residue forcing collapses to $A=\{1\}$; the general
odd-$p$ question is open here and is a legitimate follow-up.)

## 4b.  The deep regime: many targets, depth far past $\log_4 q$

Owner: `scripts/deep_run_anomaly_scan.py`
-> `state/.../deep_run_anomaly_receipt.json`.

Section 5c shows a denominator census is blind past depth $\log_4 q$.  The
instrument that is not blind is the run law: by $(3.1)$ the maximal run of
consecutive selected ranks below $N$,

$$R_N=\max\{\text{run of consecutive selected ranks} < N\},$$

is a single integer recording the closest approach to death over the entire
history, and death at rank $m$ requires $R\approx m$.  Under the
Bernoulli$(1/2)$ null $R_N$ is Gumbel with mode $\log_2 N$ and scale
$1/\ln 2=1.4427$, so over $S$ independent targets the sample maximum should
sit near $\log_2 N+1.4427\ln S$.

At depth $N=2.5\times10^4$ over denominators
$101,211,509,1021,4099,10007$ (so $\log_4 q\in[3.3,6.6]$ --- the scan runs
about $4000$ times deeper than the forced regime):

* $247$ survivors, $148$ deaths, $0$ undecided;
* **every death occurs at rank $\le 10$**, i.e. entirely inside the forced
  shallow regime; the histogram is $96$ deaths at rank $1$, $29$ at rank $2$,
  $10$ at rank $3$, then a thin tail ending at rank $10$;
* $R_N$ histogram concentrated on $11$--$18$ (mode $13$), tail
  $19,20,21,22$ with one target each;
* predicted sample maximum $\log_2(25000)+1.4427\ln 247=22.56$; **observed
  $22$**;
* mean support density $0.49606$.

**What $R_N$ does and does not measure --- corrected.**  By $(3.1)$ the run
length satisfies $\delta_m\in(T_{m+L+1},T_{m+L}]$, so $L$ is finite exactly
when $\delta_m>0$, i.e. exactly when the target survives that skip, and death
is $L=\infty$.  **There is no finite run length that implies death.**  What
$R_N$ measures is the scale-free closeness $\min_m \delta_m/T_m\approx2^{-R_N}$,
not a distance to a threshold; an earlier draft of this section said death at
those ranks "would have required runs of that length", which is the reading
that `erdos257_hole_geometry/notes/ProgrammeSpine.md` Section 4 retracts, and
it is withdrawn here too.  Its counterexample is decisive and applies to any
such reading: a support with $A\cap[11,510]=\emptyset$ has a run of $500$ zeros
beginning at position $11$ and survives trivially, because long runs place the
orbit near a hole *boundary* and always on the safe side of it.

What survives is the comparison itself: $R_N$ is a statistic of the word, its
distribution matches the Bernoulli$(1/2)$ Gumbel law, and that is a genericity
measurement.  The earlier run at depth $1.2\times10^4$ over five denominators
gave the same picture ($231$ survivors, predicted maximum $21.4$, observed
$23$, mean density $0.49797$).

**Death ranks track the measure prediction exactly.**  For denominator $q$
the expected number of targets dying at rank $n$ is
$qE\cdot 2^{n-1}\gamma_n/E\approx\tfrac13 q2^{-n}$, so the deepest death
should sit near $\log_2(q/3)$.  Measured against Section 4's census:

| $q$ | $\log_2(q/3)$ | deepest death observed |
|---:|---:|---:|
| $997$ | $8.4$ | $11$ |
| $2047$ | $9.4$ | $10$ |
| $4096$ | $10.4$ | $9$ |
| $5041$ | $10.7$ | $10$ |
| $10007$ | $11.7$ | $12$ |

The agreement is to within one or two ranks across a factor of ten in $q$.
**A death appreciably beyond $\log_2(q/3)$ would be the first arithmetic
signal in this problem; none has appeared.**

## 4c.  Adversarial structure tests on the word

Owner: `scripts/support_word_pseudorandomness_battery.py`
-> `state/.../support_word_pseudorandomness_receipt.json`.

Every claim in Sections 4 and 4b is negative --- "no structure was found" ---
and such a claim is worth exactly as much as the sharpest test that failed to
break it.  This is that test, run on the certified forced-greedy word at
$N=6\times10^4$ for six targets.  It matters mathematically because, by the
run law $(3.1)$, *any* mechanism biasing the word towards long selected runs
is a mechanism for Erdos 257 and any biasing it away is a mechanism against;
a single hidden period or arithmetic correlation would be that mechanism.

| test | null | observed range over $1/21,\,4/9,\,3/11,\,1/465,\,17/29,\,90/511$ |
|---|---|---|
| density | $0.5$ | $0.4969$--$0.5041$ ($\lvert z\rvert\le2.0$) |
| spectral $\max_{k\ne0}\lvert\hat b(k)\rvert$ | $\sqrt{N\log N}=812.5$ | $770$--$891$, ratio $0.95$--$1.10$ |
| autocorrelation, $3000$ lags | $\max\lvert z\rvert\approx\sqrt{2\log 3000}=4.0$ | $3.36$--$4.03$ |
| correlation with $\mu,\lambda,(-1)^{\omega},d\bmod2,v_2\bmod2,\mathbf 1_{\text{prime}},\mathbf 1_{\text{sqfree}}$ | $\max\lvert z\rvert\approx2.7$ over $42$ tests | $\le 2.46$ |
| non-overlapping $k$-block $\chi^2/\mathrm{dof}$, $k=8,12$ | $1$ | $0.86$--$1.01$ |
| $\Pr[b_{kn}=1\mid b_n=1]$, $2\le k\le24$ | $0.5$ | $0.469$--$0.525$ |

The spectral test is the strong one.  A word with *any* hidden period $M\le N$
would show a Fourier spike of order $N/2=3\times10^4$; the largest observed
coefficient is $891$, i.e. at the level a Bernoulli word produces.  This
subsumes and vastly extends the earlier "no eventual period below $720$"
check.

One test came within reach of significance and has now been resolved as
noise.  The non-overlapping $4$-block $\chi^2/\mathrm{dof}$ was $2.44$
($z=3.95$) for $4/9$ at $N=6\times10^4$.  Re-running the battery over fifteen
targets at $N=4\times10^4$ moves the outlier to a different target --- $4/9$
falls to $z=0.63$ and the largest becomes $3/11$ at $z=4.45$, against an
expected maximum of $2.33$ over fifteen tests.  A signal that relocates when
the sample changes is not a signal.

That wider run also exposed a defect in this instrument, now fixed.  The
battery had no death test, so a dead target silently returned an all-ones word
--- death being exactly an infinite run of takes, $(3.1)$ --- and every
statistic then measured a constant sequence.  $29/31$ and $13/17$ entered the
table that way, reporting a $4$-block $\chi^2/\mathrm{dof}$ of $9998$ and a
spectral ratio of $0.003$.  Both are dead at rank $1$: they lie in the level-one
Cantor gap $(T_1,z_1)=(0.6067,1)$, since $29/31=0.935$ and $13/17=0.765$.  The
battery now carries the certified $r_n>T_n$ test and reports such targets as
dead instead of scoring them.

**Reading.**  The greedy support word of a rational target is
pseudorandom against every test applied.  That is not evidence that Erdos 257
is false --- it cannot be --- but it is evidence about *mechanism*: none of
the structure a proof would need to exploit is present in the word at these
depths.

## 4f.  The divisor lattice carries no bias either

Owner: `scripts/divisor_richness_bias_probe.py`
-> `state/.../divisor_richness_bias_receipt.json`.

Section 4c tested the support as a binary *word* --- translations, spectrum,
blocks --- and found nothing.  That test is structurally blind to the divisor
lattice, and there is a concrete dynamical reason to expect a bias there.  The
carry obeys $Q_n=2Q_{n-1}+t_n-f_A(n)\ge0$, hence

$$f_A(n)\;\le\;2Q_{n-1}+t_n,$$

so a large divisor load must be paid for by carry banked in advance, and carry
is usually small.  The forced greedy is therefore under standing pressure to
keep the divisors of highly composite ranks *out* of the support.  That is a
mechanism indexed by divisibility, not by translation, and it is close to what
the reservoir and density family of the closeout has been reaching for.

Two statistics, on the certified word:

*   $\Pr[n\in A\mid d(n)=k]$ and $\Pr[n\in A\mid\omega(n)=k]$.  Measured flat
    at $0.500$ across every bin, $\lvert z\rvert\le1.9$ --- **no membership
    bias by divisor richness at all**.
*   $\mathbb E\big[f_A(n)/d(n)\big]$ binned by $d(n)$.  This one *does* run
    below $\tfrac12$ and rise with $d$: $0.253$ at $d=2$, $0.395$ at $d=8$,
    $0.441$ at $d=36$.

The second looks like structure and is not.  $\mathbb E[f_A(n)/d(n)]=\tfrac12$
holds under no realistic null: $f_A$ weights *small* divisors heavily, since a
small $d$ divides many $n$, so the statistic is governed by the density of $A$
near the origin rather than by its bulk density.  With $1\notin A$ alone the
prediction is already $\tfrac12-\tfrac1{2d(n)}$, which reproduces the $d=2$
cell exactly ($0.250$).  The correct null resamples $A$ by independent
Bernoulli membership with the **empirical density of $A$ inside each dyadic
block** $[2^i,2^{i+1})$, preserving the transient.  Against $40$ such
replicates:

At certified depth $3\times10^4$ over seven targets --- $1/21$, $4/9$,
$3/11$, $1/465$, $1/5$, $90/511$, $1013/2048$ --- the comparison covers $119$
cells and the **largest deviation anywhere is $\lvert z\rvert=1.70$**, against
an expected maximum of $\sqrt{2\log 119}=3.09$.  The five largest cells are
$-1.70$ ($1013/2048$, $d=28$), $1.66$ ($4/9$, $d=10$), $-1.56$ ($1/21$,
$d=2$), $1.55$ ($1/465$, $d=6$), $-1.47$ ($1013/2048$, $d=14$).  The
membership statistic is equally flat: over the $35$ cells of
$\Pr[n\in A\mid\omega(n)=k]$ the largest is $\lvert z\rvert=2.06$ against an
expected $2.66$.

**The entire apparent deficit is the density profile of $A$, not
divisor-lattice structure.**

**Consequence.**  The hypothesis that the forced greedy anti-correlates with
divisor richness --- that it must thin the support where the divisor lattice
concentrates --- is measured and false.  A proof cannot recruit that pressure,
even though the carry inequality makes it look available.  Together with
Section 4c this closes both the additive and the multiplicative structure
searches on the support word.

## 4h.  One fact, not four: the tail is a renormalization flow to a gapless point

Owner: `scripts/tail_renormalization_flow.py`
-> `state/.../tail_renormalization_flow_receipt.json`.

Sections 1, 4d, 4e and 4g record four separate facts --- $\lvert C\rvert=1$;
base $2$ is the only base where rational targets survive; Erdos 257 is the
minimal positive-gap member of the family $1/(b^k-c)$; the death rate is
summable.  They are one fact.

**The identity.**  For all $n\ge0$, $k\ge1$,

$$b^{\,n}z_{n+k}\;=\;\frac{b^{\,n}}{b^{\,n+k}-1}\;=\;\frac{1}{b^{k}-b^{-n}}\;=\;z^{(c)}_k\Big|_{c=b^{-n}}. \tag{4h.1}$$

Verified in exact rational arithmetic over $3720$ pairs, $b\in\{2,3,5,10\}$,
$n\le30$, $k\le30$: no failures.  So **the depth-$n$ tail of the system,
rescaled by $b^n$, is exactly the neighbour family of Section 4e at parameter
$c=b^{-n}$.**  Running the greedy deeper *is* flowing $c$ geometrically to $0$.

**What the flow can and cannot remove.**  For $z_k=1/(b^k-c)$,

$$\gamma_k \;=\; z_k-T_k \;=\; \underbrace{b^{-k}\,\frac{b-2}{b-1}}_{\text{independent of }c}
\;+\; c\,b^{-2k}\,\frac{b^{2}-2}{b^{2}-1}\;+\;O(b^{-3k}). \tag{4h.2}$$

The first term does not involve $c$ and **vanishes exactly when $b=2$**.
Measured:

| $b$ | $c$ | scaled gap | value |
|---:|---|---|---|
| $2$ | $1$ | $4^{k}\gamma_k$, $k=3\ldots6$ | $0.7906,\ 0.7241,\ 0.6944,\ 0.6803\to\tfrac23$ |
| $2$ | $2^{-8}$ | $4^{k}\gamma_k$ | $0.0026058,\dots\to 0.0026042=\tfrac23c$ |
| $2$ | $2^{-12}$ | $4^{k}\gamma_k$ | $0.00016280\to0.00016276=\tfrac23c$ |
| $3$ | $1$ | $9^{k}\gamma_k$ | $14.41,\ 41.39,\ 122.4,\ 365.4$ |
| $3$ | $3^{-4}$ | $9^{k}\gamma_k$ | $13.51,\ 40.51,\ 121.5,\ 364.5=\tfrac12\cdot3^{k}$ |

At $b=3$ the scaled gap converges to $\tfrac12\cdot3^{k}$, i.e.
$\gamma_k=\tfrac12 3^{-k}$, and is **essentially unchanged as $c$ runs over four
orders of magnitude**: the flow cannot touch it.  At $b=2$ the whole of
$\gamma_k$ is the $c$ term, to seven digits.

**The unification.**

*   $b\ge3$: a $c$-independent gap of order $b^{-k}$ survives the flow, so
    $\lvert C_b\rvert=0$ and rational targets die --- the $0$ survivors out of
    $2868$ measured in Section 4d.
*   $b=2$: the entire gap is carried by the flow parameter, so at depth $n$ it
    is $\tfrac23 2^{-n}4^{-k}$.  Hence $\lvert C\rvert=1$ (Section 1), Erdos 257
    is the minimal positive-gap member of its family (Section 4e), and the
    conditional death rate is summable **because the flow parameter
    $c_n=2^{-n}$ is summable** (Section 4g).

**Consequence for a proof.**  A proof of Erdos 257 must control the
$c\to0^{+}$ limit uniformly, and it cannot appeal to any quantity that
survives that limit: at $c=0$ the achievement set is the whole interval and
the statement is *false*, with the explicit witness of Section 4e.  Equally it
cannot appeal to anything that would also hold at $b\ge3$, where the gap is
$c$-independent and the conclusion is free.  The theorem lives exactly in the
gap between those two, and $(4h.2)$ says that gap is one term of one
expansion.

## 4d.  Base two is the unique base in which rational targets survive at all

Owner: `scripts/base_b_rational_survival_scan.py`
-> `state/.../base_b_rational_survival_receipt.json`.
(The measure/dimension side is already mapped by `base_b_tractability_map.py`;
what is asked here is about *targets*, not about the set.)

Erdos 257 is the $b=2$ case of: for infinite $A$, is
$\sum_{a\in A}(b^{a}-1)^{-1}$ irrational?  With $z_n=(b^n-1)^{-1}$ and
$T_n=\sum_{k>n}z_k$ the gap series is

$$\gamma_n=z_n-T_n=\sum_{j\ge1}b^{-jn}\,\frac{b^{j}-2}{b^{j}-1},$$

whose $j=1$ term vanishes **iff $b=2$**.  So at $b=2$ the gaps are
$\tfrac23 4^{-n}$, quadratically smaller than the bridges $T_n\sim2^{-n}$,
and $|C_2|=1$; for $b\ge3$ the gaps are $\sim b^{-n}\frac{b-2}{b-1}$, of the
same order as the bridges, $|C_b|=0$, $\dim_H C_b=\log2/\log b$.

The scan runs the certified forced greedy on rational targets in each base
(denominators $101,509,1021,4099,10007$, depth $600$):

| $b$ | $\dim_H C_b$ | $\lim\gamma_n/z_n$ | targets | survivors | survivor fraction | deepest death | predicted all-dead depth |
|---:|---:|---:|---:|---:|---:|---:|---:|
| $2$ | $1$ | $0$ | $669$ | $\mathbf{415}$ | $0.6203$ | $10$ | --- |
| $3$ | $0.6309$ | $0.5$ | $626$ | $0$ | $0$ | $17$ | $22.7$ |
| $4$ | $0.5$ | $0.6667$ | $644$ | $0$ | $0$ | $19$ | $13.3$ |
| $5$ | $0.4307$ | $0.75$ | $582$ | $0$ | $0$ | $8$ | $10.1$ |
| $7$ | $0.3562$ | $0.8333$ | $569$ | $0$ | $0$ | $5$ | $7.4$ |
| $10$ | $0.3010$ | $0.8889$ | $447$ | $0$ | $0$ | $4$ | $5.7$ |

Across $2868$ rational targets in bases $3,4,5,7,10$, **not one survives**,
and each base's deepest death sits at the predicted
$\log_2 q/\log_2(b/2)$.  Base $2$ has $62.03\%$ surviving, which is $1/E$.

**This is the sharpest mechanism statement available.**  The vanishing of the
leading gap term at $b=2$ is not a technical inconvenience --- it is the whole
difficulty.  For $b\ge3$ the survivors carry measure zero, rationals die at a
computable depth, and a measure or gap-density argument has room to operate.
At $b=2$ the survivors carry full measure, so no argument of that shape can
exist.  Operationally: **any proposed proof of Erdos 257 that would also go
through for some $b\ge3$ is thereby known to be insufficient**, because it
would be proving something the gap structure already gives for free.  A
proof must use a property that fails the instant $b$ exceeds $2$.

## 4e.  Erdos 257 is the minimal positive-gap member of its own family

Owner: `scripts/neighbour_family_gap_sign_lab.py`
-> `state/.../neighbour_family_gap_sign_receipt.json`.

Section 4d varied the base.  Vary instead the constant.  For
$z^{(c)}_n=\dfrac{1}{2^{n}-c}$,

$$z^{(c)}_n=2^{-n}+c\,4^{-n}+O(8^{-n}),\qquad
T^{(c)}_n=2^{-n}+\tfrac{c}{3}4^{-n}+O(8^{-n}),$$

so

$$\gamma^{(c)}_n \;=\; z^{(c)}_n-T^{(c)}_n \;=\; \tfrac{2c}{3}\,4^{-n}+O(8^{-n}).$$

**The sign of the gap is the sign of $c$, and its scale is $4^{-n}$ for every
$c$** --- always quadratically below the bridges $2^{-n}$.  Whenever
$z_n\le T_n$ at every rank the set of subsums is the full interval
$[0,\sum z_n]$, so the analogue of Erdos 257 is false there.  Measured in
exact rationals, with a certified tail enclosure at depth $500$:

| $c$ | $z_n$ | $\sum z_n$ | $\lim 4^{n}\gamma_n$ | certified gaps | structure | analogue |
|---:|---|---:|---:|---:|---|---|
| $-2$ | $\frac{1}{2^n+2}$ | $0.63225$ | $-4/3$ | $0$ | full interval | **FALSE** |
| $-1$ | $\frac{1}{2^n+1}$ | $0.76450$ | $-2/3$ | $0$ | full interval | **FALSE** |
| $0$ | $2^{-n}$ | $1$ | $0$ | $0$ | full interval (exactly $z_n=T_n$) | **FALSE** |
| $+1$ | $\frac{1}{2^n-1}$ | $1.6066952$ | $+2/3$ | all | Cantor, $\lvert C\rvert=1$ | **OPEN (Erdos 257)** |
| $+2$ | $\frac{1}{2^n-2}$ | $0.8033476$ | $+4/3$ | all | Cantor | OPEN |

($c=2$ is not new: $\frac{1}{2^n-2}=\frac12 z^{(1)}_{n-1}$, and the measured
total $0.8033476=E/2$ confirms it.  The $c=0$ row is settled by hand ---
$z_n=2^{-n}=T_n$ identically, so no strict inequality exists for a numerical
enclosure to certify, and the lab correctly reports it undecided rather than
claiming it.)

**The negative side is constructively false.**  For $c=-1$ every value in
$[0,0.76450]$ is a subsum, while every *finite* subsum of $\frac{1}{2^a+1}$
has odd denominator, since each $2^a+1$ is odd.  Therefore

$$\sum_{a\in A}\frac{1}{2^{a}+1}=\frac12 \quad\text{for an infinite }A,$$

with $A=\{1,3,5,6,7,9,13,15,17,18,19,21,22,26,\dots\}$ the forced greedy
support, which the lab runs to depth $2000$ selecting $1025$ ranks, $510$ of
them beyond depth $1000$.  For $c=0$ the same is immediate: $\frac13=\sum_{k\ge1}2^{-2k}$.

**Consequence.**  Erdos 257 is the *first* member of its own family with a
positive gap, and the gap it has is the smallest the family permits ---
relative size $\tfrac23 2^{-n}$ against the bridges.  One step down the
family and the problem is not merely easier, it is false with an explicit
witness.  Together with Section 4d (one step up in the base and every
rational dies) this brackets the problem tightly: **Erdos 257 occupies the
unique parameter point at which the achievement set is a Cantor set of full
measure.** Any argument that does not degrade as $c\downarrow0$ or $b\uparrow3$
is proving something that is either false or free.

### 4e.1  Even denominators need no infinitude argument

Every finite subsum of $\frac{1}{2^a-1}$ has odd denominator.  Hence a target
$x$ with **even** denominator can never be a finite Mersenne sum, and so

> if a target with even denominator survives the forced greedy, it is a
> counterexample outright --- the support is infinite automatically.

This removes a side condition rather than adding one, and it identifies the
canonical candidates.  The census already carries such targets: $q=512$,
$1024$, $2048$, $4096$ all show survivor fractions $0.623$--$0.624$, and
$1013/2048$ survives to certified depth $4\times10^4$ in the support-word lab.
It also fixes the correct target ring in $(5b.1)$: for even denominators the
criterion is $\Lambda(\ell,A)\in\mathbb Z[\tfrac12]$, not $\mathbb Z$.

## 4g.  The exact size of the conspiracy Erdos 257 requires

Owner: `scripts/required_excess_death_budget.py`
-> `state/.../required_excess_death_budget_receipt.json`.

$C$ has Lebesgue measure exactly $1$ inside $[0,E]$.  Of the $\lfloor qE\rfloor$
lattice points $p/q$ in $(0,E)$, a measure heuristic therefore predicts
$q(E-1)=0.6067q$ deaths and $q\lvert C\rvert=q$ survivors.  Erdos 257 asserts
that the only rationals in $C$ are the finite Mersenne sums.  So the exact
statement of what the theorem demands is:

$$\text{required excess deaths}\;=\;q\;-\;\#\{\text{finite Mersenne sums of denominator }q\}.$$

**The finite sums can be counted exactly.**  Let $x=\sum_{a\in F}z_a=p/q$ in
lowest terms, $F$ finite, and let $a\in F$ be maximal for divisibility inside
$F$.  By Bang's theorem $2^{a}-1$ has a primitive prime divisor $r$ whenever
$a\notin\{1,6\}$, and $r\mid 2^{b}-1$ iff $a\mid b$.  Writing
$x=N/\prod_{b\in F}(2^{b}-1)$ with $N=\sum_{c\in F}\prod_{b\ne c}(2^{b}-1)$,
every term with $c\ne a$ carries the factor $2^{a}-1$ and vanishes mod $r$,
while the $c=a$ term is $\prod_{b\ne a}(2^{b}-1)$, which $r$ divides only if
$a\mid b$ for some $b\in F\setminus\{a\}$ --- excluded by maximality.  Hence
$r\nmid N$ and $r$ survives into the reduced denominator, so $r\mid q$.  For
prime $q$ this forces $r=q$ and $a=\operatorname{ord}_q(2)$.  Every element of
$F$ divides a divisibility-maximal element, so

$$F\;\subseteq\;\{1,2,3,6\}\cup\{d:\ d\mid \operatorname{ord}_q(2)\}, \tag{4g.1}$$

which is small enough to enumerate completely; the reduced denominator of each
candidate is then computed exactly.  Measured:

| $q$ | $\operatorname{ord}_q(2)$ | lattice points | measure-predicted survivors | **finite sums (exact)** | required excess deaths |
|---:|---:|---:|---:|---:|---:|
| $97$ | $48$ | $155$ | $97$ | $0$ | $97$ |
| $101$ | $100$ | $162$ | $101$ | $0$ | $101$ |
| $193$ | $96$ | $310$ | $193$ | $0$ | $193$ |
| $257$ | $16$ | $412$ | $257$ | $0$ | $257$ |
| $509$ | $508$ | $817$ | $509$ | $0$ | $509$ |
| $673$ | $48$ | $1081$ | $673$ | $0$ | $673$ |
| $997$ | $332$ | $1601$ | $997$ | $0$ | $997$ |
| $1613$ | $52$ | $2591$ | $1613$ | $0$ | $1613$ |
| $2731$ | $26$ | $4387$ | $2731$ | $0$ | $2731$ |
| $4099$ | $4098$ | $6585$ | $4099$ | $0$ | $4099$ |
| $10007$ | $5003$ | $16078$ | $10007$ | $0$ | $10007$ |
| $127=2^7-1$ | $7$ | $204$ | $127$ | $\mathbf 2$ | $125$ |
| $8191=2^{13}-1$ | $13$ | $13160$ | $8191$ | $\mathbf 2$ | $8189$ |
| $131071=2^{17}-1$ | $17$ | $210591$ | $131071$ | $\mathbf 2$ | $131069$ |

The displayed prime table is a measurement, not a classification.  The
universal claim that a non-Mersenne prime admits no finite Mersenne sum, and
that a Mersenne prime $q=2^e-1$ admits exactly two, is **false**:
$1/3+1/15=2/5$, and the composite table immediately below already lists
$q=5$ with sums $2/5,\ 7/5$.  What survives is a necessary-condition theorem,
not a census.  If a finite Mersenne sum has prime reduced denominator $p$ and
$L=\operatorname{ord}_p(2)>1$, then its support has a unique
divisibility-maximal element $L$; every prime divisor of $\Phi_L(2)$ equals
$p$; and $v_p(2^L-1)=1$.  These conditions do not classify all realisable
prime denominators.  The two-row Mersenne-prime pattern $F=\{e\}$ giving
$1/q$ and $F=\{1,e\}$ giving $1+1/q$ remains the measured behaviour of those
particular $q$ in the table, not a completeness theorem.

### 4g.1  Composite denominators, and the flagship targets

The same argument runs for composite $q$.  For a divisibility-maximal
$a\in F$ and $r$ a primitive prime divisor of $2^{a}-1$ we still get $r\mid q$,
so $a=\operatorname{ord}_r(2)$ for some prime $r\mid q$; adding the Bang
exceptions,

$$F\;\subseteq\;\bigcup\Big\{\operatorname{div}(a)\ :\ a\in\{1,6\}\cup\{\operatorname{ord}_r(2):r\mid q\ \text{prime}\}\Big\}, \tag{4g.2}$$

a superset of the true constraint, so enumerating it and computing each
reduced denominator exactly keeps the count exact.  Measured:

| $q$ | prime factors | subsets enumerated | finite sums | the sums |
|---:|---|---:|---:|---|
| $3$ | $3$ | $15$ | $2$ | $1/3,\ 4/3$ |
| $5$ | $5$ | $31$ | $2$ | $2/5,\ 7/5$ |
| $7$ | $7$ | $15$ | $2$ | $1/7,\ 8/7$ |
| $9$ | $3$ | $15$ | $\mathbf 0$ | --- |
| $15$ | $3,5$ | $31$ | $2$ | $1/15,\ 16/15$ |
| $21$ | $3,7$ | $15$ | $2$ | $10/21,\ 31/21$ |
| $33$ | $3,11$ | $63$ | $\mathbf 0$ | --- |
| $45$ | $3,5$ | $31$ | $\mathbf 0$ | --- |
| $63=2^6-1$ | $3,7$ | $15$ | $8$ | $1/63,\ 64/63,\ 22/63,\ 10/63,\dots$ |
| $105$ | $3,5,7$ | $31$ | $2$ | $22/105,\ 127/105$ |
| $255=2^8-1$ | $3,5,17$ | $63$ | $6$ | $1/255,\ 256/255,\ 86/255,\dots$ |
| $465$ | $3,5,31$ | $63$ | $2$ | $46/465,\ 511/465$ |
| $511=2^9-1$ | $7,73$ | $31$ | $4$ | $1/511,\ 512/511,\ 74/511,\ 585/511$ |
| $1023=2^{10}-1$ | $3,11,31$ | $63$ | $4$ | $1/1023,\ 1024/1023,\dots$ |
| $2047=2^{11}-1$ | $23,89$ | $31$ | $2$ | $1/2047,\ 2048/2047$ |
| $2049$ | $3,683$ | $63$ | $\mathbf 0$ | --- |
| $4095=2^{12}-1$ | $3,5,7,13$ | $63$ | $16$ | $1/4095,\ 4096/4095,\ 1366/4095,\dots$ |

Powers of two admit none at all: every finite Mersenne sum has odd
denominator.

**Consequence for the targets this directory actually studies.**  None of them
is a finite Mersenne sum:

* $q=9$ admits **no** finite sums, so $4/9$ is not one;
* $q=21$ admits exactly $10/21$ and $31/21$, so $1/21$, $2/21$, $5/21$ and
  $8/21$ are not;
* $q=465$ admits exactly $46/465$ and $511/465$, so $1/465$ is not;
* $q=511$ admits exactly $1/511,512/511,74/511,585/511$, so $90/511$ is not;
* $q=2048$ is a power of two, so $1013/2048$ is not.

Every one of the flagship targets is therefore a **genuine counterexample
candidate**: if its forced greedy never dies, its support is infinite and
Erdos 257 is false.  That removes a side condition which had not been checked
--- survival alone would not have sufficed had any of them turned out to be a
finite sum.

**What this says.**  For every non-Mersenne prime $q$, Erdos 257 asserts

$$C\;\cap\;\tfrac1q\mathbb Z\;=\;\emptyset,$$

i.e. a closed set of measure $1$ inside an interval of length $1.6067$
contains **not one** of the $\lfloor qE\rfloor$ lattice points.  The required
excess is the entire surviving population, $q$ points.

**Where that excess would have to live, stated correctly.**  The natural
first reading --- "the theorem needs a factor $2^{D}$ more deaths at depth
$D$" --- is the wrong invariant.  Let $\rho_n$ be the conditional probability
of death at rank $n$ given survival to $n-1$.  Survival forever has
probability $\prod_n(1-\rho_n)$, which vanishes **iff $\sum_n\rho_n=\infty$**.
So the correct statement is a summability one:

> Erdos 257 requires $\sum_{n\ge1}\rho_n=\infty$ for every rational target,
> while the Cantor measure gives $\rho_n\approx\tfrac13 2^{-n}$, which is
> summable with total $\log(E)$-worth of mass concentrated almost entirely
> below rank $5$.

Two consequences that a bare factor-counting misses.

*   **No constant-factor mechanism can work, at any depth.**  Multiplying a
    summable rate by any constant leaves it summable, so the survivor
    probability stays positive.  A proof must produce a rate that is not
    merely larger but *non-summable* --- decaying no faster than $1/n$, say
    --- which is an infinitely stronger conclusion than "deaths are more
    frequent than the measure suggests".
*   **The measured rate is decisively not of that kind.**  If $\rho_n\ge c/n$
    held, the expected deaths per target below depth $N$ would be
    $c\log N\approx10c$ at $N=2.5\times10^4$, so essentially every target
    would already be dead.  The deep-run scan finds $247$ of $395$ alive, i.e.
    $\sum_{n\le2.5\times10^4}\rho_n\approx0.475$, of which effectively all
    comes from $n\le10$.  Measured deaths match the measure at every $q$
    tested ($q=10007$: $6078$ observed against $6071$ predicted).

So the whole of the required divergence must come from
$n>2.5\times10^{4}$, with the partial sums up to that depth already measured
and bounded.

**This is not evidence that Erdos 257 is false.**  The rationals are a
measure-zero set, and a measure-zero set may perfectly well be disjoint from a
closed set of full measure; that is precisely what the theorem claims.  What
the table fixes is the *shape* of what a proof must supply: a non-summable
death rate whose entire divergence lives beyond every depth reached here, and
uniform over every denominator.  Any mechanism that biases the death rate by a
constant factor, or that acts only below a bounded depth, is provably
incapable of producing it, because summable rates stay summable.

### 4g.2  The same statement as a Diophantine condition

Worth recording because it names a standard invariant.  Section 3 gives death
at rank $m$ as $\delta_m=T_m-r_{m-1}<0$, i.e. $u_{m-1}=2^{m-1}r_{m-1}$
reaching $\tfrac12$ from below within $2^{m-1}\gamma_m\approx\tfrac13 2^{-m}$.
Since $u_{m-1}=\{2^{m-1}\alpha\}$ up to $O(2^{-m})$, with
$\alpha=\sum_{a\in A}2^{-a}$, this is

$$\|2^{m}\alpha\|\;\lesssim\;\tfrac23\,2^{-m}
\qquad\Longleftrightarrow\qquad
\Big|\alpha-\frac{p}{2^{m}}\Big|\;\lesssim\;\tfrac23\,(2^{m})^{-2}.$$

So:

> $x\in C$ $\iff$ $\alpha$ is **badly approximable by dyadic rationals at
> exponent $2$**, with the explicit constant $\tfrac23$; and Erdos 257 asserts
> that every $\alpha$ arising from a rational $x$ admits infinitely many
> dyadic approximations of exponent $2$.

Almost every real is badly approximable in this sense --- $\sum_m 2^m\cdot\tfrac23 4^{-m}<\infty$
and Borel--Cantelli --- which is again $\lvert C\rvert=1$.

**Two corrections.**  First, this criterion is not new here: it is derived,
with the same constant, in `erdos257_hole_geometry/notes/ProgrammeSpine.md`
Section 4.  Second, an earlier draft of this subsection quantified it by run
lengths --- "measured dyadic exponent $1+\max_m L_m/m\approx1.0009$" --- which
is the reading that note retracts, for the reason given in Section 4b above.
That sentence is withdrawn.

The same source records the deeper obstruction, which is worth carrying here:
the criterion lives in the *extended* coordinate on all of $[0,E]$, and for a
point already known to lie in $C$ it holds automatically.  So it cannot be
evaluated for a candidate target without already knowing that target's
itinerary --- that is, without already knowing the answer.  What remains
correct and useful is the framing: the theorem is the claim that an implicitly
defined family of reals is uniformly *non*-generic in a standard Diophantine
sense.

## 5.  The counterexample set is closed under finite modification

A one-line lemma with a methodological consequence that the directory's
framing currently gets backwards.

> **Lemma.**  Let $A$ be infinite with $x=\sum_{a\in A}z_a\in\mathbb Q$, and
> let $F\subseteq\mathbb N$ be finite.  Then $A\triangle F$ is infinite and
> $$\sum_{a\in A\triangle F}z_a \;=\; x+\sum_{a\in F\setminus A}z_a-\sum_{a\in F\cap A}z_a\;\in\;\mathbb Q .$$
> So $A\triangle F$ is again a counterexample.

*Proof.*  Both displayed sums are finite sums of rationals.  $\square$

Consequences, all immediate:

1.  **No minimal counterexample, and no isolated one.**  Counterexamples
    occur in infinite families; the number of counterexample values in any
    interval is $0$ or infinite.
2.  **Free normalisation at any finite prefix.**  If a counterexample exists
    then for every $N$ one exists with $A\cap[1,N]=\emptyset$ --- namely the
    greedy remainder $r_N$, which is rational with support $A\cap(N,\infty)$
    --- and one exists with $A\supseteq[1,N]$.  Hence

    $$\text{Erdos 257}\iff \text{for every }\varepsilon>0\text{, no rational
      in }(0,\varepsilon)\text{ has infinite greedy support.}$$

3.  **The problem is a tail statement.**  Membership of the counterexample
    class depends only on the tail of the support word, so a *proof* of
    Erdos 257 cannot draw on the exact initial state: whatever prefix a
    hypothetical counterexample has, another one has any other prefix.

Point 3 corrects an emphasis in `Erdos257ResearchFrontierCloseout.md`, whose
"exact missing piece" is stated as a *global ancestry--boundary exclusion*
for a trajectory that "starts at the exact rational source state".  For a
**disproof** --- exhibiting one surviving target such as $1/465$ or $4/9$ ---
source-specific forcing is exactly right and the initial state is the whole
resource.  For a **proof** it cannot be, by the Lemma: the initial state
carries no information about whether the class is empty.  Sockets 1 and 2 of
that closeout are disproof sockets and are unaffected; socket 3 (dense-support
irrationality) is the proof socket and is correctly stated as a tail
condition.  Work that seeks a proof by exploiting the ancestry of a
particular rational source is spending on a resource that provably cannot
decide the question.

Note also that $E-x=\sum_{a\notin A}z_a$, so $C$ is symmetric about $E/2$;
since $E$ is irrational (Erdos, 1948), at most one of $A,\ \mathbb N\setminus A$
can give a rational, and in particular no counterexample has cofinite support.

## 5b.  A carry-free criterion: the $\Lambda$ integrality law

Owner: `scripts/lambda_integrality_criterion_lab.py`
-> `state/.../lambda_integrality_criterion_receipt.json`.

Every $z_a$ has odd denominator, so $x=\sum_{a\in A}z_a$ is rational exactly
when $(2^{\ell}-1)x\in\mathbb Z$ for some $\ell\ge1$; one may take
$\ell_0=\operatorname{ord}_q(2)$, and then the condition holds for every
multiple of $\ell_0$.  Division with remainder in the *exponent* gives, for
all $a,\ell$,

$$\frac{2^{\ell}-1}{2^{a}-1}
=\underbrace{2^{\ell\bmod a}\cdot\frac{2^{\,a\lfloor \ell/a\rfloor}-1}{2^{a}-1}}_{\in\ \mathbb Z}
\;+\;\frac{2^{\,\ell\bmod a}-1}{2^{a}-1},$$

and the second summand is summable over $a\in A$ (for $a>\ell$ it is
$(2^\ell-1)/(2^a-1)$).  Hence the exact congruence

$$(2^{\ell}-1)\,x \;\equiv\; \Lambda(\ell,A)\pmod 1,\qquad
\Lambda(\ell,A):=\sum_{a\in A}\frac{2^{\,\ell\bmod a}-1}{2^{a}-1}, \tag{5b.1}$$

and therefore

> **Erdos 257 $\iff$ for every infinite $A\subseteq\mathbb N$ and every
> $\ell\ge1$, $\Lambda(\ell,A)\notin\mathbb Z[\tfrac12]$.**

(The dyadic ring, not $\mathbb Z$, is the right target: $x$ is rational iff its
binary expansion is eventually periodic, i.e. $2^{m}(2^{\ell}-1)x\in\mathbb Z$
for some preperiod $m$ and period $\ell$, and the same exponent division gives
$2^m(2^\ell-1)x\equiv 2^m\Lambda(\ell,A)\pmod 1$.  When $x$ has odd
denominator --- the case for every finite Mersenne sum --- one may take $m=0$
and the condition is plain integrality.)

Every term lies in $[0,\tfrac12)$ and vanishes exactly when $a\mid\ell$.  No
carry, no cylinder, no reservoir, no dyadic seam appears: the entire problem
is that a convergent sum of explicit rationals is never an integer.

**What the terms actually weigh.**  Put $j_a(\ell)=a-(\ell\bmod a)$, the
distance from $\ell$ up to the next multiple of $a$ (and $j_a=a$ when
$a\mid\ell$).  Then, exactly,

$$\frac{2^{\ell\bmod a}-1}{2^{a}-1}
= 2^{-j_a(\ell)}\Big(1-\frac{2^{\,j_a(\ell)}-1}{2^{a}-1}\Big),
\qquad\text{so}\qquad
\Lambda(\ell,A)=\sum_{a\in A}2^{-j_a(\ell)}\;-\;\sum_{a\in A}\frac{1-2^{-j_a(\ell)}}{2^{a}-1}. \tag{5b.2}$$

So $\Lambda$ is dominated by those $a\in A$ whose *first multiple above*
$\ell$ is only a few steps above $\ell$, with geometric weight $2^{-j}$.
That recovers $\sum_{j\ge1}f_A(\ell+j)2^{-j}$, the quantity the integer-carry
coordinate calls $Q_\ell$ --- but now derived with no dynamics at all, purely
from exponent arithmetic.  The two descriptions of Erdos 257 are the same
object seen from opposite sides, and $(5b.1)$ is the side with no carries in
it.

**Independent validation.**  $(5b.1)$ is a hard cross-check of the whole
pipeline, because the support $A$ is produced by dyadic enclosures on the
real remainder while $\Lambda$ is a carry-free exponent sum.  At certified
depth $1.2\times10^4$ the lab confirms integrality of $\Lambda(k\ell_0,A)$ to
within $1.7\times10^{-113}$ --- the residual being exactly the truncation of
$A$ --- on every progression tested:

| target | $\ell_0=\operatorname{ord}_q(2)$ | multiples checked | max distance to $\mathbb Z$ |
|---|---:|---:|---:|
| $1/21$, $2/21$, $8/21$, $4/9$ | $6$ | $666$ | $<1.69\times10^{-113}$ |
| $1/5$ | $4$ | $1000$ | $<1.66\times10^{-113}$ |
| $90/511$ | $9$ | $444$ | $<1.61\times10^{-113}$ |
| $3/11$ | $10$ | $400$ | $<1.63\times10^{-113}$ |
| $1/465$ | $20$ | $200$ | $<1.61\times10^{-113}$ |
| $17/29$ | $28$ | $142$ | $<1.66\times10^{-113}$ |

For $\ell$ *not* a multiple of $\ell_0$ the distance to $\mathbb Z$ takes only
the values forced by $(5b.1)$ --- for $x=4/9$ exactly
$\tfrac19,\tfrac29,\tfrac13,\tfrac49$, which is $\{(2^\ell-1)\cdot\tfrac49\}$.

The integer values themselves are informative: on the progression they are
$0,0,0,\dots,1,0,1,\dots$ --- small and slowly growing --- and they coincide
with the integer carry, since for $\ell\in\ell_0\mathbb Z$ one has
$\theta_\ell=\theta_0$ and hence

$$\Lambda(k\ell_0,A)\;=\;\tilde Q_{k\ell_0},$$

the same integer the directory's carry recurrence computes.  The carry-free
route and the carry route return literally the same number.

**Status of this reformulation.**  Under the admission rule of
`Erdos257ResearchFrontierCloseout.md` this is *not* a new route: it is the
same residual in another normalisation, and it produces no one-way theorem by
itself.  Its value is (i) it states Erdos 257 with no dynamics, no carry and
no cylinder in it, which is the form in which Section 5's characteristic-two
elimination applies directly, and (ii) it is a genuinely independent check on
every support word this directory computes.

**Where the barrier reappears.**  $(5b.1)$ makes the shape of the obstacle
explicit.  Fix $\ell_0$ and try to defeat integrality by moving $\ell$ inside
$\ell_0\mathbb Z$.  Taking $\ell=\operatorname{lcm}(1,\dots,M)$ annihilates
every term with $a\le M$, and comparing $\ell$ with $\ell+\operatorname{lcm}$
of a chosen subset isolates any prescribed finite family of $a$.  What cannot
be controlled is the set of $a\in A$ with $a>M$: their residues $\ell\bmod a$
move with $\ell$ and their contribution is neither small nor computable from
a finite prefix.  This is the same *global reachability from the actual
initial state* named in `Erdos257ResearchFrontierCloseout.md`, now visible
without any dynamical apparatus --- evidence that the barrier is intrinsic
and not an artefact of the carry, cylinder, or reservoir coordinates in
which it has previously been met.

## 5c.  What a denominator census can and cannot see

A methodological bound that constrains this directory's own evidence, and
invalidates a natural class of future census work.

The greedy decisions to depth $N$ depend on $x$ only through an interval of
width $\gamma_N=\tfrac23 4^{-N}(1+O(2^{-N}))$: two targets agreeing to $2N$
binary digits and not straddling a gap boundary have identical words to depth
$N$.  Rationals with denominator $q$ are $1/q$-spaced.  Hence for

$$N \;>\; \log_4 q + O(1)$$

the depth-$N$ statistics of $\{p/q\}$ are *forced* to agree with the
Cantor-measure statistics of a uniform real, and every death in such a census
necessarily occurs at depth $O(\log q)$.  The census of Section 4 confirms
this exactly --- deepest death $12$ at $q=10007$, where $\log_4 q=6.6$ --- but
it therefore carries **no information about the deep regime**, which is where
Erdos 257 lives.

The consequence for evidence design: a wide-but-shallow survivor census over
many denominators is uninformative past $\log_4 q$, no matter how many
targets it scans.  The informative shape is the opposite one --- **few
targets, run to depth $N\gg\log_4 q$** --- scored by an observable that is
sensitive at every depth.  The run law $(3.1)$ supplies exactly such an
observable, and `deep_run_anomaly_scan.py` is the corresponding instrument.

## 6.  A correction that future work should not repeat

The truncated-carry relaxation

$$Q_n=2Q_{n-1}+t_n-f_A(n),\qquad b_n=1 \text{ iff the resulting } Q_n\ge0$$

is **not** the forced greedy.  It maximises the truncated sum
$\sum_{m\le n}f_A(m)2^{-m}$ subject to staying below the truncated target,
but it ignores the pulses that an already-selected $d\le n$ will place at
multiples $m>n$; those are the term $\Gamma_n=\sum_{m>n}c^{(n)}_m2^{-m}$ in
$\sum_{d\le n}b_dz_d=\sum_{m\le n}f_A(m)2^{-m}+\Gamma_n$.  The relaxation
therefore banks digits that already overspend.  For $x=1/21$ it first
diverges from the forced greedy at **rank 6**: exactly, $r_5=1/21-1/31=10/651$
while $z_6=1/63=10.33/651$, so rank $6$ must be skipped, and the relaxation
takes it and dies at rank $10$.  A survivor found by the relaxation is still
a genuine representation (its success is sound, by monotone convergence),
but its *failures are not failures of the problem*.  The directory's own
$1/21$ engine (`check_twenty_one_greedy.py`, and the quotient recurrence in
`twenty_one_computational_structure_lab.py` that is cross-checked against
it) is the forced greedy and is unaffected.

## 7.  What this does and does not establish

Established here, and reproducible from the two receipts:

*   the exact gap series $(0.1)$, the measure identity $(1.1)$, the
    normalised map and hole $(2.2)$--$(2.3)$, and the run law $(3.1)$;
*   the characteristic-two counterexample family of Section 5;
*   the survivor-density and margin statistics of Section 4;
*   the relaxation correction of Section 6.

Not established, and not claimed:

*   nothing here proves or disproves Erdos 257, and no finite computation
    can;
*   the statistics are consistent with the null model, which is evidence
    about *mechanism*, not a probabilistic proof that any particular target
    survives;
*   the run law $(3.1)$ is exact but is a criterion, not a bound: it does
    not by itself bound $R_N$;
*   the characteristic-two result excludes a class of arguments; it does not
    suggest that the real problem is false.
