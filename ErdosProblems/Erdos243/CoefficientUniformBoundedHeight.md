# Coefficient-uniform bounded LCM height (ordinary)

Assimilated Type B r5 ordinary proof, 7 September 2026.  Not a replacement of
the Lean-checked bounded-negative flagship `boundedNegativePart_eventually_zero`.
Not a parent theorem for Erdős #243.  Vanishing is used only after boundedness,
to obtain stationarity.  The unit-fraction specialisation of the original-coordinate
criterion is already admitted; this note records the coefficient-general arithmetic.

Source return: `public-source-redacted://state/type_b_return_batches/erdos_revision_packets_r5_20260907/work/erdos_243/revision_r5/01_research_note.md`.
Finite checks: `scripts/check_erdos243_r5_revision_claims.py`.
Lean finite fence (if compiled): `CoefficientDivisorFence.lean`.

# Persistent divisors constrain jumps, not just states
## Ordinary research note for the fifth review of Erdős #243

**Status, 7 September 2026.** The theorems below are proved here as ordinary mathematics. They are proposed additions, not assertions of a completed Lean build, independent refereeing, priority, or resolution of Erdős #243. The supplied r5 snapshot is the baseline. The unit-numerator LCM-record method is already in that snapshot; the additions are its coefficient-uniform bounded-height formulation without normalised vanishing, a finite height certificate, the positive-numerator transfer, and exact examples separating the assumptions.

The existing bounded-negative theorem remains the short note's lead. These additions explain which part of its mechanism is reusable.

## 1. The distinction that makes the extension work

The primitive unit-fraction proof makes old multipliers coprime to later numerators. That particular assertion need not survive a change of numerator. The first-crossing proof needs less: when an old modulus divides both the current numerator and the clearing denominator, it divides the **jump**. A positive jump bounded by B cannot be divisible by a modulus exceeding B.

This replaces a restriction on admissible states by a restriction on admissible transitions. Integer coefficient forcing is a multiple of the clearing denominator, so it disappears from that divisibility test.

## 2. Coefficient-uniform bounded LCM height

**Theorem 1.** Let a_n ≥ 2 and L_n,U_n > 0 be integers, and let b_n be arbitrary integers. Put

\[
 \rho_n=\gcd(L_n,a_n),\qquad
 L_{n+1}=\operatorname{lcm}(L_n,a_n).
\]

Suppose

\[
 \rho_n U_{n+1}=a_nU_n-b_nL_n=U_n-V_n,
 \qquad V_n=b_nL_n-(a_n-1)U_n.
\]

If V_n ≥ −B eventually, for an integer B ≥ 0, then (U_n) is bounded.

There is **no** centring or normalised-vanishing assumption. There is no primitive gcd hypothesis, bound on b_n, or hypothesis that the states are tails of a convergent series.

### Proof

Discard the finite prefix before the lower bound. Since rho_n ≥ 1 and U_{n+1} > 0,

\[
 U_{n+1}\le \rho_nU_{n+1}=U_n-V_n\le U_n+B. \tag{1}
\]

If B=0, this already proves boundedness. Suppose B≥1 and, for a contradiction, that U is unbounded. There are then infinitely many strict running-record steps whose source U_n exceeds B: a record value above 2B has source above B by (1).

At such a step rho_n must equal 1. Indeed, rho_n ≥ 2 would give

\[
 U_{n+1}\le (U_n+B)/2<U_n,
\]

contrary to the record property. The multipliers at these record steps are pairwise coprime. An earlier multiplier divides every later L_n, whereas a multiplier at a fresh record is coprime to the current L_n. As these multipliers are integers at least 2, only finitely many of them are at most B.

Choose B earlier record multipliers m_0,...,m_{B−1}, each exceeding B. They are pairwise coprime and, after some time T, all divide L_n. Let

\[
 R=\max\{B,U_0,\ldots,U_T\},\qquad P=\prod_{i=0}^{B-1}m_i.
\]

By the Chinese remainder theorem choose z with

\[
 R<z\le R+P,\qquad m_i\mid z+i\quad(0\le i<B). \tag{2}
\]

As U is unbounded, there is a first step n≥T with U_{n+1}≥z+B. Its source satisfies U_n<z+B. By (1), U_n≥z, so U_n>B and U_{n+1}>U_n. The same argument as above gives rho_n=1. Set

\[
 d=U_{n+1}-U_n=(a_n-1)U_n-b_nL_n.
\]

Then 1≤d≤B. By (2), the particular source U_n=z+i is divisible by m_i. Since m_i also divides L_n, it divides d. This contradicts 0<d≤B<m_i. Therefore U is bounded. ∎

### A finite, explicit certificate

The second half of the proof does not require an infinite supply. Once B pairwise-coprime old multipliers exceeding B have appeared, and the lower bound is valid, (2) gives

\[
 \boxed{U_n<z+B\le R+P+B\quad(n\ge T).} \tag{3}
\]

Thus the proof has a finite certificate: a jump cap, a finite list of persistent divisors, and a CRT-covered interval. The fact that this list must appear on an unbounded trajectory is a separate argument. That separation is useful both for exposition and for formalisation.

The candidate Lean file in this packet formalises the intended **one-step certificate** and its iteration, not the construction of the CRT list or the global theorem. Its proof text has not been compiled in this environment.

### Only record errors need be bounded

**Corollary 1a (record-only version).** Theorem 1 remains true if the lower bound V_n≥−B is required only at all sufficiently late strict running-record steps

\[
 \mathcal R=\{n:U_{n+1}>\max_{j\le n}U_j\}.
\]

**Proof.** If U were unbounded, it would have arbitrarily high record steps. At those steps the assumed lower bound gives (1). A record value above 2B has source above B, hence rho=1. This again supplies arbitrarily many pairwise-coprime old multipliers greater than B. The first crossing of the CRT threshold is itself a record step, so (1) is available at that step too. These are the only steps at which the proof uses the jump bound. For B=0 no sufficiently late record can occur. ∎

Equivalently, every unbounded orbit in this coefficient-general class has unbounded negative V along its record steps. Large errors away from records are irrelevant to this particular height bound. The finite certificate (3) also holds under the record-only hypothesis.

### Stationarity uses the limit only afterwards

**Corollary 2.** Under Theorem 1, if V_n/U_n → 0, then V_n=0 eventually. Consequently rho_n=1 and U_{n+1}=U_n eventually.

**Proof.** Choose a positive integer K bounding U_n. The limit gives |V_n|<U_n/K≤1 eventually. Since V_n is integral, V_n=0 there. Then rho_nU_{n+1}=U_n. Thus U is a positive nonincreasing integer sequence and stabilises, after which rho_n=1. ∎

Notice the order: arithmetic supplies boundedness; the limit and integrality supply exact vanishing. The proof does not need zero to be absorbing in the coefficient-general setting.

## 3. Raw denominator-cleared states

**Corollary 3.** Suppose a_n≥2, C_n,D_n>0 and b_n are integers, with

\[
 C_{n+1}=a_nC_n-b_nD_n,\qquad D_{n+1}=a_nD_n,
\]

and define

\[
 E_n=b_nD_n-(a_n-1)C_n=C_n-C_{n+1}.
\]

If E_n≥−B eventually and E_n/C_n→0, then E_n=0 eventually. On that tail,

\[
 \boxed{b_n(a_{n+1}-1)=b_{n+1}a_n(a_n-1).} \tag{4}
\]

**Proof.** Set L_n=lcm(D_0,a_0,...,a_{n−1}) and M_n=D_n/L_n. The ratio M_n is a positive integer. Telescoping the raw recurrence gives

\[
 C_n/D_n=C_0/D_0-\sum_{j<n}b_j/a_j.
\]

Every denominator on the right divides L_n. Hence

\[
 U_n=L_n C_n/D_n=C_n/M_n
\]

is a positive integer. Put V_n=E_n/M_n=b_nL_n−(a_n−1)U_n. The exact LCM update is the one in Theorem 1. Also V_n≥−B eventually and V_n/U_n=E_n/C_n→0. Corollary 2 gives V_n=0 and thus E_n=0 eventually.

Now C is eventually a positive constant C. The two adjacent identities b_nD_n=(a_n−1)C and b_{n+1}D_{n+1}=(a_{n+1}−1)C, together with D_{n+1}=a_nD_n, give (4) after multiplying to eliminate D_n and cancelling C. No division by b_n is required. ∎

For b_n=1 this recovers the unit-fraction conclusion. It does not replace the source-checked theorem in the paper: the new generality is an ordinary consequence of the record mechanism pending separate verification.

## 4. A positive-numerator criterion in the original variables

**Theorem 4.** Let a_n be strictly increasing positive integers and b_n positive integers. Assume

\[
 \lambda_n=\frac{b_{n+1}a_n^2}{b_na_{n+1}}\longrightarrow1.
\]

Put A_n=lcm(a_1,...,a_{n−1}), with A_1=1. If

\[
 \sum_{n\ge1}b_n/a_n\in\mathbb Q,
 \qquad
 \boxed{\limsup_{n\to\infty}
 \frac{A_nb_n}{a_n}(\lambda_n-1)<+\infty,} \tag{5}
\]

then (4) holds eventually. Convergence of the positive series follows from the ratio assumption and a_n→∞; it need not be imposed separately.

Equivalently, failure of eventual recurrence (4), together with the other displayed hypotheses, proves irrationality of the series.

### Proof: the analytic bridge in full

Write t_n=b_n/a_n. Then

\[
 \frac{t_{n+1}}{t_n}=\frac{\lambda_n}{a_n}\to0.
\]

Thus t_n→0 and the series converges. Moreover b_n≥1 gives 1/a_n≤t_n. Eventually lambda_n≤2 and t_n<1/4, so

\[
 t_{n+1}\le2t_n^2.
\]

It follows by iteration that t_n decays at least doubly exponentially, and a_n≥1/t_n grows at least doubly exponentially.

For P_n=∏_{j<n}a_j, the exact identity

\[
 P_nt_n=t_1\prod_{j<n}\lambda_j
\]

and lambda_j→1 give P_nt_n=exp(o(n)). This is an upper and lower subexponential estimate; only the upper estimate is needed below.

Let x_n=∑_{j≥n}t_j. Since the successive ratios are eventually at most 1/2, a two-term expansion with a uniformly bounded remaining geometric tail gives

\[
 x_n=t_n\left(1+\frac{\lambda_n}{a_n}
       +O\!\left(\frac1{a_na_{n+1}}\right)\right). \tag{6}
\]

Let q be a positive denominator of the rational sum, and put

\[
 L_n=\operatorname{lcm}(q,a_1,\ldots,a_{n-1}),\quad
 U_n=L_nx_n,\quad V_n=L_n[b_n-(a_n-1)x_n].
\]

Rationality implies U_n is a positive integer, and V_n is integral. Clearing x_n−x_{n+1}=b_n/a_n gives the exact LCM dynamics. Equation (6) gives

\[
 \frac{V_n}{U_n}
 =1-\frac{a_nx_{n+1}}{x_n}\to0, \tag{7}
\]

because a_nx_{n+1}/x_n=lambda_n(1+o(1)). It also gives the sharper dictionary

\[
 V_n+L_nt_n(\lambda_n-1)
 =O\!\left(L_nt_n(1/a_n+1/a_{n+1})\right)=o(1). \tag{8}
\]

For the last equality use L_n≤qP_n, P_nt_n=exp(o(n)), and the doubly exponential lower growth of a_n. Finally,

\[
 L_n/A_n=q/\gcd(q,A_n)\in[1,q].
\]

Thus the finite upper bound in (5) gives an eventual lower bound on the integral V_n through (8). There is no assumption that q eventually divides A_n. Theorem 1 and (7) force V_n=0 eventually. The same holds for the product-cleared error, so Corollary 3 gives (4). ∎

The same proof permits (5) to be imposed only along the canonical LCM record indices. That is a state-dependent sufficient condition, not a condition phrased solely in successive original terms.

### Scope and antecedents

For b_n=1 this is the already-admitted LCM-weighted criterion, not a new unit-fraction headline. For varying b_n, the terminal recurrence is exactly the weighted Sylvester equality appearing in Badea's 1993 positive-term criteria. The proposed contribution here is the different one-sided, finite weighted-defect hypothesis and its coefficient-independent first-crossing proof, not the discovery of weighted Sylvester sequences. No literature-wide novelty claim is made.

Within the lambda_n→1 setting, Badea's eventual inequality

\[
 a_{n+1}\ge(b_{n+1}/b_n)a_n(a_n-1)+1
\]

implies lambda_n−1≤1/(a_n−1). Hence the left side of (5) has limsup at most zero, using A_nt_n≤P_nt_n=exp(o(n)). This verifies inclusion of that classical sufficient region **within this setting**; it is not an unconditional comparison of the two theorems' full hypothesis classes.

The weighted rational examples w_n=1+b_nt∏_{j<n}w_j and their telescoping sums are already in Badea. They are appropriate test cases, not a new construction attributed to this review.

## 5. Three exact examples separating the hypotheses

### 5.1 Unit numerators: bounded LCM height without zero error

Start k_0=1 and set

\[
 k_{n+1}=k_n(k_n+1),\quad L_n=2k_n,\quad
 a_n=2(k_n+1),\quad b_n=1,\quad U_n=1.
\]

Then gcd(L_n,a_n)=2 and lcm(L_n,a_n)=2k_n(k_n+1)=L_{n+1}. Moreover

\[
 \rho_nU_{n+1}=2=a_nU_n-L_n,
 \qquad V_n=-1.
\]

The denominator sequence begins 4,6,14,86,3614,... and

\[
 \frac1{a_n}=\frac1{L_n}-\frac1{L_{n+1}},\qquad
 \sum_{n\ge0}\frac1{a_n}=\frac12.
\]

Thus bounded height and bounded negative error alone do not imply V=0. Normalised vanishing fails: V_n/U_n=−1. The quadratic ratio a_{n+1}/a_n²→1/2, not 1. This is not a counterexample to #243 or to the flagship.

### 5.2 Even permanent freshness does not replace normalised vanishing

Start L_0=U_0=1. At an even step, L is odd and U=1. Take b=1 and a=L+2, yielding

\[
 L'=L(L+2)\equiv3\pmod4,\qquad U'=2.
\]

At the next step take b'=3 and a'=(3L'+1)/2. Both a' and L' are odd, gcd(a',L')=1, and

\[
 L''=a'L'\text{ is odd},\qquad U''=2a'-3L'=1.
\]

This repeats indefinitely. Every overlap factor is 1, U alternates between 1 and 2, and V alternates between −1 and 1. The multipliers begin

\[
 3,5,17,383,97667,\ldots
\]

and are strictly increasing. Exact telescoping gives

\[
 \frac13+\frac35+\frac1{17}+\frac3{383}+\cdots=1.
\]

The normalised errors alternate between −1 and 1/2. Correspondingly lambda_n has limiting values 2 and 1/2 along the two parities. This defeats the claim that bounded LCM height plus absence of overlap should force stationarity in the coefficient-general system.

### 5.3 Old multipliers may divide later numerators

Start L_0=1,U_0=2 and take a_0=b_0=3. Then L_1=3,U_1=3. For n≥1 take b_n=3 and a_n=L_n+1. Every subsequent overlap is 1, U_n=3 throughout, and V_n=0. The old multiplier 3 divides every later numerator.

Thus the primitive unit-numerator assertion “each old multiplier is coprime to every later numerator” is false for positive integral coefficients. Nevertheless Theorem 1 applies. The jump-divisibility formulation is exactly what survives this change of forcing.

## 6. What this does and does not buy for #243

The new ordinary proof separates two tasks that the original argument intertwined:

1. a coefficient-independent arithmetic bound on the LCM height;
2. an analytic/discrete conversion from bounded height to exact stationarity.

It supplies a transfer to a natural larger class of positive rational series. It does **not** derive a lower bound on V from the unqualified #243 hypotheses. In the unit-fraction parent, the admitted unresolved target remains

\[
 \exists B\ge0:\quad \liminf_{X\to\infty}\frac1X
 \sum_{\substack{n\in\mathcal R\\U_n\le X}}(-V_n-B)_+=0.
\]

The next argument must control the cumulative cost at the actual crossing heights, or provide an equally effective canonical arithmetic constraint. Separate estimates of small local error, plentiful old moduli, and rare overlap do not automatically synchronise those quantities.

## References and verification boundaries

The proof development above is self-contained apart from the Chinese remainder theorem. Literature comparisons are documented in `03_literature_and_claims.md`. The input's existing record method is in `ErdosProblems/Erdos243/LcmRecordExcess.md`; the canonical transfer and existing LCM criterion are in `LcmDefectCriterionReduction.md` and the corresponding live claim records. The test program checks finite identities and examples, not the infinite quantified theorems. The accompanying Lean file is a candidate requiring compilation.
