---
title: "Erdős 1049: quantitative selector escape and cyclotomic boundary signatures"
subtitle: "R5 mathematical dossier and source-facing refinements"
date: "7 September 2026"
lang: en-GB
---

# Scope and disposition

The live R5 short note supplies the mathematical authority for this review. Its rational-base theorem and exact normalised Hankel order remain the flagship results. The principal edit is to expose cancellation before homogenisation, then print the degree, positivity and denominator argument together. The second proof is shortened through the already supplied formal moment expansion. Neither edit changes the theorem's mathematical conclusion.

This dossier supplies two further ordinary arguments. The first is a quantitative extension of the live bounded-fibre escape lemma. It asks for the multiplicity of real values *inside a modular fibre*, then bins those values into short intervals. Its application to the narrow R4 family identifies an obstruction to certification by the full remainder span. The second turns radial root-of-unity asymptotics into linear independence over $\mathbb C(z)$ of arbitrary finite sets of positive dilates of the divisor Lambert series, including any finite collection of their Euler derivatives.

The first argument is an elementary consequence of the supplied finite lemma. The second combines elementary asymptotics with classical positivity of gcd matrices. Bibliographical novelty of the resulting mixed differential-dilation statement has not been established. These are ordinary proofs for adjudication, not independently refereed results or completed Lean formalisation. No new irrational base is claimed beyond the live theorem. In particular, neither argument proves irrationality of $F(3/2)$.

The March 2026 Bell–Smertnig preprint already implies that the divisor generating series is not $k$-Mahler for any $k\ge2$ [BS]. Thus the single-$k$ corollary below is known, and the live note's statement that its discussion says nothing about single-$k$ systems should be updated from the literature. The proposed mixed-dilation proof has a stronger scope and a direct, problem-specific mechanism.

# 1. A quantitative version of bounded-fibre escape

## 1.1 The finite theorem

**Theorem A (conditional multiplicity and short-interval escape).** Let $\mathcal A$ be a nonempty finite set of cardinality $N$. Let
$$
f:\mathcal A\longrightarrow\mathcal B,\qquad
u:\mathcal A\longrightarrow\mathbb R,
$$
where $|f(\mathcal A)|\le Q$. Suppose that $u(\mathcal A)$ is contained in an interval of length $T\ge0$. Assume that every simultaneous fibre has cardinality at most $k$:
$$
\#\{x\in\mathcal A:f(x)=b,\ u(x)=y\}\le k
\quad(b\in\mathcal B,\ y\in\mathbb R).
$$
For any $\delta>0$, the inequality
$$
\boxed{N>Qk\left(\left\lfloor\frac T\delta\right\rfloor+1\right)}
\tag{1.1}
$$
implies the existence of $x,y\in\mathcal A$ such that
$$
f(x)=f(y),\qquad 0<|u(x)-u(y)|<\delta.
$$
In particular $x\ne y$.

**Proof.** Choose $c$ with $u(\mathcal A)\subset[c,c+T]$. Give $x$ the bin label
$$
b(x)=\left\lfloor\frac{u(x)-c}{\delta}\right\rfloor
\in\{0,\ldots,\lfloor T/\delta\rfloor\}.
$$
At most $Q(\lfloor T/\delta\rfloor+1)$ pairs $(f(x),b(x))$ occur. By (1.1), one such cell contains more than $k$ points. They cannot all have the same $u$-value, because $f$ is already fixed in that cell. Choose two with distinct values. A half-open bin has diameter strictly less than $\delta$ between any two of its members. This gives both inequalities. The use of $\lfloor T/\delta\rfloor+1$ also handles an attained right endpoint when $T/\delta$ is an integer. $\square$

The relevant multiplicity is conditional on the modular signature. Equal real values in different modular fibres do not obstruct the desired collision. A bound for the full $u$-fibre also suffices, but can be unnecessarily stronger.

This is an application of the live theorem `exists_ne_map_eq_map_ne_of_card_mul_lt` to the signature augmented by a bin. The companion Lean source gives that finite composition explicitly. It does not claim to construct bins, estimates or source remainders in Lean.

## 1.2 Application to primitive integer rows

Fix real $\xi$ and integer pairs
$$
w_j=(A_j,B_j)\in\mathbb Z^2,\quad 1\le j\le M,
\qquad e_j=A_j\xi-B_j.
$$
Let $D\ge1$, and take $\mathcal A=\{0,1\}^M$ with
$$
f(\varepsilon)=\sum_j\varepsilon_jw_j\pmod D,
\qquad u(\varepsilon)=\sum_j\varepsilon_je_j.
$$
The exact span of the subset-sum values is
$$
T=\sum_j|e_j|,
$$
since their largest value is $\sum_{e_j>0}e_j$ and their smallest is $\sum_{e_j<0}e_j$. Let $Q$ bound the number of possible modular signatures, and let $k$ bound the conditional multiplicity in Theorem A. For an integer $n\ge1$, the explicit sufficient condition is
$$
\boxed{2^M>Qk\left(\left\lfloor\frac{nT}{D}\right\rfloor+1\right).}
\tag{1.2}
$$
Then there is $\lambda\in\{-1,0,1\}^M\setminus\{0\}$ such that
$$
D\mid\sum_j\lambda_jA_j,\qquad
D\mid\sum_j\lambda_jB_j,
$$
and
$$
0<\left|\sum_j\lambda_je_j\right|<D/n.
$$
After division by $D$ this is a nonzero integer linear form in $\xi$ of absolute value less than $1/n$.

When the pairs are homogeneous evaluations of actual source polynomials, the nonzero real remainder also guarantees that the combined polynomial pair and the combined specialised integer pair are both nonzero. These conclusions follow from the *last* map, rather than from a rank assertion about an earlier map.

Condition (1.2) has three source-dependent quantities: modular image size, conditional multiplicity of exact real values, and real remainder span. It has no coefficient-height factor. Height is still useful for proving estimates on these quantities, or for determinant arguments, but it is not an extra factor in the scalar irrationality criterion.

## 1.3 The exponent form

Suppose, on a scale $n^2$, that
$$
M_n\ge(m-o(1))n^2,\quad
\log Q_n\le(q+o(1))n^2,\quad
\log k_n\le(\kappa+o(1))n^2,
$$
$$
\log T_n\le(\tau+o(1))n^2,\qquad
\log D_n\ge(d-o(1))n^2.
$$
Then (1.2) follows eventually from
$$
\boxed{m\log2>q+\kappa+\max\{0,\tau-d\}.}
\tag{1.3}
$$
Indeed the logarithm of $\lfloor nT_n/D_n\rfloor+1$ is at most
$(\max\{0,\tau-d\}+o(1))n^2$; a strict margin absorbs all lower-order terms.

If, in addition, $\log D_n=(d+o(1))n^2$ and the modular row image satisfies $Q_n\le D_n$, the criterion simplifies to
$$
\boxed{m\log2>\kappa+\max\{d,\tau\}.}
\tag{1.4}
$$
Under the same two-sided exponent assumption on $D_n$, the ambient estimate $Q_n\le D_n^2$ instead gives
$$
m\log2>\kappa+\max\{2d,d+\tau\}.
$$
Thus the proved modular collapse removes a full exponential cost, but does not remove either remainder multiplicity or remainder span.

For the wide R4 rectangle at its native scale $m$, there are $6m^2+12m$ rows and $D_m=6^{m^2}$ with $Q_m=D_m$. A sufficient quantitative goal is consequently
$$
\boxed{\kappa+\max\{\log6,\tau\}<6\log2.}
\tag{1.5}
$$
No bound establishing (1.5) for those primitive real remainders is supplied here. The source's bounded *unnormalised* positive remainder cannot be substituted for $T_m$: each $e_j$ must be measured after the specified integral clearing and primitive normalisation.

A multiplicity estimate at $\xi=F(3/2)$ must not assume that $\xi$ is irrational. Signed noncollapse of integer pairs makes the real-value map injective at an irrational target, but using that implication here would assume the desired conclusion. The useful estimate must hold independently of the target's unknown arithmetic status.

## 1.4 Local refinement

One can use a span $T_b$ and conditional multiplicity $k_b$ separately in each nonempty modular fibre. The same proof gives the sufficient condition
$$
N>\sum_{b\in f(\mathcal A)}k_b
 \left(\left\lfloor T_b/\delta\right\rfloor+1\right).
\tag{1.6}
$$
This identifies a meaningful next estimate when the full span is too large: control the distribution *inside modular fibres*, or restrict to an explicitly constructed large subfamily of selectors with a shorter range. Theorem A applies to any such finite subfamily. Its cardinality, conditional multiplicity and span must all be proved for that same subfamily.

# 2. What the narrow R4 family teaches about this method

The following use of R4 is conditional only on results the live packet already records as ordinary arguments. It does not silently upgrade their formal evidence.

Let the narrow source-derived family at scale $m$ have $M_m$ rows. Write
$$
H_m=\max_j|A_j|,\qquad T_m=\sum_j|A_j\xi-B_j|.
$$
The supplied R4 arguments give, for sufficiently large admissible $m$,
$$
M_m=(\lfloor m/10\rfloor+1)^2,
\qquad
\log(M_mH_m)\le K_{\min}(m)\log2-5m^2,
\tag{2.1}
$$
and every pair of distinct source rows has a nonzero minor divisible by $2^{K_{\min}(m)}$. The first coordinates are nonzero.

**Corollary B (full-span counting obstruction).** For every fixed real $\xi$,
$$
\boxed{T_m\ge M_m e^{5m^2}.}
\tag{2.2}
$$
Consequently, Theorem A with the full binary selector set, the full modular row-lattice image bound, and the full remainder span cannot certify divided errors below $1/n$ for this family, for any positive modulus $D$ and any $n\ge1$, once $m$ is sufficiently large.

**Proof.** Choose two distinct rows. For $e_j=A_j\xi-B_j$,
$$
A_iB_j-A_jB_i=A_je_i-A_ie_j.
$$
Hence
$$
2^{K_{\min}(m)}\le|A_iB_j-A_jB_i|
\le H_m(|e_i|+|e_j|)\le H_mT_m.
$$
Equation (2.1) gives (2.2). A lattice generated by primitive integer rows contains a primitive row whose reduction modulo $D$ has order $D$. Its modular image therefore has size $Q\ge D$. Also $k\ge1$. Since $\lfloor x\rfloor+1>x$ for all $x\ge0$,
$$
Qk\left(\left\lfloor\frac{nT_m}{D}\right\rfloor+1\right)>nT_m.
$$
But $\log 2^{M_m}=((\log2)/100+o(1))m^2$, whereas $\log T_m\ge5m^2+\log M_m$. Thus the sufficient inequality (1.2) fails for all such $D,n$. $\square$

This is a failure of the stated **global-span certificate**, not a theorem excluding every small collision. A set with a huge total span can still contain two very close points. The R4 regular-scale infinite-limsup theorem is a separate, stronger conclusion about actual minimum errors on its specified scale. The present corollary explains why a particularly natural quantitative pigeonhole refinement cannot certify success from the narrow family even though local cancellation and eventual real nonvanishing have been established.

The wide shifted rectangle is outside (2.1), so Corollary B says nothing about its actual approximation quality. Nor does it exclude a restricted selector family with a proved smaller span or the fibre-specific estimate (1.6).

# 3. One Smith invariant records both local compression and residual index

This section restates an already supplied elementary result because it is the most useful way to organise the short note's arithmetic. It is not a new priority claim.

Let $\Lambda\subset\mathbb Z^2$ be a rank-two lattice generated by primitive integer rows. Let $g>0$ be the gcd of their $2\times2$ minors. Its Smith invariants are $1,g$: the gcd of all matrix entries is one because any single primitive row has coprime coordinates, and the product of the invariants is the minor gcd.

For an integer $D\ge1$, put
$$
\Gamma_D=(\Lambda\cap D\mathbb Z^2)/D.
$$
Then
$$
\boxed{|\operatorname{im}(\Lambda\bmod D)|=\frac{D^2}{\gcd(g,D)},\qquad
[\mathbb Z^2:\Gamma_D]=\frac{g}{\gcd(g,D)}.}
\tag{3.1}
$$
To prove both identities, use a unimodular change of ambient coordinates taking $\Lambda$ to $\mathbb Z\oplus g\mathbb Z$. Such a change preserves $D\mathbb Z^2$. The modular coordinates have respectively $D$ and $D/\gcd(g,D)$ values. The intersection is $D\mathbb Z\oplus\operatorname{lcm}(g,D)\mathbb Z$; division by $D$ proves the index formula.

If $D\mid g$, the modular image has $D$ elements, and making $g$ still larger does not compress that image further. Meanwhile the residual index is $g/D$. This is the saturation trade-off: local image compression has reached its one-coordinate limit while the divided lattice can continue becoming more restrictive.

For two independent rows in $\Gamma_D$ with $|A_i|\le H$ and $|A_i\xi-B_i|\le\varepsilon$,
$$
\boxed{2H\varepsilon\ge[\mathbb Z^2:\Gamma_D].}
\tag{3.2}
$$
Their nonzero determinant is an integer multiple of the lattice index and has absolute value at most $2H\varepsilon$. This is a necessary bound for a two-independent-row argument. It is not an extra hypothesis in the one-form irrationality test.

The wide R4 family has
$$
v_2(g_m)=559m^2+68m+2,\qquad v_3(g_m)=m(m+1).
$$
At $D=6^{m^2}$, (3.1) gives modular image size exactly $D$ and a residual index divisible by
$$
2^{558m^2+68m+2}3^m.
$$
These two facts belong next to one another in any report of that family's local gain.

## 3.1 A necessary budget for the full-span counting certificate

There is a general constraint behind the narrow-family calculation. Suppose the $M$ primitive rows span a rank-two lattice with minor gcd $g$, let $H=\max_j|A_j|$, and use the entire binary selector set and its span $T=\sum_j|A_j\xi-B_j|$. Then
$$
T\ge g/H.
$$
Indeed a nonzero minor has absolute value at least $g$, while it is at most $H(|e_i|+|e_j|)\le HT$.

Take the full row-lattice image as the modular bound, $Q=D^2/\gcd(g,D)$, and test (1.2). Since $k\ge1$ and $\lfloor nT/D\rfloor+1>nT/D$, passing that sufficient test requires
$$
\boxed{2^M H> nD\,\frac{g}{\gcd(g,D)}.}
\tag{3.3}
$$
In particular, when $D\mid g$, it requires $2^M H>ng$, independently of $D$. Raising the modulus while it divides $g$ cannot rescue this *global-span, full-lattice-image certificate* from a failure of that necessary budget. The statement is about this sufficient test, not a necessary condition for an actual successful selector. A smaller observed image, a restricted selector set or short ranges inside modular fibres can change the test and must be analysed separately.

# 4. Cyclotomic boundary signatures and rational-function rank

Set
$$
\mathcal L(z)=\sum_{n\ge1}\frac{z^n}{1-z^n}
=\sum_{n\ge1}\tau(n)z^n,\qquad |z|<1,
\qquad \Theta=z\frac d{dz}.
$$
All series and differentiated series below converge locally uniformly in the open unit disc.

**Theorem C (mixed differential-dilation independence).** Fix distinct positive integers $m_1,\ldots,m_r$ and nonnegative integers $s_1,\ldots,s_r$. The functions
$$
\boxed{\{1\}\ \cup\ 
\{\Theta^j[\mathcal L(z^{m_i})]:1\le i\le r,\ 0\le j\le s_i\}}
\tag{4.1}
$$
are linearly independent over $\mathbb C(z)$.

In particular $1,\mathcal L(z^{m_1}),\ldots,\mathcal L(z^{m_r})$ are linearly independent over $\mathbb C(z)$ for every set of distinct positive dilations. The statement concerns linear functional relations only. It asserts neither algebraic independence nor linear independence of values at an algebraic point.

**General boundary-rank criterion.** Let $f_1,\ldots,f_r$ be analytic on the open unit disc. Suppose there are infinite sets $E_1,\ldots,E_r$ on the unit circle, an invertible complex matrix $M=(M_{hi})$, and a real function $A(t)\to+\infty$ as $t\downarrow0$, such that for each fixed $\zeta\in E_h$ there is $c_\zeta\ne0$ with
$$
\lim_{t\downarrow0}\frac{f_i(\zeta e^{-t})}{A(t)}=c_\zeta M_{hi}
\quad(1\le i\le r).
$$
Then $1,f_1,\ldots,f_r$ are linearly independent over $\mathbb C(z)$.

To prove this, clear the denominators in a proposed relation and take the radial limit at each fixed $\zeta\in E_h$. The polynomial $\sum_i M_{hi}P_i(z)$ vanishes at the infinitely many points of $E_h$, so it is zero. Invertibility of $M$ makes all $P_i$ zero; the constant-function coefficient is then zero as well. No uniformity over $\zeta$ is needed. This elementary criterion is the reusable mechanism of the dilation proof. For higher derivatives, the same argument is applied first at the largest singular scale and then successively to lower orders.

## 4.1 The radial signature

**Lemma C1.** If $\zeta$ is a root of unity of order $d$, then
$$
\mathcal L(\zeta e^{-t})
=\frac{\log(1/t)}{dt}+O_d(t^{-1})
\quad(t\downarrow0).
\tag{4.2}
$$
More generally, for $m\ge1$ and $s\ge0$,
$$
\boxed{
\Theta^s[\mathcal L(z^m)]\big|_{z=\zeta e^{-t}}
=\frac{s!\gcd(d,m)}{dm}
 \frac{\log(1/t)}{t^{s+1}}
+O_{d,m,s}(t^{-s-1}).}
\tag{4.3}
$$

**Proof for $s=0$.** In the Lambert sum split the indices into $d\mid n$ and $d\nmid n$. The first part is exactly $\mathcal L(e^{-dt})$. For every nontrivial $d$th root $\eta$,
$$
\min_{0\le r\le1}|1-r\eta|>0.
$$
The finitely many such roots therefore give a common bound on the remaining summands by $C_de^{-nt}$, whose sum is $O_d(t^{-1})$. Finally
$$
\mathcal L(e^{-u})=u^{-1}\log(1/u)+O(u^{-1}).
$$
To verify the last estimate, use $(e^x-1)^{-1}=x^{-1}+O(1)$ for $0<x\le1$ and sum up to $1/u$; the remaining geometric tail is $O(u^{-1})$. Replacing $\zeta$ by $\zeta^m$ and $t$ by $mt$ gives (4.3) for $s=0$, because the order of $\zeta^m$ is $d/\gcd(d,m)$.

**Derivative estimate.** We do not differentiate the preceding $O$-term. Define
$$
F_s(x)=\sum_{k\ge1}k^s e^{-kx}.
$$
For $0<x\le1$, comparison with the integral of $y^se^{-xy}$ gives
$$
F_s(x)=s!x^{-s-1}+O_s(x^{-s}),
\tag{4.4}
$$
with $O(1)$ when $s=0$. One way to make the comparison explicit is to bound the sum-integral error by the total variation of $y^se^{-xy}$ on $[0,\infty)$ plus its endpoint value; this is $O_s(x^{-s})$. For $x\ge1$, $F_s(x)\le C_s e^{-x}$.

Termwise differentiation gives
$$
\left(-\frac d{du}\right)^s\mathcal L(e^{-u})
=\sum_{n\ge1}n^sF_s(nu).
$$
For $n\le1/u$, (4.4) supplies
$$
s!u^{-s-1}\sum_{n\le1/u}\frac1n+O_s(u^{-s-1}).
$$
The terms $n>1/u$ contribute $O_s(u^{-s-1})$ by the exponential bound. Thus the leading term is $s!u^{-s-1}\log(1/u)$.

For a nontrivial root $\eta$, the function
$$
\left(r\frac d{dr}\right)^s\frac{r\eta}{1-r\eta}
$$
is a rational function bounded by $C_{d,s}r$ on $0\le r\le1$. This follows by induction: its denominator is a power of $1-r\eta$, its numerator has a factor $r$, and the denominator stays away from zero. The nonmultiple indices in the differentiated Lambert sum are consequently bounded by
$$
C_{d,m,s}\sum_{n\ge1}(mn)^s e^{-mnt}=O_{d,m,s}(t^{-s-1}).
$$
On the multiple indices the function is $\mathcal L(e^{-ht})$, where $h=md/\gcd(d,m)$. The chain rule multiplies its $s$th derivative by $h^s$, leaving leading coefficient $s!/h$. Also $\Theta=-d/dt$ along $z=\zeta e^{-t}$. This proves (4.3). $\square$

The implied constants may depend on the order $d$. No uniform estimate over all roots is used: each radial limit is taken at its fixed root before a polynomial root-counting argument is applied.

Root-of-unity expansions for Lambert series are classical and are treated much more fully in [DK, Section 2.4]. Only the elementary leading coefficient is needed here.

## 4.2 The arithmetic matrix

**Lemma C2 (classical gcd Gram matrix).** For distinct positive integers $m_1,\ldots,m_r$, the real symmetric matrix
$$
G_{ij}=\gcd(m_i,m_j)
$$
is positive definite, and hence invertible over $\mathbb C$.

**Proof.** Let $M=\operatorname{lcm}(m_1,\ldots,m_r)$. The elementary identity $\sum_{d\mid n}\varphi(d)=n$ gives
$$
\gcd(m_i,m_j)=\sum_{d\mid M}\varphi(d)
\mathbf1_{d\mid m_i}\mathbf1_{d\mid m_j}.
$$
Therefore, for $c\in\mathbb C^r$,
$$
\boxed{c^*Gc=
\sum_{d\mid M}\varphi(d)
\left|\sum_{i:d\mid m_i}c_i\right|^2.}
\tag{4.5}
$$
All weights are positive. If $c\ne0$, choose the largest $m_i$ for which $c_i\ne0$. The sum associated with $d=m_i$ is exactly $c_i$, because any other multiple in the selected set is larger and has zero coefficient. Thus (4.5) is strictly positive. $\square$

This is a classical incidence-Gram proof of gcd-matrix positivity. The proposed use is to interpret this matrix as a collection of boundary signatures of the Lambert dilates.

## 4.3 Proof of Theorem C

Clear rational-function denominators in a proposed relation to obtain
$$
P_0(z)+\sum_{i=1}^r\sum_{j=0}^{s_i}
P_{ij}(z)\Theta^j[\mathcal L(z^{m_i})]=0,
\qquad P_0,P_{ij}\in\mathbb C[z].
\tag{4.6}
$$
Let $s$ be the largest derivative order with a nonzero coefficient. Set missing $P_{is}$ equal to zero. At a root of unity $\zeta$ of order $d$, divide (4.6), evaluated at $z=\zeta e^{-t}$, by $s!t^{-s-1}\log(1/t)$ and let $t\downarrow0$. Lower derivative orders and the polynomial term tend to zero. Lemma C1 gives
$$
\sum_{i=1}^r\frac{\gcd(d,m_i)}{m_i}P_{is}(\zeta)=0.
\tag{4.7}
$$
Let $M=\operatorname{lcm}(m_1,\ldots,m_r)$. For each fixed $h\in\{1,\ldots,r\}$ choose the infinitely many distinct orders
$$
d_k=m_h(1+kM),\qquad k\ge1.
$$
Since $1+kM$ is coprime to every $m_i$,
$$
\gcd(d_k,m_i)=\gcd(m_h,m_i).
$$
Choose one primitive root of each order $d_k$. Equation (4.7) says that the polynomial
$$
Q_h(z)=\sum_{i=1}^r\frac{\gcd(m_h,m_i)}{m_i}P_{is}(z)
$$
vanishes at infinitely many distinct points. Hence $Q_h$ is identically zero. The coefficient matrix is $G\operatorname{diag}(1/m_i)$, which is invertible by Lemma C2. All $P_{is}$ vanish, contradicting the choice of $s$. Descending through the finite derivative orders leaves $P_0=0$. This proves the theorem. $\square$

For example, the three dilation indices $1,2,3$ produce
$$
G=\begin{pmatrix}1&1&1\\1&2&1\\1&1&3\end{pmatrix},
\qquad \det G=2.
$$
The proof establishes invertibility for arbitrary distinct indices, rather than only for this finite example.

## 4.4 Consequences and exact boundaries

For any fixed $k\ge2$, apply Theorem C with $m_i=k^{i-1}$. No nontrivial finite equation
$$
P_0(z)+\sum_i P_i(z)\mathcal L(z^{k^i})=0
$$
exists. In particular, no finite-dimensional $\mathbb C(z)$-space containing $\mathcal L$ is stable under $z\mapsto z^k$. The same is true for any proposed finite linear system which, after elimination, yields a finite differential-dilation relation of the displayed kind.

The single-$k$ conclusion is already a consequence of [BS]. Theorem C adds arbitrary mixed positive dilation indices and Euler derivatives to this direct proof. The searches recorded below did not establish priority for that full statement.

The result does not rule out nonlinear differential relations, nonlinear Mahler relations, infinite systems, $q$-difference equations with a different independent variable, or arithmetic arguments directly at $z=2/3$. It also does not prove that a particular finite Padé determinant is nonzero. Global functional independence and normality at a specified order are different assertions.

# 5. Sharp scope tests and a cheap Padé consequence

## 5.1 Many boundary singularities alone are insufficient

For $k\ge2$ set
$$
G_k(z)=\sum_{r\ge0}z^{k^r}.
$$
Then
$$
G_k(z)-G_k(z^k)=z.
\tag{5.1}
$$
At every root of unity whose order divides a power of $k$, all sufficiently late terms of $G_k(\zeta e^{-t})$ are positive real. Their sum grows as $\log(1/t)/\log k+O(1)$. These roots are dense on the unit circle, so the function has a dense set of boundary singularities, yet (5.1) is a finite Mahler relation.

The useful invariant in Theorem C is the *arithmetic variation of the leading coefficients*, not merely the presence or density of singularities. The gcd matrix separates these coefficients for distinct Lambert dilations.

## 5.2 Root-of-unity twists really can introduce relations

For prime $p$ and $\zeta_p=e^{2\pi i/p}$, a roots-of-unity filter and the identity
$$
\tau(pn)=2\tau(n)-\mathbf1_{p\mid n}\tau(n/p)
$$
give
$$
\boxed{\sum_{j=0}^{p-1}\mathcal L(\zeta_p^jz)
=2p\mathcal L(z^p)-p\mathcal L(z^{p^2}).}
\tag{5.2}
$$
For $p=2$ this is
$$
\mathcal L(-z)=4\mathcal L(z^2)-\mathcal L(z)-2\mathcal L(z^4).
$$
Thus Theorem C must specify *positive dilates*. A blanket assertion including arbitrary root-of-unity twists would be false. The $p=2$ identity is also a special case of [DK, equation (2.52)]. Finite trace identities such as (5.2) do not close the infinite positive-dilation orbit.

A natural follow-up is to classify rational-function linear relations among a fixed finite family of twisted dilates. The trace relations are unavoidable antecedents for that question. No completeness classification is proved here.

## 5.3 Functional nonvanishing is available cheaply; specialisation is not

Take any $r$ of the nonconstant functions in Theorem C, denoted $f_1,\ldots,f_r$. For $D\ge0$, the space
$$
\{P_0+P_1f_1+\cdots+P_rf_r: \deg P_i\le D\}
$$
has dimension $(r+1)(D+1)$ over $\mathbb Q$ when the functions have their rational Taylor coefficients, and the coefficient map is injective by Theorem C. Imposing vanishing of the first $(r+1)(D+1)-1$ Taylor coefficients is fewer homogeneous rational linear equations than unknowns. There is consequently a nonzero remainder with order at least $(r+1)(D+1)-1$; rational coefficients can be cleared to integers.

This constructs a nonzero *function*. It supplies no useful coefficient-height bound, no specified primitive local divisor, and no nonvanishing at $2/3$. In particular, multiplication by $(3z-2)$ raises the degree and forces a specialisation zero without destroying functional nonvanishing. Functional rank cannot replace the real-remainder escape estimate in Section 1.

## 5.4 Infinite dilation closure is different

The finiteness assumption in Theorem C is essential. Möbius inversion gives the exact identity
$$
\sum_{m\ge1}\mu(m)\mathcal L(z^m)=\frac{z}{1-z},\qquad |z|<1.
\tag{5.4}
$$
Indeed the coefficient of $z^n$ on the left is $(\mu*\tau)(n)=1$, since $\tau=1*1$ and $\mu*1$ is the convolution identity. The rearrangement is absolutely convergent: $\tau(n)\le n$ gives $\mathcal L(r^m)\le r^m/(1-r^m)^2$ for $0<r<1$.

For a truncation after $m=M$, the same bound gives
$$
\left|\sum_{m>M}\mu(m)\mathcal L(z^m)\right|
\le\frac{r^{M+1}}{(1-r)(1-r^{M+1})^2},\qquad r=|z|<1.
\tag{5.5}
$$
This is classical Möbius inversion with an elementary explicit tail estimate, not a new identity. It shows exactly how a rational right-hand side can arise from infinitely many dilates despite finite linear independence. A truncated identity still contains Lambert values; it is not a rational approximation to $\mathcal L(2/3)$ without a separate arithmetic construction for those values.

# 6. A tighter, effective cyclotomic evaluation bound

The live rational-base theorem uses degree to compare polynomial values with powers of the base. The standard divisor-count estimate can be made more explicit at essentially no cost.

For $x>1$, define
$$
B(x)=\sum_{d\ge1}\frac{-\log(1-x^{-d})}{d}<\infty.
$$
A convenient elementary upper bound is
$$
B(x)\le\frac{-\log(1-x^{-1})}{1-x^{-1}}.
$$
Indeed $-\log(1-y)\le y/(1-y)$ and $1-x^{-d}\ge1-x^{-1}$.

For cyclotomic polynomials,
$$
\log\Phi_\ell(x)-\varphi(\ell)\log x
=\sum_{d\mid\ell}\mu(\ell/d)\log(1-x^{-d}).
$$
If real weights satisfy $|c_\ell|\le C$ for $\ell\le N$, then absolute summation gives
$$
\boxed{
\left|\sum_{\ell\le N}c_\ell
 [\log\Phi_\ell(x)-\varphi(\ell)\log x]\right|
\le CNB(x).}
\tag{6.1}
$$
The proof is
$$
\sum_{\ell\le N}\sum_{d\mid\ell}-\log(1-x^{-d})
=\sum_{d\le N}\lfloor N/d\rfloor[-\log(1-x^{-d})]
\le NB(x).
$$
No uniformity as $x\downarrow1$ is claimed. For the fixed direction in the live theorem the weights $1-\nu_\ell$ are zero or one. Thus the cyclotomic evaluation error is $O_x(n)$ with an explicit constant, rather than the weaker $O_x(n\log n)$ estimate in the derivation.

If $H_n(x)$ is the positive source remainder before cancellation and $P=(x^{-1};x^{-1})_\infty$, the literal product gives
$$
P^2\le H_n(x)\le P^{-2}/(1-x^{-a_0}).
$$
Writing $K_n=\deg A_n$ and $W_n=\deg U_n$ for the raw and cancelled first coefficients, (6.1) yields
$$
\log\Lambda_n(x)=-(K_n-W_n)\log x+O_x(n),
$$
and hence
$$
\log\bigl(b^{W_n}\Lambda_n(a/b)\bigr)
=K_n\log b-(K_n-W_n)\log a+O_{a/b}(n).
\tag{6.2}
$$
The asymptotic limits of $K_n$ and $W_n$ still require the supplied summatory-totient argument. Estimate (6.1) does not improve the limiting threshold by itself. It gives an effective fixed-base error term useful for finite-size checks and makes the proof's two distinct limits visible.

# 7. Separate scalar irrationality from a determinant or measure estimate

The live equation labelled `eq:negative-margin` combines coefficient height and the selected error. It is a sufficient objective in some determinant and irrationality-measure strategies; it is not necessary for the scalar irrationality implication.

For an explicit counterexample, define positive integers $P_r,Q_r$ by
$$
P_r+Q_r\sqrt2=(1+\sqrt2)^r.
$$
Then $P_r^2-2Q_r^2=(-1)^r$ and
$$
0<|Q_r\sqrt2-P_r|=\frac1{P_r+Q_r\sqrt2}\longrightarrow0.
$$
Nevertheless
$$
P_r|Q_r\sqrt2-P_r|\longrightarrow\frac12.
$$
Even after the quadratic reindexing $r=n^2$, the logarithm of this height-error product divided by $n^2$ tends to zero, rather than to a negative number. The nonzero integer forms already prove irrationality. Requiring a strictly negative height-error exponent would discard this perfectly valid scalar mechanism.

The statement the short note needs for the actual source family is
$$
\exists\lambda_n:\quad D_n\mid A(\lambda_n),B(\lambda_n),
\quad 0<|A(\lambda_n)F(3/2)-B(\lambda_n)|<D_n/n.
$$
Theorems A and the supplied bounded-fibre lemma are possible ways of obtaining such selectors. Equation (3.2) is a distinct necessary condition when two independent small rows are demanded.

# 8. A structural map of the accumulated failures

**Polynomial integrality versus integer-valuedness.** Rational specialisation requires actual integral coefficient polynomials and their post-cancellation degree. The polynomial conclusion of Zudilin's Lemma 7 is the relevant input. Integer-base evaluation alone would be insufficient. This is the successful mechanism in the flagship.

**Selector count versus the later maps.** The maps are
$$
\{-1,0,1\}^M\ \longrightarrow\ \mathbb Z[X]^2
\ \xrightarrow{H_W}\ \mathbb Z^2
\ \xrightarrow{(A,B)\mapsto A\xi-B}\ \mathbb R.
$$
A nonzero input need not survive any particular arrow. Repeated source rows falsify the first inference. The linearly independent polynomials $(2X-3)X^j$ all vanish at $3/2$, falsifying the second inference. A nonzero pair $(s,r)$ annihilates a rational target $r/s$, falsifying the third. Real nonvanishing implies survival of the earlier arrows, but those earlier statements do not imply real nonvanishing.

**Polynomial rank versus specialised rank.** A family can have arbitrarily large dimension over $\mathbb Q$ as a space of polynomial coefficient vectors and collapse under evaluation. Rank over $\mathbb Q$, rank over $\mathbb Q(X)$, and absence of short signed relations after specialisation must never be interchanged. Pairs lie in a two-dimensional space over $\mathbb Q(X)$ regardless of their coefficient-vector dimension over $\mathbb Q$.

**Formal Hankel order versus fixed-$q$ size.** The modification $C_Nq^{B_N}(1-q)^{N^3}$ preserves the formal first term and introduces cubic logarithmic decay at every fixed $0<q<1$. The supplied positive measure, rather than formal order alone, supplies the separate two-sided analytic estimate. The R3 sharper power-law asymptotic remains a candidate and is not imported into the lead.

**Local congruence depth versus divided approximation.** Formula (3.1) displays both image compression and residual index. A large minor gcd does not determine real error. The wide R4 family is a concrete unresolved example; the narrow family has both a proved regular-scale failure and the full-span counting obstruction of Section 2.

**Dense singularities versus functional closure.** Equation (5.1) shows that a natural boundary does not preclude a Mahler relation. Theorem C needs the full-rank gcd signature. Its success still supplies no special-value irrationality theorem.

**Model inequalities versus universal no-go theorems.** The rectangular Hermite–Padé calculation excludes its specified exponent model. The Archimedean cap assumes final ordinary polynomials, a base-independent height constant, and a decay asymptotic at every real base greater than one. Neither statement excludes arbitrary approximation methods at $3/2$.

# 9. Connections to the sibling corpus

The #249 note studies coefficient-section spaces for Euler's totient and exact $k$-kernel rank. Theorem C studies a different operator and coefficient field: substitution $z\mapsto z^m$ over $\mathbb C(z)$, with differential extensions. The conceptual connection is a rank witness that rules out a specified finite closure. It is not a theorem identifying these ranks. Bell–Smertnig also explicitly treats the totient generating function, so a new standalone claim that it is not $k$-Mahler would require that antecedent.

The #269 finite-separable representation obstruction similarly requires the function family, coefficient field and evaluation set to be fixed. A rank witness excludes that representation, rather than resolving an unrelated arithmetic value. The invariant-design lesson transfers; the analytic proof here does not automatically transfer.

The #243 state-recovery constructions distinguish stored state from the information needed by the recurrence. Theorem A makes an analogous separation for selector data: a modular signature, a real bin and exact-value multiplicity have distinct roles. It is a reusable finite theorem, but no #243 or #257 endpoint is inferred without constructing the associated maps and bounds.

The #257 irrationality results use genuine source-specific arithmetic and tail estimates. They illustrate what is still needed at #1049: a producer of the estimates, rather than a generic implication whose difficult hypotheses have acquired new names. No stronger #257 theorem is claimed from the present work.

# 10. Source fidelity, literature and verification

The supplied `01_short_note.tex` is the patch base. The live title and the mathematical assertion labelled `res:rational-base-threshold` are preserved. Its source-attribution sentence is moved out of the theorem and corrected: the polynomial inclusion is Zudilin's display (23), while display (24) is the subsequent integer-specialisation step. The Pochhammer length correction already accepted in R4 is retained, not presented as a new discovery.

The exact checks in `checks/check_r5.py` verify the thirteen omega intervals on all 48 rational breakpoint cells, the rational lower-bound calculation for $81/200<\theta^*$, the power comparisons for $31/4$, 210 gcd Gram matrices, root-order arithmetic, 39 mixed derivative/dilation polynomial columns through Taylor degree 350 over a finite field, the twist and Möbius-inversion identities, and finite instances of Theorem A. The infinite proofs are those written above, not extrapolations from those checks.

The Lean module is candidate source using the live bounded-fibre theorem and its exact argument schema. No Lean binary or Mathlib build was available in this environment, and a toolchain download attempt failed at DNS resolution. No Lean compilation or kernel acceptance is claimed. The module has no `sorry`, new axiom or unchecked evaluation; that textual fact is distinct from successful elaboration. The analytic theorem is not represented as formalised.

The main paper comparison read the primary 1994, 2004 and 2016 sources. Zudilin's printed page 156 and Lemma 7 on page 161 were visually checked. The full text of Koizumi–Yokoi, arXiv:2608.26918, could not be retrieved despite a direct PDF attempt. Its relevance to priority therefore remains an unresolved bibliographical check. The existing manuscript should use its exact proven statements without a best-known or first-proof superlative.

## References and search record

[BS] J. Bell and D. Smertnig, *Mahler series with multiplicative coefficient sequences*, arXiv:2603.23456v1, 24 March 2026. Theorem in Section 1 and the explicit divisor/totient examples were inspected. https://arxiv.org/html/2603.23456v1

[DK] D. Dorigoni and A. Kleinschmidt, *Resurgent expansion of Lambert series and iterated Eisenstein integrals*, arXiv:2001.11035v1. Section 2.4 gives root-of-unity expansions; equation (2.52) supplies a relevant twist relation. https://arxiv.org/html/2001.11035v1

[BV94] P. Bundschuh and K. Väänänen, *Arithmetical investigations of a certain infinite product*, Compositio Mathematica 91 (1994), 175–199. https://www.numdam.org/item/CM_1994__91_2_175_0.pdf

[Z04] W. Zudilin, *Heine's basic transform and a permutation group for q-harmonic series*, Acta Arithmetica 111 (2004), 153–164. Source identities (7)–(11), polynomial Lemma 7 and the final direction are the relevant antecedents. https://www.impan.pl/shop/en/publication/transaction/download/product/82435

[Z16] W. Zudilin, *On the irrationality of generalized q-logarithm*, Research in Number Theory 2 (2016), Article 15. Section 2 announces a rational-base condition with an unspecified constant; Section 4 supplies the normalised Hankel construction. https://arxiv.org/html/1601.02688v2

[BV15] P. Bundschuh and K. Väänänen, *Algebraic independence results on the generating Lambert series of the powers of a fixed integer*, Hardy–Ramanujan Journal 38 (2015), 36–44. The functions are supported on powers of a fixed integer, rather than the full divisor Lambert series. This is a relevant distinction in the functional-independence search. https://hrj.episciences.org/1358/pdf

[T1] T. Tao, *On the importance of partial progress*. https://terrytao.wordpress.com/career-advice/on-the-importance-of-partial-progress/

[T2] T. Tao, *Maximising the results-to-effort ratio*. https://terrytao.wordpress.com/advice-on-writing-papers/maximising-the-results-to-effort-ratio/

[T3] T. Tao, *Use the introduction to sell the key points of your paper*. https://terrytao.wordpress.com/advice-on-writing-papers/use-the-introduction-to-%E2%80%9Csell%E2%80%9D-the-key-points-of-your-paper/

The searches for mixed-dilation and differential linear independence found related sparse Lambert series, special-value results and root-of-unity expansions, but no source establishing the exact full statement (4.1). This is an incomplete priority search, not evidence of novelty.
