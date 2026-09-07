---
title: "From Poisson extremisers to polynomial critical spectra"
subtitle: "Round-five research return for Erdős #1041"
author: "Research return prepared for Will Cook"
date: "7 September 2026"
fontsize: 11pt
papersize: a4
geometry: margin=25mm
colorlinks: true
header-includes:
  - \usepackage{amsmath,amssymb,amsthm,mathtools}
  - \usepackage{microtype}
  - \setlength{\emergencystretch}{2em}
---

## Status and the new question answered

The supplied `SharpPowerDiscProducts.md` already records the ordinary sharp
$4s$ free-point hierarchy from the preceding return. Its use for critical
values gives an upper bound, but free-point sharpness does not by itself
prove that the exponent is sharp for polynomial critical configurations.
The latter configurations satisfy an additional derivative constraint.

This return supplies explicit monic polynomials realising the limiting
extremal measures. The construction proves that the numerator $4s$ in the
critical-value exponent $4s/(n-1)$ is sharp uniformly in degree, under the
stated critical-point moment conditions. A double scaling proves the same
sharpness with the least critical-value modulus bounded below by any fixed
$\tau<1$, even when every radius-$4/3$ separation test fails. It also gives a general joint
critical-point/critical-value limit theorem for powers of finite Blaschke
products. The sharpness models themselves have very short connections, including a
high-critical family with length $O(1/n)$. A second scaling has the exact
intrinsic-distance limit $2(1-e^{-\alpha/2})$ and disproves a
degree-uniform modulus of metric stability:
sharpness of a global spectral inequality and difficulty of the path
problem are different notions.

All analytic arguments in this document are ordinary proofs proposed for
independent checking. Their novelty has not been established. The attached
Lean module records algebraic identities only and was not compiled here.
Both rational finite certificates were executed successfully with the
Python standard library. No claim that the parent problem is solved is made.

## 1. The construction in one line

Fix $0<b<1$ and define
\[
 A(z)=z(z+b),\qquad D(z)=1+bz,\qquad
 B(z)=\frac{A(z)}{D(z)},\qquad
 F_N(z)=A(z)^N-D(z)^N.                                      \tag{1}
\]
The rational function $B$ is a finite Blaschke product of degree two.
Therefore $F_N$ is a monic polynomial of degree $2N$, and all its roots
are simple and lie on the unit circle. Its roots are the preimages of the
$N$th roots of unity under $B$.

The boundary argument derivative is
\[
 \frac{d}{d\theta}\arg B(e^{i\theta})
 =1+\frac{1-b^2}{|1+be^{i\theta}|^2}.
\]
Consequently the limiting root measure is
\[
 d\nu_b(\zeta)=\frac12\left(1+\frac{1-b^2}{|1+b\zeta|^2}\right)dm(\zeta)
 =\Re\frac1{1+b\zeta}\,dm(\zeta),                         \tag{2}
\]
where $dm=d\theta/(2\pi)$.
This is exactly the nonconstant endpoint measure of the preceding
free-point theorem: half uniform measure and half harmonic measure at $-b$.

There is an equally useful critical-value identity. If $F_N'(c)=0$, then
\[
 A(c)^{N-1}A'(c)=D(c)^{N-1}D'(c),
\]
and hence
\[
 A'(c)F_N(c)=D(c)^{N-1}\bigl(A(c)D'(c)-D(c)A'(c)\bigr).
                                                               \tag{3}
\]
For the quadratic model this becomes
\[
 F_N(c)=-(1+bc)^{N-1}\frac{bc^2+2c+b}{2c+b}.                    \tag{4}
\]
The denominator cannot vanish at a critical point: at $c=-b/2$ the
critical equation would have right-hand side $b(1-b^2/2)^{N-1}>0$ and
left-hand side zero.

The construction does not prescribe a derivative and then hope that an
antiderivative has admissible roots. It enforces the root constraint first,
through a circle covering, and derives the derivative spectrum afterwards.

## 2. A general transfer theorem

Let $a_1,\ldots,a_d$ lie in the open unit disc, with at least one $a_j=0$
and at least one $a_j\ne0$. Put
\[
 A(z)=\prod_{j=1}^d(z-a_j),\qquad
 D(z)=\prod_{j=1}^d(1-\overline{a_j}z),\qquad B=A/D,
\]
and $F_N=A^N-D^N$, of degree $n=dN$.
The zero factor ensures $\deg D<d$, so $F_N$ is monic without an additional
normalisation. The nonzero factor ensures $D$ is nonconstant.
Write $c_{N,1},\ldots,c_{N,n-1}$ for the critical points with multiplicity,
and set
\[
 d\nu_B(\zeta)=\frac1d\sum_{j=1}^d
 \frac{1-|a_j|^2}{|\zeta-a_j|^2}\,dm(\zeta).
\]

**Theorem 1 (Blaschke-power joint spectral law).** All roots of $F_N$ are
simple and lie on the unit circle. For every continuous function
$\Phi$ on $\overline{\mathbb D}\times[0,2]$,
\[
 \lim_{N\to\infty}\frac1{dN-1}\sum_{k=1}^{dN-1}
 \Phi\!\left(c_{N,k},|F_N(c_{N,k})|^{1/(dN)}\right)
 =\int \Phi\!\left(\zeta,|D(\zeta)|^{1/d}\right)d\nu_B(\zeta).
                                                               \tag{5}
\]
In particular, for every $p>0$,
\[
 \lim_{N\to\infty}\frac1{dN-1}\sum_k
 |F_N(c_{N,k})|^{p/(dN-1)}
 =\int |D(\zeta)|^{p/d}\,d\nu_B(\zeta).                      \tag{6}
\]
The same limit holds with exponent $p/(dN)$.

### Proof: root placement

On the circle, $B=e^{i\beta}$ has strictly positive angular derivative
\[
 \beta'(\theta)=\sum_j\frac{1-|a_j|^2}{|e^{i\theta}-a_j|^2}>0
\]
and degree $d$. Thus $B^N=1$ has exactly $dN$ distinct solutions there.
Neither $A$ nor $D$ vanishes on the circle; all these roots of $F_N$ are
simple. Since $F_N$ is monic of degree $dN$, there are no additional roots.
The critical points belong to the closed unit disc by Gauss--Lucas.
Moreover $|F_N(c)|\le2^{dN}$ for $|c|\le1$, which explains the compact
second-coordinate interval in (5).

### Proof: almost all critical points approach the circle

The exact derivative formula gives, throughout the open disc,
\[
 \frac{F_N'(z)}{N D(z)^{N-1}}=B(z)^{N-1}A'(z)-D'(z).
                                                               \tag{7}
\]
Since $|B|<1$ there, the left side converges locally uniformly to $-D'$.
This analytic limit is not identically zero. For any radius $r<1$, choose
$r<R<1$ so that $D'$ has no zeros on $|z|=R$. Rouché's theorem on that
circle shows that, for all sufficiently large $N$, the number of critical
points in $|z|<R$ is exactly the number of zeros of $D'$ there. This count
is bounded independently of $N$. The proportion in $|z|\le r$ therefore
tends to zero.

This step is essential. Weak convergence of root measures alone does not
force convergence of critical-point measures: $z^n-1$ is a counterexample.
Here the nonconstant denominator supplies the nonzero limiting logarithmic
field that prevents macroscopic critical collapse.

### Proof: the limiting angular measure

Fix $R>1$. On a neighbourhood of $|z|=R$, $A$ and $A'$ do not vanish,
$|D/A|<1$, and
\[
 F_N'=N A^{N-1}A'\left[1-\frac{D'}{A'}(D/A)^{N-1}\right].
\]
The bracket converges to one together with its derivative. Thus
\[
 \frac1{dN-1}\frac{F_N''}{F_N'}\longrightarrow\frac1d\frac{A'}A
\]
uniformly on that circle. By the argument principle, for each integer
$k\ge0$,
\[
 \frac1{dN-1}\sum_\ell c_{N,\ell}^k
 \longrightarrow\frac1d\sum_{j=1}^d a_j^k.                 \tag{8}
\]
Every weak subsequential limit of the critical measures is supported on
the circle by (7). On the circle the positive and negative Fourier moments
are the moments in (8) and their conjugates. Trigonometric polynomials are
dense in continuous functions, so these moments determine the limiting
measure uniquely. The Poisson representation gives precisely $\nu_B$.
Hence the entire critical-measure sequence converges to $\nu_B$.

### Proof: values at the critical points

There is an annulus $r<|z|\le1$ on which $D$, $A'$ and
\[
 W=AD'-DA'
\]
are nonzero. Indeed $D$ has no zeros in the closed disc; $A'$ has no zeros
on the circle by the strict circle logarithmic-derivative estimate; and
$W=-D^2B'$ is nonzero there because $\beta'>0$.
Consequently $H=W/A'$ has positive lower and finite upper modulus bounds
on a sufficiently thin closed annulus.
At its critical points, (3) gives
\[
 |F_N(c)|^{1/(dN)}=|D(c)|^{(N-1)/(dN)}|H(c)|^{1/(dN)}.
\]
This converges uniformly on the annulus to $|D(c)|^{1/d}$. The exceptional
critical points outside the annulus form a vanishing fraction and have
bounded second coordinate. Uniform continuity of $\Phi$, followed by the
critical-measure convergence, proves (5). To obtain (6), use boundedness
and uniform convergence of $x\mapsto x^{pdN/(dN-1)}$ to $x^p$ on $[0,2]$.
This completes the proof.

## 3. The critical-value power is genuinely sharp

Here is the upper inequality being sharpened in scope, not in magnitude.
Let $f$ be monic of degree $n\ge2$, with roots in the closed unit disc,
and let its critical points be $c_1,\ldots,c_m$, $m=n-1$. If
\[
 \sum_{j=1}^m c_j^k=0\quad(1\le k<s),
\]
then the registered ordinary $4s$ theorem and polar comparison give
\[
 \boxed{\frac1m\sum_{j=1}^m|f(c_j)|^{4s/m}\le1.}          \tag{9}
\]
For $s=1$ there are no moment conditions.

For completeness, the proof is recalled in Section 6; it is not a new
claim of this return. The new assertion is optimality **within the
polynomial class**.

**Theorem 2 (sharp degree-uniform exponent numerator).** For every integer
$s\ge1$ and every real $p>4s$, there is a monic polynomial with simple
roots strictly inside the unit disc whose critical points satisfy the
first $s-1$ vanishing power-sum conditions but
\[
 \frac1{n-1}\sum_{f'(c)=0}|f(c)|^{p/(n-1)}>1.              \tag{10}
\]
Thus $4s$ cannot be replaced by any larger degree-independent numerator in
(9). The assertion concerns uniformity across degrees, not the optimal
exponent in any particular degree.

### Proof when $s=1$

Use (1). Theorem 1 gives
\[
 \lim_N\frac1{2N-1}\sum_{F_N'(c)=0}|F_N(c)|^{p/(2N-1)}
 =J_b(p):=\int |1+b\zeta|^{p/2}\,d\nu_b(\zeta).           \tag{11}
\]
By (2),
\[
 J_b(4)=\int |1+b\zeta|^2\Re\frac1{1+b\zeta}\,dm
       =\int\Re(1+b\zeta)\,dm=1.                        \tag{12}
\]
The positive random variable $X=|1+b\zeta|^2$ is nonconstant under
$\nu_b$. Therefore strict Jensen gives
\[
 p>4\quad\Longrightarrow\quad J_b(p)=\int X^{p/4}d\nu_b>1.
\]
For a sufficiently large finite $N$, the average in (11) is already
strictly larger than one. Its roots currently lie on the circle. Replace
it by
\[
 \widetilde F_N(z)=r^{2N}F_N(z/r),\qquad 0<r<1.
\]
This is monic with simple roots of modulus $r$. Its critical values are
$r^{2N}F_N(c)$, so its average is multiplied by
$r^{2Np/(2N-1)}$. For $r$ sufficiently close to one the strict violation
persists. This proves the open-disc claim without silently passing a
boundary equality into a strict inequality.

### Proof with moment cancellation

Put
\[
 F_{N,s}(z)=F_N(z^s)
 =\bigl[z^s(z^s+b)\bigr]^N-(1+bz^s)^N,
 \qquad n=2Ns.                                           \tag{13}
\]
Its roots are simple and on the circle. Its critical points consist of
$s-1$ copies of zero and the complete $s$-fold fibres above the critical
points of $F_N$. Rotational symmetry makes every critical power sum of
orders $1,\ldots,s-1$ vanish exactly. Since $F_N(0)=-1$,
\[
 \frac1{2Ns-1}\sum_{F_{N,s}'(c)=0}|F_{N,s}(c)|^{p/(2Ns-1)}
 =\frac{s\sum_{F_N'(u)=0}|F_N(u)|^{p/(2Ns-1)}+s-1}{2Ns-1}.
\]
The limit is
\[
 \int |1+b\zeta|^{p/(2s)}\,d\nu_b=J_b(p/s),              \tag{14}
\]
which is larger than one for $p>4s$. Radial contraction preserves the
moment cancellations and, when sufficiently small, the strict violation.
This proves Theorem 2.

### Scale-covariant form

For roots in a disc of centre $h$ and radius $R>0$, the upper inequality is
\[
 \sum_{j=1}^{n-1}|f(c_j)|^{4s/(n-1)}
 \le(n-1)R^{4sn/(n-1)},                                  \tag{15}
\]
under $\sum_j(c_j-h)^k=0$ for $1\le k<s$. The constant is attained by
$(z-h)^n-\lambda$ with $|\lambda|=R^n$. The exponent numerator is sharp
uniformly in degree by Theorem 2. These are two different sharpness claims.
The centre and radius must be transported together; a change of centre is
not free.

## 4. Sharpness persists in the high-critical regime

A restriction to $\mu>13/25$ does not permit a larger degree-uniform
moment exponent. A second scaling of the same construction proves this,
and also gives a high-critical family with short explicit connectors.

Fix $\lambda>0$, put $b_N=\lambda/N$, and set
\[
 F_N(z)=[z(z+b_N)]^N-(1+b_Nz)^N,\qquad m=2N-1.
\]
Let $c_{N,1},\ldots,c_{N,m}$ be the critical points, and write
$Y_{N,j}=\log|F_N(c_{N,j})|$. For every fixed $p>0$,
\[
 \boxed{\frac1m\sum_j|F_N(c_{N,j})|^{p/m}
 =1+\frac{\lambda^2p(p-4)}{16N^2}+o(N^{-2}).}       \tag{H1}
\]
Moreover
\[
 \min_j|F_N(c_{N,j})|\longrightarrow e^{-\lambda},
 \qquad
 \max_j|F_N(c_{N,j})|\longrightarrow e^{\lambda}.   \tag{H2}
\]
This scaling controls the actual critical values, whereas the fixed-$b$
law controlled their degree-normalised roots.

### Proof of the second-order law

Every critical point approaches the circle uniformly. Indeed, on a fixed
closed subdisc $|z|\le r<1$, the quantity $|B_N(z)|$ is bounded by some
$q<1$ for all sufficiently large $N$, while $|A_N'|$ is bounded. The
critical equation would give $q^{N-1}O(1)\ge b_N=\lambda/N$, which is
impossible. Gauss--Lucas supplies the other inclusion.

For a fixed integer $k<N$, the top $k$ coefficients of $F_N'$ agree with
those of $N A_N^{N-1}A_N'$. Newton identities therefore give exactly
\[
 \frac1m\sum_j c_{N,j}^k
 =\frac{(N-1)(-b_N)^k+(-b_N/2)^k}{2N-1}.          \tag{H3}
\]
In particular $M_1=-b_N/2$ and $M_2=O(b_N^2)$. These identities, the
uniform approach to the circle, and uniqueness of Fourier moments imply
that the critical-point measures converge to uniform arclength.

On a fixed annulus containing all critical points for large $N$, the exact
value identity (4) gives
\[
 Y_{N,j}=(N-1)\Re\log(1+b_Nc_{N,j})+
 \Re\log\left(1+\frac{b_Nc_{N,j}^2}{2c_{N,j}+b_N}\right).
                                                               \tag{H4}
\]
The logarithms here are the branches tending uniformly to zero as $b_N$
tends to zero. Taylor estimates are uniform because $|c_{N,j}|\ge1/2$.
They give
\[
 Y_{N,j}=\lambda\Re c_{N,j}+O(N^{-1}),
\]
and, using (H3) before taking absolute values,
\[
 \begin{split}
 \frac1m\sum_jY_{N,j}&=-\frac{\lambda^2}{2N}+O(N^{-2}),\\
 \frac1m\sum_jY_{N,j}^2&=\frac{\lambda^2}{2}+o(1),\\
 \max_j|Y_{N,j}|&=O(1).
 \end{split}                                                   \tag{H5}
\]
For the first identity, expand the first logarithm through degree two:
its mean is $b_NM_1-(b_N^2/2)M_2+O(b_N^3)
=-b_N^2/2+O(b_N^3)$. The mean of the second logarithm is $O(b_N^2)$,
since its linear term is $(b_N/2)c$ and $M_1=-b_N/2$.
For the second identity use
$\operatorname{mean}(\Re c)^2=(\operatorname{mean}|c|^2+\Re M_2)/2\to1/2$.

Expand $e^{pY/m}$ with a uniform cubic remainder and substitute (H5).
The linear contribution is $-p\lambda^2/(4N^2)$; the quadratic
contribution is $p^2\lambda^2/(16N^2)$. This proves (H1).
Uniform approximation by $\lambda\Re c$, together with full support of
the limiting uniform measure, proves (H2).

### High-critical sharpness theorem

**Theorem 3.** Fix $s\ge1$, $p>4s$, and $0<\tau<1$. There exist monic
polynomials with simple roots in the open unit disc such that their first
$s-1$ critical-point power sums vanish, their least critical-value modulus
is greater than $\tau$, and
\[
 \frac1{n-1}\sum_{f'(c)=0}|f(c)|^{p/(n-1)}>1.
\]
They can additionally be chosen so that **no selected critical value passes
the radius-$4/3$ separation test at any centre in $[0,1]$**.

Choose
\[
 0<\lambda<\min\{-\log\tau,\tfrac12\log(4/3)\}.
\]
For $F_{N,s}(z)=F_N(z^s)$, the calculation in (H1), including the $s-1$
critical points at zero, becomes
\[
 \frac1{2Ns-1}\sum_{F_{N,s}'(c)=0}|F_{N,s}(c)|^{p/(2Ns-1)}
 =1+\frac{\lambda^2p(p-4s)}{16s^2N^2}+o(N^{-2}).     \tag{H6}
\]
The critical-value minimum tends to $e^{-\lambda}>\tau$.
Contract by $r_N=1-N^{-3}$ for $N\ge2$, replacing $F_{N,s}$ by
$r_N^{2Ns}F_{N,s}(z/r_N)$. Its effect on the mean is a multiplicative
$1+O(N^{-3})$, and on critical-value moduli is $1+O(N^{-2})$.
The strict violation and lower critical-value bound persist. Rotational
symmetry preserves the exact low-moment cancellations.

For the separation assertion, (H4) also gives the complex estimate
$F_N(c)=-\exp(\lambda c)+o(1)$ uniformly over its critical points.
The additional critical value in the composition is $-1$.
Consequently every pair of critical values satisfies
\[
 |v_i/v_j-1|\le e^{2\lambda}-1+o(1)<1/3.
\]
For every $a\in[0,1]$, $|v_i/v_j-a|\le1-a+|v_i/v_j-1|<4/3$.
Contraction leaves these ratios unchanged. This proves all assertions.

The theorem excludes an improvement of the universal power numerator even
within the high-critical branch and outside the displayed separation
criterion. It does not exclude a stronger inequality involving additional
attachment or spatial data.

### A short contained connection in the same high-critical family

**Theorem 4.** For fixed $0<\lambda\le1$, two roots of the degree-$2N$
polynomial $F_N$ above have a connection inside $\{|F_N|<1\}$ with
\[
 \operatorname{length}(\gamma_N)
 \le\frac{\log(2/\lambda)+\pi+o(1)}N.                \tag{H7}
\]
The roots initially lie on the circle. Any radial contraction of the entire
polynomial preserves this containment and decreases the length. Thus the
contracted polynomials supply a solved high-critical family with simple
open-disc roots. For sufficiently small fixed $\lambda$, their critical
values fail the radius-$4/3$ test as in Theorem 3.

**Proof.** One root is $\zeta_1=-1$. Let $\zeta_2$ be the next root in
positive angular order. Since the boundary argument derivative of $B_N$
is $2+O(N^{-1})$ uniformly, their angular separation is
$\pi/N+O(N^{-2})$.
Put $C=\tfrac12\log(2/\lambda)>0$ and $t_N=e^{-C/N}$.
Join each root radially to $t_N\zeta_j$, and join those endpoints along
the shorter arc of the circle $|z|=t_N$.

Uniformly for $t_N\le t\le1$ and $|\zeta|=1$,
\[
 \log\frac{B_N(t\zeta)}{B_N(\zeta)}
 =2\log t+O\bigl(b_N(1-t)\bigr).
\]
This follows by writing $B_N(z)=z^2(1+b_N/z)/(1+b_Nz)$ and expanding the
two logarithmic differences. At a root $B_N(\zeta_j)^N=1$, so
\[
 B_N(t\zeta_j)^N=t^{2N}\bigl(1+O(N^{-1})\bigr).
\]
On these radial segments, $D_N(t\zeta_j)^N\to e^{-\lambda}$ uniformly.
Hence $|F_N(t\zeta_j)|\le e^{-\lambda}(1+o(1))<1$ for large $N$.
On the inner circular arc,
$|B_N(t_N\zeta)|^N=e^{-2C}(1+o(1))=\lambda/2+o(1)$ and
$|D_N(t_N\zeta)|^N\to e^{-\lambda}$ uniformly. Therefore
\[
 |F_N|\le e^{-\lambda}(1+\lambda/2)+o(1)<1.
\]
The two radial lengths total $2C/N+O(N^{-2})$, and the inner arc has
length $\pi/N+O(N^{-2})$. This proves (H7).

The mechanism separates three constraints. The circle covering places all
roots exactly. Radial motion suppresses the oscillatory term while retaining
its cancellation at the root. An inner arc lies in a sector where the
nonoscillatory term has modulus below one. Marginal critical-value moments
remain sharp, yet compatible nearby branches yield a short path.

Theorem 4 is an ordinary asymptotic theorem. The proof gives a finite
threshold depending on $\lambda$ through uniform estimates; no numerical
value of that threshold is claimed. It does not certify that a particular
small degree lies beyond that threshold.


### A tunable intrinsic-distance limit

There is a second useful scale. Fix $\alpha>0$, take
$\lambda_N=e^{-\alpha N}$ and $b_N=\lambda_N/N$, and use the same $F_N$.
For the closed-level all-curve functional in the supplied corpus,
\[
 \boxed{\Lambda(F_N)\longrightarrow
             2\bigl(1-e^{-\alpha/2}\bigr).}             \tag{H8}
\]
This gives any limiting distance strictly between zero and two using
polynomials whose coefficients approach those of $z^{2N}-1$
exponentially fast. The roots of $F_N$ remain simple and exactly on the
unit circle.

**Lower bound.** The coefficient $\ell^1$ distance from $F_N$ to
$z^{2N}-1$ is at most
$2((1+b_N)^N-1)\le4\lambda_N$ for large $N$.
On every separating ray
$\arg z=(2k+1)\pi/(2N)$, the reference polynomial has modulus
$1+|z|^{2N}$. Hence for
\[
 R_N=(4\lambda_N)^{1/(2N)},
\]
these rays have $|F_N(z)|>1$ when $R_N<|z|\le1$.
For $|z|\ge1$, the error is at most $4\lambda_N|z|^{2N}$, so the same
exclusion holds there. No route through the exterior can bypass the barriers.
There is one root in each angular sector, by continuously varying $b$ from
zero to $b_N$: all roots stay simple on the circle and none can cross a
separating ray. A path between different roots must therefore enter
$|z|\le R_N$. Its length is at least $2(1-R_N)$.
Since $R_N\to e^{-\alpha/2}$, this proves the required lower limit.

**Upper bound.** Let $\zeta_1=-1$ and $\zeta_2$ be the next root, whose
angular separation is $\pi/N+o(N^{-1})$. Set
\[
 t_N=(\lambda_N/4)^{1/(2N-1)}\longrightarrow e^{-\alpha/2}.
\]
Use the two radial segments to $t_N\zeta_j$ and the shorter circular arc
at radius $t_N$. All their radii have a fixed positive lower bound.
For $t_N\le t\le1$, the factorisation
$B_N(z)=z^2(1+b_N/z)/(1+b_Nz)$ gives
\[
 \big|\arg B_N(t\zeta_j)^N\big|=O(\lambda_N/N)
             \quad\pmod {2\pi}.
\]
Here $\Im\zeta_j=O(N^{-1})$; expand the two logarithmic differences to
first order in $b_N$, with remainder $O(Nb_N^2)$ on the fixed annulus.
Also $|B_N(t\zeta_j)|\le1$, and
\[
 |D_N(t\zeta_j)|^N=1-\lambda_Nt+o(\lambda_N)
\]
uniformly there. Thus the radial segments have $|F_N|<1$ for large $N$.
On the inner circular arc,
\[
 |B_N|^N=t_N^{2N}(1+o(1))
       =\lambda_Nt_N/4\,(1+o(1)),
 \qquad
 |D_N|^N=1-\lambda_Nt_N+o(\lambda_N).
\]
Consequently $|F_N|<1$ throughout that arc as well. The resulting length
is $2(1-t_N)+O(N^{-1})$, proving the matching upper limit and (H8).
The error bounds here are for fixed $\alpha$; the positive limiting radius
is used explicitly.

**The matching critical circle.** The critical points themselves converge in
empirical distribution to uniform measure on $|z|=e^{-\alpha/2}$, and all
of their radii converge to that number uniformly. On any fixed circle
$|z|=r>0$, the critical equation has left side
$B_N(z)^{N-1}(2z+b_N)=2z^{2N-1}(1+o(1))$ and right side $b_N$.
The former is exponentially smaller when $r<e^{-\alpha/2}$ and exponentially
larger when $r>e^{-\alpha/2}$. Rouché therefore places every critical point
between any two fixed circles straddling this radius. The exact Newton
moments (H3) tend to zero at every positive order. Uniqueness of Fourier
moments on the limiting circle proves uniform angular distribution.
Thus the radius determining the intrinsic-distance limit is also the
limiting critical radius, rather than a radius introduced only by the
proof's estimates.

**Corollary (no degree-uniform modulus of metric stability).** There is no
function $\omega(\delta)\to0$ as $\delta\downarrow0$ such that
\[
 |\Lambda(f)-\Lambda(g)|\le\omega(\|f-g\|_{\mathrm{coeff},1})
\]
for every degree and every $f,g$ in its closed root-disc class. The same
failure holds with the uniform norm on the closed unit disc in place of the
coefficient $\ell^1$ norm.
Indeed $g_N=z^{2N}-1$ has $\Lambda(g_N)=2$, while the input norm difference
tends to zero and the output difference tends to $2e^{-\alpha/2}>0$.
This concerns uniformity across degrees. It is consistent with the
registered fixed-degree lower semicontinuity used to pass from generic
configurations to all configurations.


## 5. A finite exact witness, and a short geometric connector

### A rational-coefficient degree-eight counterexample to exponent $8/7$

Take $b=1/2$, $N=4$:
\[
 F(z)=z^8+2z^7+\tfrac32z^6+\tfrac12z^5
       -\tfrac12z^3-\tfrac32z^2-2z-1.
\]
Let $r=999/1000$ and $G(z)=r^8F(z/r)$. All eight roots of $G$ are simple
and have modulus $r$. The attached certificate proves
\[
 \boxed{\frac17\sum_{G'(c)=0}|G(c)|^{8/7}
 >\frac{3763187}{3500000}>1.075>1.}                       \tag{16}
\]
The value $8/7$ is a proposed strengthening, not the proved $4/7$ bound.
No contradiction with (9) occurs.

The verifier uses seven disjoint rational discs. For each disc centre $z_0$
and radius $\varepsilon$, the exact Taylor expansion of $F'$ verifies
\[
 |F''(z_0)|\varepsilon>
 |F'(z_0)|+\sum_{k\ge2}\frac{|F^{(k+1)}(z_0)|}{k!}\varepsilon^k.
\]
It uses a rational lower bound on the left and rational upper bounds on
the right. Rouché therefore gives one critical point in each disc.
A Taylor bound for $F$ supplies a rational $L_j<|F(c_j)|^2$.
For the recorded rational $y_j$, the verifier checks
\[
 y_j^7<(r^{16}L_j)^4.
\]
Thus $y_j<|G(rc_j)|^{8/7}$ without evaluating a fractional power.
The seven lower bounds sum to more than seven. The executable replay is
`python checks/check_degree8.py`; it uses only Python's integer and
rational arithmetic. Its output is included.

### A finite exact witness beyond both scalar criteria

Set $N=12$, $b=1/120$, $r=999999999/10^9$, and
$G(z)=r^{24}F_{12}(z/r)$. The standard-library verifier
`checks/check_high_critical.py` proves, by twenty-three disjoint rational
critical-point discs,
\[
 |G(c_j)+1|<1/12 \quad\hbox{for every critical point},
\]
and
\[
 \boxed{\frac1{23}\sum_j|G(c_j)|^{8/23}
 >\frac{46001266667}{46000000000}>
 1+\frac1{40000}.}                                      \tag{HC}
\]
All roots are simple and have modulus $r<1$ by the same circle-covering
argument. The value discs imply $\mu>11/12>13/25$ and
$|v_i/v_j-1|<2/11$. Thus $|v_i/v_j-a|<13/11<4/3$ for every
$a\in[0,1]$: no critical value passes that separation test.
The witness refutes a proposed exponent $8/23$ and does not refute the
proved exponent $4/23$ or the root-connection conjecture.

The verifier constructs the polynomial from its binomial formula,
independently checks the Rouché inequalities, verifies the strict common
critical-value disc, and raises positive rational moment bounds to the
23rd power. No floating-point root is trusted in the replay.

### The sharpness family is not a hard path family

The same construction has short connectors for elementary reasons.
For $b=1/2$ and $|z+1|\le1/8$,
\[
 |A(z)|\le\frac98\frac58=\frac{45}{64},\qquad
 |D(z)|\le\frac9{16}.
\]
For $N\ge2$,
\[
 |F_N(z)|\le2(45/64)^N\le2(45/64)^2<1.                   \tag{17}
\]
Also $-1$ is a root of $F_N$. Since $\beta'\ge4/3$, the next root in
positive circular order has angular separation at most $3\pi/(2N)$.
For $N\ge38$ this is less than $1/8$ (use $\pi<22/7$). Its chord to
$-1$ lies in the convex ball above, hence in the open unit lemniscate, and
has length at most $3\pi/(2N)<1/8$.

After radial contraction the conclusion persists: the chord length is
multiplied by $r$, and the polynomial values by $r^{2N}$. Thus this is an
explicit solved family of dense polynomials, not a counterexample to
Erdős #1041. It is separate new ordinary mathematics and has not been
inserted into the live note.

For the general construction in Theorem 1, $D(0)=1$ and $D$ is nonconstant
and zero-free in the closed disc. Therefore $\log|D|$ has circle mean zero
and is nonconstant. Some open boundary arc has $|D|<1$. Since $|A|=|D|$
on the circle, a small convex neighbourhood of a point of that arc has
$|A|,|D|\le q<1$. It contains at least two roots of $F_N$ for all large
$N$, by the root distribution. For those $N$ with $2q^N<1$, their straight
chord is contained in the open unit lemniscate. The neighbourhood can be
chosen with diameter below two. Thus every fixed nontrivial Blaschke-power
family considered here is eventually a short-connection family.

This is an exact distinction: the extremisers that make a global spectral
bound sharp can be geometrically easy because a small arc carries many
roots in a region of exponentially small polynomial modulus.

## 6. The upper inequality and the reusable Poisson mechanism

This section restates the ordinary corpus input to make the new sharpness
claim self-contained. It is not re-announced as new.

For positive weights $w_j$ summing to one and $c_j\in\mathbb D$, put
\[
 g(z)=\exp\sum_jw_j\log(1-\overline{c_j}z),\quad
 h(z)=g(z)^{p/2}=1+\sum_{\nu\ge1}b_\nu z^\nu,
\]
using the analytic logarithms zero at the origin. If $G=|g|$ and
$P=\sum_jw_jP_{c_j}$, then on the circle
\[
 P=1-\frac4p\Re\frac{zh'}h.
\]
Poisson evaluation and Taylor orthogonality give the exact identity
\[
 \sum_jw_jG(c_j)^p+
 \sum_{\nu\ge1}\left(\frac{4\nu}{p}-1\right)|b_\nu|^2+
 \sum_jw_j\int |h(\zeta)-h(c_j)|^2P_{c_j}(\zeta)dm=1.     \tag{18}
\]
The last term is nonnegative. When the first $s-1$ moments of the points
vanish, $h=1+O(z^s)$. Taking $p=4s$ makes every remaining coefficient
weight nonnegative. Radial contraction, followed by passage through
finite coefficient sums, proves the closed-disc version.

To pass to critical values, first take a polynomial with roots strictly
inside the disc. Write $q=f'/n$ and
$q^\#=\prod_j(1-\overline{c_j}z)$. On $|\zeta|=1$,
\[
 \Re\frac{\zeta f'(\zeta)}{f(\zeta)}>\frac n2,
 \quad\hbox{so}\quad |nf(\zeta)-\zeta f'(\zeta)|<|f'(\zeta)|.
\]
The function $(f-zq)/q^\#$ is analytic on the closed disc and has modulus
less than one there by the maximum principle. At a critical point this gives
\[
 |f(c_j)|\le\prod_k|1-\overline{c_k}c_j|.
\]
Apply (18) with equal weights and $p=4s$; then contract boundary-root
polynomials to get (9). For an enclosing disc other than the unit disc,
normalise both centre and scale to obtain (15).

At $p=4$, the missing first-coefficient penalty has a geometric meaning.
The exterior map $\Psi(z)=z g(1/z)^2=z+b_1+b_2/z+\cdots$ has positive
boundary angular derivative $P(e^{-i\theta})$, and its area deficit is
$\sum_{\nu\ge2}(\nu-1)|b_\nu|^2$. The unpenalised $b_1$ is a translation.
The sharp density (2) is chosen so that $g^2=1+bz$, the translated-disc
case. The construction (1) now shows that this analytic equality mechanism
is compatible with actual polynomial derivatives in the large-degree limit.

## 7. A failed shortcut and what repairs it

A tempting argument is: approximate the extremising free-point measure by
critical points, integrate the corresponding derivative, and choose a
constant to put all roots in the disc. The last step is not licensed by
Gauss--Lucas, which goes from roots to critical points, not conversely.
Even fixing $f'=nz^{n-1}$ leaves the arbitrary integration constant in
$f=z^n+C$, so derivative containment does not control root containment.
A proposed existential choice of the constant would require a separate
proof; it is not supplied by this example or by the free-point theorem.

The Blaschke-power construction avoids this missing inference. Root
placement is exact from the outset. The derivative equation then gives
(3), and the two different limits in the interior and exterior determine
its critical spectrum. This is a reusable way of separating a feasibility
constraint from an asymptotic objective without discarding either.

The case $b=0$ is a necessary adversarial test. Then $F_N=z^{2N}-1$ and
all critical points are zero, whereas for every fixed $b>0$ all critical
points in the quadratic construction approach the circle. The limits
$b\downarrow0$ and $N\to\infty$ do not commute. It would be incorrect to
remove the nonconstant-denominator assumption from Theorem 1.

The $p=4$ endpoint is another test: (12) is equality in the limit, not a
finite violation of the upper inequality. The finite certificate checks
$p=8$, deliberately above the proved endpoint. Repeated critical points
in (13) are counted with their exact multiplicity, including the $s-1$
points at zero.

## 8. What this teaches about the remaining geometric problem

The general target is still the all-curve inequality $\Lambda(f)\le2$ on
the closed root-disc class. The registered generic-closure argument handles
the passage to the strict open-disc formulation. None of (5), (9), or
(15) controls a root-to-root path.

For an admissible canonical critical arc, write
\[
 X_c=|f(c)|^{1/n},\qquad Q_c=\frac{L_c}{2X_c}.
\]
The task is to select an admissible $c$ with $X_cQ_c\le1$.
A marginal bound on the $X_c$ does not control the joint behaviour of
$X_c$, attachment data, and $Q_c$. The sharp spectral construction shows
that even a high-critical lower bound and failure of the displayed
separation test do not improve the universal power numerator. The short
inward-arc connection in Theorem 4 gives a separate positive family theorem.
A sharp spectral example need not threaten the geometric conclusion.

The surviving research directions should therefore retain either a
specified inverse-sheet attachment or a demonstrably usable noncanonical
competitor. Three concrete questions remain useful. First, can the
registered admissible-arc product inequality be proved with its wall and
collision behaviour controlled? Second, can a near-saturation analysis
classify alternatives into a collapsed binomial-type component and a
nonconstant-denominator region carrying a short local chord? The latter is
a research question, not an implication proved here. Third, can the
collective-window argument choose a value path using the actual
monodromy of the critical cluster, rather than an average over directions
unrelated to the required attachment? The full parent problem remains
open under every formulation above.

\newpage

## 9. Sources and reproducibility

The proof uses elementary covering, Poisson-kernel and argument-principle
facts. Useful primary-authored background is S. R. Garcia, J. Mashreghi and
W. T. Ross, *Finite Blaschke products: a survey*, arXiv:1512.05444, especially
the boundary argument derivative and circle preimages. The construction
and critical-value limit above are proved here rather than attributed to
that survey.

The general relation between root and critical-point empirical measures
has an extensive literature. Z. Kabluchko, *Critical points of random
polynomials with independent identically distributed roots*,
arXiv:1206.6692, proves a random-root convergence theorem. T. R. Reddy,
*Limiting empirical distribution of zeros and critical points of random
polynomials agree in general*, arXiv:1609.00675, discusses the obstruction
to unrestricted deterministic convergence. Neither is invoked as a proof
of (5): the deterministic power construction is treated directly here.

For the original geometric question, retain the exact comparison with
Erdős--Herzog--Piranian, *Metric properties of polynomials* (1958),
Problem 5, and Pendyala's *A Degree-Four Lemniscate Path Theorem*,
arXiv:2606.24875. The latter concerns a root-pair path theorem; it is not
the spectral limit studied here. No comprehensive priority conclusion is
claimed for the new transfer theorem or exponent sharpness.

The attached standard-library checkers and rational JSON certificates verify
(16) and (HC), including the latter witness's high-critical and
nonseparated status. The Lean file `BlaschkePowerCriticalValues.lean` proves only the
listed algebraic identities if accepted by the target kernel; it has not
been run in this environment. No theorem about weak convergence, Poisson
integration or the full sharp hierarchy is represented as Lean-checked.
