# Synchronising positive-return criteria for Mersenne subseries

**Status.** New ordinary mathematical arguments developed against the round-5 packet. No Lean build of the analytic results has been performed. Historical novelty is unassessed. The reciprocal-summable theorem remains the manuscript flagship. These results do not decide universal Erdős #257 or membership of 1/2 or 1/21.

**Main conclusion.** The finite-prime weighted class and the strengthened positive-cover class can be combined: every infinite subset of the union of one host from each class has an irrational subseries at every integer base. In particular, the previously constructed host `A_W ∪ A*` is covered, although it belongs to neither individual class. The proof supplies common small displacements rather than adding two irrational numbers.

## 1. Definitions and the arithmetic consumer

For an integer b ≥ 2 and A ⊆ N_{>0}, write

\[
 X_A(b)=\sum_{a\in A}\frac1{b^a-1},\qquad
 \Delta_{b,A}(N)=\sum_{a\in A}
     \frac{b^{N\bmod a}-1}{b^a-1}.
\]

These series converge for fixed N. Their summands are nonnegative, and the second series has strictly positive value whenever A is infinite and N > 0: choose a ∈ A greater than N. Division of N by a gives

\[
 \Delta_{b,A}(N)=(b^N-1)X_A(b)-J_{b,A}(N),
 \qquad
 J_{b,A}(N)=\sum_{\substack{a\in A\\a\le N}}
       \sum_{j=1}^{\lfloor N/a\rfloor}b^{N-ja}\in\mathbb Z. \tag{1.1}
\]

Thus rationality X_A(b)=p/q, q ≥ 1, forces every positive displacement to be at least 1/q. Also

\[
 A\subseteq E\cup F\quad\Longrightarrow\quad
 \Delta_{b,A}(N)\le\Delta_{b,E}(N)+\Delta_{b,F}(N). \tag{1.2}
\]

Overlaps cause no difficulty. The supplied all-base comparison is
\(\Delta_{b,A}(N)\le2\Delta_{2,A}(N)\). Its sharper ordinary factor-one version is already in the r4 record. Either version suffices below.

Call a host H **return-admissible** if for all ε > 0 and N₀ there is N ≥ max(1,N₀) with Δ_{2,H}(N) < ε. This definition permits finite hosts and is inherited by subsets. Every infinite subset of a return-admissible host has irrational X_A(b) at every integer base. This is a name for a proved sufficient mechanism, not an equivalent formulation of irrationality.

## 2. A finite two-scale modular estimate

Let 1 < B ≤ 2 and L,d ≥ 1 be integers. Put

\[
 w_{B,d}(n)=\frac{B^{n\bmod d}}{B^d-1},\qquad
 A_T(B,L,d)=\frac1T\sum_{m=1}^T w_{B,d}(Lm).
\]

For integers R ≥ 0 and M ≥ 1 define the finite averaging operator

\[
 \mathscr D_{L;R,M}F
   =\frac1M\sum_{j=R}^{R+M-1}\frac1{2^j}
          \sum_{m=1}^{2^j}F(Lm). \tag{2.1}
\]

Equivalently, choose j uniformly from the indicated interval, then choose m uniformly from 1,…,2^j, and evaluate F at Lm. This is an actual finite probability distribution.

### Theorem 2.1 (uniform dyadic-shell bound)

For every choice of the above parameters,

\[
 \boxed{\quad
 \mathscr D_{L;R,M}w_{B,d}
 \le\frac{1+4L/M}{d(B-1)}.
 \quad} \tag{2.2}
\]

The starting index R is arbitrary. The estimate is uniform as B decreases to one and as d grows. Dependence on the sampling modulus is only L/M. The leading constant one is optimal uniformly: take L=d=1 and let M grow.

#### Proof

There are three regimes, with T=2^j.

**Completed or partly completed periods: d ≤ LT.** Let g=gcd(L,d). A complete orbit of Lm modulo d has length d/g and total atom mass 1/(B^g−1). Consequently

\[
 A_T(B,L,d)
 \le\frac{g}{d(B^g-1)}+\frac1{T(B^g-1)}
 \le\frac1{d(B-1)}+\frac1{T(B-1)}. \tag{2.3}
\]

The last step is the elementary inequality B^g−1 ≥ g(B−1). For all dyadic lengths with d ≤ L2^j, their reciprocal sum is at most 2L/d. Indeed, if j₀ is the first such index in the interval, the sum is at most 2^{1−j₀} ≤ 2L/d. Thus the total incomplete-period error across these lengths is at most

\[
 \frac{2L}{d(B-1)}. \tag{2.4}
\]

**Before the middle of the first period: d > 2LT.** There is no wrap, and N=Lm ≤ LT satisfies 2N ≤ d−1. The arithmetic–geometric mean inequality gives

\[
 \frac{B^d-1}{B-1}=\sum_{i=0}^{d-1}B^i
 \ge dB^{(d-1)/2}\ge dB^N.
\]

Hence every sampled atom is at most 1/[d(B−1)]. The same proof can be written using pairs of integer powers; the fractional exponent is only a convenient notation for their geometric mean.

**The transition shell: LT < d ≤ 2LT.** At most one dyadic length lies in this regime. There is still no wrap, so

\[
 A_T(B,L,d)
 =\frac{B^L}{T(B^L-1)}\frac{B^{LT}-1}{B^d-1}.
\]

Convexity of B^t−1 on [0,d], with value zero at zero, implies
\((B^{LT}-1)/(B^d-1)\le LT/d\). Therefore

\[
 A_T(B,L,d)
 \le\frac{LB^L}{d(B^L-1)}
 \le\frac{LB}{d(B-1)}
 \le\frac{2L}{d(B-1)}. \tag{2.5}
\]

The far and near regimes together cost at most M/[d(B−1)] in their main terms. Equations (2.4) and (2.5) add at most 4L/[d(B−1)]. Divide by M. \(\square\)

**What changed from r3.** The r3 interpolation estimate controls a fixed-L average by B^L/(d log B), then takes a limit. Equation (2.2) controls a finite average with moving L provided M/L is large. This is the additional uniformity needed to combine the two methods. It is not merely a different proof of pointwise convergence.

### Corollary 2.2 (countable nonnegative majorants)

For c_d ≥ 0 and C=Σ_d c_d/d < ∞, let

\[
 V_B(n)=\sum_{d\ge1}c_dw_{B,d}(n).
\]

Then

\[
 \mathscr D_{L;R,M}V_B
 \le(1+4L/M)\frac C{B-1}. \tag{2.6}
\]

This follows by nonnegative interchange of sums. No uniform bound on individual c_d, no finite support, and no dominated-convergence interchange are needed. The finite right-hand side also ensures finiteness at every sample point carrying positive probability.

More generally, for B_j ∈ (1,2], coefficients c_{j,d} ≥ 0, and nonnegative t_j,

\[
 \mathscr D_{L;R,M}\!\left(\sum_j t_jV_{B_j}\right)
 \le(1+4L/M)\sum_j\frac{t_jC_j}{B_j-1}. \tag{2.7}
\]

This is the common estimate used by the hybrid proof.

## 3. The strengthened cover criterion, with a finite proof

For finite F ⊆ N_{>0}, define

\[
 f_F(n)=\#\{a\in F:a\mid n\},\qquad
 U_F(n)=\sum_{r\ge1}2^{-r}f_F(n+r).
\]

A strengthened positive cover consists of finite sets F_j, numbers 0 < α_j ≤ 1, positive weights η_j with Σ_j η_j=1, and c_{j,d} ≥ 0 such that

\[
 f_{F_j}(n)^{\alpha_j}\le\sum_{d\mid n}c_{j,d},\quad
 C_j=\sum_{d\ge1}\frac{c_{j,d}}d,\quad
 K=\sum_j\frac{C_j\eta_j^{-\alpha_j}}{2^{\alpha_j}-1}<\infty. \tag{3.1}
\]

Let \(V=\bigcup_j F_j\). Write B_j=2^{α_j} and

\[
 V_j(n)=\sum_{r\ge1}B_j^{-r}\sum_{d\mid n+r}c_{j,d}
       =\sum_{d\ge1}c_{j,d}w_{B_j,d}(n).
\]

Subadditivity of t↦t^{α_j}, applied first to finite sums and then by monotone convergence, gives

\[
 U_{F_j}(n)^{\alpha_j}\le V_j(n). \tag{3.2}
\]

Given ρ>0, set t_j=ρη_j and

\[
 S_J(n)=\sum_{j>J}t_j^{-\alpha_j}V_j(n),\qquad
 K_J(\rho)=\sum_{j>J}\frac{C_jt_j^{-\alpha_j}}{B_j-1}.
\]

Because ρ^{−α_j} ≤ max(1,ρ^{-1}), we have K_J(ρ)→0. If L is divisible by every member of \(\bigcup_{j\le J}F_j\), then the corresponding displacement atoms vanish at every multiple of L. At any such multiple N with S_J(N)<1,

\[
 \Delta_{2,A}(N)\le\sum_{j>J}U_{F_j}(N)\le\rho
 \qquad(A\subseteq V). \tag{3.3}
\]

On the other hand, Corollary 2.2 gives the **finite, uniform estimate**

\[
 \boxed{\quad
 \mathscr D_{L;R,M}S_J\le(1+4L/M)K_J(\rho).
 \quad} \tag{3.4}
\]

Choose J with K_J(ρ)<1/4, then choose L to freeze the prefix, then choose M ≥ 4L. The right-hand side is below 1/2, so a sample with S_J<1 exists. Choosing L to be a multiple of an arbitrarily prescribed integer also yields arbitrarily late samples. This reproves return-admissibility of the strengthened-cover class without the r3 interpolation argument.

This proof is a replacement mechanism for an already registered ordinary criterion. Its additional content is the finite bound (3.4), which remains usable when L changes for another reason.

## 4. A weighted averaging estimate with an extra prescribed modulus

Let P be a finite nonempty prime set, define

\[
 h_P(a)=\prod_{p\in P}p^{v_p(a)},\qquad
 W=\sum_{a\in E}\frac{h_P(a)}{a(2^{h_P(a)}-1)}<\infty. \tag{4.1}
\]

The following is the finite estimate underlying the weighted proof in the supplied analytic supplement. We include the parameter choices to make the synchronisation argument self-contained.

Fix any L₀≥1, any κ>0, and a finite F⊆E such that the weighted mass of \(E\setminus F\) is below κ. Let L be a common multiple of L₀ and all elements of F. Put p_*=max P, r=|P|, and, for large integers H,

\[
 Q_0(H)=\prod_{p\in P}p^{\lfloor\log_pH\rfloor},\quad
 Q(H)=LQ_0(H),\quad G(H)=\lfloor H/p_*\rfloor,\quad
 M(H)=\lfloor2^{G(H)/2}\rfloor. \tag{4.2}
\]

Then Q≤LH^r and Q/M→0. With the operator from (2.1),

\[
 \begin{split}
 \mathscr D_{Q;M,M}\Delta_{2,E}\le{}&\kappa+\frac{2QW}{M}\\
 &+\frac{G(1+\log Q+2M\log2)+Q}{2^G-1}
       +4\,2^{-M}.
 \end{split} \tag{4.3}
\]

Every term after κ tends to zero as H→∞, with L and F fixed.

### Proof of (4.3)

For g=gcd(Q,a), the complete-orbit argument gives

\[
 \frac1T\sum_{m=1}^T\frac{2^{Qm\bmod a}-1}{2^a-1}
 \le\frac{g}{a(2^g-1)}+\frac1{T(2^g-1)}. \tag{4.4}
\]

If h_P(a)≤H, then h_P(a) divides Q₀(H). Monotonicity of n/(2^n−1) bounds the main term by the weighted summand in (4.1). The finite prefix F contributes zero. The incomplete-period terms, truncated to a≤QT, are handled by the finite dyadic identity

\[
 \sum_{j=M}^{2M-1}2^{-j}\sum_{a\le Q2^j}\gamma_a
 \le2Q\sum_a\frac{\gamma_a}{a},\qquad \gamma_a\ge0, \tag{4.5}
\]

with γ_a=1_E(a)/(2^{h_P(a)}−1). To prove (4.5), interchange the finite sums and use Σ_{j:Q2^j≥a}2^{-j}≤2Q/a. Its right-hand series is at most W.

If h_P(a)>H, the gcd g is at least G. Indeed, either every individual P-prime-power component is at most H, in which case all of h_P(a) divides Q₀, or one component exceeds H and Q₀ contains a power greater than H/p_*. Summing (4.4) for a≤QT bounds this class by

\[
 \frac{G(1+\log(QT))+Q}{2^G-1}.
\]

Finally, the outer tail a>QT costs at most 4/T: no such atom wraps, and

\[
 \sum_{a>QT}\frac{2^{Qm}-1}{2^a-1}\le 2\,2^{Qm-QT},\qquad
 \sum_{m=1}^T2^{Qm-QT}\le2.
\]

Average these bounds over T=2^j, M≤j<2M. This proves (4.3). The asymptotics follow because Q is polynomial in H whereas M is exponential in G∼H/p_*. \(\square\)

**Scope of the input.** This is the supplied finite-prime weighted argument with an arbitrary additional fixed divisor L₀ imposed. The new hybrid theorem uses the same estimate and the same sampling distribution. No assertion of convergence of the infinite-support ordinary mean for a fixed Q is made.

## 5. The hybrid theorem

### Theorem 5.1 (weighted–cover synchronisation)

Suppose E satisfies (4.1) for some finite nonempty P, and V has a strengthened positive cover (3.1). Then E∪V is return-admissible. Consequently,

\[
 \boxed{\quad
 \sum_{a\in A}\frac1{b^a-1}\notin\mathbb Q
 \quad\text{for every infinite }A\subseteq E\cup V
 \text{ and every integer }b\ge2.
 \quad} \tag{5.1}
\]

#### Proof

Fix a desired binary tolerance ε>0 and a minimum index N₀. Let ρ=ε/3. Choose J so that K_J(ρ)<1/16. Choose a finite F⊆E whose weighted complement has mass κ<ρ/16. Let L be a positive common multiple of all elements of F and \(\bigcup_{j\le J}F_j\), and of max(1,N₀).

Use Q(H), G(H), M(H) from (4.2). All prefix atoms from both components vanish on Q(H)-multiples. Equations (3.4) and (4.3) apply to the **same** distribution:

\[
 \mathscr D_{Q;M,M}S_J\le(1+4Q/M)K_J(\rho)<\tfrac18
\]

for large H, and

\[
 \mathscr D_{Q;M,M}\bigl(\Delta_{2,E}/\rho\bigr)<\tfrac18
\]

for large H. Thus the finite average of the nonnegative test

\[
 Z(N)=\Delta_{2,E}(N)/\rho+S_J(N)
\]

is below 1/4. Some sample N=Qm has Z(N)<1. At that same N,

\[
 \Delta_{2,E}(N)<\rho,\qquad
 \Delta_{2,V}(N)\le\rho,
\]

and therefore Δ_{2,E∪V}(N)<2ρ<ε. Since N≥Q≥L≥N₀ and ε,N₀ were arbitrary, the host is return-admissible.

Any infinite A⊆E∪V has strictly positive displacement at every positive N. Equations (1.1), (1.2), and the supplied base comparison now exclude rationality at every integer base. \(\square\)

### Corollary 5.2 (strict enlargement of the two individual classes)

Let \(\mathcal W\) be the union of the finite-P weighted classes and \(\mathcal V\) the strengthened positive-cover class, both defined at base two. Let

\[
 \mathcal H=\{A:A\subseteq E\cup V\text{ for some }E\in\mathcal W,
                         V\in\mathcal V\}.
\]

Then all infinite members of \(\mathcal H\) have irrational X_A(b) at every integer base. Moreover,

\[
 \mathcal W\cup\mathcal V\subsetneq\mathcal H.
\]

**Proof.** The r3 host A* is odd and squarefree, lies in V, and lies in no finite-P weighted class. The r4 host A_W consists of exponents 2^k d with k≥2 and d odd, lies in W, and lies in no strengthened positive-cover class. Both exclusions quantify over all candidate parameters and covers, as proved in the supplied notes. Theorem 5.1 covers their disjoint union. If that union belonged to either individual class, downward closure would place the excluded component in the same class, a contradiction. \(\square\)

For clarity, the constructions being used are:

\[
 A^*=\bigcup_{j\ge1}\{q_jd:d\mid M_j\},\quad
 2^{3j}<q_j<2^{3j+1},\quad
 \sum_{p\mid M_j}\frac1p\in[4^j,4^j+1],
\]

with pairwise disjoint reserved primes and odd squarefree prime blocks, and

\[
 A_W=\bigcup_{k\ge2}\{2^kd:d\mid N_k\},\quad
 \sum_{p\mid N_k}\frac1p\in[2^{k-2},2^{k-2}+1],
\]

with pairwise disjoint odd prime blocks. Their defining prime blocks need not be computably small. We do not claim to enumerate them in the finite checker. Their existence is established by divergence of the prime reciprocal sum and the elementary prime interval input already used in the packet.

The new statement concerns the **mixed host**, not a new discovery of either component or of their individual irrationality.

### Corollary 5.3 (an ideal of sufficient supports)

The class H is closed under taking subsets, finite unions and finite changes. It is the smallest such finite-union ideal containing W and V. It is not closed under arbitrary countable unions.

**Proof.** Each class is downward closed and contains all finite sets. If E₁ and E₂ have weighted prime sets P₁ and P₂, use P=P₁∪P₂. The P-part of each exponent is larger, and t/(2^t−1) decreases with t, so the union still has finite weighted mass. If V₁ and V₂ have covers with weights η and θ, interleave their frames and use weights η/2 and θ/2. Since 2^α≤2, the new total cost is at most twice the sum of the two old costs. Thus V is also closed under finite unions. It follows that the class of subsets of one W-host union one V-host is closed under finite unions and is exactly their generated ideal.

Every prime singleton belongs to H. Their countable union does not, by the prime-core barrier in Proposition 7.1 and return-admissibility of H. Countable gluing consequently requires a tail budget; it cannot follow from the mere existence of certificates for each component. \(\square\)

This makes the structural contribution precise: the two already-separated criteria generate a strictly larger finite-union ideal whose infinite members are still irrational at every integer base. The ideal statement is a consequence of Theorem 5.1 and the explicit rescaling of positive covers, not a claim that all return-admissible hosts form an ideal.

## 6. Bounded rational alphabets and a necessary boundary

### Proposition 6.1 (bounded nonnegative lattice coefficients)

Let H be return-admissible. Suppose D≥1 and C>0 are fixed, and

\[
 \lambda_a\in D^{-1}\mathbb Z\cap[0,C],\qquad
 \{a:\lambda_a>0\}\subseteq H
\]

has infinitely many elements. Then

\[
 \sum_a\frac{\lambda_a}{b^a-1}\notin\mathbb Q
 \qquad\text{for every integer }b\ge2.
\]

**Proof.** The weighted displacement is strictly positive and bounded by CΔ_{b,H}(N). Multiplication of its analogue of (1.1) by D clears every coefficient denominator. If the sum were p/q, a nonzero displacement would be at least 1/(Dq). Return-admissibility contradicts that gap. \(\square\)

This is a cheap consequence of the already checked close-return mechanism for reciprocal-summable H, and of Theorem 5.1 for mixed hosts. It allows arbitrary nonperiodic coefficients from any fixed finite set of nonnegative rational numbers. It is not linear independence, which would require signed combinations.

The common denominator cannot simply be dropped. For any strictly increasing positive integers a_j and any fixed integer b≥2, put

\[
 \lambda_{a_j}=(b^{a_j}-1)(b^{-a_j}-b^{-a_{j+1}}).
\]

These are rational numbers strictly between zero and one, but

\[
 \sum_{j\ge1}\frac{\lambda_{a_j}}{b^{a_j}-1}=b^{-a_1}\in\mathbb Q. \tag{6.1}
\]

The equality is telescoping. It holds even if a_j=j², whose reciprocal mass converges. The coefficients depend on the chosen base. Thus boundedness and positivity alone do not replace the fixed arithmetic lattice.

## 7. A whole class on which positive returns are impossible

### Proposition 7.1 (prime-core barrier)

Let \(\mathbb P\) be the prime support. For every positive N,

\[
 \boxed{\quad\Delta_{2,\mathbb P}(N)>\frac13.\quad} \tag{7.1}
\]

Consequently the same bound holds for every support containing all primes, regardless of which composite exponents are added.

**Proof.** Its divisor incidence is ω(n), the number of distinct prime factors. For N≥1 all N+r are at least two, hence

\[
 T_N=\sum_{r\ge1}\omega(N+r)2^{-r}\ge1.
\]

On the other hand,

\[
 X_{\mathbb P}(2)\le\sum_{a\ge2}\frac1{2^a-1}
 <\frac43\sum_{a\ge2}2^{-a}=\frac23.
\]

The strict inequality follows already from any exponent a>2. Subtract to obtain (7.1). Adding support elements adds nonnegative displacement atoms. \(\square\)

Prime-support irrationality is independently established by Tao–Teräväinen, Theorem 1.3 of arXiv:2512.01739v2. Proposition 7.1 therefore separates **irrationality** from the entire small-positive-displacement mechanism, not just from one choice of cover or modulus. It also shows that the hybrid theorem leaves a genuine third regime.

More generally, if a support E has divisor incidence c_E(n)≥κ for all n≥n₀ and X_E(b)<κ/(b−1), then

\[
 \Delta_{b,E}(N)\ge\kappa/(b-1)-X_E(b)>0\qquad(N\ge n_0-1).
\]

This is a structural obstruction to this particular return functional. It is not a rationality theorem or a claim that all irrationality methods fail.

## 8. Why the initially tempting combination fails

The two separately established facts

\[
 \forall\varepsilon>0\ \exists N:\Delta_E(N)<\varepsilon,
 \qquad
 \forall\varepsilon>0\ \exists N:\Delta_V(N)<\varepsilon
\]

do not give a common N. For an exact abstract countermodel, let

\[
 f(n)=\begin{cases}(n+1)^{-1},&n\text{ even},\\1,&n\text{ odd},\end{cases}
 \qquad
 g(n)=\begin{cases}1,&n\text{ even},\\(n+1)^{-1},&n\text{ odd}.\end{cases}
\]

Both have arbitrarily late arbitrarily small positive values, while
\(f(n)+g(n)=1+(n+1)^{-1}>1\) for every n. These are not asserted to be actual Mersenne displacement functions; they refute the proposed logical inference from separate recurrence alone.

A second attempted repair also has a genuine gap: freeze a cover prefix, choose the weighted modulus Q(H), and appeal to convergence of the cover mean for this fixed Q(H). That gives a threshold T₀(Q(H)), with no comparison to the window allowed by the weighted proof. A diagonal argument cannot invent that comparison. Theorem 2.1 supplies the missing finite estimate and makes both errors small on one prescribed schedule.

This is the useful failure-to-mechanism chain:

separate return witnesses → synchronisation missing;
fixed-modulus convergence → moving-modulus uniformity missing;
finite dyadic-shell estimate → common distribution available;
common distribution → hereditary irrationality of mixed hosts.

## 9. Strong follow-up questions

1. **A general compatibility class.** Characterise support classes admitting a small-displacement certificate under finitely supported measures with arbitrarily large forced divisibility. Is there a natural capacity whose finite-union closure is exactly captured by such common schedules? Pointwise return-admissibility alone does not prove closure.
2. **The separated-return regime.** Can one combine the hybrid method with an analytic prime-supported component? Proposition 7.1 shows that this requires a different test functional, such as phase cancellation or an anti-concentration estimate; no improvement to the positive return bound can suffice for the full prime component.
3. **Actual rational targets.** For the actual greedy selector, prove or refute cofinal inequalities c_x(N+1)≥Q_N+β_N. Theorem 5.1 only helps a target after proving that its actual support belongs to the hybrid class. Proving this for the 1/2 support, for example, would exclude membership rather than construct it. No such classification is supplied here.
4. **Formalisation.** The finite shell estimate is the highest-leverage analytic target. Its three components are (2.3), the centred geometric-sum bound, and the single transition-shell estimate (2.5). The finite gluing and joint-witness combinators in the returned Lean candidate isolate these pieces without claiming to have formalised them.

## 10. Authority and external sources

Packet premises: `docs/research/erdos257-eight-return-proofs.md`, Part r1, Theorem 1 and equations (11)–(29); `StrengthenedVariableExponentCover.md`, Theorems A.1–A.2 and B.2; `CoverFirstLogarithmicMoment.md`, B.1–B.4; and the checked all-base displacement transfer in `AllBaseReciprocalSupportIrrationality.lean`.

External context: P. Erdős, *On the irrationality of certain series*, Math. Student 36 (1968), 222–226, issued 1969, especially pp. 222 and 226; T. Tao and J. Teräväinen, *Quantitative correlations and some problems on prime factors of consecutive integers*, arXiv:2512.01739v2, Theorem 1.3. The finite-shell estimate and hybrid consequence are claims of this return, with no historical-priority assertion.
