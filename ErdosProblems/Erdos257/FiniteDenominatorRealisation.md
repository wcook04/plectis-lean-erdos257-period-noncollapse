# Finite denominators: a false inverse, a prime-lcm formula, and an explicit gap

Ordinary arithmetic. Historical novelty unassessed. None of this replaces
the Lean-checked finite-period noncollapse theorems
`finite_period_noncollapse`, `finite_period_noncollapse_rat_den`,
`coprime_base_den_finiteErdosSum`, and `lcm_lt_den_finiteErdosSum`.

## Negative result

Write \(\mathcal D_b(L)\) for the reduced denominators of nonempty finite
sums \(\sum_{n\in F}(b^n-1)^{-1}\) with \(\operatorname{lcm}(F)=L\). The
proposed equality
\[
\mathcal D_b(L)
=\{D:D\mid b^L-1,\ \operatorname{ord}_D(b)=L\}
\]
is false. In the manuscript notation,
\[
\mathcal D_2(6)=\{21,63\},
\]
although \(9\mid 2^6-1\) and \(\operatorname{ord}_9(2)=6\).

**Proof.** Every exponent in a finite support of lcm \(6\) divides \(6\), so
\(F\subseteq\{1,2,3,6\}\). If \(6\notin F\), lcm \(6\) forces \(2,3\in F\),
giving denominator \(21\); adjoining \(1\) only adds an integer. If
\(6\in F\), the numerator over \(63\), modulo \(63\), is
\(1+21\varepsilon_2+9\varepsilon_3\in\{1,22,10,31\}\), all coprime to
\(63\). Thus the denominator is \(63\). Finally \(2^3\equiv-1\pmod9\) and
\(2,2^2\not\equiv1\pmod9\), proving order \(6\). ∎

Exact enumeration of those supports is in
`scripts/reconstruct_variable_exponent_dagger.py` (`check_d1_denominator_realisation`).

## Prime-lcm classification

For every integer \(b\ge2\) and prime \(p\), put \(M=b^p-1\). Then
\[
\mathcal D_b(p)=\Bigl\{M,\ \frac{M}{\gcd(b-1,p+1)}\Bigr\}.
\]

**Proof.** Necessarily \(F=\{p\}\) or \(F=\{1,p\}\). The first denominator
is \(M\). For the second put \(S=M/(b-1)=1+b+\cdots+b^{p-1}\). The numerator
over \(M\) is \(1+S\). Since \(\gcd(S,1+S)=1\),
\[
\gcd(M,1+S)=\gcd(b-1,1+S)=\gcd(b-1,p+1).
\]
Reduction gives the formula. ∎

This closes the equality question negatively and supplies a complete first
classification. It does not provide the height estimate needed for an
actual final-skip argument.

## Ordinary noncancellation (unsigned and signed)

The r3 gap is closed as an ordinary argument, and the signed unit-coefficient
extension is Lean-checked in
`ErdosProblems/Erdos257/SignedFinitePeriodNoncollapse.lean`.

**A.1.** If \(\ell\mid\Phi_n(b)\) and \(e=v_\ell(b^n-1)\) for integers
\(b\ge2\) and \(n\ge2\), then \(\operatorname{ord}_{\ell^e}(b)=n\).  For odd
\(\ell\) the lifting-the-exponent formula for \(v_\ell(b^m-1)\) inverts, via
the cyclotomic factorisation of \(b^m-1\), to force \(n=f\ell^j\) with
\(f=\operatorname{ord}_\ell(b)\).  The full valuation is then an exact-order
exponent.  For \(\ell=2\) the same inversion uses the two-adic formula with
\(a=v_2(b-1)\) and \(c=v_2(b+1)\).  There are no exceptional pairs in this
prime-power formulation: \(\Phi_6(2)=3\) has no prime of order \(6\), but
\(v_3(2^6-1)=2\) and \(\operatorname{ord}_9(2)=6\).  Lean: 
`cyclotomic_prime_dvd_imp_exactOrder_full_val`,
`exactOrder_two_mod_nine`.

**A.2 (unsigned repair of `res:period`).** Let \(F\) be nonempty and finite,
with \(0\notin F\), and \(S=\sum_{n\in F}(b^n-1)^{-1}=P/D\) in lowest terms.
Every summand denominator divides \(b^L-1\) for \(L=\operatorname{lcm}(F)\),
so \(D\mid b^L-1\), hence \(\gcd(b,D)=1\) and \(\operatorname{ord}_D(b)\mid L\).
If some exponent is at least \(2\), a divisibility-maximal \(n\ge2\) supplies,
by A.1, a prime power \(\ell^e\) which divides \(b^m-1\) exactly when
\(n\mid m\).  Maximality makes the \(n\)-summand the unique term of
\(\ell\)-adic valuation \(-e\).  A finite sum with a unique least valuation
has that valuation, so \(v_\ell(S)=-e\), \(S\ne0\), and \(\ell^e\mid D\).
Thus \(n\mid\operatorname{ord}_D(b)\).  Every member of \(F\) divides a
divisibility-maximal member, so \(L\mid\operatorname{ord}_D(b)\).  The remaining
case is \(F=\{1\}\), where \(S=1/(b-1)\).  If \(L\ge2\) then
\(L=\operatorname{ord}_D(b)\le\varphi(D)<D\).

**Signed unit coefficients.** The same unique-valuation argument applies with
\(\varepsilon_n\in\{-1,1\}\): units do not change the valuation of a summand.
Lean: `signed_finite_period_noncollapse`.  Arbitrary nonzero integer
coefficients fail: \(1/(2-1)+3/(2^2-1)=2\) has lcm \(2\) and denominator \(1\).

**Order \(6\) is not only from \(9\).** For \(F=\{2,6\}\) the local witness is
\(\operatorname{ord}_9(2)=6\) inside \(D_F=63\).  Separately,
\(\operatorname{ord}_{21}(2)=\operatorname{lcm}(2,3)=6\) for \(F=\{2,3\}\).
The live short-note sentence that order \(6\) in a divisor of \(63\) can only
come from \(9\) was false as a global mechanism.

**A.3 (ordinary).** Write \(R_b(n)=\prod_{\ell\mid\Phi_n(b)}\ell^{v_\ell(b^n-1)}\).
On a divisibility-maximal \(n\ge2\), every such \(\ell\) has
\(v_\ell(D)=v_\ell(b^n-1)\), so \(R_b(n)\mid D\).  Distinct maximal exponents
have disjoint cyclotomic prime sets, hence the product of those \(R_b(n)\)
divides \(D\).  Lean currently checks the one-prime identity
`signed_divisibility_maximal_cyclotomic_den_val`; the product statement stays
ordinary.

**D.2.** Cyclotomic *lower* bounds on \(D_F\) make rational-difference lower
bounds \(1/(q D_F)\) *smaller*, not larger.  They do not prove the actual
selector inequality, and they do not decide \(1/2\) or \(1/21\).
