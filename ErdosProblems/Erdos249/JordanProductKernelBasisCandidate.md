# Jordan-product kernel basis (ordinary candidate, not in the manuscript)

Type B r3 proposed a full $k$-kernel basis for
$f(n)=n^a\prod_i J_{s_i}(n)^{m_i}$ with a nonempty Jordan product, same
indexing family as the totient, rank $k^e+1$, and integral reductions.

**Not new.** Live Lean already proves affine independence for the special
case $n^q\varphi(n)^m$ ($m\ge1$) as
`linearIndependent_totientPowAffineForms` in
`Erdos257PeriodNoncollapse/AllBaseTotientKernel.lean`.  That statement is
not re-registered.  The all-base *rank* for that class is still open in
Lean (the module says the $f_{q,m}$ reductions are missing).

**Collision.** Martin (annex `martin-2006-simultaneous-phi-inequalities`)
is the affine-ordering antecedent for totient independence.  Coons
(`coons-2010-nonautomaticity-number-theoretic-functions`) is non-regularity
of $\varphi$.  Bell–Smertnig
(`arxiv-2603-23456-bell-smertnig-mahler-multiplicative`) classifies
multiplicative Mahler series and mentions Jordan totients as examples; it
does not state this finite-level basis.  Search result, not a priority
claim.

**Checked here.** Exact scalar identities and $C_f$ integrality:
`scripts/check_jordan_product_kernel_scalars.py --quick` (`all_checks_pass`).
The empty product $f(n)=n$ has kernel rank $2$ at $k=2$, $e=1,2,3$, so
the exponential rank formula fails without a Jordan factor.

**Checked here, r4.** Empty-product rank obstruction is now Lean-checked as
`affineNatSeq_span_finrank_le_two` in
`ErdosProblems/Erdos249/AffineTotientSignature.lean` (focused
`lean_fast_build` exit 0, 2026-09-07): affine sequences `n ↦ an+b` span a
space of dimension at most two.  The nonempty Jordan-product rank `k^e+1`
claim is still not Lean.

**Evidence class.** Ordinary-proof candidate for the nonempty product;
Lean-checked for the empty-product rank `≤ 2` obstruction.  Not in
the kernel-basis paper.  Does not decide $S$.
