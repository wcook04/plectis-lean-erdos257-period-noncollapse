# Finite certificates for unrestricted channel-moment ideals (Type B r5)

Ordinary proofs plus exact integer checks for Erdős #68. Type B is advisory.
Novelty versus the external literature is unassessed. The parent series

\[
S=\sum_{n\ge2}\frac1{n!-1}
\]

remains open.

## Lead judgement (not a freeze)

The live title and first numbered theorem stay the two incomparable
denominator exclusions and the companion-orbit rationality criterion.
That is a judgement that the paper's centre has not moved, not a
preservation rule. The new stopping theorem decides an auxiliary gcd
for channel kernels. It is not a stronger statement about \(S\), not an
irrationality instance, and not a replacement for the exclusions
\(q\nmid 299999!\) and \(q\ge 2^{39990}>10^{12038}\). Replacing Theorem 1
by the stopping test would bury the \(S\)-facing exact criterion behind
an optimisation lemma.

`--quick` and full replay:

```
./repo-python Erdos68/scripts/check_moment_saturation.py --quick
./repo-python Erdos68/scripts/check_moment_saturation.py --max-d 24 --limit 800
```

Focused Lean target `ErdosProblems.Erdos68.TailIdealCertificate` is
generic transport; it assumes the lcm envelope and does not formalise
the factorial arithmetic. This-wave `lean_fast_build --jobs 2` first
exited 75, then queued future `cf_3c203a9ba0ad46a1af65` completed
**exit 0** (`✔ Built ErdosProblems.Erdos68.TailIdealCertificate (70s)`,
child `cmdrun_20260907T142428Z_64619`). Not imported from
`ErdosProblems.lean` / `Root.lean`. Needed barrel import if later
admitted: `ErdosProblems.Erdos68.TailIdealCertificate`. Do not
Palomar-submit these generic lemmas as a parent theorem.

## Collision with the live corpus

- The attainable-moment formula \(L_D g_D/\gcd(g_D,a_D)\mathbb Z\) is the
  r4 ordinary result `attainable_moment_ideal_support_n_ge_2`. Round 5
  supplies the missing finite certificate that \(g_D\) is determined by a
  stopping test, so unrestricted-support scans through 40 are no longer
  the evidence boundary.
- The factor \(12 L_D\mid M\) on support \(n\ge2\) remains
  `DivisorChannelBasis.lean`. The unrestricted \(\mu_D\) may be larger
  than \(12 L_D\) (e.g. \(\mu_4=1380=12 L_4\)).
- Sharp radius / \(\liminf N/D^{3/2}\ge 4\sqrt2/9\) is already in the
  long record under `res:radius-constant`. Not a new constant.
- Compressed primitive grids remain a different family. Minimum moment
  and minimum upper support are different objectives (\(D=4\): 1380 versus
  4140 on support through 6).
- The generating identity at \(x=1\) gives a real vanishing that does
  not identify the p-adic sums \(\beta_p\).

## Ordinary envelope and stopping

Write \(\Lambda_n=\operatorname{lcm}(1,\ldots,n)\) and \(u_n=[e_1]U_n\).
If \(d\mid n\), Legendre's formula yields \(\Lambda_n\mid W_{d,n}\Lambda_d\).
Induction in the scalar recurrence then gives \(\Lambda_n\mid u_n\).

If \(N>D\ge2\) and \(g_{D,N}=\gcd(u_{D+1},\ldots,u_N)>0\) divides
\(\Lambda_{N+1}\), then \(g_D=g_{D,N}\). A plateau of a gcd is not itself
the certificate; the envelope test is. For every fixed \(D\) the test
succeeds by index \(D^4\) (Bertrand plus the exact prime-power valuations
\(v_2(u_{2^k})=k\) and \(v_p(u_{2p^k})=2k\)). That horizon is sufficient,
not claimed sharp. Actual stops through \(D=24\) are much smaller, except
\(D=24\) where the gcd last changes at 32 but the envelope test waits
until 728 because \(3^6=729\).

The multiplier \(\tau_D=\mu_D/L_D\) has no prime factor exceeding \(2D\).
Together with the admitted \(\log L_D\) growth this gives
\(\log\mu_D/\log L_D\to 1\). Support correction is negligible at log
scale. It does not prove residual nonintegrality.

## Exact certificates (this-wave replay)

Byte-identical to the Type B JSON
`35199226bdd05e2ab7f9a8a9710c18382c2f7a2b7936409a26bfa028815d13fb`.
Twenty-three unrestricted-support rows, 3883 transport tests, 98
prime-power valuation tests, 35 p-adic nonvanishing certificates
(primes \(\le 149\)).

| \(D\) | \(g_D\) | \(\tau_D\) | stop \(N\) |
|---:|---:|---:|---:|
| 2–3 | 12 | 12 | 4 |
| 4–5 | 60 | 12 | 8 |
| 6–7 | 840 | 24 | 12 |
| 8–9 | 7560 | 216 | 26 |
| 10–11 | 83160 | 216 | 26 |
| 12–13 | 2162160 | 432 | 26 |
| 14–17 | 36756720 | 432 | 26 |
| 18–21 | 698377680 | 432 | 26 |
| 22–23 | 16062686640 | 9936 | 26 |
| 24 | 21684626964000 | 13413600 | 728 |

Depth 4: \(L_4=115\), \(a_4=-55\), \(u_6=-180\), \(u_8=-4200\),
\(23u_6-u_8=60\mid\Lambda_9\), so \(\mu_4=1380\), attained by
\(12K_4+253U_6-11U_8\).

For \(p=17\), \(\beta_{17}\equiv 221\pmod{289}\) with
\(v_{17}(\beta_{17})=1\); the stored clearing is
\(17\beta_{17}\equiv 3757\pmod{4913}\). Nonvanishing for every prime is
unproved. The p-adic dichotomy is ordinary: \(\beta_p=0\) keeps
\(v_p(\mu_D)=e_p\); \(\beta_p\neq 0\) forces \(v_p(\mu_D)\to\infty\).

## What this does not do

- Does not prove cofinal \(m\nmid Z_m\).
- Does not raise the parent.
- Does not formalise the factorial envelope in Lean.
- Does not exclude every \(299999\)-smooth denominator of any magnitude:
  the live exclusion is \(q\nmid 299999!\).
- Does not claim priority versus Myerson or treat Palomar as accepted.
