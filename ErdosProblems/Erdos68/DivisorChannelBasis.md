# Divisor-coordinate channel basis (Type B r4)

Ordinary and Lean-checked identities for Erdős #68 channel arithmetic.
Novelty versus the external literature is unassessed. The parent series

\[
S=\sum_{n\ge2}\frac1{n!-1}
\]

remains open. The live lead is unchanged: the two incomparable finite
denominator exclusions \(q\nmid 299999!\) and \(q\ge2^{39990}>10^{12038}\).

`--quick` checker:

```
./repo-python Erdos68/scripts/check_divisor_channel_basis.py --quick
```

Focused Lean target: `ErdosProblems.Erdos68.DivisorChannelBasis`.

## Collision with the live corpus

- `ChannelIntegralCongruence.lean` already checks \(V_d\equiv M\pmod{d!-1}\)
  on unrestricted support, hence \(L_D\mid M\) after annihilating channels
  through \(D\). The factor \(12\) uses the stricter manuscript support
  \(n\ge2\). It does not contradict the general Lean statement.
- `PrimeUnitTranslator.lean` is the prime case \(U_p=T_p\).
- `FactorialChannelCertificate.lean` already has `channelEvent_eq_zero_of_not_dvd`.
  The missing divisor-event identity is \(V_d(T_n)=(d!-1)W_{d,n}1_{d\mid n}\).
- `canonical_channel_kernel_D2_D12` and the \(D=9\) residue under printed
  support \(n\ge2\) plus moment \(M=L_D\) are impossible (even versus odd).
  Auxiliary kernels \(K_D\) with an index-\(1\) coordinate explain how a
  moment-\(L_D\) construction can exist on a larger domain. The unavailable
  coefficient arrays are not reconstructed here.
- Compressed primitive grids (`CompressedPrimitiveChannelKernel.md`) remain
  a remote-support construction. Minimal upper support \(N_{\min}(D)\) is a
  different optimisation.
- The continued-fraction endpoint convention is ordinary geometry. It is
  not a new enclosure and does not promote \(q>10^{12040}\). The \(80000\)-bit
  scan is not rerun.

## Lean-checked finite identities

On the Finsupp presentation of `FactorialChannelCertificate.lean`,
`ErdosProblems.Erdos68.DivisorChannelBasis` checks:

- \(T_n=n e_{n-1}-e_n\), \(M(T_n)=0\), and
  \(V_d(T_n)=(d!-1)W_{d,n}1_{d\mid n}\) for \(n,d\ge2\).
- Recursion \(U_n=T_n-\sum_{d\mid n,\,2\le d<n}W_{d,n}U_d\),
  \(M(U_n)=0\), \(V_d(U_n)=(d!-1)1_{d=n}\).
- Odd \(n\ge2\) have vanishing index-\(1\) coordinate of \(U_n\).
- For support \(n\ge2\), \(12\mid M-2V_2\). If channels \(2,\ldots,D\) vanish
  and \(D\ge2\), then \(12L_D\mid M\).
- Sharpness examples: \(-6e_2+e_4\) has moment \(12=12L_2\);
  \(-6e_2-8e_3+5e_4\) has moment \(60=12L_3\).

Focused target `ErdosProblems.Erdos68.DivisorChannelBasis` exited 0.

## Ordinary (not this-wave Lean)

- Unique expansion of every finite integer vector in the \(e_1,U_n\) basis,
  and composite translators such as \(U_9\).
- Canonical auxiliary kernel \(K_D=L_De_1-\sum_{d=2}^D\frac{L_D}{d!-1}U_d\),
  primitivity, and unique expansion of low-channel kernels.
- Attainable-moment ideal \(L_D\cdot g_D/\gcd(g_D,a_D)\,\mathbb Z\) on
  support \(n\ge2\). The unrestricted generator is now finitely
  determined by the r5 stopping test \(\Lambda_n\mid u_n\) and
  \(g_{D,N}\mid\Lambda_{N+1}\) (`TailIdealCertificate.md`); scans
  through upper support \(40\) are no longer the evidence boundary.
- Analytic identity \(\sum_{n\ge2}u_n x^n/(n!-x^n)=x^2\) for \(|x|<\sqrt2\),
  with \(u_n=[e_1]U_n\).
- Sharp minimal upper support \(N_{\min}(D)=D+1\) (\(D\) odd) or \(D+2\)
  (\(D\) even), beyond the \(D=2,3\) witnesses above.
- Residual transparency \(\mathcal R(U_n)=1\), \(\mathcal R(K_D)=L_D(S-H_D)\).
- Closed-versus-open continued-fraction endpoint convention. Live numerical
  lead unchanged.
- Compressed primitive channel kernel (r3 leftover): remains ordinary plus
  `--quick` PASS; no Lean statement this wave.

The five cofinal arithmetic producers are not claimed proved.
