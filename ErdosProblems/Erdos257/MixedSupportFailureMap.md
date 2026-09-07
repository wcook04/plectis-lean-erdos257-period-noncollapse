# What the failed routes determine

All locations below refer to the round-5 packet unless explicitly identified as a public sibling source. “New” denotes an ordinary result supplied in this return, not a Lean or historical-priority claim.

## 1. The structural map

| Proposed information | Exact surviving obstruction | Information that would cross this boundary | Location and disposition |
|---|---|---|---|
| Separate arbitrarily small positive returns for two hosts | Two positive sequences can have disjoint small-value sets; their sum can be everywhere greater than one. Separate limiting means also supply no rate when the modulus moves. | Small means for both tests under the **same finite probability measure**, uniformly over the chosen modulus. | **New:** `MixedSupportSynchronisation.md`, §§2–5 and §8. This closes the exact union question in `CoverFirstLogarithmicMoment.md`, §B.4, lines 141–144. |
| Finite-cost strengthened positive covers | Every cover costs at least the periodic first logarithmic moment of divisor incidence. The obstruction survives all alternative decompositions and auxiliary weights. | A different functional, or prime-power weighting that reduces the actual shifted atoms without paying the incidence cost. | Already landed: `CoverFirstLogarithmicMoment.md`, B.1–B.3. The new mixed theorem combines this branch with the weighted branch. |
| Small positive displacement as a universal irrationality criterion | The full prime support has displacement greater than 1/3 at every positive shift. Adding any composite exponents preserves that lower bound. | Phase cancellation, anti-concentration, or another arithmetic obstruction to a rational lattice. A better constant in a positive-return estimate cannot help. | **New:** research Proposition 7.1. The earlier full-support 1/2 barrier remains valid. Tao–Teräväinen Theorem 1.3 proves prime irrationality by an independent analytic mechanism. |
| Reciprocal divergence as a substitute for prime incidence structure | The exact localisation identity holds at an exponent a only when a is coprime to every other selected exponent. For the support 2P, shared-factor covariances contribute a quadratic reciprocal-mass term. | Exact localised dilation, admissible affine-cube supply, and a quantified comparison between off-diagonal errors and diagonal variance. | Already landed: `TaoTeravainenIncidenceBoundary.md`, §§2–3. Its opening now correctly records that fixed-dilation prime-power irrationality can still handle 2P by a modified argument. |
| Growth, integrality and irregularity of a carry sequence | An arbitrary coefficient stream may be chosen to telescope to a rational value. Coefficients must remain the divisor transform of a single Boolean selector. | The exact Möbius inverse condition, coupled to actual greedy selection or an arithmetic nonconcentration estimate. | Short note `res:bmc`; long `a257_front.tex`, `thm:bmc`. Sibling #251, `res:telescope`. **New companion example:** bounded positive rational coefficients on square exponents telescope when the common denominator hypothesis is removed. |
| Unbounded tails and small zero windows | Both hold for every infinite or nonempty support, respectively. They do not distinguish rational candidates. | Arithmetic alignment relative to a fixed denominator lattice or a concrete selector load. | Already landed: `ElementarySupportConstraints.md`; short `res:unbounded`, `res:sublog`. Surgical edits remove their redundant theorem-level prominence, rather than claiming a newly discovered correction. |
| Denominator periods or lower denominator bounds | In a rational-difference inequality, larger denominators weaken the lower bound on the difference. Surviving cyclotomic factors do not supply the needed upper height control. | Upper height bounds at selected ranks, sufficiently long actual gaps, or a direct selector-load estimate. | Already landed finite arithmetic: `SignedFinitePeriodNoncollapse.lean`, `FiniteDenominatorRealisation.md`. Short `res:period`; long `a257_p1a.tex`, `lem:denominator-survival` and `lem:denominator-sandwich`. |
| Geometry, dimension, or almost-sure irrationality | These do not classify a specified rational point of an achievement set. Unique coding also prevents freely averaging over many representations of the same target. | Actual-orbit recurrence or a uniform arithmetic obstruction on the coding image. | Short `res:geometry`, `res:supportvolume`; long `a257_front.tex`, `bar:canon`, `bar:measure`. Preserve geometry as geometry. |
| Long finite scans of a repair schedule | A prescribed multiplicative schedule can be disproved at infinitely many arithmetic inputs, while unrestricted cofinal repairs remain possible. | A cofinal estimate for the actual selector without the falsified schedule restriction. | `EightReturnSynthesis.md` and the original short-note deadline subsection, lines 572–618. Archive the certified fixed-multiplier failures and phase masks under the actual-target chapter. |

## 2. Two distinctions the short note should enforce

### Method failure versus value failure

A positive lower bound on a chosen displacement proves that this displacement cannot certify irrationality by small returns. It says nothing by itself about whether the series is rational. Prime support provides the decisive example: the new barrier and the external irrationality theorem both hold.

Similarly, the covariance calculation for 2P refutes a naive transfer of a particular independent-prime proof. It does not refute irrationality for 2P; the packet's analytic extension already covers that value. Never describe the example as an unresolved support solely because one transfer failed.

### A necessary condition versus an exact endpoint

The general repair equivalence is useful because it leaves the exact unresolved inequality in the same variables:

\[
Q_{N+1}-Q_N=Q_N+\beta_N-c_x(N+1).
\]

A cofinal inequality on this actual pair proves membership. Replacing c_x by an arbitrary pulse stream, or replacing the existence of repairs by a density prediction, changes the problem. The long record's route-collapse results should explain those changes at the point of use rather than repeatedly rebranding equivalent endpoints.

## 3. What really transfers to sibling problems

### Erdős #249: finite averaging and common witnesses

The public file `ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean`, at checkpoint `5e28e73cf70a0ccf3219bb7197401307fb6d3bfd`, lines 20–135, defines a dyadic block mean bound of 89/100 for the actual first-harmonic phase. It derives that bound from an 11/100 proportion of nonpositive real parts, and turns it into the finite 9/10 certificate after a uniform 1/100 truncation allowance.

The transfer from this return is the finite-budget assembly principle: choose one measure; bound each error under that measure; take a common witness. The returned Lean candidate isolates that step. The positive modular-atom estimate does not establish the totient phase-density premise. Totient's Möbius-weighted representation has cancellation and cannot be treated as a nonnegative cover merely by changing the coefficient names.

A meaningful next task in #249 would be to replace a qualitative tail approximation by a quantitative estimate uniform on the selected dyadic blocks, then combine it with a genuinely proved phase estimate. This return provides no new actual phase estimate and no #249 irrationality result.

### Erdős #251: keep the arithmetic lattice visible

The sibling short note's `res:telescope` records

\[
\sum_{n=0}^{N-1}\frac{2K_n-K_{n+1}}{2^{n+1}}
=K_0-\frac{K_N}{2^N}.
\]

This explains why arbitrary irregular forcing can coexist with rational sums. The new bounded-coefficient example on square exponents is another exact instance of the same failure principle: once coefficients may vary through rationals of unbounded denominator, they can cancel the selected denominators and telescope. A fixed rational alphabet restores the lattice in the positive-return proof.

This is a conceptual transfer, not a new theorem about the actual prime-gap sequence.

## 4. The strongest next questions

### 4.1. A countable gluing criterion with a tail budget

The new mixed class is an ideal under finite unions and finite changes. It cannot be closed under arbitrary countable unions: the prime singletons belong, while their union has a uniform positive displacement gap. Seek a quantitative condition on a sequence of weighted/cover hosts that controls the sum of their residual tests under a common moving-modulus schedule. Mere membership of every component in a good class is insufficient.

A useful theorem would give explicit summable tolerances and common schedule costs, with an example showing necessity of a tail condition. This would extend the finite gluing result without pretending that arbitrary unions preserve irrationality.

### 4.2. An intrinsic converse to the logarithmic obstruction

For a host A, define the finite-prefix obstruction

\[
\Lambda(A)=\sup_{F\subseteq A,\ F\text{ finite}}\mathbb E_F\Psi(f_F).
\]

Finite strengthened cover cost forces finite Lambda. Is there a natural extra structural condition under which finite Lambda produces a positive cover of comparable cost? The divisor-cube calculation gives a sharp model but does not prove this general converse. An optimal dual description would explain the method independently of hand-chosen decompositions.

Before proposing an unrestricted equivalence, examine finite families with overlapping prime factors whose fractional divisor transform is signed. The example F={2,3} already shows why a formal Möbius inversion need not yield nonnegative majorants.

### 4.3. Crossing the prime-core barrier

For the full prime component, common small-positive-return schedules are impossible. A hybrid involving prime-supported irrationality must therefore couple different arithmetic functionals, rather than force the prime displacement towards zero. The external theorem's weighted short-shift correlations suggest the relevant direction; an unproved assertion of independence is inadequate.

A useful intermediate target is a support whose incidence splits into a controlled positive part and a genuinely decorrelated phase part, with a nonvanishing variance or harmonic gap after all mixed errors are charged. No such general theorem is claimed here.

### 4.4. Classify the actual greedy support before applying support theorems

The new mixed theorem could exclude a rational target if its actual greedy support were proved to belong to the mixed class and to be infinite under membership. It does not prove that classification. Conversely, a proof of membership must supply actual repairs. Keep these opposing directions distinct: a stronger irrationality class is not automatically a stronger construction of a rational point.
