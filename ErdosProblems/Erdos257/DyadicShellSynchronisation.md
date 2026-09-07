# Formalisation boundary and landing order

`DyadicShellSynchronisation.lean` is an **uncompiled candidate**, targeting the packet's Lean/Mathlib v4.29.1. A usable compiler and its Mathlib build were not available in this run. The file contains three finite proof scripts and no admitted propositions; this is a source inspection, not a kernel receipt. No claim that it compiles is made.

The three declarations are deliberately narrower than the ordinary research theorem:

- `exists_common_sample_of_weighted_sum_lt_one`: a finite probability argument extracting one sample satisfying both nonnegative error budgets.
- `finite_average_le_of_two_error_budgets`: the algebraic averaging step, with the near and transition budgets explicitly assumed.
- `transition_index_unique`: uniqueness of the transition regime for a sequence with a stated doubling property.

They do **not** prove the near/far estimates, the countable-majorant interchange, the weighted parameter schedule, or the mixed-support irrationality theorem. In particular, compiling these finite interfaces would not register the headline result.

## Analytic declarations still needed

1. Define `modularAtom B d n = B^(n % d)/(B^d-1)` for B>1 and positive d, and the finite two-scale mean.
2. Prove the complete residue-cycle identity, including gcd and period length. Reuse the existing atom-orbit modules rather than reconstructing the mathematics inside a certificate.
3. Prove the far no-wrap bound by pairing terms of the geometric sum, avoiding fractional powers if convenient.
4. Prove the transition no-wrap geometric-sum bound. This is a finite convexity inequality, not an asymptotic statement.
5. Sum the reciprocal dyadic errors and instantiate the finite gluing lemma. This yields research Theorem 2.1 with all B,L,d,R,M quantifiers visible.
6. Transport through nonnegative countable sums, first with fixed B and then with B_j=2^alpha_j. An ENNReal intermediate can make the interchange clean; the finite right-hand budget supplies finiteness.
7. Reuse the weighted support proof with an arbitrary additional prefix modulus. Record the full finite error estimate, not only eventual existence of one return.
8. Apply both estimates to the same finite measure. Extract the common sample and invoke the existing all-base rational-lattice consumer.

The highest-leverage declaration is step 5. A standalone proof of it would be useful beyond this particular union theorem. Step 8 is short after the quantitative interfaces exist.

## Mathematical statement to register after completion

If E has finite finite-prime weighted mass and V has a strengthened positive fractional divisor cover, then every infinite A contained in E union V has an irrational Mersenne subseries at every integer base at least two. Infinitude, positivity, finite P, the cover summability, and the common parameter schedule must remain visible. No statement that universal Erdős #257 is solved follows.
