# Affine sections, divisor ranks, and dilation closure (ordinary candidate)

Type B r5 research memorandum
`AffineSectionsLocalFactorsDilationClosureCandidate.tex` (byte-identical to
the packet's `ordinary_proofs/r5_research.tex`).

**Lead.** The live short note still leads with the totient \(k\)-kernel
basis. Title and Theorem 1 were chosen from landed mathematics, not frozen:
compiled r5 Lean is helper algebra (periodic transport, Boolean inverse,
Mersenne coefficient identities). The \(\sigma/\tau\) rank formulae and the
analytic dilation-closure theorem remain ordinary. None of that moves the
paper's centre or decides \(S\). Integral coordinates and periodic freezing
are in the note as displayed corollaries of the existing basis.

**Specialization collision.** The proposed \(\sigma/\tau\) formula recovers
the already measured rank 41 at \((k,e)=(6,2)\)
(`all_base_multiplicative_kernel_rank_receipt.json`). That finite number is
not a new discovery. At \((6,3)\) the checker gives 230 versus 229. No
priority claim.

**Dilation.** Finite rational linear closure of \(F_{a,r}\) for bounded
integer weights is equivalent to eventual periodicity. Natural boundary does
not imply value irrationality: \(F_{\mu,1}(1)=1/b\). Coefficient identities
are Lean-checked; the series/natural-boundary theorem is not.

**Lean this wave.** Focused `lean_fast_build` on
`ErdosProblems.Erdos249.{MersenneDilationAlgebra,BooleanEulerInverse,PeriodicTotientIndependence}`
completed as `cf_8309991b61ac4c53b3e3` exit 0; oleans present. Completeness
of signature classification (\(\dim=\#\Sigma\)) remains residual. Not
imported from Root.lean. Palomar not touched.

**Evidence class.** Ordinary proofs plus exact finite checks
(`scripts/check_new_rank_formula.py`, `scripts/check_note_facts.py`), and
Lean-checked helper modules as named. Does not decide \(S\).
