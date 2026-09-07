# Long-record transfers and corrections

Local r5 archive (not an R-checkout mutation). Label-keyed destinations
against the previous published assembly. Replaced short-note blocks live in
`removed_to_long_record.tex`; applyable fragments are in `fragments/`.
Do not paste a second complete short paper into the record.

The supplied long record is a previous published assembly. The current short note, disposition and attached Lean modules have precedence for claim status. Locations below refer to the authored parts supplied in `12_long_record_authored_parts.zip`, under `reasoning-parts/erdos249/`. Keep those authored parts as the edit surface and regenerate the aggregate later. Do not paste a second complete short paper into the record.

## 1. Basis, integral coordinates and the simpler signature proof

**Destination:** `a249_p4.tex`, section `sec:mahler-defect`, immediately following the existing finite-level kernel discussion. The long front matter's `a249_front.tex`, proposition `prop:rank`, should point to that location.

Use `note_edits/fragments/basis_before_theorem.tex`, the unchanged `kept_all_base_theorem.tex`, and `basis_after_theorem.tex` as the mathematical replacement. If the long record already defines the section notation, retain those definitions and start at the theorem. Preserve its historic comparison with Coons, and cite Martin for the stronger affine-ordering antecedent.

Append the ordinary progression-freezing and Boolean-inverse proof from research labels `lem:freeze`, `eq:tensor`, and `thm:signature` as a separate subsection. The previous mixed-content signature classification remains an ordinary theorem until the finite regrouping/CRT/cube interfaces are compiled. Its upper bound and content identities are already in `AffineTotientSignature.lean`; they should not acquire a second provenance entry.

Keep the counterexample to ambient integral saturation directly after `prop:integral`: `phi(4n+3)/2` is integer-valued but outside the generated integral module. Record eventual independence as deletion-of-prefix robustness, not as a claim about sequence-space saturation.

## 2. Bounded-residue irrationality and classification

**Destination:** `a249_front.tex`, theorem **`thm:residueobservable`**. This is the exact existing label, with no hyphen. The surrounding proof is the place for the complete signed pulse and residue-isolation argument in `fragments/residues.tex`.

The elementary dyadic converse is `3 f(1)/4 + c/4` when f is constant with value c on even classes. Do not attach recurrence of every even residue to that direction. Preserve the independent, more substantial recurrence/isolation arguments used in the forward direction or in the ordinary all-modulus classification.

The old family-by-family status narrative moves to `a249_family_catalogue.tex`. It should reference the current attached residue modules. Do not reintroduce the older private/unpublished-source descriptions near the end of `a249_front.tex`.

## 3. The exact full-depth and canonical endpoint proofs

**Destination:** `a249_p1b.tex`, propositions `prop:TE-04` and `prop:TE-05`, and then `prop:TE-06`. Insert or replace their explanation with the complete proof in `fragments/tails.tex`, using the record's existing notation where equivalent.

This receives the source catalogue entries carrying labels `res:supply`, `res:equivalences`, `res:open`, `res:slackcriterion`, `res:actualsign`, `res:squarecrt`, `res:squareenclosure`, and `res:actualorbit`. The common endpoint is the canonical central residue gap for every basepoint c and odd denominator v. Distinguish this equivalence from the stronger first-harmonic and prime-tail sufficient criteria.

Keep `res:weight` with the checked weighted-tail reduction preceding these propositions. Preserve its convergence and coefficient hypotheses. Retain the nonintegral phase/certificate definitions from the former introduction only once.

The recurrence for `rho_(H,N,M)` in the new tail fragment is an exact search interface. It does not manufacture the quantified central gap.

## 4. Carry rank and falsifying controls

**Destination:** `a249_p1b.tex`, proposition `prop:D5cons`; cross-reference `a249_front.tex`, `prop:period-not-rank`. Replace the obsolete invitation to construct a rational high-carry-rank control with the existing `ParityPerturbedRationalControl` result.

This receives removed labels `res:carryrank`, `res:periodic` and `prob:carryrank`. Keep the distinction between the proved all-level carry lower bound `2^e-1` and the finite measurements of full coefficient evaluation ranks. Do not write that the rational control has exactly the same full kernel rank as phi at every depth.

The larger density-one and congruence controls are separate families in `EightReturnObstructionsAndPrefixValuation.md`. Do not amalgamate their hypotheses. Place the rigidity statements from `PrefixValuationAndControlRigidity.lean` beside them: an exact dilation law plus a sufficiently small defect can force equality with phi, so one cannot preserve all proposed properties in a distinct control.

## 5. Möbius-Mersenne, Hankel and rational-closure obstructions

**Destination:** `a249_p2.tex`, subsection `ssec:lambert` and proposition `prop:lambertengine`, for the identity labelled `eq:lambert`; `a249_p1b.tex`, proposition `prop:D7-inv`, for the power ladder. The sum-of-Möbius-squares identity also belongs beside `a249_p2.tex`, `ssec:mobius`, `prop:mobsq`.

Move removed label `res:gcdmoment` to the existing gcd layer `a249_p2.tex`, `prop:gcdlayer`, with its own hypotheses. Move the signed Hankel question `prob:hankel` to the ladder discussion, but update its premise: rank-uniform nonvanishing for `s >= 2` is already established in the current ordinary corpus. Its remaining obstruction is reduced denominator height relative to nonzero approximation error.

Append the new research theorem `thm:dilation` immediately after the definition of the auxiliary-numerator ladder, clearly outside checked Lean claims. State the variable: b is fixed, and dilation means `z -> b z`, not `z -> z^b`. The rational Möbius first-power control and the bounded-rational-weight counterexample must remain adjacent to the theorem.

The sharp positive rank-one theorem has its existing home in `a249_front.tex`, **`thm:rankonefloor`**. The long front matter states it and links its Lean proof; do not claim that this location contains a full ordinary proof when it does not. The r3 positive-coefficient polynomial extension is an ordinary result in the current packet and should be referenced separately from positive averaging after quotients are formed.

## 6. Denominator records and actual prime support

**Destinations:** `a249_p2.tex`, `ssec:farey`, `lem:farey`, `prop:gapwindow`, `thm:denom-record`, and `ssec:certtable`; also `a249_front.tex`, `thm:cfdenom`.

This receives source labels `res:denominator` and `sec:denominator`. Keep the exact continued-fraction comparisons `q >= 2^39989` and `q > 10^12038` as separate bounds and preserve the distinction between that computational receipt and the smaller Lean-checked Farey exclusion. Those values are already correct in the live short note.

The fresh-prime blocks (`res:index`, `res:freshprimedeficit`, `res:primindex`, `res:factorideal`, `res:foreignresidue`, `sec:fresh-prime`, `prob:cyclotomic`, `prob:diagonal`) belong after `a249_p1b.tex`, `prop:CP-06` and `prop:CP-07`, with the compatibility counterexample beside **`prop:CP-03-kill`**. The latter is the existing warning that primitive Mersenne prime support alone does not contradict a rational carry orbit. Preserve that dependency boundary for any resultant generalisation.

The r4 cyclic-resultant theorem, its bad-characteristic counterexample and its growth hypotheses remain ordinary results. The new work here does not re-prove or promote them.

## 7. First harmonics, prime sampling and the canonical search

**Destination:** `a249_p1b.tex`, `prop:AR-04-inv` through `prop:AR-06-inv`, with the actual-orbit reductions next to the corresponding `TE` propositions. This receives the removed `sec:conditional-criteria` and `prob:firstharmonic` blocks.

Retain the exact sufficient prime-tail real-part bound for the totient value. Place the existing binary-normal, dimension-one prime-locking construction in the same subsection as a counterexample to inference from global normality. It is not a counterexample for the actual value S.

The old `res:actualorbit` entry should point here only for its analytic sufficient conditions; the full-depth equivalence itself belongs in destination 3. Use cross-references rather than repeat the statement with different quantifiers.

## 8. Catalogue and archival integrity

`note_edits/transferred_source_blocks.tex` contains every replaced source block verbatim, including all 27 labels removed from the focused core. The old `R1`–`R24` inventory goes after the mathematical summary in `a249_front.tex` or into `a249_family_catalogue.tex`, with the route-specific proof destinations above. Existing labels already defined in the long record must be cross-referenced, not defined a second time.

The two discarded front-matter panels and the historical editor instructions are archival prose, not material to reproduce in the published long record. The full original bibliography is retained in the archive so that route-specific citations travel with their claims.

The proposed divisor-function rank theorem belongs in a new research subsection immediately after the all-base kernel discussion in `sec:mahler-defect`, or in a separate companion paper. It has not earned a replacement of the existing totient flagship. Its local translation mechanism is relevant to that subsection; its complete proof is in research label `thm:divisor-rank`.
