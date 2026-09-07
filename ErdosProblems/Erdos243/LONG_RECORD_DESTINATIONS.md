# Erdős #243 — r5 long-record destinations (by label)

This is a destination and repair map, not a modified frozen `02_long_record.tex`.
The r4/r5 packet checkouts were not mutated. There is no live companion `.tex`
under `ErdosProblems/papers/` besides the short note; appendix bodies remain
in `erdos-243-reciprocal-tail-rigidity.tex` after the r5 labelled edits.

## Short-note anchors after the r5 surgical edits

| Label | Present in live short note | Destination in a later short/long split |
|---|---|---|
| `res:bounded`, `sec:bounded` | yes | keep |
| `res:originalbounded` | yes (page one) | keep |
| `sec:state`, `sec:defect`, `sec:barrier` | yes | keep required lemmas |
| `sec:mass` | yes | keep; not an incomparable endpoint class |
| `sec:lcmrecords` | yes | keep main theorem; do not enumerate every weight |
| `sec:constant`, `sec:periodic` | yes, now appendices | companion; retain references |
| `app:feedback` | yes, appendix | companion feedback section |
| `sec:records` | yes, appendix | companion catalogue; keep a short log-log link |
| `res:cubicrate` | yes | compact secondary; companion proof must carry L1/L2 |
| `app:antecedents` | yes, appendix | companion; keep Bado as comparison only |
| `app:index` | yes | repository/companion after mathematics |
| `app:residue` | yes | long record with script scope |
| `sec:open` | yes | keep `∃B: liminf F_B(X)/X=0`; migrate side branches |

Ordinary log-log / record criteria already live in `SlowNegativePartRigidity.md`
and `LcmRecordExcess.md`. They are not new r5 progress.

## Companion repairs, keyed by assembly label

Do not treat the older `02_long_record.tex` (packet tree, not this directory)
as source-current. When that assembly is next edited, apply these by label:

| Label | Repair |
|---|---|
| `res:cubicexclusion` | exceptional lower density positive per fixed rational profile; do not replace density zero by a uniform 1/28 |
| `res:modseven`, `sec:modseven` | plus word at starts 0 mod 7; minus word at starts 1 mod 7; 1/7 is those phases only. Cite `CubicNeighbourIdentity.lean` ring identities and empty `F_7` transport |
| `eq:shiftedsign` | γ = −θ + Λ; trichotomy θ < Λ, = Λ, > Λ. The old blanket sign implication is false |
| `res:recordamplified`, global clause after `res:epochenergy` | keep local inequalities; demote global iff without an epoch producer and overlap control |
| integer covering windows | integer endpoints and integer length; rounding is a hypothesis |
| quadratic negative-norm continuation | do not transfer integral-k sign argument verbatim; at k=1/2 both displayed norms are positive |
| variable-rise / barrier extension | `∀ω ∃family ∃walk`; family depends on ω. Occupied ordinary theorem: `VariableRiseCounterexample.md` |

Preserve each strongest falsifying example next to the failed implication.

## Not a live long-record mutation this wave

No `02_long_record.tex` exists in the live papers tree. Appendix relocation
inside the short note is already done by the 50 labelled edits. Cutting those
appendices out into a new competing manuscript is a later typesetting assembly,
not this closeout.
