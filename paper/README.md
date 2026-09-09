<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Papers

For the repository layout, sources of truth, build path, and release
infrastructure, start with the plain-language
[`ARCHITECTURE.md`](../ARCHITECTURE.md) at the repository root.

Each of the eight covered Erdős problems has a short first-read paper and a
longer complete reasoning record. All eight problems remain open. The papers
report partial results, failed or equivalent routes, finite evidence, and the
exact obligations that survive.

These papers are mathematical exposition. Some results are checked in Lean;
others are ordinary mathematical arguments or applications of cited external
theorems. Each paper states the boundary for its own claims. Lean files are
proof authority only for the exact declarations they check, and
[`docs/claims.json`](../docs/claims.json) records the selected public claim
interfaces.

The manuscript layer (the `.tex` sources and rendered PDFs) is licensed
CC-BY-4.0; see [`REUSE.toml`](../REUSE.toml) at the repository root.

## Problem papers

| Problem | Short paper | Complete reasoning record |
|---|---|---|
| #68 | [Two Incomparable Denominator Exclusions for ∑ₙ≥₂ 1/(n!−1)](../erdos-68-factorial-denominator-irrationality.pdf) ([source](erdos-68-factorial-denominator-irrationality.tex)) | [The Factorial-Denominator Series: Complete Reasoning Record](../erdos68-factorial-reasoning-surface.pdf) ([source](erdos68-factorial-reasoning-surface.tex)) |
| #243 | [Excluding the Bounded Negative Part](../erdos-243-reciprocal-tail-rigidity.pdf) ([source](erdos-243-reciprocal-tail-rigidity.tex)) | [Reciprocal-Tail Rigidity: Complete Reasoning Record](../erdos243-reciprocal-tail-reasoning-surface.pdf) ([source](erdos243-reciprocal-tail-reasoning-surface.tex)) |
| #249 | [A Basis for the 2-Kernel of Euler's Totient](../erdos-249-binary-totient-series.pdf) ([source](erdos-249-binary-totient-series.tex)) | [The Binary Totient Series](../erdos249-totient-reasoning-surface.pdf) ([source](erdos249-totient-reasoning-surface.tex)) |
| #251 | [A Countermodel for Growth-and-Parity Arguments on the Prime-Gap Dyadic Series](../erdos-251-prime-gap-dyadic-series.pdf) ([source](erdos-251-prime-gap-dyadic-series.tex)) | [Prime Gaps and Dyadic Tails: Complete Reasoning Record](../erdos251-prime-gap-reasoning-surface.pdf) ([source](erdos251-prime-gap-reasoning-surface.tex)) |
| #257 | [Reciprocal-Summable Support Irrationality at Every Integer Base](../erdos-257-mersenne-support-subseries.pdf) ([source](erdos-257-mersenne-support-subseries.tex)) | [Reciprocal Mersenne Subseries](../erdos257-mersenne-reasoning-surface.pdf) ([source](erdos257-mersenne-reasoning-surface.tex)) |
| #269 | [No Finite Separable Representation at Three Prime Generators](../erdos-269-three-prime-running-lcm.pdf) ([source](erdos-269-three-prime-running-lcm.tex)) | [The Three-Prime Running LCM: Complete Reasoning Record](../erdos269-running-lcm-reasoning-surface.pdf) ([source](erdos269-running-lcm-reasoning-surface.tex)) |
| #1041 | [Sharp Solved Families and Constant-Factor Paths in Polynomial Lemniscates](../erdos-1041-lemniscate-newton-flow.pdf) ([source](erdos-1041-lemniscate-newton-flow.tex)) | [Lemniscates and Newton Flow: Complete Reasoning Record](../erdos1041-lemniscate-reasoning-surface.pdf) ([source](erdos1041-lemniscate-reasoning-surface.tex)) |
| #1049 | [Irrationality of F(31/4) and the Exact Normalized Hankel Order](../erdos-1049-rational-base-lambert.pdf) ([source](erdos-1049-rational-base-lambert.tex)) | [Rational-Base Lambert Series: Complete Reasoning Record](../erdos1049-rational-base-lambert-reasoning-surface.pdf) ([source](erdos1049-rational-base-lambert-reasoning-surface.tex)) |

The short paper is the first read. The complete reasoning record preserves the
wider working context, including routes that failed, finite experiments, and
open obligations. The older joint #249/#257 paper is retained for provenance;
it is not the entry point for either problem.

### Returning from a problem note to checked evidence

The notes are exposition, not proof authority.  To return from any note to the
machine-owned problem record, run the matching route below.  Each problem route
returns its exact paper/source record, checked module inventory, and open
obligation handles; the [complete eight-problem source map](../docs/SOURCE_MAP.md#complete-eight-problem-return-matrix)
keeps the same joins readable.  For a source-fingerprinted continuation packet,
use the route-memory command in the last column.

| Problem | Public problem route | Resumable route-memory handoff |
|---|---|---|
| #68 | `python3 scripts/query_corpus.py --route erdos_68` | `python3 scripts/query_route_memory.py --problem 68` |
| #243 | `python3 scripts/query_corpus.py --route erdos_243` | `python3 scripts/query_route_memory.py --problem 243` |
| #249 | `python3 scripts/query_corpus.py --route erdos_249` | `python3 scripts/query_route_memory.py --problem 249` |
| #251 | `python3 scripts/query_corpus.py --route erdos_251` | `python3 scripts/query_route_memory.py --problem 251` |
| #257 | `python3 scripts/query_corpus.py --route erdos_257` | `python3 scripts/query_route_memory.py --problem 257` |
| #269 | `python3 scripts/query_corpus.py --route erdos_269` | `python3 scripts/query_route_memory.py --problem 269` |
| #1041 | `python3 scripts/query_corpus.py --route erdos_1041` | `python3 scripts/query_route_memory.py --problem 1041` |
| #1049 | `python3 scripts/query_corpus.py --route erdos_1049` | `python3 scripts/query_route_memory.py --problem 1049` |

## What the two paper forms do

The eight short papers are the reader entry points. The eight complete
reasoning records preserve the wider working context and are neither proof
authority nor substitutes for the shorter papers.

Lean files are proof authority only for the exact declarations they check;
[`docs/claims.json`](../docs/claims.json) records selected public claim
interfaces. Kernel checking a root module does not promote every declaration
into a reviewed public claim. The papers also contain ordinary mathematical
reasoning and explicitly attributed external results, with their verification
limits stated locally.

The notes share `problem-note-preamble.tex`, which fixes the house macros and
the one pinned source revision every link resolves against. Links are validated
against that pinned commit rather than the working tree, so a note cannot decay
when a later wave moves declarations:

```sh
python3 ../scripts/check_problem_note_sources.py --coverage
```

Pinning buys safety at a price: a note whose links can never break can instead
fall silently behind. `--coverage` is the meter for that. It reports, per
problem, the fraction of the declarations that exist **now** which the note
actually links, and whether the modules have changed since the pin, and it
fails below `note_coverage_floor` in `docs/problem_index_source.json`. Drift is
therefore a failing check with a worklist attached, not something a reader
discovers.

When a note falls through the floor: rewrite it against the current source,
repin `\commit` in the shared preamble to a commit that is **pushed** (links
resolve on GitHub, so an unpushed local merge is not a valid pin), rebuild, and
refresh the digests in `docs/publication_contract.json`.

That last step has a command; it is not a hand edit. `python3
scripts/check_publication_contract.py --restamp` prints every digest that no
longer describes the file it names, and `--restamp --apply` writes them. It
touches nothing but those digest strings, so the title, claim scope, and
authority posture of a row stay where a human put them — read `git diff` on the
source first and confirm the revision is one you meant to publish, because the
command recomputes bytes, it does not review mathematics. It refuses any row
whose `.tex` moved while its `.pdf` did not: that pair means the published PDF
was never rebuilt from the source beside it, and stamping the new source would
record a manuscript the released artifact does not print. Rebuild the PDF and
restamp the pair together.

`docs/problems.json`, built by `scripts/build_problem_index.py`, is the
machine-readable index over the same material: one row per problem naming its
modules, its note, what is checked, what is not, and the obligation that
survives.

To add a note, write the `.tex`, add its stem to `PAPERS` and `NOTES` in the
`Makefile`, register it once in `docs/publication_contract.json` with class
`problem_note`, add its rendered PDF to the CC-BY override in `REUSE.toml`, add
its row to `publication_architecture.problem_series` in `docs/claims.json`, and
add its problem to `docs/problem_index_source.json`. The contract checker fails
if any of those five are missing.

## Systems and historical papers

| Role | Paper |
|---|---|
| Publication architecture | [Problem-Sized Lean Worlds](../claim-faithful-publication-systems-paper.pdf) ([source](claim-faithful-publication-systems-paper.tex)) |
| Agent navigation and validation | [From a Cold Clone to a Proof Receipt](../cold-clone-to-proof-receipt.pdf) ([source](cold-clone-to-proof-receipt.tex)) |
| Open participation and credit | [From Spare Compute to Cumulative Mathematics](../open-source-mathematics-strategy.pdf) ([source](open-source-mathematics-strategy.tex)) |
| Retired joint #249/#257 record | [Tail Certificates and Achievement-Set Geometry for Erdős Problems 249 and 257](../erdos249-257-main-paper.pdf) ([source](erdos249-257-main-paper.tex)) |

The three systems papers explain the repository architecture, cold-clone path,
and contribution model. They make no claim of a solved endpoint, peer review,
community acceptance, or measured improvement in mathematical discovery. The
joint #249/#257 record remains available for provenance, while the individual
problem papers above are the maintained reader routes.

## Build

```sh
# with tectonic (recommended; fetches TeX packages on first run)
tectonic erdos249-257-main-paper.tex

# or with a TeX Live install
pdflatex erdos249-257-main-paper.tex && pdflatex erdos249-257-main-paper.tex

# or
make
```

The outputs include all 20 native manuscripts registered in
[`docs/publication_contract.json`](../docs/publication_contract.json): eight
short papers, eight complete reasoning records, the retired joint paper, and
three repository-level papers. `make` currently synchronises every rendered
PDF to the repository root; the publication contract and public links presently
depend on that location.

## Contents

The bullets below index the archived joint record for historical navigation;
the canonical reader route is the individual problem note for the question at
hand. The systems paper is outlined by its description above.

- The Mersenne–Lambert ladder that places both constants on one line.
- The [composite-dilation defect](../Erdos249257/CompositeDilationDefect.lean):
  an exact foreign-divisor correction, zero on prime support, with no arbitrary-
  support tail bound or irrationality conclusion.
- Erdős–Borwein-type irrationality (the #257 direction): full support at every base, plus named infinite-support cases.
- The totient constant `S` (Erdős #249): the unconditional denominator bound, the coprimality reading, and the exact reduction to finite certificates.
- Formalisation architecture and mathematical lessons: how infinite questions are separated from finite kernel-checkable witnesses.
- The formalisation method: how checked statements, finite computations, exact reductions, and the unresolved steps in Erdős #249 and #257 are kept distinct.
- Artefact availability, verification, and a conclusion stating the exact open boundaries once.
- Auxiliary binary-carry criteria and the compact declaration map in appendices.
- The sublogarithmic zero-window theorem for divisor coverage forced by a hypothetical rational support value.
