<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis: research on eight open Erdős problems

![Eight open problems: papers, checked results, failed routes, and open questions another researcher can continue](.github/system-map.png)

This repository contains short papers, full reasoning records, computations,
and Lean proofs developed while working on Erdős problems 68, 243, 249, 251,
257, 269, 1041, and 1049. **All eight problems remain open.** Each paper says
what has been established, which parts have been checked in Lean, and the exact
question where the argument stops.

A finished theorem records one successful route. This project also keeps the
routes that stopped: what was tried, why it failed, and what another researcher
could try next. The papers are written for mathematicians; the formal source
preserves a checked floor for the statements it covers. The aim is to let
people and later models continue from a shared record instead of repeating the
same search. Mathematical meaning, novelty, significance, and the next useful
idea still require human judgement.

Plectis is an independent, AI-assisted prototype built and directed by Will
Cook. Models helped draft prose, proofs, and software; Cook reviewed the claims
and sources and is responsible for the release. The corpus is still being
formalised and has not received independent mathematical review.

Choose one way in:

- **Read:** [open the mathematics site](https://wcook04.github.io/plectis/maths/)
  or use [A reader's way in](HUMAN_ENTRY.md).
- **Continue:** choose a bounded question in the
  [eight-frontier issue](https://github.com/wcook04/plectis-erdos/issues/105)
  and follow [CONTRIBUTING](CONTRIBUTING.md).
- **Check:** use [REPRODUCIBILITY](docs/REPRODUCIBILITY.md) to inspect one
  claim, build one Lean module, or replay the release.

## Problem papers

For a first look, start with **#257** for restricted irrationality and
achievement sets, or **#249** for exact reductions, finite certificates, and
recorded failed routes.

| Problem | Topic | Short paper | Full reasoning record |
|---|---|---|---|
| **#68** | Factorial-denominator irrationality | [paper](erdos-68-factorial-denominator-irrationality.pdf) | [record](erdos68-factorial-reasoning-surface.pdf) |
| **#243** | Reciprocal-tail rigidity | [paper](erdos-243-reciprocal-tail-rigidity.pdf) | [record](erdos243-reciprocal-tail-reasoning-surface.pdf) |
| **#249** | Binary totient series | [paper](erdos-249-binary-totient-series.pdf) | [record](erdos249-totient-reasoning-surface.pdf) |
| **#251** | Prime-gap dyadic series | [paper](erdos-251-prime-gap-dyadic-series.pdf) | [record](erdos251-prime-gap-reasoning-surface.pdf) |
| **#257** | Mersenne-support subseries | [paper](erdos-257-mersenne-support-subseries.pdf) | [record](erdos257-mersenne-reasoning-surface.pdf) |
| **#269** | Three-prime running LCM | [paper](erdos-269-three-prime-running-lcm.pdf) | [record](erdos269-running-lcm-reasoning-surface.pdf) |
| **#1041** | Lemniscates and Newton flow | [paper](erdos-1041-lemniscate-newton-flow.pdf) | [record](erdos1041-lemniscate-reasoning-surface.pdf) |
| **#1049** | Rational-base Lambert series | [paper](erdos-1049-rational-base-lambert.pdf) | [record](erdos1049-rational-base-lambert-reasoning-surface.pdf) |

The #269 record includes an earlier two-prime argument due to Steve Fan. It is
not claimed here as a new result or a Lean theorem. The
[joint #249/#257 manuscript](erdos249-257-main-paper.pdf) is retained for
archive and provenance; the individual papers above are the current entrances.

## What the checks establish

Comparator checks nineteen proof-bearing modules against separately declared
statements and a fixed axiom budget. [`formalization.yaml`](formalization.yaml)
records the source, boundary, `sorry` count, and axioms for each selected
result. [`docs/claims.json`](docs/claims.json) owns claim status, and
[`docs/PALOMAR_RESULT_SHOWCASE.json`](docs/PALOMAR_RESULT_SHOWCASE.json) owns
reader-priority ranking. [RESULTS](docs/RESULTS.md) gives the strongest checked
result for each problem, while [prior art](docs/PRIOR_ART.md) records earlier
and subsuming work.

The [verification dossier](docs/EXTERNAL_VERIFICATION.md) covers all eight
problem programmes. The [methodology](METHODOLOGY.md) explains what each
check establishes.

These checks establish only their stated formal and computational scope. They
do not decide whether a formal statement captures the intended problem,
whether a result is new, whether the exposition is clear, or whether an open
problem has been solved.

## Contribute

A useful contribution can be a new idea, a correction, a counterexample, a
failed route with a checkable reason, clearer exposition, or a repaired check.
You can open the
[plain-language research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml)
without preparing a patch, or open a pull request for a focused change.

Accepted work receives a public receipt identifying the contributor, the exact
files or results, the starting commit, what was checked, and what remains
limited. Corrections preserve earlier lineage. The
[open-source mathematics paper](open-source-mathematics-strategy.pdf) explains
the design; the [credit policy](docs/research-commons/CREDIT_POLICY.md) gives
the exact boundary. This mechanism is a prototype until an outside
contribution has completed the public path.

## Read or verify locally

You do not need to clone the repository to read the papers. For one local claim
inspection, use the current checkout and the tracked verifier:

```bash
git clone --depth=1 --filter=blob:none --single-branch https://github.com/wcook04/plectis-erdos.git
cd plectis-erdos
python3 scripts/verify_claims.py --claim eb_full_support
```

For the reader-only sparse checkout, the 43-module quick proof checkout, a
focused Lean build, or full-history release validation, follow
[REPRODUCIBILITY](docs/REPRODUCIBILITY.md). The Lean route needs `elan`; the
runbook links the setup guide before its first build command. Cloning runs no
project code and the repository defines no submodules, Git LFS filters, or
hooks. [SECURITY](SECURITY.md) documents the execution boundary.

To give an agent one bounded continuation, use the
[frontier relay](docs/FRONTIER_RELAY.md). Agents working inside the repository
start with [AGENTS.override.md](AGENTS.override.md); the
[agent workbench](docs/AGENT_WORKBENCH.md) holds the detailed navigation and
build contract. The [agent-navigation paper](cold-clone-to-proof-receipt.pdf)
explains that design.

## Citation and licence

The citation anchor is release `v0.9.0`; [CITATION.cff](CITATION.cff) carries
the metadata. The project uses Apache-2.0, with the separately identified prior
work and MIT-0 wrapper recorded in [REUSE.toml](REUSE.toml) and the
[licence texts](LICENSES/Apache-2.0.txt). See [CONTRIBUTING](CONTRIBUTING.md) for corrections and
the contribution boundary.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

The layer a mathematician should judge is small: 140 curated claim records in 30 contribution families, reaching Lean source through 449 principal declaration links. `SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem.

The rest is engineering inventory. About 92% of the 155,274 declarations (142,668 across 695 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,214 |
| Formal results and supporting lemmas | 152,720 |
| Curated claim records | 140 |
| Contribution families | 30 |

Generated shards are counted as formal source and never as separate
mathematical claims. Claim records span every status, including cited and
open, and are partitioned exactly once.
These are navigation counts, not novelty claims.
<!-- END generated_corpus_at_a_glance -->

<!-- BEGIN generated_principal_declaration_anchors -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Following a result into Lean

The paper links each headline result to the relevant source. For a particular
topic, start with the [source map](docs/SOURCE_MAP.md); it gives the module
order without asking you to decode Lean declaration names first.
<!-- END generated_principal_declaration_anchors -->

## Architecture and provenance

[ARCHITECTURE](ARCHITECTURE.md) explains the public validation system and links
to the system map. [SCOPE](SCOPE.md) defines what belongs to the mathematical
corpus. The broader [Plectis site](https://wcook04.github.io/plectis/) and
[public tools repository](https://github.com/wcook04/plectis) describe the
surrounding research system; neither is needed to read or continue the papers.

An agent arriving cold starts at [`AGENTS.override.md`](AGENTS.override.md).
[The Agent Workbench](docs/AGENT_WORKBENCH.md) keeps machine routing and kernel
probes out of the human reading path.

[Where I actually am](HUMAN_ENTRY.md#where-i-actually-am) gives the author's
account of why the work is being released at this stage and how to get in
touch.
