<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Reading and working with the research

Choose a problem, read its short paper, then follow the argument into the
longer record or the supporting source. All eight original Erdős problems
remain open. You can contribute a correction, explanation, counterexample or
useful failed approach without solving one.

## Read

- [The papers](papers/README.md): the eight problems and their papers.
- [Results and open questions](RESULTS.md): the stated progress and its limits.
- [Prior work](PRIOR_ART.md): antecedents, attribution and comparisons.
- [Related problems](RELATED_PROBLEMS.md): connections across the collection.

The short papers explain the main ideas. The long records retain more detail,
attempts and unresolved steps. Each result's own evidence boundary matters:
an ordinary mathematical argument and a Lean-checked declaration are different
kinds of evidence.

## Check

Start with the [source map](SOURCE_MAP.md) to locate the evidence for a result.
[Reproducibility](REPRODUCIBILITY.md) gives the checkout and verification
commands. [External verification](EXTERNAL_VERIFICATION.md) explains the
selected Comparator interfaces and their limits.

The [claim record](claims.json) binds statements to their status and supporting
artifacts. [Methodology](../METHODOLOGY.md) explains the separate roles of Lean,
repository checks and mathematical review. A navigation page or a successful
repository check does not establish a stronger mathematical statement.

## Contribute

[Contributing](../CONTRIBUTING.md) explains how to send an observation or a
focused pull request. [Credit and stewardship](research-commons/CREDIT_POLICY.md)
explains how accepted work is attributed, including negative results and
corrections. The [research commons](research-commons/README.md) describes how
another researcher can resume and return a longer investigation.

For an AI-assisted session, use [the research-shift guide](FRONTIER_RELAY.md).
Coding agents start at [the agent entry](../AGENTS.override.md); the
[agent workbench](AGENT_WORKBENCH.md) documents the detailed tools.

## Where things live

| Location | Purpose |
|---|---|
| [`paper/`](../paper/README.md) | Manuscript sources and rendered PDFs. |
| [`docs/papers/`](papers/README.md) | Reading pages and indexes derived from the manuscripts. |
| [Source map](SOURCE_MAP.md) | Routes into the Lean libraries, grouped by mathematical problem. |
| [`docs/claims.json`](claims.json) | Authored public claims, evidence links and status. |
| [Corpus orientation](ORIENTATION.md) | Generated technical navigation after choosing a problem. |
| [Research commons](research-commons/README.md) | Contribution, review and attribution records. |

[How the repository works](../ARCHITECTURE.md) explains source ownership,
generated files and the release process. The research-system papers have a
separate role from the eight mathematical problem papers; find both through
[the paper catalogue](papers/README.md).

The [earlier joint #249/#257 manuscript](../erdos249-257-main-paper.pdf)
is retained as historical context. Start with the current individual problem
papers instead.
