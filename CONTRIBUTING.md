<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Contributing

This repository is public so that other people can clone it, do useful work,
and send that work back. A contribution does not have to solve an Erdős
problem. A corrected proof step, a counterexample, a failed route with a reason
another person can check, a clearer boundary, or a repaired public check can
all save future work.

If you want to help but do not yet have a target, begin with the pinned
[eight-frontier issue](https://github.com/wcook04/plectis-erdos/issues/105).
It links each problem paper and lists useful contributions beyond complete
proofs.

Participation is governed by the [code of conduct](CODE_OF_CONDUCT.md). Direct
criticism of a proof, claim, experiment, or repository decision is welcome;
harassment and attacks on contributors are not.

Treat this contributor path as a prototype until an independent cold-clone run
and an accepted outside contribution are recorded publicly. Reports about setup
friction, unclear instructions, broken links, agent-skill portability, unsafe
defaults, or unnecessary steps are substantive architecture contributions, not
housekeeping beneath the project's notice.

A cold reader is part of the validation surface. The cold-clone comprehension
program runs as a combined baseline-plus-adversarial release-gate check: it
reconstructs what a fresh clone can answer from the public files alone, and it
plants mutations that a comprehending reader would catch. A failure therefore
blocks the release gate, in the same way a broken claim link or a stale
projection does.

There are two first-class tracks:

1. **Mathematics:** proofs, reductions, computations, counterexamples,
   corrections, exposition, and reproducible negative or inconclusive results.
2. **Architecture:** ideas or implementations that improve agent workflows,
   navigation, validation, reproducibility, tooling, governance, or the public
   contributor experience.

You can contribute an architecture idea before you have code. Use the
[architecture proposal form](https://github.com/wcook04/plectis-erdos/issues/new?template=architecture_proposal.yml)
or read the [architecture contribution path](docs/research-commons/ARCHITECTURE_CONTRIBUTIONS.md).
If an idea is adopted, the accepting change preserves the originator's credit
in a tracked artifact and accepted receipt.

The ordinary contribution path is enough: fork or clone the repository, make
a focused change, and open a pull request. Explain the question you started
from, what you changed or learned, what another person can inspect, and what
remains unresolved. If you have an observation but no finished patch, open the
[plain-language research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml)
and write it in your own words. You do not need to learn the receipt format
before telling us something useful.

For compute contributions, begin with a bounded route exposed by the papers,
claim registry, or agent entry. The present routes are authored in the public
corpus and should name the question, evidence class, and stopping condition;
qualified external mathematical review is not claimed for every route. You may
run them through Claude Code, Codex, Cursor, Antigravity, another agent harness,
ordinary scripts, or your own reasoning. The runner is your choice; the
returned evidence boundary is the shared contract.

If an agent reports a solution, submit the source and evidence as a
**candidate**, not as an established solution. Maintainers first replay it and
try to break it. Lean acceptance establishes that the written formal
declaration follows in the pinned environment; it does not by itself establish
that the declaration means what was intended, is novel, settles the original
problem, or has been accepted by mathematicians. Work that survives internal
triage can be prepared for Comparator and Palomar and placed before the Erdős
Problems community or another appropriate research audience. Those external
routes do not transfer their authority back to a repository status field.

## What happens to returned work

The issue or pull request keeps the public history of a proposed change. When
maintainers accept the work, they can commit a short receipt recording who
contributed, which files or results are being credited, which public commit the
work began from, what was checked, and what remains limited. The public credit
pages are rebuilt from accepted receipts. The credit then travels with every
clone instead of living only in a notebook, chat, or web page.

Acceptance and mathematical claim status are separate. An
accepted correction can be credited without being called a new theorem. A
negative or inconclusive result can be credited when it rules out a route or
leaves a reproducible stopping point. A formal proof can be accepted as an
artifact while novelty, exposition, or a stronger public claim still needs
work. Earlier credit remains visible when a later contribution corrects or
supersedes it.

Credit is attached to the work actually returned. The receipt records
contributors, collaborators, tool operators, and disclosed model systems as
different roles instead of collapsing them into one author field. The project
does not rank people by commit count, diff size, or the number of generated
records. See the
[credit and stewardship policy](docs/research-commons/CREDIT_POLICY.md) for the
full boundary and the [accepted contributions](docs/research-commons/CONTRIBUTIONS.md)
for the public, receipt-backed view.

Artifact credit may also carry CRediT-aligned contribution roles such as
conceptualization, formal analysis, methodology, software, validation, and
writing. Select every role that is accurate; no single role is privileged, and
the roles describe work rather than deciding authorship.

## Staying in sync

A returned contribution records the public commit where the work began. Later
readers can then separate the contribution from changes that landed in the
meantime. Git retains the common ancestor between that starting point and the
contributor's branch, so maintainers can inspect the original change even when
the public main branch has advanced. They first replay the contribution in its
original context, then reconcile the reviewed substance with the current
repository. A real conflict is new integration work and receives its own
credit; it is not a reason to erase the original contribution.

Once accepted work reaches the public main branch or a tagged release, an older
clone can fetch it and merge or rebase in the usual way. The receipt, the
credited artifact, and the public credit page arrive together as repository
files. This does not depend on a private development checkout. Validation and
downstream consequence checks are repeated after reconciliation because an
old-branch receipt cannot certify the current repository state.

If two contributions overlap, preserve both histories and reconcile them in a
new change; do not silently rewrite the earlier return. If a later discovery
shows an accepted artifact was wrong, make a corrective return that names the
earlier one and says whether it should be retained as history, superseded, or
withdrawn from current use.

## What is welcome

Mathematical errors and overstatements are especially valuable reports. So are
Lean build failures, broken source or paper links, missing attribution,
exposition that hides an assumption, counterexamples to intermediate claims,
and improvements to the clone-local checks. New formal results are welcome,
but their public description must be no stronger than the evidence, and all
eight headline Erdős problems remain open unless an extraordinary independent
mathematical process establishes otherwise.

Ordinary prose, citation, and tooling corrections can arrive as normal pull
requests. A structured research return is useful when the history matters: for
example, a bounded investigation that another person should be able to resume,
or a negative result whose exact starting point and evidence should not be
lost. The [research commons guide](docs/research-commons/README.md) explains
that lifecycle without requiring you to read a schema.

Architecture proposals and implementations use the same accepted-receipt and
public-credit rail as mathematical returns, but they do not claim a fictional
problem number. Their structured frontier declares `track: architecture` and a
bounded architecture area. The existing `continue_research.py` continuation
package remains the specialized front door for mathematical problem sessions.

## For agents and maintainers

The human route above is the contract. The machinery below implements it; none
of it is a prerequisite for reporting a useful result. Agents should use the
clone-local [research-return skill](skills/erdos-research-return/SKILL.md), and
the [consequence-propagation skill](skills/propagate-research-consequences/SKILL.md)
after a stable result, and
the [pull-request submission skill](skills/submit-pull-request/SKILL.md) when
turning owned work into commits and a proposed GitHub return. That skill stops
before pushing or opening the pull request unless the contributor explicitly
authorises those external actions. Maintainers should preserve the
contributor's prose rather than replacing it with machine field names.

To open and package a bounded, attributable structured research session, use
`scripts/continue_research.py`. Its `start`, `check`, and `package` commands
bind the public origin, starting commit, contributor identity, problem route,
evidence, and route-memory receipt. The resulting `return.json` and
`route-memory.json` may accompany a pull request. Validate them with
`scripts/validate_research_return.py` before submission. The detailed field
contract is in the [return package template](docs/research-commons/RETURN_PACKAGE_TEMPLATE.md).

After a contribution has actually landed, `scripts/accept_research_return.py`
can bind the reviewed result to its accepted public commit. Then
`scripts/build_research_contributions.py` and
`scripts/build_research_contribution_recognition.py` rebuild the accepted-only
credit views. A submitted return must never appear there before acceptance,
and an accepted receipt must never silently strengthen `docs/claims.json`.

For an ordinary source change, run the narrow checks named by the agent entry
and the affected subsystem. Lean changes must build with the pinned toolchain.
Changes to claims, papers, or generated projections must follow the authority
and builder order in [AGENTS.md](AGENTS.md). CI exercises the public return
validator, the acceptance boundary, and the accepted-only attribution views.
