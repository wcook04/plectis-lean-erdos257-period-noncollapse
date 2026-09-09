#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check that the newcomer architecture guide stays concrete and jargon-free."""

from __future__ import annotations

import json
import os
import re
import stat
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
GUIDE = ROOT / "ARCHITECTURE.md"
README = ROOT / "README.md"
AGENTS = ROOT / "AGENTS.md"
PAPER_README = ROOT / "paper" / "README.md"
SYSTEMS_PAPER = ROOT / "paper" / "claim-faithful-publication-systems-paper.tex"
SYSTEMS_PDF = ROOT / "claim-faithful-publication-systems-paper.pdf"
PUBLICATION_CONTRACT = ROOT / "docs" / "publication_contract.json"
MAX_GUIDE_BYTES = 18_000
# Keep the architecture paper bounded without accumulating one-off magic-number
# raises.  Its legitimate explanatory load grows with the canonical publication
# inventory, whose exact membership is independently checked against the build
# and licence manifests.  A stable conceptual base plus a small per-artifact
# allowance therefore scales only when the governed public surface scales.
# The base now covers the complete private-to-public architecture rather than
# the former release-check case study: authority-aware routing, temporal work
# leases, resident metabolism, trace projections, federated mathematical
# memory, proof/publication gates, the scale/review boundary, and the public
# job lifecycle from invocation through consequence propagation and old-base
# assimilation. The enlarged base also covers the coupled discovery and corpus-
# stewardship roles, local-to-general digestion, and their public skill routes.
# The per-artifact increment remains the only
# inventory-dependent allowance.
# Raised from 66,000 on 2026-09-02. The base is meant to move only when the
# architecture the paper describes enlarges, and two sections now sit inside it
# that the previous base did not cover: the mathematical reasoning loop, and the
# argument for scaling from one clone to a search network. The per-artifact
# increment is still the only inventory-dependent allowance, and the guide
# itself was brought back under its own budget by cutting a restatement rather
# than by raising anything.
# Raised again from 70,000 on 2026-09-02, by the size of one further section the
# previous base did not cover: the compiled comprehension packet that an agent
# reasons over before it reaches the mathematics. The paper was first tightened
# and a duplicated drill-down ladder was cut, so the raise covers the new
# architecture and nothing else.
SYSTEMS_PAPER_BASE_BYTES = 73_000
SYSTEMS_PAPER_BYTES_PER_ARTIFACT = 1_000


class UnsafeArchitectureInput(ValueError):
    """An architecture-check input escaped the checkout or is not a file."""


def safe_architecture_text(path: Path, root: Path = ROOT) -> str:
    """Read one architecture input through a no-follow regular-file descriptor."""
    root = Path(os.path.abspath(root))
    candidate = Path(os.path.abspath(path))
    if candidate != root and root not in candidate.parents:
        raise UnsafeArchitectureInput(f"architecture input escaped checkout: {candidate}")
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeArchitectureInput(f"symlinked architecture input: {candidate}")
        if current == root:
            break
        if current.parent == current:
            raise UnsafeArchitectureInput(f"architecture input escaped checkout: {candidate}")
        current = current.parent
    if not candidate.is_file():
        raise UnsafeArchitectureInput(
            f"architecture input is not a regular file: {candidate}"
        )

    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeArchitectureInput(
            f"architecture input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeArchitectureInput(
                f"architecture input is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        try:
            return b"".join(chunks).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise UnsafeArchitectureInput(
                f"architecture input is not UTF-8: {candidate}"
            ) from exc
    finally:
        os.close(descriptor)

SECTION_ORDER = (
    "## What this repository is",
    "## The architecture in one page",
    "## Which file is authoritative for what",
    "## Repository map",
    "## A complete example",
    "## What happens when a change is made",
    "## How the checks run",
    "## What the checks do not prove",
    "## Where to start",
)

REQUIRED_ANCHOR_GROUPS = {
    "purpose_and_boundary": (
        "eight unsolved problems in mathematics",
        "reviewed claim registry covers #249 and #257",
        "All eight mathematical problems remain open",
        "does not claim a solution to any of them",
        "self-contained public release",
    ),
    "three_decisions": (
        "Lean decides whether a formal proof",
        "A mathematician decides whether the public wording",
        "The release program decides whether the files",
    ),
    "authority_owners": (
        "Erdos249257.lean",
        "docs/claims.json",
        "docs/methodology.json",
        "scripts/check_release.py",
        ".github/workflows/lean.yml",
    ),
    "worked_example": (
        "certified_kill_instances",
        "verified finite instance",
        "beyond every fixed cutoff",
    ),
    "validation_split": (
        "lake build",
        "python3 scripts/check_release.py",
        "does not run Lean",
    ),
    "guarantee_ceiling": (
        "does not mean that a program understood every sentence",
        "does not prove that every important sentence was selected",
    ),
    "paper_lifecycle_boundary": (
        "The eight individual problem papers are the active mathematical routes",
        "archived provenance only, not an active gateway",
        "The archived combined #249/#257 PDF is not a default reading route",
    ),
}

REQUIRED_PATHS = (
    "Erdos249257.lean",
    "ErdosProblems.lean",
    "docs/claims.json",
    "docs/methodology.json",
    "docs/publication_contract.json",
    "docs/publication_evidence.json",
    "docs/ORIENTATION.md",
    "docs/SOURCE_MAP.md",
    "scripts/check_release.py",
    "scripts/check_cold_clone_comprehension.py",
    ".github/workflows/lean.yml",
    "paper/erdos249-257-main-paper.tex",
)

# These labels belong to the evaluation history or to private agent doctrine.
# A first-principles repository guide has no reason to make a cold reader decode
# them. The full words Type A and Type B are included because they are private
# role labels in the parent workflow, not part of this public Lean project.
BANNED_SHORTHAND = (
    re.compile(r"\bM(?:10|[1-9])\b"),
    re.compile(r"\b9/10\b"),
    re.compile(r"\b5,207\b"),
    re.compile(r"\bMRS\b"),
    re.compile(r"\bquantifier\b", re.IGNORECASE),
    re.compile(r"\bType A\b", re.IGNORECASE),
    re.compile(r"\bType B\b", re.IGNORECASE),
    re.compile(r"\bAccess Skeleton\b", re.IGNORECASE),
    re.compile(r"\bVinum\b", re.IGNORECASE),
)

PAPER_SECTION_ORDER = (
    r"\section{The problem: many kinds of evidence}",
    r"\section{The whole lifecycle in one picture}",
    r"\section{The private workbench}",
    r"\section{The mathematical reasoning loop}",
    r"\section{The public Lean repository}",
    r"\section{Comparator, Palomar, and publication}",
    r"\section{One complete boundary: finite is not unbounded}",
    r"\section{Inspection routes}",
    r"\section{What can be trusted}",
    r"\section{Scaling from one clone to a search network}",
    r"\section{Relation to other approaches}",
    r"\section{Conclusion}",
    r"\section{Reproducibility}",
)

PAPER_REQUIRED_ANCHOR_GROUPS = {
    "plain_purpose": (
        "compares it with neighbouring systems along stated dimensions and claims no priority",
        "claim-transition architecture",
        "six things that are commonly collapsed",
        "after a proof is found, what exactly may move into a reviewed public claim",
        "All eight problems remain open",
        "does not claim a solution to any of them",
    ),
    "problem_worlds_and_nonfungible_authority": (
        "A problem is a mathematical world, not a folder",
        "bounded neighbourhood inside a problem-sized world",
        "The architecture treats six resources as non-fungible",
        "More reasoning cannot buy a write lease",
        "two coupled graphs with a guarded crossing",
        "Neither graph may rewrite the other by implication",
    ),
    "private_authority_and_concurrency": (
        "Durable state lives in files",
        "Type A and Type B",
        "substrate access, not model quality",
        "claims exact paths for a bounded lease",
        "append-only ledgers and immutable receipts",
        "fan-in barrier",
    ),
    "executable_control_plane": (
        "typed option surface",
        "past work from present permission",
        "SQLite store in write-ahead-log mode",
        "daemon as not running while queued jobs remained visible",
        "always-on architecture",
        "currently healthy service",
    ),
    "continuous_trace_boundary": (
        "313 visible progress updates and 3,491 command events",
        "compressed trace has an observation boundary",
        "Completeness is therefore an explicit field",
        "authority-bearing artefact and receipt",
    ),
    "mathematical_reasoning_and_graphs": (
        "Experiments are route selectors",
        "A failed agent attempt",
        "A Lean no-go theorem",
        "Every no-go keeps its scope visible",
        "Problem-sized Lean worlds and bounded theorem neighbourhoods",
        "1,024 Lean modules and 153,396 declarations",
        "177 exact results, seven open producers, 72 negative results",
        "designed omission, not exhaustive loading",
        # The comprehension packet was promoted out of this subsection into one
        # of its own, and the federation sentence was rewritten there. The
        # property the old anchor held is the one still pinned: the working
        # memory federates and copies nothing into a central index. The three
        # anchors after it pin the rest of that new section, so a later rewrite
        # cannot delete the packet, its authority boundary, or its two refusals
        # without this check going red.
        "nothing is copied into a central index",
        "Comprehension before the mathematics",
        "The workspace plans inference and concludes nothing",
        "reported as unanchored",
        "semantic second pass",
        "no projection may bulk-strengthen a family of claims",
    ),
    "assurance_and_digestion": (
        "Comparator: an exact-statement firewall",
        "Comparator-checked",
        "Review selection, and what the Palomar registry is not",
        "proof generation, verification, exposition, publication and community digestion",
        "natural friction",
        "Paper authoring itself participates in this loop",
        "active digestion and interpretability pass in Tao's sense",
        "That reflexivity is provenance, not validation",
        "never local status fields",
    ),
    "worked_boundary_and_failure": (
        "forall t\\le82",
        "No matter how large a fixed checked bound is",
        "relationship had not been registered",
        "Nine of the ten edits were rejected",
        "original run logs were not retained",
        "other nine edits were not rerun",
    ),
    "scale_without_authority_inflation": (
        "result mining",
        "semantic single-flight queue",
        "host-wide Mathlib resource",
        "four separate scaling limits",
        "no-go graph as a new mathematical object",
        "graph-conditioned models",
        "design target rather than a reported benchmark",
    ),
    "public_return_and_credit": (
        "fork or clone the repository",
        "pull request or research-progress issue",
        "Only an accepted receipt enters",
        "Acceptance, mathematical claim status, and release inclusion remain separate",
        "Attribution and pull requests are standard practice",
    ),
    "real_public_routes": (
        "Erdos249257.lean",
        "ErdosProblems.lean",
        "docs/claims.json",
        "scripts/check_release.py",
        ".github/workflows/lean.yml",
        "docs/research-commons/CONTRIBUTIONS.md",
    ),
}

# The cold-reader architecture guide still avoids private Type A/B labels and
# unexplained quantifier jargon.  The systems paper has the different job of
# explaining those mechanisms and the finite/unbounded mathematical boundary.
PAPER_BANNED_SHORTHAND = (
    re.compile(r"\bM(?:10|[1-9])\b"),
    re.compile(r"\b9/10\b"),
    re.compile(r"\b5,207\b"),
    re.compile(r"\bMRS\b"),
    re.compile(r"\bAccess Skeleton\b", re.IGNORECASE),
    re.compile(r"\bVinum\b", re.IGNORECASE),
)


def normalise(text: str) -> str:
    return " ".join(text.split())


def normalise_tex(text: str) -> str:
    """Flatten the small subset of TeX used by load-bearing prose anchors."""
    for _ in range(3):
        text = re.sub(
            r"\\(?:textbf|emph|texttt)\{([^{}]*)\}",
            r"\1",
            text,
        )
    text = text.replace(r"\_", "_").replace("{", "").replace("}", "")
    return normalise(text)


def require(condition: bool, message: str) -> None:
    """Enforce a release check even when callers run Python with ``-O``."""
    if not condition:
        raise AssertionError(message)


def validate_guide(text: str) -> None:
    size = len(text.encode("utf-8"))
    require(size <= MAX_GUIDE_BYTES, (
        f"ARCHITECTURE.md is {size} bytes (budget {MAX_GUIDE_BYTES})"
    ))

    positions = [text.find(heading) for heading in SECTION_ORDER]
    require(all(position >= 0 for position in positions), (
        f"architecture guide lost section sequence {SECTION_ORDER}"
    ))
    require(positions == sorted(positions), "architecture guide sections are out of order")

    compact = normalise_tex(text)
    for group_id, anchors in REQUIRED_ANCHOR_GROUPS.items():
        for anchor in anchors:
            require(normalise(anchor).casefold() in compact.casefold(), (
                f"architecture guide lost {group_id} anchor {anchor!r}"
            ))

    for pattern in BANNED_SHORTHAND:
        require(not pattern.search(text), (
            f"architecture guide exposes private or evaluation shorthand {pattern.pattern!r}"
        ))

    for rel in REQUIRED_PATHS:
        require((ROOT / rel).exists(), f"architecture guide names missing path {rel}")
        require(rel in text, f"architecture guide no longer routes through {rel}")

    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        if target.startswith(("http://", "https://", "#")):
            continue
        path = target.split("#", 1)[0]
        require((ROOT / path).exists(), f"architecture guide has broken local link {target}")


def validate_systems_paper(text: str) -> None:
    """Keep the PDF source architecture-first rather than experiment-first."""
    size = len(text.encode("utf-8"))
    contract = json.loads(safe_architecture_text(PUBLICATION_CONTRACT))
    artifact_count = len(contract["artifacts"])
    byte_budget = (
        SYSTEMS_PAPER_BASE_BYTES
        + SYSTEMS_PAPER_BYTES_PER_ARTIFACT * artifact_count
    )
    require(size <= byte_budget, (
        f"systems architecture paper is {size} bytes "
        f"(budget {byte_budget} for {artifact_count} governed artifacts)"
    ))

    require(
        "Problem-Sized Lean Worlds" in text
        and "An authority-separated architecture from AI search to public mathematical claims"
        in text
    , "systems paper lost its plain architecture title")
    require(
        text.count("% BEGIN generated_semantic_coverage_macros") == 1
        and text.count("% END generated_semantic_coverage_macros") == 1,
        "systems paper lost its semantic-corpus builder region",
    )

    positions = [text.find(heading) for heading in PAPER_SECTION_ORDER]
    require(all(position >= 0 for position in positions), (
        f"systems paper lost section sequence {PAPER_SECTION_ORDER}"
    ))
    require(positions == sorted(positions), "systems paper sections are out of order")

    compact = normalise_tex(text)
    for group_id, anchors in PAPER_REQUIRED_ANCHOR_GROUPS.items():
        for anchor in anchors:
            require(normalise(anchor).casefold() in compact.casefold(), (
                f"systems paper lost {group_id} anchor {anchor!r}"
            ))

    for pattern in PAPER_BANNED_SHORTHAND:
        require(not pattern.search(text), (
            f"systems paper exposes private or score-like shorthand {pattern.pattern!r}"
        ))

    require(len(re.findall(r"\bsentence\b", text, flags=re.IGNORECASE)) <= 4, (
        "systems paper has drifted back to a sentence-centred case study"
    ))
    require("certified_kill_instances" not in compact, (
        "systems paper regressed from public mathematical meaning to an internal claim id"
    ))
    require(SYSTEMS_PDF.is_file(), "rendered systems architecture PDF is missing")


def validate_entry_links(
    readme: str,
    agents: str,
    paper_readme: str,
    guide: str,
) -> None:
    readme_first_impression = (
        readme.encode("utf-8")[:6_000].decode("utf-8", errors="ignore")
    )
    require("](ARCHITECTURE.md)" in readme,
            "README lost the architecture guide entry link")
    require(
        "](claim-faithful-publication-systems-paper.pdf)" in guide,
        "architecture guide lost the printable systems-paper route",
    )
    compact_guide = normalise(guide).casefold()
    require(
        "you do not need to know lean" in compact_guide
        and "project history" in compact_guide,
        "architecture guide lost the no-Lean/no-history entry boundary",
    )
    for phrase in (
        "conditional producer",
        "unbounded or cofinal supply",
        "lcm-diagonal scales",
        "producer carry",
    ):
        require(phrase not in readme_first_impression.casefold(), (
            f"README first impression exposes unexplained phrase {phrase!r}"
        ))
    require("ARCHITECTURE.md" in agents, "AGENTS lost the architecture guide route")
    require("plain-language human guide" in agents,
            "AGENTS lost the plain-language architecture guide route")
    compact_paper_readme = normalise(paper_readme)
    require("[`ARCHITECTURE.md`](../ARCHITECTURE.md)" in paper_readme,
            "paper README lost the architecture guide route")
    require(
        "short first-read paper" in compact_paper_readme
        and "longer complete reasoning record" in compact_paper_readme,
        "paper README lost the short-paper/reasoning-record boundary",
    )
    require(
        "repository layout, sources of truth, build path, and release infrastructure"
        in compact_paper_readme,
        "paper README lost the architecture-guide role",
    )
    require(
        "older joint #249/#257 paper is retained for provenance" in compact_paper_readme
        and "not the entry point for either problem" in compact_paper_readme,
        "paper README lost the maintained-versus-historical route boundary",
    )
    for manuscript in (
        "erdos249-257-main-paper.tex",
        "claim-faithful-publication-systems-paper.tex",
    ):
        require(manuscript in paper_readme,
                f"paper README lost manuscript route {manuscript}")


def main() -> int:
    validate_guide(safe_architecture_text(GUIDE))
    validate_systems_paper(safe_architecture_text(SYSTEMS_PAPER))
    validate_entry_links(
        safe_architecture_text(README),
        safe_architecture_text(AGENTS),
        safe_architecture_text(PAPER_README),
        safe_architecture_text(GUIDE),
    )
    print("architecture guide: first-principles structure and entry links verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
