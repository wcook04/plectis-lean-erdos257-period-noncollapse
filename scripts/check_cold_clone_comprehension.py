#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify bounded first-contact comprehension in a fresh public checkout.

This evaluator deliberately does *not* concatenate the exhaustive claim,
methodology, or declaration owners.  A cold reader starts from the compact
human surfaces; a coding agent starts from the bounded corpus query and then
follows typed packets.  The authoritative owners remain available as explicit
expansions, but are not evidence for first-contact comprehension.

This checks navigation semantics and response budgets, not Lean proof
correctness.  The pinned Lean source checked by the kernel remains proof
authority.
"""

from __future__ import annotations

import argparse
from collections import Counter
import contextlib
import copy
import io
import json
import os
import re
import stat
import subprocess
import sys
from functools import lru_cache
from pathlib import Path
from typing import Any

import build_corpus_descriptor
import build_semantic_corpus
import check_architecture_guide
import query_corpus
import query_expert_handoffs
import query_semantic
import validation_singleflight as singleflight

ROOT = Path(__file__).resolve().parent.parent


def require(condition: bool, message: str) -> None:
    """Keep cold-clone checks active when invoked with ``python -O``."""
    if not condition:
        raise AssertionError(message)


class UnsafeColdCloneInput(ValueError):
    """A cold-clone evaluator input is outside the regular checkout boundary."""


def _is_allowed_platform_alias(path: Path) -> bool:
    """Permit the host's canonical temporary-directory aliases only."""
    try:
        aliases = {
            Path("/var"): Path("/private/var"),
            Path("/tmp"): Path("/private/tmp"),
        }
        return path in aliases and path.resolve(strict=True) == aliases[path]
    except OSError:
        return False


def _canonical_input_path(path: Path) -> Path:
    """Resolve only the explicitly permitted macOS temporary aliases."""
    candidate = Path(os.path.abspath(path))
    if len(candidate.parts) >= 2:
        alias = Path(os.sep, candidate.parts[1])
        if _is_allowed_platform_alias(alias):
            return alias.resolve(strict=True).joinpath(*candidate.parts[2:])
    return candidate


def _safe_cold_clone_path(path: Path) -> Path:
    """Reject checkout escapes and symbolic-link path components."""
    root = Path(os.path.abspath(ROOT))
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeColdCloneInput(f"symlinked cold-clone input: {candidate}")
        if current == root:
            break
        if current.parent == current:
            raise UnsafeColdCloneInput(f"cold-clone input escaped checkout: {candidate}")
        current = current.parent
    return candidate


def safe_read_text(rel: str) -> str:
    """Read a public cold-clone surface through a no-follow regular descriptor."""
    candidate = _canonical_input_path(_safe_cold_clone_path(ROOT / rel))
    if not candidate.is_file():
        raise UnsafeColdCloneInput(f"cold-clone input is not a regular file: {candidate}")
    directory_flags = os.O_RDONLY
    directory_flags |= getattr(os, "O_CLOEXEC", 0)
    directory_flags |= getattr(os, "O_DIRECTORY", 0)
    directory_flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        directory = os.open(os.sep, directory_flags)
    except OSError as exc:
        raise UnsafeColdCloneInput(
            f"cold-clone input could not be opened safely: {candidate}"
        ) from exc
    descriptor = -1
    try:
        for component in candidate.parts[1:-1]:
            child = os.open(component, directory_flags, dir_fd=directory)
            try:
                if not stat.S_ISDIR(os.fstat(child).st_mode):
                    raise OSError(
                        f"cold-clone input parent is not a directory: {candidate.parent}"
                    )
            except BaseException:
                os.close(child)
                raise
            os.close(directory)
            directory = child
        flags = os.O_RDONLY
        flags |= getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NONBLOCK", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        descriptor = os.open(candidate.name, flags, dir_fd=directory)
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeColdCloneInput(
                f"cold-clone input is not a regular file: {candidate}"
            )
        with os.fdopen(descriptor, "r", encoding="utf-8") as stream:
            descriptor = -1
            return stream.read()
    except OSError as exc:
        raise UnsafeColdCloneInput(
            f"cold-clone input could not be opened safely: {candidate}"
        ) from exc
    finally:
        os.close(directory)
        if descriptor >= 0:
            os.close(descriptor)


INDEXED_PROBLEM_NUMBERS = frozenset(
    row["erdos_number"]
    for row in json.loads(safe_read_text("docs/problems.json"))["problems"]
)
INDEXED_PROBLEM_ORDER = tuple(
    row["erdos_number"]
    for row in json.loads(safe_read_text("docs/problems.json"))["problems"]
)
INDEXED_PROBLEM_COUNT = len(INDEXED_PROBLEM_NUMBERS)
QUERY = ROOT / "scripts" / "query_corpus.py"
SEMANTIC_QUERY = ROOT / "scripts" / "query_semantic.py"
EXPERT_HANDOFF_QUERY = ROOT / "scripts" / "query_expert_handoffs.py"
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
SYSTEMS_EXPERT_QUESTION_ID = "XQSYS-ten-minute-hostile-reader"
HUMAN_SURFACES = (
    "README.md",
    "ARCHITECTURE.md",
    "SCOPE.md",
    "docs/ORIENTATION.md",
)
# The paper shelf is a generated first-contact surface with its own authority
# (Palomar's candidate ranking plus the paper corpus).  Keep it outside the
# compact human-surface budget so this gate can check the shelf without
# changing the existing README contract.
PAPER_LIBRARY_SURFACE = "docs/papers/README.md"
# The shelf carries one section per shipped paper, so its size tracks the paper
# corpus and not the prose around it. The flat 40,000 was set at a smaller
# corpus and the shelf has been over it for some time; only the --quick lane
# runs this check, so it went unseen. Base plus one section's allowance.
PAPER_LIBRARY_BASE_BUDGET_BYTES = 8_000
PAPER_LIBRARY_BYTES_PER_PAPER = 4_400
PAPER_LIBRARY_FIRST_CONTACT_BUDGET_BYTES = (
    PAPER_LIBRARY_BASE_BUDGET_BYTES
    + PAPER_LIBRARY_BYTES_PER_PAPER
    * len(json.loads(safe_read_text("docs/papers/corpus.json"))["papers"])
)
# Volatile semantic counts live on the audit surfaces, not the compact README.
CENSUS_SURFACES = ("docs/RESULTS.md", "docs/TRUTH_AUDIT.md")
INCREMENTAL_BUILD_SURFACES = (
    "README.md",
    # The build contract moved off the front page with the rest of the detail
    # when the README was cut to its reader budget. It is on the document the
    # README names, verbatim, and this contract reads both.
    "docs/AGENT_WORKBENCH.md",
    "docs/REPRODUCIBILITY.md",
    ".github/workflows/lean.yml",
    "scripts/lean_fast_build.py",
)
# Whole-file ceilings are intentionally looser than the fixed first-contact
# prefix below. They prevent accidental bloat without making the next honest
# sentence a release failure.
HUMAN_SURFACE_BUDGET_BYTES = {
    # The fixed prefix below protects the verdict and the direct eight-problem
    # mathematical card. Whole-file allowance scales with the canonical
    # problem registry instead of preserving the original two-lane ceiling.
    # 300 bytes per problem was measured against shorter rows; the eight-problem
    # table states each checked frontier and what remains, which runs longer.
    # Measured at eight problems: 18,569 bytes, or 321 bytes per problem above
    # the 16,000 fixed prefix. 400 leaves room for one further problem without
    # reopening this line, and still fails on a runaway projection.
    # 2026-08-11: raised to fund the measured generated-share denominator,
    # first-screen AI-assistance boundary, and falsifiable #269 chronology.
    # Attribution and trust calibration outrank byte thrift; the ceiling still
    # fails on a runaway projection.
    # 2026-08-15: raised to fund the external-verification mechanism on the
    # first screen. The section named "External verification" previously spent
    # every byte on prior-art boundaries and release identity and never said
    # what the verification is, so a reviewer could not learn from the README
    # that nineteen propositions are separately declared, Comparator-checked
    # against a fixed axiom budget, and covered by an adversarial fixture, nor
    # that the same check runs in continuous integration. "Has anyone actually
    # run this?" is the first question a sceptical reviewer asks. A cheap
    # inspection route is what a formal-methods reviewer asks for first; the
    # ceiling still fails on a runaway projection.
    # 2026-08-15: raised to name the Agent Workbench on the reader surface. The
    # workbench, its typed move grammar, the three-rung invention ladder, and
    # the one landed prospective session were documented in docs/ and in
    # AGENTS.md but appeared nowhere in the README, so a human reviewer arriving
    # at the front page could not learn that agent sessions here are append-only
    # ledgers, that stored probes replay, or that a kernel-checked module was
    # derived inside one. Reviewers judge the claim discipline as much as the
    # mathematics. Funded with slack rather than to the byte: a ceiling that
    # leaves four spare bytes makes the next honest sentence a release failure,
    # which is how a budget stops guarding prose and starts shaping it. The
    # ceiling still fails on a runaway projection.
    # Also funds naming the Formal Conjectures crosswalk and the related-problem
    # map, which were reachable only from the replay document and a verification
    # contract despite answering a reviewer's first two questions: how do these
    # statements line up with the public benchmark, and what is already known
    # about the neighbouring problems.
    # 2026-08-16: raised to fund two first-contact repairs a cold clone proved
    # were missing. The README sent a newcomer to `lake exe cache get` without
    # ever saying where `lake` comes from: `elan` appeared nowhere in this
    # repository's documentation, so the first build command a reader was given
    # was `command not found` unless they already had the toolchain. The
    # setup-guide pointer and the toolchain sentence are the fix, and they must
    # sit above the command rather than eighteen lines below it. The second is
    # `scripts/verify_claims.py`, which landed with CI enforcement and an entry
    # in AGENTS.md but nothing on the reader surface: the repository's cheapest
    # concrete verb -- follow one claim to its source, receipts, and stopping
    # point, in under a second, with no Lean installed -- was invisible to the
    # human it was built for. Funded with slack, per the note above.
    # 2026-08-16, later the same day: the verb moved from that route list onto
    # the first screen, and this ceiling did not move to pay for it. Naming it
    # under "Read or run it" made it findable by a reader already committed to
    # reading; a reader still deciding met eight problem papers, an
    # external-verification account, a formal-results table, an open-wall
    # section and a corpus census before anything they could run. Stating the
    # command under the opening verdict made the paragraph that introduced it
    # 15,000 bytes later redundant, and deleting that paid for the move with
    # ~230 bytes to spare. Prefer that trade to a raise: a budget raised for
    # every honest sentence stops being a budget. The positional assertion in
    # `validate_human_first_contact` now pins the verb above the first heading,
    # so a future raise cannot quietly buy the old ordering back.
    # 2026-08-18: raised to name the residual evaluator on the reader surface.
    # The note above warned that a ceiling with four spare bytes makes the next
    # honest sentence a release failure; this one had nine, and the sentence it
    # refused was the one telling a proof-search reader that `hypOf%` turns "did
    # this sketch reduce the target or rename it" into a question for the
    # kernel. That reader is the one most likely to have the failure the tool
    # addresses, and every route to it ran through a document they had no
    # reason to open. Six lines, funded with slack rather than to the byte.
    # 2026-08-31: raised to fund the wider-system map and the author's-state
    # note, both operator-requested. The README named the front door in one
    # sentence and nothing else about the estate; a reader had no route to the
    # website, the videos, or the doctrine without leaving for the site first.
    # The map sits under the opening routes; the author's note closes the file,
    # after the licence, as the last thing read. The paragraph that pointed at
    # the front door was deleted since the map now owns it. The verify command
    # stays above the first heading, so the positional pin below still holds.
    # Funded with slack rather than to the byte, per the notes above.
    # Raised 27_200 -> 27_600 when the generated corpus region grew with the
    # 2026-09-01 reconciliation (claim records 103 -> 129) and the system-map
    # figure line joined the header. Authored prose shrank in the same pass.
    # Raised 27_600 -> 28_400 for the framing reorder (operator-directed,
    # 2026-09-01): the first screen now answers why these problems, what the
    # intended outcome was, what Lean contributes, and why the repository is
    # public, before the results inventory.
    "README.md": 28_400 + 400 * INDEXED_PROBLEM_COUNT,
    "ARCHITECTURE.md": 18_000,
    # SCOPE.md must list every remaining-open identifier and its bounded query,
    # so two lines of it are spoken for by each registered proposition: measured
    # at 139 bytes a proposition against 2,528 bytes of prose. The flat 4,000
    # was set at eleven propositions and could not survive the repository
    # registering the eight its own papers already state.
    "SCOPE.md": 2_800
    + 160
    * len(
        json.loads(safe_read_text("docs/claims.json"))["remaining_open_propositions"]
    ),
    # The generated orientation is budgeted by its own builder, which scales
    # with the registered open boundary and the mathematical programmes it is
    # required to carry. Pinning a second, smaller number here meant this gate
    # could reject a file the builder had just certified as bounded.
    "docs/ORIENTATION.md": build_corpus_descriptor.orientation_markdown_budget_bytes(
        len(json.loads(safe_read_text("docs/orientation.json"))[
            "remaining_open_propositions"
        ]),
        len(json.loads(safe_read_text("docs/orientation.json"))[
            "mathematical_programmes"
        ]),
    ),
}
# The compact README is the newcomer contract. It must fit the mathematical
# identity, the eight-paper index, the evidence boundary, and direct routes to
# contribution and reproducibility without turning the front page into a
# setup runbook. Detailed checkout variants are validated at their routed
# owner below.
README_FIRST_CONTACT_BUDGET_BYTES = 12_000
SUMMARY_PACKET_BUDGET_BYTES = 32_256
# Sized when the corpus indexed six problems. #68 and #1041 bring their own
# vocabulary routes, so the dictionary packet grew past it. Raised rather than
# trimmed: dropping routes to fit would make the packet silently incomplete.
# A detail packet also carries the remaining-open propositions attached to the
# claims or programme it names, so the ceiling has to move with the registered
# open boundary. Holding it fixed meant that registering a proposition the
# papers already state read as a runaway projection.
REMAINING_OPEN_PROPOSITION_COUNT = len(
    json.loads(safe_read_text("docs/claims.json"))["remaining_open_propositions"]
)
# One registered open proposition's row, with its statement and target claim.
OPEN_PROPOSITION_PACKET_BYTES = 400
# Documents the README names on its first screen and whose content a cold reader
# following it therefore reaches. They carry the recoverable detail the front
# page used to hold itself.
FIRST_CONTACT_ROUTED_SURFACES = (
    "docs/RESULTS.md",
    "docs/AGENT_WORKBENCH.md",
    "docs/REPRODUCIBILITY.md",
    "CONTRIBUTING.md",
)
PACKET_BUDGET_BYTES = (
    20_480 + OPEN_PROPOSITION_PACKET_BYTES * REMAINING_OPEN_PROPOSITION_COUNT
)
# The expert-handoff compact index is the one packet that is a chooser over
# every handoff at once, and this gate pins most of its content itself: it
# requires six rows, and requires ten fields of each mathematical row to equal
# `python3 scripts/query_semantic.py expert-questions` field-for-field. Those
# pinned rows plus the packet scaffolding measure 16,612 bytes on their own --
# 81% of the fixed packet budget above -- so the derived navigation the surface
# exists to provide has under 3,900 bytes to live in.
#
# Measured on 2026-08-31, after densifying the emitter (the packet had reached
# 116,052 bytes by repeating one family's ten source-current supports, with
# their family-level fields and one boundary paragraph carried twice on every
# row, into three of the six rows):
#
#     16,612  six pinned question rows and packet scaffolding
#      2,094  derived navigation, one bounded block per problem (two today)
#              plus the receipt naming the withheld contract prose
#      5,137  source-current support index: the family block once, the ranked
#              head of two of ten supports, and the omission receipt
#     ------
#     23,843  measured total
#
# Every arrangement that fits 20,480 has to delete something the bounded-surface
# discipline keeps: with the navigation block the support index has to lose its
# boundary paragraph, its omitted-declaration names *and* its ranked head; drop
# the navigation block entirely and the head still has to go to zero. A head of
# zero is a pointer, not a bounded surface. So this surface gets its own named
# ceiling rather than a hollowed-out packet.
#
# 26,624 leaves 2,781 bytes of headroom. That is one more systems handoff --
# measured at 2,852 bytes for the one that exists, and the only growth axis the
# protocol leaves open, since protocol_errors() freezes the mathematical
# handoffs at five and the support head is capped by COMPACT_SUPPORT_HEAD. It
# still fails on a runaway projection: the pre-densification packet was 4.4x
# this ceiling.
EXPERT_HANDOFF_INDEX_BUDGET_BYTES = 26_624
# The publication architecture is the one intentionally portfolio-wide
# packet: it carries one route-memory row for every selected family, while
# ordinary detail packets remain under the fixed agent budget above. Keep a
# fixed allowance for the architecture envelope and scale only with the
# source-controlled family index.
PUBLICATION_ARCHITECTURE_BASE_BUDGET_BYTES = 12_000
PUBLICATION_ARCHITECTURE_BYTES_PER_FAMILY = 1_200


# instant_orientation is the second portfolio-wide packet: its whole purpose is
# to hand a cold agent the ranked mathematical signal, which carries one row per
# reviewed family. Holding it to the fixed detail budget asked the route to be
# incomplete, and the ceiling was already exceeded before the eight open
# propositions were registered. Scale it with the same family index instead.
INSTANT_ORIENTATION_BASE_BUDGET_BYTES = 8_000
INSTANT_ORIENTATION_BYTES_PER_FAMILY = 1_200


def instant_orientation_budget_bytes(family_count: int) -> int:
    """Return the bounded budget for the ranked mathematical-signal route."""
    require(
        type(family_count) is int and family_count > 0,
        "instant orientation family count must be a positive integer",
    )
    return (
        INSTANT_ORIENTATION_BASE_BUDGET_BYTES
        + INSTANT_ORIENTATION_BYTES_PER_FAMILY * family_count
    )


def publication_architecture_budget_bytes(family_count: int) -> int:
    """Return the bounded budget for the portfolio architecture packet."""
    require(
        type(family_count) is int and family_count > 0,
        "publication architecture family count must be a positive integer",
    )
    return (
        PUBLICATION_ARCHITECTURE_BASE_BUDGET_BYTES
        + PUBLICATION_ARCHITECTURE_BYTES_PER_FAMILY * family_count
    )


# A module packet enumerates that module's declarations, so its size is a
# property of the module a claim happens to name, not of the query. The fixed
# detail budget rejected the assembled certificate kernel outright. Scale it
# with the atlas row count for the module being asked about. A row carries the
# declaration's full statement, measured at about 1.3 KB across the modules this
# gate walks, so the per-declaration allowance is sized from that rather than
# tuned until one module fits.
MODULE_PACKET_BASE_BYTES = 12_000
MODULE_PACKET_BYTES_PER_DECLARATION = 1_400
@lru_cache(maxsize=1)
def atlas_module_declaration_counts() -> dict[str, int]:
    """Load the exhaustive atlas only for full module-packet checks."""
    counts: dict[str, int] = {}
    for row in json.loads(safe_read_text("docs/declaration_atlas.json"))["declarations"]:
        module = row.get("module")
        if module:
            counts[module] = counts.get(module, 0) + 1
    return counts


def module_packet_budget_bytes(module: str) -> int:
    """Return the bounded budget for one module's declaration packet."""
    return max(
        PACKET_BUDGET_BYTES,
        MODULE_PACKET_BASE_BYTES
        + MODULE_PACKET_BYTES_PER_DECLARATION
        * atlas_module_declaration_counts().get(module, 0),
    )


AGENT_TOUR_BUDGET_BYTES = query_corpus.agent_tour_budget_bytes(
    INDEXED_PROBLEM_COUNT, REMAINING_OPEN_PROPOSITION_COUNT
)
PROOF_AUTHORITY = "Lean source checked by the pinned Lean kernel"
SELF_APPRAISAL_PHRASES = (
    "ambitious",
    "crazy good",
    "exceptional",
    "extraordinary",
    "groundbreaking",
    "impressive",
    "insane",
    "major achievement",
    "research-grade",
    "unprecedented",
)
GATEWAY_PAPER = "paper/erdos249-257-main-paper.tex"
# The slice includes the introduction and both exact proof spines through page 3.
# 2026-09-02: raised from 12,000 to the measured size of that slice. The pin was
# set when this manuscript was the live reading route; it is now kept for archive
# and provenance and the eight per-problem notes are the route a reader is sent
# to, so shortening an archived introduction to fit a ceiling would edit the
# record rather than improve a front door. The assertions around this one still
# hold the opening to no self-appraisal and no visible implementation path.
GATEWAY_OPENING_BUDGET_BYTES = 15_000
CLAUDE_ENTRY_BUDGET_BYTES = 1_500
STORY_ROUTES = (
    "erdos257_half_story",
    "erdos249_certificate_story",
    "structured_support_families",
    "erdos249_diagonal_arithmetic",
    "boolean_mobius_constraints",
    "transport_curvature_programme",
    "lambert_obstruction_interfaces",
    "probabilistic_gcd_geometry",
    "half_carry_compactness_programme",
    "arithmetic_obstruction_interfaces",
)
# The first ten are the #257 half story in route order, the rest the #249
# certificate story. The two half-value countermodels below were added to the
# route and not here, so the pinned prefix stopped matching a route that had
# grown more exact.
STORY_CLAIMS = (
    "greedy_achievement_geometry",
    "half_greedy_two_thirds_band",
    "terminal_scaled_vanishing_half_countermodel",
    "cofinal_cylinder_half_countermodel",
    "half_membership_seam_classification",
    "fatal_gap_right_tail_classification",
    "twenty_one_quotient_greedy_frontier",
    "final_middle_cell_escape",
    "final_middle_neg_two_phase_sieve",
    "last_producer_tail_escape_reduction",
    "certificate_reduction",
    "certificate_completeness",
    "first_harmonic_certificate_interface",
    "first_harmonic_pivot_decomposition",
)
DISCOVERY_ROUTE_QUERIES = {
    "how close is problem 249": "erdos249_certificate_story",
    "what remains open for 257": "erdos257_half_story",
    "achievement set topology": "erdos257_half_story",
    "periodic weighted Lambert series": "structured_support_families",
    "diagonal pincer and fresh loss": "erdos249_diagonal_arithmetic",
    "binary carry rigidity": "boolean_mobius_constraints",
    "why local induction fails": "half_carry_compactness_programme",
    "dyadic prefix compression": "half_carry_compactness_programme",
    "first harmonic pivot decomposition": "transport_curvature_programme",
    "strategy countermodels": "transport_curvature_programme",
    "Mersenne Lambert identities": "lambert_obstruction_interfaces",
    "what probability and gcd identities are formalized": "probabilistic_gcd_geometry",
    "what Stern Brocot or continued fraction geometry is proved": "probabilistic_gcd_geometry",
    "what exact run geometry is proved": "probabilistic_gcd_geometry",
    "formal proof trust": "change_or_verify_release",
    "denominator obstruction": "arithmetic_obstruction_interfaces",
    "how big is the corpus": "instant_orientation",
    "what is formally checked": "instant_orientation",
    "what other exact mathematics is there": "instant_orientation",
    "what else is formally checked besides Erdos 249 and 257": "instant_orientation",
    "what is proved": "browse_claim_status",
    "what is formalised": "browse_claim_status",
    "what is formalized": "browse_claim_status",
    "which results are unconditional progress": "browse_claim_status",
    "what is reduced": "browse_claim_status",
    "what is computed": "browse_claim_status",
    "show verified finite computations": "browse_claim_status",
    "show conditional reductions": "browse_claim_status",
    "which claims are cited only": "browse_claim_status",
    "list open claims": "browse_claim_status",
    "where are the Lean proofs": "follow_one_claim",
    "what is new mathematics": "trace_prior_art",
    "how do I verify this": "change_or_verify_release",
    "what is still missing": "understand_methodology_and_open_boundary",
    "what remains open": "understand_methodology_and_open_boundary",
}
DISCOVERY_MULTI_ROUTE_QUERIES = {
    "what is ruled out": {
        "transport_curvature_programme",
        "lambert_obstruction_interfaces",
        "arithmetic_obstruction_interfaces",
    }
}
PROOF_PLAN_QUERIES = {
    "blocked_integer_tail": (
        "I need to prove totientTail (N + h) - totientTail N is an integer "
        "from a rational totient series; which theorem applies?"
    ),
    "context_ready_curvature": (
        "I need to prove Irrational (∑' n : ℕ, "
        "(Nat.totient n : ℝ) / 2 ^ n) from a SharpCurvatureSupply"
    ),
}


@lru_cache(maxsize=None)
def read(rel: str) -> str:
    """Read each immutable committed surface once per validation process."""
    return safe_read_text(rel)


def quick_summary() -> dict[str, Any]:
    """Load the committed bounded projection without spawning corpus queries."""
    orientation = json.loads(read("docs/orientation.json"))
    return {
        "remaining_open_propositions": orientation["remaining_open_propositions"],
        "status_taxonomy": orientation["status_taxonomy"],
        "mathematical_programmes": orientation["mathematical_programmes"],
    }


def validate_route_memory_descriptor(descriptor: dict[str, Any]) -> None:
    """Keep the CI first-contact descriptor bound to the route-memory rail."""
    compact_graph = descriptor.get("compact_graph")
    if not isinstance(compact_graph, dict):
        raise AssertionError("corpus descriptor compact graph is missing")
    contract = compact_graph.get("route_memory_contract")
    if not isinstance(contract, dict):
        raise AssertionError("corpus descriptor route-memory contract is missing")
    expected_query = (
        "python3 scripts/query_route_memory.py --problem <problem_number> "
        "[--route <mathematical_programme_id>]"
    )
    if compact_graph.get("route_memory_query") != expected_query:
        raise AssertionError("corpus descriptor route-memory query drifted")
    if contract.get("selector_source") != "docs/problems.json::problems.erdos_number":
        raise AssertionError("corpus descriptor route-memory selector source drifted")
    if contract.get("problem_selectors") != list(INDEXED_PROBLEM_ORDER):
        raise AssertionError("corpus descriptor route-memory selector coverage drifted")
    if contract.get("validate") != (
        "python3 scripts/query_route_memory.py --validate <packet.json>"
    ):
        raise AssertionError("corpus descriptor route-memory validation command drifted")
    if contract.get("authority_posture") != (
        "derived_navigation_resume_state_not_claim_or_proof_authority"
    ):
        raise AssertionError("corpus descriptor route-memory authority boundary drifted")
    if set(contract.get("rejections", [])) != {
        "stale_source_snapshot",
        "cross_problem_route_or_declaration",
        "invented_reference",
        "resume_state_mismatch",
    }:
        raise AssertionError("corpus descriptor route-memory rejection contract drifted")
    if descriptor.get("capabilities", {}).get("claim_first_route_memory_resume") is not True:
        raise AssertionError("corpus descriptor route-memory capability is not advertised")
    problem_index = descriptor.get("expansion", {}).get("problem_index")
    if not isinstance(problem_index, dict) or problem_index.get("path") != "docs/problems.json":
        raise AssertionError("corpus descriptor problem-index expansion drifted")


def check_route_memory_descriptor() -> None:
    validate_route_memory_descriptor(json.loads(read("docs/corpus_descriptor.json")))


def run_child(
    command: list[str], *, cwd: Path = ROOT
) -> subprocess.CompletedProcess[str]:
    """Run a cold-clone child without ambient process state or hangs."""
    return subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )


def check_semantic_corpus_freshness() -> dict[str, Any]:
    """Return an exact receipt, rebuilding only when the receipt cannot prove freshness."""
    receipt = build_semantic_corpus.load_cached_check()
    if receipt is not None:
        return receipt
    completed = run_child(
        [
            sys.executable,
            str(ROOT / "scripts" / "build_semantic_corpus.py"),
            "--check",
            "--full-check",
        ],
        cwd=ROOT,
    )
    require(completed.returncode == 0, completed.stdout.strip() or completed.stderr.strip())
    receipt = build_semantic_corpus.load_cached_check()
    require(receipt is not None, "semantic corpus full check produced no exact receipt")
    return receipt


def encoded_bytes(value: Any) -> int:
    return len(json.dumps(value, ensure_ascii=False, sort_keys=True).encode("utf-8"))


def query_packet(*args: str, budget_bytes: int = PACKET_BUDGET_BYTES) -> dict[str, Any]:
    """Exercise the public CLI parser while reusing its immutable JSON caches.

    A cold agent process naturally keeps loaded projections in memory across a
    navigation session. Spawning one Python process per assertion made the
    evaluator repeatedly parse the exhaustive declaration atlas and measured
    process-start overhead rather than comprehension. The full check retains a
    real external-process smoke below; this hot path uses the same parser and
    dispatch as ``main`` while retaining the packet before output encoding.
    """
    packet, output_format = query_corpus.query_args_packet(args)
    require(output_format == "json", "cold-clone packet query selected card output")
    raw = (json.dumps(packet, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    require(len(raw) <= budget_bytes, f"query {' '.join(args) or '<summary>'} emitted {len(raw)} bytes "
        f"(budget {budget_bytes})")
    return packet


def validate_query_cli_process_smoke() -> None:
    """Prove each installed query script works as a standalone cold process."""
    smoke_commands = (
        (
            [sys.executable, str(QUERY), "--route", "agent_native_corpus_navigation"],
            lambda packet: packet.get("kind") == "reading_route"
            and packet.get("route", {}).get("id") == "agent_native_corpus_navigation",
        ),
        (
            [sys.executable, str(SEMANTIC_QUERY), "problem-registry", "--limit", "1"],
            lambda packet: packet.get("returned_problem_count") == 8
            and isinstance(packet.get("problems"), list),
        ),
        (
            [sys.executable, str(EXPERT_HANDOFF_QUERY)],
            lambda packet: isinstance(packet.get("results"), list),
        ),
    )
    for command, accepts in smoke_commands:
        completed = run_child(command, cwd=ROOT.parent)
        if completed.returncode != 0:
            raise AssertionError(completed.stdout.strip() or completed.stderr.strip())
        require(accepts(json.loads(completed.stdout)), "cold-clone comprehension invariant")


def _in_process_query_main(module: Any, args: tuple[str, ...]) -> tuple[int, str, str]:
    """Exercise a CLI parser while retaining immutable projection caches."""
    stdout = io.StringIO()
    stderr = io.StringIO()
    previous_argv = sys.argv
    try:
        sys.argv = [str(module.__file__), *args]
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            return_code = module.main()
    finally:
        sys.argv = previous_argv
    return return_code, stdout.getvalue(), stderr.getvalue()


def semantic_query_packet(
    *args: str, budget_bytes: int = PACKET_BUDGET_BYTES
) -> dict[str, Any]:
    """Exercise the semantic CLI without reparsing its atlas for every assertion."""
    return_code, stdout, stderr = _in_process_query_main(query_semantic, args)
    if return_code != 0:
        raise AssertionError(stdout.strip() or stderr.strip())
    raw = stdout.encode("utf-8")
    require(len(raw) <= budget_bytes, f"semantic query {' '.join(args)} emitted {len(raw)} bytes "
        f"(budget {budget_bytes})")
    return json.loads(stdout)


def expert_handoff_packet(
    *args: str, budget_bytes: int = PACKET_BUDGET_BYTES
) -> dict[str, Any]:
    """Exercise expert-handoff parsing while retaining immutable input caches."""
    return_code, stdout, stderr = _in_process_query_main(query_expert_handoffs, args)
    if return_code != 0:
        raise AssertionError(stdout.strip() or stderr.strip())
    raw = stdout.encode("utf-8")
    require(len(raw) <= budget_bytes, f"expert-handoff query {' '.join(args) or '<default>'} emitted "
        f"{len(raw)} bytes (budget {budget_bytes})")
    return json.loads(stdout)


def check_expert_handoff_protocol() -> str:
    """Run the cross-domain protocol's own structural self-check."""
    return_code, stdout, stderr = _in_process_query_main(
        query_expert_handoffs, ("--check",)
    )
    if return_code != 0:
        raise AssertionError(stdout.strip() or stderr.strip())
    return stdout.strip()


def human_tasks(summary: dict[str, Any]) -> dict[str, list[list[str]]]:
    """Facts a reader must recover from the bounded README first contact.

    Each task contains conjunctions of semantic anchor groups.  Alternatives
    within one group permit harmless wording changes; satisfying one task with
    tokens scattered across three documents is deliberately impossible.
    """
    open_rows = {row["id"]: row for row in summary["remaining_open_propositions"]}
    return {
        "identity_and_public_boundary": [
            ["self-contained public"],
            ["Plectis"],
            ["not an entrypoint into any private development system"],
        ],
        "state_problem_frontier": [
            ["All eight problems remain open"],
            ["S = ∑ φ(n)/2ⁿ"],
            ["∑_{n∈A} 1/(2ⁿ - 1)"],
            ["every infinite", "for every infinite"],
        ],
        "recover_blank_slate_problem_card": [
            ["#68"],
            ["n!−1", "n!-1"],
            ["#243"],
            ["rapidly growing"],
            ["Sylvester recurrence"],
            ["#249"],
            ["∑ φ(n)/2ⁿ"],
            ["#251"],
            ["∑ p_n/2ⁿ"],
            ["#257"],
            ["every infinite"],
            ["#269"],
            ["running lcms"],
            ["#1041"],
            ["lemniscate"],
            ["#1049"],
            ["rational bases"],
            ["no query is required"],
            ["does not require `ai_workflow`", "does not require ai_workflow"],
        ],
        "distinguish_release_source_and_authority": [
            ["latest tagged release and citation anchor"],
            ["formal-source checkpoint"],
            ["this release ships", "not a new tagged release"],
            [PROOF_AUTHORITY],
        ],
        "recover_headline_statuses": [
            ["formalised here"],
            ["conditional reduction"],
            ["verified finite instance"],
            ["does not show that the actual orbit avoids", "does not show the actual orbit avoids"],
            ["does not prove successful cases beyond every fixed cutoff"],
        ],
        "recover_farey_boundary": [
            ["classical Farey/mediant bound"],
            ["Farey's method supplies the number directly"],
            ["numerical delta `0`", "numerical delta 0"],
            ["exactly the Farey bound, not an improvement"],
        ],
        "recover_breadth_beyond_headlines": [
            ["eventually-periodic nonnegative weighted irrationality"],
            ["signed irrational-or-base-terminating dichotomy"],
            [
                "five binary-carry criteria/consequences",
                "five binary-carry criteria or consequences",
            ],
            ["two scoped #249 no-go countermodels"],
        ],
        "recover_independent_exact_packages": [
            ["fair-coin coprimality", "P(gcd(X,Y)=1)"],
            ["squared-Lambert gcd moments"],
            ["Stern–Brocot cylinder law"],
            ["(2/3)^d"],
            ["Fibonacci/continuant run stability"],
            ["F_{r+3}"],
            ["tempered binary tail rigidity"],
            ["exact Möbius-shadow denominator"],
            ["scalar-localisation height obstruction"],
        ],
        "recover_scale_and_assembly": [
            ["Lean modules"],
            ["Formal results and supporting lemmas"],
            ["Curated claim records"],
            ["Contribution families"],
            ["navigation counts, not novelty claims"],
        ],
        "name_exact_open_frontier": [
            [open_rows["remaining_open.erdos_249_irrationality"]["statement"],
             "Prove that `S = ∑ φ(n)/2ⁿ` is irrational"],
            [open_rows["remaining_open.unbounded_certificate_supply"]["statement"],
             "Produce the unbounded certificate supply"],
            [open_rows["remaining_open.universal_257_all_infinite_supports"]["statement"],
             "Prove irrationality of `∑_{n∈A} 1/(2ⁿ - 1)` for every infinite"],
        ],
        "route_exact_expert_handoffs": [
            ["exact expert handoffs"],
            ["what input is requested"],
            ["current guess"],
            ["alternatives"],
            ["discriminating evidence"],
            ["checked consumer"],
            ["endpoint-or-counterexample boundary"],
            ["python3 scripts/query_expert_handoffs.py"],
        ],
        "choose_a_next_read": [
            # The anchor is "a route into the manuscripts exists", not the name
            # of one manuscript. This read ["Exposition PDF"] alone, which is
            # the label of the joint #249/#257 paper -- the single manuscript
            # docs/papers/corpus.json records as retired, whose "problem-specific
            # successors are the active reader routes". So the gate required the
            # reader's next-read bullet to name the superseded paper, and
            # naming the live per-problem route instead failed it.
            ["per-problem papers", "Exposition PDF", "joint PDF", "docs/papers"],
            ["AGENTS.md"],
            ["docs/orientation.json"],
            ["docs/SOURCE_MAP.md"],
        ],
        "navigate_without_compiling": [
            ["Whole-corpus agent navigation"],
            ["without a Lean build"],
            ["--tour --format card"],
            ["corpus scale"],
            ["mathematical map"],
            ["canonical eight-problem map"],
            ["problem-registry"],
            [
                "distinct reviewed #249/#257 open-proposition frontier",
                "exact open frontier",
            ],
            ["agent_native_corpus_navigation"],
            ["every indexed declaration"],
            ["exact dependencies for both loaded roots"],
            ["navigation projections, not proof authority"],
        ],
    }


def first_bytes(text: str, limit: int) -> str:
    return text.encode("utf-8")[:limit].decode("utf-8", errors="ignore")


def normalized(text: str) -> str:
    return " ".join(text.split())


def contains_any(text: str, alternatives: list[str]) -> bool:
    compact = normalized(text).casefold()
    return any(normalized(token).casefold() in compact for token in alternatives)


def validate_incremental_build_contract(surfaces: dict[str, str]) -> None:
    """Keep cache reuse, focused rebuilding, and the cold-clone boundary aligned."""
    require(set(surfaces) == set(INCREMENTAL_BUILD_SURFACES), "cold-clone comprehension invariant")
    readme = surfaces["README.md"] + "\n" + surfaces["docs/AGENT_WORKBENCH.md"]
    readme_flat = normalized(readme)
    runbook = surfaces["docs/REPRODUCIBILITY.md"]
    workflow = surfaces[".github/workflows/lean.yml"]
    planner = surfaces["scripts/lean_fast_build.py"]
    build_job = re.search(
        r"(?ms)^  build:\n(?P<body>.*?)(?=^  [A-Za-z0-9_-]+:\n|\Z)",
        workflow,
    )
    require(build_job is not None, "Lean CI lost its build job")
    build_job_body = build_job.group("body") if build_job is not None else ""

    for token in (
        "A cold clone can navigate before this step",
        "--lake-staleness",
        "--changed-from <git-ref>",
        "rebuild only the selected or stale dependency cone",
    ):
        require(normalized(token) in readme_flat, f"README lost incremental-build contract: {token}")

    # The detailed build contract belongs to the reproducibility runbook. Keep
    # its prerequisite before its first build command without forcing those
    # commands above the paper index on the repository front page.
    toolchain_guide = runbook.find(
        "https://leanprover-community.github.io/get_started.html"
    )
    first_build_command = runbook.find("python3 scripts/lean_fast_build.py --jobs 2")
    require(toolchain_guide >= 0, "reproducibility runbook no longer tells a reader where the Lean toolchain comes from")
    require(first_build_command >= 0, "reproducibility runbook lost its coordinated Lean build command")
    require(toolchain_guide < first_build_command, "reproducibility runbook names the Lean setup guide only after the first build command; "
        "a reader without elan hits `command not found` before they reach it")
    first_build_block_end = runbook.find("```", first_build_command)
    require(
        first_build_block_end > first_build_command
        and "ErdosProblems.Erdos249.PeriodMultipleEscape"
        in runbook[first_build_command:first_build_block_end],
        "reproducibility runbook makes a full-corpus build the first Lean success path",
    )
    require("elan" in readme, "README no longer names Lean's toolchain manager")
    require(
        re.search(r"(?m)^\s*lake build\b", runbook) is None,
        "reproducibility runbook bypasses the host-shared Lean build wrapper",
    )
    require(
        all(
            target in runbook
            for target in (
                "Erdos249257",
                "ErdosProblems",
                "Examples",
                "FormalConjecturesAdapter",
                "FormalConjecturesVariants",
                "ResidualBench",
            )
        ),
        "reproducibility runbook lost a supported public build target",
    )
    focused_replay = runbook.find("ErdosProblems.Erdos249.PeriodMultipleEscape")
    complete_replay = runbook.find("Erdos249257 ErdosProblems")
    require(
        0 <= focused_replay < complete_replay,
        "runbook must offer a focused Lean success before the complete release replay",
    )
    require(
        "fetches the pinned cache when needed" in readme_flat,
        "README no longer states that the build wrapper owns cache acquisition",
    )

    # Every token below describes something the workflow *does*. "# v5" sat in
    # this list too, and it describes only which version of the cache action
    # was current when the list was written — so a routine bump to v6 failed
    # this check with "Lean CI lost cache/build contract", naming a contract
    # that had not changed. The policy is asserted below instead: pinned to a
    # commit, annotated with the version that commit is.
    for token in (
        "uses: actions/cache@",
        "path: .lake",
        "restore-keys:",
        # Two workers, not four: four exhausted the runner while compiling
        # FactorialZeroPlateau.
        "python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness",
        "python3 scripts/build_lean_dependency_index.py --check --full-check",
        "No Lean source or proof-environment input changed; compilation is unchanged.",
    ):
        require(token in workflow, f"Lean CI lost cache/build contract: {token}")

    unpinned = [
        line.strip()
        for line in workflow.splitlines()
        if line.strip().startswith(("- uses: actions/", "uses: actions/"))
        and not re.search(r"uses: actions/[\w-]+(?:/[\w-]+)*@[0-9a-f]{40} # v[\d.]+$", line.strip())
    ]
    require(not unpinned, "Lean CI uses an action that is not pinned to a commit with a version "
        "comment, so a reader cannot tell what it resolves to: "
        + "; ".join(unpinned))
    require(
        re.search(
            r"^\s*run:\s*python3 scripts/check_cold_clone_comprehension\.py\s*$",
            workflow,
            re.M,
        )
        is None,
        "Lean CI repeats the standalone cold-clone baseline after the release "
        "gate already runs the combined baseline-plus-adversarial program",
    )
    require(
        len(re.findall(r"(?m)^\s*run:\s*python3 scripts/lean_fast_build\.py\b", build_job_body))
        == 1,
        "Lean CI must have exactly one coordinated build-wrapper owner",
    )
    require(
        re.search(r"(?m)^\s*run:\s*lake build\b", build_job_body) is None,
        "Lean CI launches a duplicate raw Lake build outside the wrapper",
    )
    for target in (
        "Erdos249257",
        "ErdosProblems",
        "Examples",
        "FormalConjecturesAdapter",
        "FormalConjecturesVariants",
        "ResidualBench",
    ):
        require(target in build_job_body, f"Lean CI wrapper lost target {target}")

    for token in (
        '"--changed-from"',
        '"--lake-staleness"',
        "final serialized Lake authority check",
        "no changed Lean modules relative to",
    ):
        require(token in planner, f"build planner lost incremental contract: {token}")


# What the README's opening tells a reader the first command will show, and the
# marker in that command's actual output that makes the promise true. Every link
# checker in this repository would stay green while these drifted apart, because
# nothing here is a link: the README describes *output*, and output changes
# without the sentence describing it changing. The 2026-08-16 instance was the
# reverse direction — the command started naming the Comparator interface and
# the write-up, and the sentence still said it printed the statement, the source
# and the receipts.
FIRST_COMMAND_PROMISES = (
    ("Comparator interface", ("SECOND FORMAL CHECK", "[BOUND]")),
    ("the paper that", ("WRITTEN UP IN", "paper/")),
    ("re-resolves the declaration", ("SOURCE (", "re-resolved in this checkout")),
    ("release receipts", ("RECEIPTS",)),
    ("where the claim\nstops", ("WHERE THIS CLAIM STOPS",)),
)

# The exact invocation the README puts in front of a reader who has not decided
# to read yet. Running any other one would test a command nobody was offered.
FIRST_COMMAND_ARGV = ("--claim", "eb_full_support")


def validate_first_command_keeps_its_promise(readme_prefix: str) -> None:
    """Run the advertised first command and require the promised output.

    A promise is only checked when the README still makes it, because dropping a
    capability and its description together is a coherent change. What must never
    happen is the description outliving the behaviour.
    """
    completed = run_child(
        [sys.executable, "scripts/verify_claims.py", *FIRST_COMMAND_ARGV],
        cwd=ROOT,
    )
    require(completed.returncode == 0, "the command the README puts on its first screen exits "
        f"{completed.returncode}: {(completed.stderr or completed.stdout).strip()[:300]}")
    output = completed.stdout
    for promise, markers in FIRST_COMMAND_PROMISES:
        if promise not in readme_prefix:
            continue
        for marker in markers:
            require(marker in output, f"README's first screen promises {promise!r}, but "
                f"`verify_claims.py {' '.join(FIRST_COMMAND_ARGV)}` prints no "
                f"{marker!r}; the description has outlived the behaviour")


def validate_human_first_contact(
    summary: dict[str, Any], surfaces: dict[str, str]
) -> None:
    require(set(surfaces) == set(HUMAN_SURFACES), "cold-clone comprehension invariant")
    for path, budget in HUMAN_SURFACE_BUDGET_BYTES.items():
        size = len(surfaces[path].encode("utf-8"))
        require(size <= budget, f"{path} is {size} bytes (budget {budget})")
        lowered = normalized(surfaces[path]).casefold()
        for phrase in SELF_APPRAISAL_PHRASES:
            require(phrase not in lowered, f"{path} uses self-appraisal phrase {phrase!r}; expose objective "
                "mathematical and formal facts instead")

    check_architecture_guide.validate_guide(surfaces["ARCHITECTURE.md"])

    readme_prefix = first_bytes(surfaces["README.md"], README_FIRST_CONTACT_BUDGET_BYTES)
    reproducibility = safe_read_text("docs/REPRODUCIBILITY.md")
    contribution_guide = safe_read_text("CONTRIBUTING.md")
    require(
        "[REPRODUCIBILITY](docs/REPRODUCIBILITY.md)" in readme_prefix,
        "README no longer routes detailed clone and build work to REPRODUCIBILITY",
    )
    require(
        "[CONTRIBUTING](CONTRIBUTING.md)" in readme_prefix,
        "README no longer routes corrections and returned work to CONTRIBUTING",
    )
    for command in (
        "git clone --filter=blob:none",
        "python3 scripts/lean_fast_build.py --jobs 2",
        "python3 scripts/check_cold_clone_comprehension.py --quick",
    ):
        require(
            command in reproducibility,
            f"reproducibility runbook lost executable route {command!r}",
        )
    require(
        "plain-language research-progress" in contribution_guide
        and "open a pull request" in contribution_guide,
        "contribution guide lost its no-patch and focused-patch return routes",
    )

    # The front page should answer what the project contains before asking a
    # mathematician to choose a checkout. Operational detail stays directly
    # reachable through the runbook and is tested there above.
    section_order = (
        "## Problem papers",
        "## What the checks establish",
        "## Contribute",
        "## Read or verify locally",
    )
    positions = [readme_prefix.find(heading) for heading in section_order]
    require(all(position >= 0 for position in positions), f"README first-contact surface lost section sequence {section_order}")
    require(positions == sorted(positions), "README first-contact sections are out of order")

    first_command_block = readme_prefix.find("```")
    last_problem = readme_prefix.find("**#1049**", positions[0])
    require(first_command_block >= 0, "README first-contact surface lost its bounded local check")
    require(
        last_problem >= positions[0] and first_command_block > last_problem,
        "README asks for a shell decision before exposing all eight papers",
    )
    require(
        "![Eight open problems:" in readme_prefix[:positions[0]]
        and "](.github/system-map.png)" in readme_prefix[:positions[0]],
        "README opening lost the mathematical research-record banner",
    )
    require(
        "#257" in readme_prefix[:last_problem]
        and "#249" in readme_prefix[:last_problem]
        and "For a first look" in readme_prefix[:last_problem],
        "README no longer recommends a concrete first paper",
    )
    validate_first_command_keeps_its_promise(readme_prefix)

    require("[agent-navigation paper](cold-clone-to-proof-receipt.pdf)"
        in readme_prefix, "README no longer exposes the cold-clone-to-proof-receipt paper")
    for problem, filename in (
        ("#68", "erdos-68-factorial-denominator-irrationality.pdf"),
        ("#243", "erdos-243-reciprocal-tail-rigidity.pdf"),
        ("#249", "erdos-249-binary-totient-series.pdf"),
        ("#251", "erdos-251-prime-gap-dyadic-series.pdf"),
        ("#257", "erdos-257-mersenne-support-subseries.pdf"),
        ("#269", "erdos-269-three-prime-running-lcm.pdf"),
        ("#1041", "erdos-1041-lemniscate-newton-flow.pdf"),
        ("#1049", "erdos-1049-rational-base-lambert.pdf"),
    ):
        require(problem in readme_prefix and f"]({filename})" in readme_prefix, f"README no longer exposes the individual Erdős {problem} paper")
    for filename in (
        "erdos249-totient-reasoning-surface.pdf",
        "erdos257-mersenne-reasoning-surface.pdf",
    ):
        require(f"]({filename})" in readme_prefix, f"README no longer exposes the full reasoning record {filename}")

    problem_portfolio = readme_prefix.find("## Problem papers")
    raw_inventory = readme_prefix.find("## Corpus at a glance")
    require(problem_portfolio >= 0, "README lost the all-problem discovery surface")
    require(raw_inventory >= 0, "README lost the raw corpus-inventory boundary")
    problem_positions = [
        readme_prefix.find(f"**#{problem}**", problem_portfolio)
        for problem in sorted(INDEXED_PROBLEM_NUMBERS)
    ]
    require(
        all(position >= problem_portfolio for position in problem_positions),
        "README no longer exposes every indexed problem before inventory",
    )
    require(
        all(position < raw_inventory for position in problem_positions),
        "README places raw scale or numeric inventory before all-problem discovery",
    )

    # The README is the human front door and is held to a word budget, so the
    # recoverable detail a cold reader needs is not all on the front page any
    # more. It is on the two documents the front page routes to by name, and it
    # was moved there verbatim rather than rewritten. Searching the front page
    # together with those routed documents keeps the property that matters --
    # a cold reader following the README can still recover every one of these
    # statements -- while allowing the front page itself to stay short. Adding a
    # document here is not free: it has to be one the README names.
    routed_first_contact = "\n".join(
        [readme_prefix]
        + [safe_read_text(path) for path in FIRST_CONTACT_ROUTED_SURFACES]
    )
    for path in FIRST_CONTACT_ROUTED_SURFACES:
        require(
            path in readme_prefix,
            f"README no longer routes its first-contact reader to {path}",
        )
    for task_id, requirements in human_tasks(summary).items():
        for alternatives in requirements:
            require(contains_any(routed_first_contact, alternatives), f"README first-contact task {task_id!r} lost semantic anchor group "
                f"{alternatives}")

    scope = surfaces["SCOPE.md"]
    require(contains_any(scope, ["does not prove", "does not solve"]), "cold-clone comprehension invariant")
    require(contains_any(scope, ["formal-source checkpoint"]), "cold-clone comprehension invariant")
    orientation = surfaces["docs/ORIENTATION.md"]
    for status in (
        "formalised here",
        "unconditional progress",
        "conditional reduction",
        "verified finite instance",
    ):
        require(contains_any(orientation, [summary["status_taxonomy"][status]]), "cold-clone comprehension invariant")
    for row in summary["remaining_open_propositions"]:
        require(row["id"] in orientation and contains_any(orientation, [row["statement"]]), "cold-clone comprehension invariant")
    for programme in summary["mathematical_programmes"]:
        require(programme["id"] in orientation, "cold-clone comprehension invariant")
        require(contains_any(orientation, [programme["title"]]), "cold-clone comprehension invariant")
        require(contains_any(orientation, [programme["claim_ceiling"]]), "cold-clone comprehension invariant")


def validate_paper_library_first_contact(
    paper_readme: str, *, ranking: list[dict[str, Any]] | None = None
) -> None:
    """Ensure the generated paper shelf leads with canonical mathematical signal.

    The exporter owns the prose; this consumer only checks the public contract:
    Palomar's ranked families come before the complete inventory, and the
    generated shelf keeps represented friction and subordinate/long-tail
    boundaries visible.  Ranking authority is loaded from the committed
    Palomar showcase rather than duplicated here.
    """
    require(
        len(paper_readme.encode("utf-8")) <= PAPER_LIBRARY_FIRST_CONTACT_BUDGET_BYTES,
        "paper-library README exceeds its bounded first-contact budget",
    )
    if ranking is None:
        showcase = json.loads(read("docs/PALOMAR_RESULT_SHOWCASE.json"))
        ranking = showcase.get("candidate_ranking")
    require(isinstance(ranking, list) and ranking, "Palomar candidate ranking is missing")
    signal_heading = paper_readme.find("## Mathematical signal first")
    ranked_heading = paper_readme.find("### Ranked frontier")
    friction_heading = paper_readme.find("### Represented natural friction")
    long_tail_heading = paper_readme.find(
        "### Explicitly subordinate, rejected, and long tail"
    )
    inventory_match = re.search(r"^## Problem portfolio \(complete \d+-paper inventory\)$", paper_readme, re.MULTILINE)
    inventory_heading = inventory_match.start() if inventory_match else -1
    positions = (
        signal_heading,
        ranked_heading,
        friction_heading,
        long_tail_heading,
        inventory_heading,
    )
    require(
        all(position >= 0 for position in positions),
        "paper-library README lost signal, friction, long-tail, or inventory headings",
    )
    require(
        list(positions) == sorted(positions),
        "paper-library README moved exhaustive inventory ahead of mathematical signal",
    )
    paper_flat = normalized(paper_readme)
    require("candidate_ranking" in paper_flat,
            "paper-library README lost Palomar ranking authority")
    require(
        (
            "not a proof, novelty, or closure claim" in paper_flat
            or "not a proof, novelty, review, or closure claim" in paper_flat
        ),
        "paper-library README lost Palomar evidence boundary",
    )
    ranked_candidates = sorted(ranking, key=lambda row: row.get("rank", 0))
    ranks = [candidate.get("rank") for candidate in ranked_candidates]
    require(
        all(isinstance(rank, int) and rank > 0 for rank in ranks),
        "Palomar candidate ranking has a non-positive or malformed rank",
    )
    require(
        len(ranks) == len(set(ranks)),
        "Palomar candidate ranking reuses an explicit rank",
    )
    previous = -1
    marker_positions: list[int] = []
    for candidate in ranked_candidates:
        rank = candidate.get("rank")
        family_id = candidate.get("family_id")
        declaration = candidate.get("declaration")
        require(isinstance(rank, int) and isinstance(family_id, str) and family_id,
                "Palomar candidate ranking row is malformed")
        require(
            isinstance(declaration, str) and declaration,
            f"Palomar candidate {family_id} lacks its checked declaration",
        )
        for field in (
            "evidence_certainty",
            "overclaim_risk",
            "mechanism_depth_and_natural_friction",
        ):
            require(
                isinstance(candidate.get(field), str) and candidate[field].strip(),
                f"Palomar candidate {family_id} lacks {field}",
            )
        marker = f"#### {rank}."
        marker_position = paper_readme.find(marker, ranked_heading)
        require(
            marker_position >= 0 and marker_position > previous,
            f"paper-library README lost canonical ranked family {family_id}",
        )
        family_position = paper_readme.find(f"`{family_id}`", marker_position)
        require(
            family_position >= marker_position and family_position < friction_heading,
            f"paper-library README detached ranked family {family_id} from frontier",
        )
        marker_positions.append(marker_position)
        previous = marker_position

    for index, candidate in enumerate(ranked_candidates):
        entry_end = (
            marker_positions[index + 1]
            if index + 1 < len(marker_positions)
            else friction_heading
        )
        entry = paper_readme[marker_positions[index]:entry_end]
        # The exporter owns this prose and renamed three of its labels; the
        # fields themselves are all still there. This consumer checks that each
        # ranked family still carries its interface, its source declaration, the
        # mechanism, the evidence ceiling and the boundary, under the names the
        # shelf actually prints.
        for label in (
            "**Checked interface:**",
            "**Source declaration:**",
            "**Hard mechanism:**",
            "**Evidence:**",
            "**Boundary:**",
        ):
            require(
                label in entry,
                f"paper-library README ranked family {candidate['family_id']} lost {label}",
            )
        require(
            candidate["declaration"] in entry,
            f"paper-library README ranked family {candidate['family_id']} lost its exact checked interface",
        )


def semantic_census_from_public(public: dict[str, Any]) -> dict[str, Any]:
    """Project the compact public census recorded by the semantic builder."""
    return {
        "indexed_problem_ids": public["indexed_problem_ids"],
        "nonrecurring_total": public["nonrecurring"]["total"],
        "nonrecurring_by_problem": Counter(public["nonrecurring"]),
        "nonrecurring_by_class": Counter(
            public["nonrecurring_by_logical_class"]
        ),
        "nonrecurring_not_assessed": public[
            "nonrecurring_prior_art_not_assessed_count"
        ],
        "bare_total": public["bare_equivalences"]["total"],
        "bare_by_problem": Counter(public["bare_equivalences"]),
        "classical_total": public["classical"]["total"],
        "classical_by_problem": Counter(public["classical"]),
        "reviewed_frontier_shortlist_count": public[
            "reviewed_frontier_shortlist_count"
        ],
        "prior_art_review_queue_count": public[
            "prior_art_review_queue_count"
        ],
        "open_antecedent_cluster_total": public[
            "open_antecedent_cluster_count"
        ],
        "open_antecedent_equivalent_total": public[
            "open_antecedent_endpoint_equivalent_count"
        ],
        "demand_lattice_counts": public["demand_lattice_counts"],
        "demand_equivalent_total": public["demand_equivalent_total"],
        "demand_equivalent_by_problem": Counter(
            public["demand_equivalent_by_problem"]
        ),
    }


def semantic_census(receipt: dict[str, Any] | None = None) -> dict[str, Any]:
    """Read the compact exact receipt, or fall back to the exhaustive graph."""
    if receipt is not None:
        return semantic_census_from_public(
            receipt["summary"]["public_semantic_census"]
        )
    corpus = json.loads(read("docs/semantic_corpus.json"))
    return semantic_census_from_public(
        corpus["summary"]["public_semantic_census"]
    )


def validate_public_semantic_census(
    census: dict[str, Any], surfaces: dict[str, str]
) -> None:
    """Keep authored public snapshots synchronized with the live graph."""
    require(set(surfaces) == set(CENSUS_SURFACES), "cold-clone comprehension invariant")
    nonrecurring = census["nonrecurring_by_problem"]
    classes = census["nonrecurring_by_class"]
    bare = census["bare_by_problem"]
    classical = census["classical_by_problem"]
    total = census["nonrecurring_total"]
    unassessed = census["nonrecurring_not_assessed"]
    demand = census["demand_lattice_counts"]
    demand_equivalent = census["demand_equivalent_total"]
    demand_equivalent_by_problem = census[
        "demand_equivalent_by_problem"
    ]
    open_cluster_total = census["open_antecedent_cluster_total"]
    open_cluster_equivalent = census[
        "open_antecedent_equivalent_total"
    ]
    scopes = (
        *census["indexed_problem_ids"],
        "both",
        "shared_substrate",
        "total",
    )

    def census_row(label: str, row: Counter[str]) -> str:
        return (
            f"| {label} | "
            + " | ".join(str(row[scope]) for scope in scopes)
            + " |"
        )

    expectations = {
        "docs/RESULTS.md": (
            "<!-- BEGIN semantic_public_census -->",
            census_row("mechanically nonrecurring candidates", nonrecurring),
            census_row("classical/prior-art formalisations", classical),
            census_row("bare open-problem equivalences", bare),
            (
                f"The nonrecurring view contains "
                f"{classes['unconditional_object_theorem']} unconditional "
                f"object theorems, {classes['barrier_no_go']} scoped "
                f"barriers, and {classes['reduction_or_transport']} "
                "reductions or transports"
            ),
            f"{unassessed} nonrecurring candidates remain unassessed",
            (
                f"frontier shortlist contains "
                f"{census['reviewed_frontier_shortlist_count']} nodes; it is "
                f"distinct from the {census['prior_art_review_queue_count']}-node "
                "public prior-art review queue"
            ),
            (
                f"Of {demand['substantial']} substantial Lean propositions "
                "extracted from hypotheses of conditional theorems, "
                f"{demand_equivalent} are provably equivalent to an endpoint"
            ),
            (
                f"{demand_equivalent_by_problem['249']} to #249 and "
                f"{demand_equivalent_by_problem['257']} to the `1/2` "
                "membership test for #257"
            ),
            (
                f"open-antecedent surface has {open_cluster_total} clusters, "
                f"of which {open_cluster_equivalent} are marked endpoint-equivalent"
            ),
            "<!-- END semantic_public_census -->",
        ),
        "docs/TRUTH_AUDIT.md": (
            "<!-- BEGIN semantic_public_census -->",
            census_row("mechanically nonrecurring candidates", nonrecurring),
            census_row("classical/prior-art formalisations", classical),
            census_row("bare open-problem equivalences", bare),
            f"{unassessed} nonrecurring candidates remain unassessed",
            (
                f"frontier shortlist contains "
                f"{census['reviewed_frontier_shortlist_count']} nodes; it is "
                f"distinct from the {census['prior_art_review_queue_count']}-node "
                "public prior-art review queue"
            ),
            (
                f"The `{demand_equivalent}/{demand['substantial']}` count is "
                "a narrower kernel-checked audit"
            ),
            (
                f"starts from {demand['conditional_declarations_walked']} "
                "conditional declarations, extracts "
                f"{demand['closed_props_extracted']} distinct closed "
                "hypothesis Props"
            ),
            (
                f"classifies {demand['substantial']} as substantial; "
                f"{demand_equivalent} of those {demand['substantial']} are "
                "endpoint-equivalent"
            ),
            (
                f"lists {open_cluster_total} entries, "
                f"{open_cluster_equivalent} marked endpoint-equivalent"
            ),
            "<!-- END semantic_public_census -->",
        ),
    }
    for path, phrases in expectations.items():
        compact = normalized(surfaces[path])
        for phrase in phrases:
            require(normalized(phrase) in compact, f"{path} semantic census is stale; missing {phrase!r}")


def validate_gateway_opening(paper: str) -> None:
    """Check that the authored introduction works without source inventory."""
    start = paper.index(r"\section{Introduction}")
    end = paper.index(r"\section{Lambert-series identities and comparison values}")
    opening = paper[start:end]
    visible_opening = re.sub(
        r"\\lword\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}\{([^{}]*)\}",
        r"\1",
        opening,
    )
    visible_opening = re.sub(
        r"\\(?:lref|lrefx)\{[^{}]*\}\{[^{}]*\}\{([^{}]*)\}",
        lambda match: re.sub(
            r"(?<=[a-z0-9])(?=[A-Z])",
            " ",
            match.group(1).replace("_", " "),
        ).lower(),
        visible_opening,
    )
    visible_opening = re.sub(
        r"\\lloc\{[^{}]*\}\{[^{}]*\}",
        "Lean source",
        visible_opening,
    )
    size = len(visible_opening.encode("utf-8"))
    require(size <= GATEWAY_OPENING_BUDGET_BYTES, f"visible gateway introduction is {size} bytes "
        f"(budget {GATEWAY_OPENING_BUDGET_BYTES})")
    requirements = {
        "both_problem_statements": [
            [r"is irrational (\#249)"],
            [r"for every infinite $A\subseteq\Npos$ (\#257)"],
        ],
        "status_table": [
            [r"Irrationality in \#249 & Open"],
            [r"Denominator exclusion & Proved"],
            [r"q>\Qzero"],
            # Pins the finite-evidence row to the band the claim record carries.
            # The band moved from 28 deposits through t = 64 to every scale
            # t <= 82; anchoring the old count would enforce an understatement
            # of the checked theorem.
            ["diagonal certificate at every scale"],
            [r"Universal assertion in \#257 & Open"],
            ["Prior work/formalised"],
            ["Open; exact reductions"],
        ],
        "exact_residuals": [
            ["An unbounded certificate supply"],
            ["the terminal bit is zero beyond every bound"],
            ["two explicit obligations"],
        ],
        "finite_open_split": [
            ["finite Lean-checkable calculation and one unbounded condition"],
            ["Neither equivalence proves the unbounded behaviour"],
        ],
        "reading_map": [
            [r"\paragraph{Reading map.}"],
            [r"Section~\ref{sec:spines}"],
            [r"Section~\ref{sec:ladder}"],
            [r"Sections~\ref{sec:eb}"],
            [r"and~\ref{sec:249}"],
        ],
    }
    for task_id, groups in requirements.items():
        for alternatives in groups:
            require(contains_any(opening, alternatives), f"gateway opening task {task_id!r} lost {alternatives}")
    for source_inventory_token in (r"\idn", "module inventory"):
        require(source_inventory_token not in opening, f"gateway opening exposes source-inventory token {source_inventory_token!r}")
    for retired_internal_label in (
        "cofinal terminal zeros",
        "certificate normal form",
    ):
        require(retired_internal_label not in opening, f"gateway opening restored retired internal label {retired_internal_label!r}")


def validate_cross_agent_entry(agents: str, claude: str) -> None:
    """Keep one shared semantic core with a small Claude-native adapter."""
    require(len(claude.encode("utf-8")) <= CLAUDE_ENTRY_BUDGET_BYTES, "cold-clone comprehension invariant")
    for path, text in (("AGENTS.md", agents), ("CLAUDE.md", claude)):
        lowered = normalized(text).casefold()
        for phrase in SELF_APPRAISAL_PHRASES:
            require(phrase not in lowered, f"{path} uses self-appraisal phrase {phrase!r}; route to objective "
                "claims, scale, and verification receipts instead")
    for token in (
        "docs/orientation.json",
        "docs/claims.json",
        "Eight-problem cold-start card",
        "must not already know a query command",
        "All eight indexed problems remain open",
        "Sylvester recurrence",
        r"\sum_{n\ge1}\varphi(n)/2^n",
        r"\sum_{n\ge1}p_n/2^n",
        r"\sum_{n\in A}1/(2^n-1)",
        "running lcms of the smooth numbers",
        "open unit lemniscate",
        "smallest resistant explicit base here is",
        "erdos-68-factorial-denominator-irrationality.pdf",
        "erdos-243-reciprocal-tail-rigidity.pdf",
        "erdos-249-binary-totient-series.pdf",
        "erdos-251-prime-gap-dyadic-series.pdf",
        "erdos-257-mersenne-support-subseries.pdf",
        "erdos-269-three-prime-running-lcm.pdf",
        "erdos-1041-lemniscate-newton-flow.pdf",
        "erdos-1049-rational-base-lambert.pdf",
        "no `ai_workflow`",
        "Lean source checked by the pinned Lean kernel",
        "not an entrypoint into any private development system",
    ):
        require(contains_any(agents, [token]), f"AGENTS.md lost shared invariant {token!r}")
    for token in (
        # This used to read "@AGENTS.md", and it was the reason the drift held.
        # scripts/test_compact_agent_entry.py asserts the opposite -- that every
        # adapter imports the compact entry -- but that test is wired into no
        # workflow, no Makefile target and not check_release.py, so it sat red
        # while this list, which does run on every pull request, pinned CLAUDE.md
        # to the 31KB deep contract. Claude Code auto-loads CLAUDE.md, so a cold
        # clone opened straight into the file the compact entry exists to defer.
        # CODEX.md and the Plectis adapters already route to the compact entry;
        # this token now agrees with them and with AGENTS.override.md's own
        # description of itself as the first-contact contract.
        "@AGENTS.override.md",
        "Claude-specific deltas only",
        "docs/orientation.json",
        "mathematical programme",
        "eight-problem cold-start card",
        "do not query merely to learn which problems exist",
        "larger ongoing formal-mathematics workflow",
        "not an entrypoint into any private development system",
    ):
        require(contains_any(claude, [token]), f"CLAUDE.md lost native adapter token {token!r}")
    require("## First read" not in claude, "CLAUDE.md duplicated the shared first-read manual")


def collect_proof_plan_packets() -> dict[str, Any]:
    """Exercise the bounded hypothesis-aware path used by a cold coding agent."""
    return {
        "blocked_integer_tail": query_packet(
            "--proof-plan",
            PROOF_PLAN_QUERIES["blocked_integer_tail"],
            "--depth",
            "2",
            "--limit",
            "8",
        ),
        "context_ready_curvature": query_packet(
            "--proof-plan",
            PROOF_PLAN_QUERIES["context_ready_curvature"],
            "--depth",
            "1",
            "--limit",
            "8",
        ),
    }


def full_ranked_signal() -> list[dict[str, Any]]:
    """Return Palomar's complete ranked signal from the summary's own drilldown."""
    orientation = json.loads(read("docs/orientation.json"))
    return orientation["mathematical_signal_first"]


def omitted_ranked_signal_rows(summary: dict[str, Any]) -> list[dict[str, Any]]:
    """Return the ranked families the bounded summary replaced with a receipt."""
    head_ranks = {row["rank"] for row in summary["mathematical_signal_first"]}
    return [row for row in full_ranked_signal() if row["rank"] not in head_ranks]


def collect_agent_packets() -> dict[str, Any]:
    """Collect only bounded query replies needed to walk the public graph."""
    summary = query_packet(budget_bytes=SUMMARY_PACKET_BUDGET_BYTES)
    publication_architecture = query_packet(
        "--publication-architecture",
        budget_bytes=publication_architecture_budget_bytes(
            summary["publication_family_count"]
        ),
    )
    expert_questions = semantic_query_packet("expert-questions")
    expert_handoffs = expert_handoff_packet(
        budget_bytes=EXPERT_HANDOFF_INDEX_BUDGET_BYTES
    )
    handoff_support_index = expert_handoffs["source_current_support_index"]
    mathematical_question_ids = [
        row["id"] for row in expert_questions["results"]
    ]
    handoff_ids = [row["id"] for row in expert_handoffs["results"]]
    semantic_corpus = json.loads(read("docs/semantic_corpus.json"))
    inventory_sample = semantic_corpus["declaration_roles"][0]
    packets: dict[str, Any] = {
        "summary": summary,
        "opens": {},
        "claims": {},
        "papers": {},
        "declarations": {},
        "sources": {},
        "modules": {},
        "sigil_modules": {},
        # --tour renders a human card by default, like --papers; the routes
        # around it default to JSON. Ask for it explicitly rather than reading
        # a reading card as a packet.
        "agent_tour": query_packet(
            "--tour", "--format", "json", budget_bytes=AGENT_TOUR_BUDGET_BYTES
        ),
        "semantic_dictionary": query_packet("--vocabulary"),
        "problem_registry": semantic_query_packet("problem-registry"),
        "problem_searches": {
            phrase: query_packet("--search", phrase, "--limit", "1")
            for phrase in ("Erdős problem 243", "Erdos problem 243")
        },
        "route": query_packet(
            "--route",
            "instant_orientation",
            budget_bytes=instant_orientation_budget_bytes(
                len(publication_architecture["family_index"])
            ),
        ),
        "agent_native_navigation_route": query_packet(
            "--route", "agent_native_corpus_navigation"
        ),
        "publication_architecture": publication_architecture,
        "publication_families": {
            row["id"]: query_packet("--publication-family", row["id"])
            for row in publication_architecture["family_index"]
        },
        "claim_statuses": {
            status: query_packet("--status", status, "--limit", "12")
            for status in summary["status_taxonomy"]
        },
        "story_routes": {
            route_id: query_packet("--route", route_id) for route_id in STORY_ROUTES
        },
        "discovery_searches": {
            search_text: query_packet("--search", search_text, "--limit", "10")
            for search_text in DISCOVERY_ROUTE_QUERIES
        },
        "discovery_multi_searches": {
            search_text: query_packet("--search", search_text, "--limit", "10")
            for search_text in DISCOVERY_MULTI_ROUTE_QUERIES
        },
        "proof_plans": collect_proof_plan_packets(),
        "story_claims": {
            claim_id: query_packet("--claim", claim_id) for claim_id in STORY_CLAIMS
        },
        "expert_questions": expert_questions,
        "semantic_inventory": semantic_query_packet(
            "inventory", "--limit", "3"
        ),
        "semantic_inventory_lookup": semantic_query_packet(
            "inventory",
            inventory_sample["declaration"],
            "--module",
            inventory_sample["module"],
            "--limit",
            "3",
        ),
        "semantic_inventory_sample": inventory_sample,
        "expert_questions_by_problem": {
            problem: semantic_query_packet(
                "expert-questions", "--problem", problem
            )
            for problem in ("249", "257")
        },
        "expert_question_details": {
            question_id: semantic_query_packet(
                "expert-questions", question_id
            )
            for question_id in mathematical_question_ids
        },
        "expert_handoffs": expert_handoffs,
        "expert_handoff_details": {
            question_id: expert_handoff_packet(
                "--question", question_id
            )
            for question_id in handoff_ids
        },
        "expert_handoff_protocol_check": check_expert_handoff_protocol(),
        "expert_handoff_review_template": expert_handoff_packet(
            "--review-template", SYSTEMS_EXPERT_QUESTION_ID
        ),
        # The bounded support index withholds source-current declarations
        # behind a named claim drilldown. Walk that command from the cold
        # clone so the receipt is checked against a real reply, not its own
        # promise.
        "expert_handoff_support_claim": query_packet(
            "--claim", handoff_support_index["family_id"]
        ),
    }
    for row in summary["remaining_open_propositions"]:
        packets["opens"][row["id"]] = query_packet("--open", row["id"])
    for row in summary["principal_claims"]:
        claim_id = row["id"]
        claim = query_packet("--claim", claim_id)
        packets["claims"][claim_id] = claim
        paper_label = claim["claim"].get("paper_label")
        if paper_label:
            packets["papers"][paper_label] = query_packet("--paper-label", paper_label)
        for declaration in claim["claim"]["declarations"][:1]:
            key = f"{declaration['module']}:{declaration['line']}"
            packets["declarations"][key] = query_packet(
                "--declaration", declaration["name"]
            )
            packets["sources"][key] = query_packet("--source", key)
            module = query_packet(
                "--module",
                declaration["module"],
                budget_bytes=module_packet_budget_bytes(declaration["module"]),
            )
            packets["modules"][declaration["module"]] = module
            sigil = module.get("paper_sigil")
            if sigil:
                packets["sigil_modules"][sigil] = query_packet(
                    "--module",
                    sigil,
                    budget_bytes=module_packet_budget_bytes(
                        module.get("module", {}).get("path", sigil)
                    ),
                )
    packets["omitted_ranked_signal"] = {
        row["family_id"]: query_packet("--declaration", row["source_declaration"])
        for row in omitted_ranked_signal_rows(summary)
    }
    artifact = query_packet("--artifact", "docs/orientation.json")
    packets["artifact"] = artifact
    digest = artifact["matches"][0]["content_digest"]
    packets["artifact_digest"] = query_packet("--artifact", digest)
    return packets


def validate_proof_plan_packets(proof_plans: dict[str, Any]) -> None:
    """Validate application boundaries and exact spines independently.

    These assertions are unconditional on purpose. Proof plans read the
    elaborated dependency index, and a committed index that predates the Lean
    tree makes every plan report itself unavailable -- which is honest, but it
    is a repository defect, not a supported state. `build_lean_dependency_index
    .py --check` in the build job fails on exactly that, and both jobs are
    required on protected main, so a released checkout always carries a current
    index. Skipping when a plan is unavailable would convert that hard failure
    into a silent pass and the spine below would never be checked again.
    """
    blocked = proof_plans["blocked_integer_tail"]
    require(blocked["kind"] == "formal_proof_plan", "cold-clone comprehension invariant")
    require(blocked["availability"] == "available", "cold-clone comprehension invariant")
    require(blocked["terminal_candidate"]["name"] == "tail_diff_int_of_den_dvd", "cold-clone comprehension invariant")
    require(blocked["plan_status"] == (
        "blocked_by_unmatched_proposition_obligations"
    ), "cold-clone comprehension invariant")
    require({
        row["name"]
        for row in blocked["application"]["obligations"]
        if row["status"] == "unmatched_proposition_obligation"
    } == {"hdvd"}, "cold-clone comprehension invariant")
    require(blocked["application"]["authority_posture"] == (
        "binder_roles_and_type_shapes_from_elaborated_Lean_context_"
        "matching_is_lexical_navigation_not_local_context_unification"
    ), "cold-clone comprehension invariant")
    require(encoded_bytes(blocked) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")

    ready = proof_plans["context_ready_curvature"]
    require(ready["kind"] == "formal_proof_plan", "cold-clone comprehension invariant")
    require(ready["availability"] == "available", "cold-clone comprehension invariant")
    require(ready["terminal_candidate"]["name"] == (
        "irrational_totientSeries_of_sharpCurvatureSupply"
    ), "cold-clone comprehension invariant")
    require(ready["plan_status"] == (
        "all_proposition_obligations_have_context_matches"
    ), "cold-clone comprehension invariant")
    require(ready["application"]["unmatched_proposition_count"] == 0, "cold-clone comprehension invariant")
    require({
        row["name"] for row in ready["exact_dependency_spine"]["steps"]
    } >= {
        "curvature_notMem_int_of_sharpCurvatureCert",
        "periodLcm_pos",
        "rational_totient_series_forces_lcm_cone_flatness",
    }, "cold-clone comprehension invariant")
    require(ready["exact_dependency_spine"]["edge_policy"] == (
        "elaborated_value_references_only"
    ), "cold-clone comprehension invariant")
    require(encoded_bytes(ready) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")


def validate_bounded_ranked_signal(
    summary: dict[str, Any], packets: dict[str, Any]
) -> None:
    """Keep the ranked signal a bounded head with an honest, reachable tail.

    The summary budget is a fixed orientation cost, so a per-family
    enumeration inside it silently turns that budget into a function of corpus
    size.  The head must stay capped, the omission receipt must state exactly
    how much was withheld, and every withheld family must still resolve
    through the follow-up commands the receipt itself names.
    """
    head = summary["mathematical_signal_first"]
    receipt = summary["bounded_summary_omission_receipt"]
    full = full_ranked_signal()
    limit = receipt["ranked_signal_head_limit"]
    head_ranks = [row["rank"] for row in head]
    require(
        limit == query_corpus.SUMMARY_RANKED_SIGNAL_HEAD,
        f"summary receipt reports ranked-signal head limit {limit}, but the "
        f"query emits {query_corpus.SUMMARY_RANKED_SIGNAL_HEAD}",
    )
    require(
        len(head) == min(limit, len(full)),
        f"bounded summary carries {len(head)} ranked-signal rows; expected "
        f"{min(limit, len(full))} (head limit {limit}, {len(full)} ranked families)",
    )
    require(
        head_ranks == list(range(1, len(head) + 1)),
        "bounded summary ranked-signal head is not the contiguous top of "
        f"Palomar's ranking: {head_ranks}",
    )
    require(
        receipt["ranked_signal_family_count"] == len(full),
        f"summary receipt claims {receipt['ranked_signal_family_count']} ranked "
        f"families, but docs/orientation.json carries {len(full)}",
    )
    require(
        receipt["omitted_ranked_signal_count"] == len(full) - len(head),
        f"summary receipt claims {receipt['omitted_ranked_signal_count']} omitted "
        f"ranked families, but {len(full) - len(head)} were withheld",
    )
    require(
        receipt["ranked_signal_drilldown"]
        == "python3 scripts/query_corpus.py --overview",
        "summary receipt does not name the full ranked-signal drilldown command: "
        f"{receipt['ranked_signal_drilldown']}",
    )
    require(
        "--declaration" in receipt["ranked_signal_family_drilldown"],
        "summary receipt does not name a per-family declaration drilldown: "
        f"{receipt['ranked_signal_family_drilldown']}",
    )
    require(
        "mathematical_signal_presentation.relational_placements"
        in receipt["omitted_fields"],
        "bounded summary withheld Palomar's relational placements without "
        "recording them in omitted_fields",
    )
    presentation = json.loads(read("docs/orientation.json"))[
        "mathematical_signal_presentation"
    ]
    withheld_placements = len(presentation["relational_placements"])
    reported_placements = summary["mathematical_signal_presentation"][
        "relational_placement_count"
    ]
    require(
        reported_placements == withheld_placements,
        f"bounded summary reports {reported_placements} withheld relational "
        f"placements, but docs/orientation.json carries {withheld_placements}",
    )

    omitted = omitted_ranked_signal_rows(summary)
    probed = packets["omitted_ranked_signal"]
    require(
        {row["family_id"] for row in omitted} == set(probed),
        "the omitted ranked families were not all probed through the receipt's "
        f"declaration drilldown: {sorted(set(probed))}",
    )
    overview_families = {
        row["family_id"]
        for row in query_corpus.repository_overview_packet()[
            "mathematical_signal_spine"
        ]["ranked_frontier"]
    }
    for row in omitted:
        family_id = row["family_id"]
        require(
            family_id in overview_families,
            f"omitted ranked family {family_id} is unreachable through the "
            "receipt's own drilldown, python3 scripts/query_corpus.py --overview",
        )
        require(
            any(
                match["qualified_name"] == row["source_declaration"]
                for match in probed[family_id]["matches"]
            ),
            f"omitted ranked family {family_id} does not resolve to "
            f"{row['source_declaration']} through the receipt's declaration "
            "drilldown",
        )


def full_source_current_supports(question_id: str) -> list[dict[str, Any]]:
    """Return every source-current support the handoff authority carries."""
    row = next(
        candidate
        for candidate in query_expert_handoffs.all_questions()
        if candidate["id"] == question_id
    )
    return query_expert_handoffs.source_current_supports(row)


def validate_bounded_expert_handoff_supports(packets: dict[str, Any]) -> None:
    """Keep the handoff support enumeration a bounded head with a live tail.

    ``source_current_supports`` grows with its family and repeats seven
    family-level fields -- one of them a boundary paragraph carried under two
    names -- on every element, so emitting it inside every matching question
    turned a fixed index cost into a function of the family's size. The head
    must stay capped and must be the contiguous top of the source order, the
    hoisted fields must really be family-level, the receipt must count and name
    exactly what was withheld, and every withheld support must still resolve
    through the commands the receipt itself names.
    """
    index_packet = packets["expert_handoffs"]
    block = index_packet["source_current_support_index"]
    receipt = block["bounded_support_omission_receipt"]
    head = block["ranked_head"]
    question_ids = block["applies_to_questions"]

    carriers = [
        row["id"]
        for row in index_packet["results"]
        if full_source_current_supports(row["id"])
    ]
    require(
        question_ids == carriers,
        f"the support index claims to serve {question_ids}, but the index rows "
        f"carrying source-current supports are {carriers}",
    )
    full = full_source_current_supports(question_ids[0])
    for question_id in question_ids[1:]:
        require(
            full_source_current_supports(question_id) == full,
            f"handoff {question_id} resolves different source-current supports "
            f"from {question_ids[0]}; one shared block would be a false merge",
        )

    limit = receipt["support_head_limit"]
    require(
        limit == query_expert_handoffs.COMPACT_SUPPORT_HEAD,
        f"support receipt reports head limit {limit}, but the query emits "
        f"{query_expert_handoffs.COMPACT_SUPPORT_HEAD}",
    )
    require(
        len(head) == min(limit, len(full)),
        f"bounded support index carries {len(head)} ranked rows; expected "
        f"{min(limit, len(full))} (head limit {limit}, {len(full)} supports)",
    )
    require(
        [row["rank"] for row in head] == list(range(1, len(head) + 1)),
        "bounded support head is not the contiguous top of the source order: "
        f"{[row['rank'] for row in head]}",
    )
    require(
        [row["source_declaration"] for row in head]
        == [row["source_declaration"] for row in full[: len(head)]],
        "bounded support head is not the top of the source order it claims: "
        f"{[row['source_declaration'] for row in head]}",
    )
    require(
        receipt["support_count"] == len(full),
        f"support receipt claims {receipt['support_count']} supports, but the "
        f"handoff authority carries {len(full)}",
    )
    omitted = full[len(head):]
    require(
        receipt["omitted_support_count"] == len(omitted),
        f"support receipt claims {receipt['omitted_support_count']} omitted "
        f"supports, but {len(omitted)} were withheld",
    )
    require(
        receipt["omitted_source_declarations"]
        == [row["source_declaration"] for row in omitted],
        "support receipt does not name the withheld declarations it withheld",
    )
    require(
        receipt["omitted_relation_counts"]
        == dict(sorted(Counter(row["relation"] for row in omitted).items())),
        "support receipt miscounts the evidence relations it withheld: "
        f"{receipt['omitted_relation_counts']}",
    )

    # The hoisted fields are the reason the block is affordable at all. They
    # are only honest to hoist while every support really does agree on them.
    for field in receipt["hoisted_family_fields"]:
        require(
            all(row[field] == full[0][field] for row in full),
            f"support receipt hoists {field!r} as family-level, but the "
            "supports disagree on it",
        )
        require(
            all(field not in row for row in head),
            f"support receipt hoists {field!r} out of the rows, but the ranked "
            "head still carries it",
        )
    aliases = receipt["family_boundary_aliases"]
    require(
        len(aliases) > 1,
        "support receipt should record every alias of the hoisted boundary",
    )
    require(
        all(
            row[alias] == block["family_boundary"]
            for row in full
            for alias in aliases
        ),
        "the hoisted family boundary is not the paragraph the supports carry "
        f"under {aliases}",
    )

    # Every withheld support must resolve through a command the receipt names.
    require(
        receipt["question_drilldown"]
        == (
            "python3 scripts/query_expert_handoffs.py --question "
            f"{question_ids[0]}"
        ),
        "support receipt does not name the per-question drilldown: "
        f"{receipt['question_drilldown']}",
    )
    detail = packets["expert_handoff_details"][question_ids[0]]
    detail_head = detail["source_current_support_index"]["ranked_head"]
    require(
        [row["source_declaration"] for row in detail_head]
        == [row["source_declaration"] for row in full],
        "the receipt's question drilldown does not return the complete support "
        "list it promises",
    )
    require(
        receipt["claim_drilldown"] == query_expert_handoffs.SUPPORT_CLAIM_DRILLDOWN,
        f"support receipt names an unexpected claim drilldown: "
        f"{receipt['claim_drilldown']}",
    )
    claim_declarations = {
        declaration["name"]
        for declaration in packets["expert_handoff_support_claim"]["claim"][
            "declarations"
        ]
    }
    for row in omitted:
        name = row["source_declaration"].rsplit(".", 1)[-1]
        require(
            name in claim_declarations,
            f"withheld support {row['source_declaration']} is unreachable "
            f"through the receipt's own drilldown, {receipt['claim_drilldown']}",
        )


def validate_bounded_expert_handoff_navigation(packets: dict[str, Any]) -> None:
    """Keep the per-problem navigation block one honest block per problem."""
    index_packet = packets["expert_handoffs"]
    navigation = index_packet["problem_navigation"]
    receipt = navigation["bounded_navigation_omission_receipt"]
    problems = navigation["problems"]
    expected = sorted({
        str(row["problem"])
        for row in index_packet["results"]
        if row["domain"] == "mathematics"
    })
    require(
        sorted(problems) == expected,
        f"navigation carries problems {sorted(problems)}, but the index rows "
        f"select {expected}",
    )
    withheld = set(receipt["omitted_fields"])
    require(withheld, "bounded navigation must name the fields it withheld")
    for problem, entry in problems.items():
        detail_question = next(
            row["id"]
            for row in index_packet["results"]
            if str(row.get("problem")) == problem
            and row["domain"] == "mathematics"
        )
        detail = packets["expert_handoff_details"][detail_question][
            "problem_navigation"
        ]["problems"][problem]
        for block_name, bounded_block in entry.items():
            complete = detail[block_name]
            for field, value in bounded_block.items():
                if field == "paper_source":
                    for nested, nested_value in value.items():
                        require(
                            complete["paper_source"][nested] == nested_value,
                            f"bounded navigation altered {block_name}."
                            f"paper_source.{nested} for problem {problem}",
                        )
                    for nested in complete["paper_source"]:
                        if nested in value:
                            continue
                        require(
                            f"{block_name}.paper_source.{nested}" in withheld,
                            f"{block_name}.paper_source.{nested} was withheld "
                            "from the index without a receipt entry",
                        )
                    continue
                require(
                    complete[field] == value,
                    f"bounded navigation altered {block_name}.{field} for "
                    f"problem {problem}",
                )
            for field in complete:
                if field in bounded_block:
                    continue
                require(
                    f"{block_name}.{field}" in withheld,
                    f"{block_name}.{field} was withheld from the index without "
                    "a receipt entry",
                )


def validate_agent_packets(packets: dict[str, Any]) -> None:
    summary = packets["summary"]
    require(summary["kind"] == "corpus_summary", "cold-clone comprehension invariant")
    require(summary["authority_posture"] == "navigation_projection_not_proof_authority", "cold-clone comprehension invariant")
    require(summary["proof_authority"] == PROOF_AUTHORITY, "cold-clone comprehension invariant")
    require(summary["release_provenance"]["posture"] == (
        "self_contained_public_projection_from_a_larger_ongoing_research_workflow"
    ), "cold-clone comprehension invariant")
    require("does not imply hidden proof authority" in (
        summary["release_provenance"]["boundary"]
    ), "cold-clone comprehension invariant")
    require(
        encoded_bytes(summary) <= SUMMARY_PACKET_BUDGET_BYTES,
        f"bounded summary encodes {encoded_bytes(summary)} bytes, over the "
        f"{SUMMARY_PACKET_BUDGET_BYTES}-byte cold-start orientation budget; "
        "densify a per-family enumeration rather than raising the budget",
    )
    require(summary["remaining_open_propositions"], "cold-clone comprehension invariant")
    require(summary["scale"]["theorem_like_count"] > (
        summary["scale"]["generated_certificate_declaration_count"]
    ), "cold-clone comprehension invariant")
    require(summary["curated_claim_count"] >= len(summary["principal_claims"]), "cold-clone comprehension invariant")
    require(summary["publication_family_count"] > 0, "cold-clone comprehension invariant")
    require(
        len(summary["mathematical_programmes"]) == len(STORY_ROUTES),
        f"bounded summary carries {len(summary['mathematical_programmes'])} "
        f"mathematical programmes, but {len(STORY_ROUTES)} story routes are "
        "declared; every programme must keep a reading route",
    )
    validate_bounded_ranked_signal(summary, packets)

    validate_proof_plan_packets(packets["proof_plans"])

    architecture = packets["publication_architecture"]
    require(architecture["kind"] == "publication_architecture", "cold-clone comprehension invariant")
    require(architecture["authority_posture"] == (
        "authored_editorial_topology_not_proof_authority"
    ), "cold-clone comprehension invariant")
    require(len(architecture["family_index"]) == summary["publication_family_count"], "cold-clone comprehension invariant")
    require(
        encoded_bytes(architecture)
        <= publication_architecture_budget_bytes(summary["publication_family_count"]),
        "cold-clone comprehension invariant",
    )
    require(set(packets["publication_families"]) == {
        row["id"] for row in architecture["family_index"]
    }, "cold-clone comprehension invariant")
    for family_id, packet in packets["publication_families"].items():
        require(packet["kind"] == "publication_family", "cold-clone comprehension invariant")
        require(packet["family"]["id"] == family_id, "cold-clone comprehension invariant")
        require(packet["claims"], "cold-clone comprehension invariant")
        require(packet["status_counts"], "cold-clone comprehension invariant")
        require(packet["family"]["primary_narrative_owner"], "cold-clone comprehension invariant")
        require(packet["family"]["consumer_or_open_obligation"], "cold-clone comprehension invariant")
        require(packet["family"]["view_decision"], "cold-clone comprehension invariant")
        require(encoded_bytes(packet) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")

    inventory = packets["semantic_inventory"]
    require(inventory["authority_posture"] == (
        "exhaustive_inventory_navigation_not_semantic_interpretation"
    ), "cold-clone comprehension invariant")
    require(inventory["total_matches"] == summary["scale"]["declaration_count"], "cold-clone comprehension invariant")
    require(inventory["returned"] == 3, "cold-clone comprehension invariant")
    require(inventory["omitted"] == inventory["total_matches"] - 3, "cold-clone comprehension invariant")
    require(all(row["module"] and row["declaration"] for row in inventory["results"]), "cold-clone comprehension invariant")
    require("does not infer a mathematical claim" in inventory["measurement_contract"], "cold-clone comprehension invariant")

    inventory_sample = packets["semantic_inventory_sample"]
    inventory_lookup = packets["semantic_inventory_lookup"]
    require(inventory_lookup["total_matches"] >= 1, "cold-clone comprehension invariant")
    require(any(
        row["id"] == inventory_sample["id"]
        for row in inventory_lookup["results"]
    ), "cold-clone comprehension invariant")
    require(encoded_bytes(inventory_lookup) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")

    navigation_route = packets["agent_native_navigation_route"]
    require(navigation_route["kind"] == "reading_route", "cold-clone comprehension invariant")
    require(navigation_route["route"]["id"] == "agent_native_corpus_navigation", "cold-clone comprehension invariant")
    cold_contract = navigation_route["route"]["cold_clone_contract"]
    require(cold_contract["navigation_requires_lean_build"] is False, "cold-clone comprehension invariant")
    require(cold_contract["navigation_source"] == "committed JSON projections", "cold-clone comprehension invariant")
    require(cold_contract["proof_authority_requires_kernel_check"] is True, "cold-clone comprehension invariant")
    require("selected target and its dependency cone" in (
        cold_contract["first_proof_build_policy"]
    ), "cold-clone comprehension invariant")
    require("Lake content traces" in cold_contract["cache_policy"], "cold-clone comprehension invariant")
    steps = navigation_route["route"]["query_steps"]
    actions = navigation_route["route"]["action_steps"]
    require(steps[0] == (
        "python3 scripts/query_corpus.py --search <ordinary-language-query>"
    ), "cold-clone comprehension invariant")
    require(any("query_corpus.py --search" in step for step in steps), "cold-clone comprehension invariant")
    require(any("query_corpus.py --proof-cone" in step for step in steps), "cold-clone comprehension invariant")
    require(all(step.startswith("python3 scripts/query_corpus.py --") for step in steps), "cold-clone comprehension invariant")
    require(any("query_semantic.py inventory" in step for step in actions), "cold-clone comprehension invariant")
    require(any("proof_workbench.py open" in step for step in actions), "cold-clone comprehension invariant")
    require(any(
        "lean_fast_build.py" in step and "<selected-target>" in step
        for step in actions
    ), "cold-clone comprehension invariant")
    require(any(
        "lean_fast_build.py" in step and "--changed-from <git-ref>" in step
        for step in actions
    ), "cold-clone comprehension invariant")
    require(any(
        "--publication-artifact agent_native_navigation_guide" in step
        for step in steps
    ), "cold-clone comprehension invariant")
    require(all(
        token not in json.dumps(navigation_route["route"])
        for token in (
            "Erdos249257.",
            "ErdosProblems/Erdos",
            "SuffixCylinderCarryPivot",
            "DynamicCancellation",
        )
    ), "cold-clone comprehension invariant")
    require({
        "docs/semantic_corpus.json",
        "docs/lean_dependency_index.json",
        "scripts/proof_workbench.py",
    }.issubset(set(navigation_route["route"]["authority_owners"])), "cold-clone comprehension invariant")
    require(navigation_route["proof_authority"] == PROOF_AUTHORITY, "cold-clone comprehension invariant")
    require(encoded_bytes(navigation_route) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")

    tour = packets["agent_tour"]
    require(tour["kind"] == "agent_corpus_tour", "cold-clone comprehension invariant")
    require(tour["authority_posture"] == (
        "computed_navigation_tour_not_proof_authority"
    ), "cold-clone comprehension invariant")
    require(tour["scale"]["declaration_count"] == summary["scale"]["declaration_count"], "cold-clone comprehension invariant")
    require(tour["scale"]["curated_claim_count"] == summary["curated_claim_count"], "cold-clone comprehension invariant")
    require(tour["scale"]["mathematical_programme_count"] == len(STORY_ROUTES), "cold-clone comprehension invariant")
    require(tour["scale"]["contribution_family_count"] == (
        summary["publication_family_count"]
    ), "cold-clone comprehension invariant")
    require(tour["scale"]["remaining_open_proposition_count"] == len(
        summary["remaining_open_propositions"]
    ), "cold-clone comprehension invariant")
    require(tour["scale"]["reviewed_remaining_open_proposition_count"] == len(
        summary["remaining_open_propositions"]
    ), "cold-clone comprehension invariant")
    require(tour["scale"]["indexed_problem_count"] == 8, "cold-clone comprehension invariant")
    require(tour["scale"]["indexed_open_problem_count"] == 8, "cold-clone comprehension invariant")
    require(tour["open_frontier_contract"]["indexed_open_problem_count"] == 8, "cold-clone comprehension invariant")
    require(tour["open_frontier_contract"][
        "reviewed_remaining_open_proposition_count"
    ] == len(summary["remaining_open_propositions"]), "cold-clone comprehension invariant")
    # The scope moved with the registry it describes. The open-proposition rows
    # used to come only from the reviewed #249/#257 core; registering the
    # propositions the #243, #249, #257 and #269 notes already state put rows
    # under all eight programmes, and the tour says so. Pinning the old wording
    # would have required the tour to describe its own contents wrongly.
    require(tour["open_frontier_contract"]["reviewed_scope"] == (
        "all eight indexed problem programmes"
    ), "cold-clone comprehension invariant")
    require(tour["budget_contract"]["maximum_encoded_bytes"] == (
        AGENT_TOUR_BUDGET_BYTES
    ), "cold-clone comprehension invariant")
    # Read from the problem registry rather than a third literal list. The
    # count above was updated to eight when #68 and #1041 were indexed and
    # this set was not, so the tour and the registry disagreed for a whole
    # release. Deriving both from docs/problems.json keeps the real check --
    # that the tour routes every indexed problem and invents none -- while
    # removing the copy that goes stale.
    require({
        row["erdos_number"] for row in tour["problem_map"]
    } == set(INDEXED_PROBLEM_NUMBERS), "cold-clone comprehension invariant")
    require(tour["formal_dependency_graph"]["loaded_library_roots"] == [
        "Erdos249257",
        "ErdosProblems",
    ], "cold-clone comprehension invariant")
    require(tour["formal_dependency_graph"]["source_resolved_node_count"] > 0, "cold-clone comprehension invariant")
    require(tour["formal_dependency_graph"]["source_resolved_direct_edge_count"] > 0, "cold-clone comprehension invariant")
    require({row["id"] for row in tour["mathematical_map"]} == set(STORY_ROUTES), "cold-clone comprehension invariant")
    require({row["id"] for row in tour["frontier"]} == {
        row["id"] for row in summary["remaining_open_propositions"]
    }, "cold-clone comprehension invariant")
    require({
        row["intent"] for row in tour["intent_lenses"]
    } == {
        "understand_the_mathematics",
        "locate_any_formal_object",
        "inspect_exact_formal_dependencies",
        "begin_a_checked_change",
        "audit_the_agent_and_release_system",
    }, "cold-clone comprehension invariant")
    require(set(tour["cold_reader_contracts"]) == {
        "research_mathematician",
        "formalisation_engineer",
        "ai_lab_researcher",
        "independent_contributor",
    }, "cold-clone comprehension invariant")
    locate_lens = next(
        row
        for row in tour["intent_lenses"]
        if row["intent"] == "locate_any_formal_object"
    )
    require("query_corpus.py --search" in locate_lens["start"], "cold-clone comprehension invariant")
    require("query_semantic.py inventory" in locate_lens["then"], "cold-clone comprehension invariant")
    require("query_corpus.py --declaration" in locate_lens["expand"], "cold-clone comprehension invariant")
    for contract in tour["cold_reader_contracts"].values():
        require(len(contract["questions_answered"]) == 3, "cold-clone comprehension invariant")
        require(contract["use"], "cold-clone comprehension invariant")
    require(tour["authority_boundary"]["proof"] == PROOF_AUTHORITY, "cold-clone comprehension invariant")
    require("no Lean build required" in tour["authority_boundary"]["navigation"], "cold-clone comprehension invariant")
    require(encoded_bytes(tour) <= tour["budget_contract"]["maximum_encoded_bytes"], "cold-clone comprehension invariant")

    problem_registry = packets["problem_registry"]
    require(problem_registry["source"] == "docs/problems.json", "cold-clone comprehension invariant")
    require(problem_registry["indexed_problem_count"] == 8, "cold-clone comprehension invariant")
    require({
        row["erdos_number"] for row in problem_registry["problems"]
    } == {68, 243, 249, 251, 257, 269, 1041, 1049}, "cold-clone comprehension invariant")
    dictionary = packets["semantic_dictionary"]
    require(dictionary["problem_registry_contract"]["source"] == (
        "docs/problems.json"
    ), "cold-clone comprehension invariant")
    require(len(dictionary["problem_registry_contract"]["problems"]) == 8, "cold-clone comprehension invariant")
    for problem_search in packets["problem_searches"].values():
        require(problem_search["routing_receipt"] == {
            "selection": "exact_problem_registry_term",
            "declaration_scan_required": False,
        }, "cold-clone comprehension invariant")
        require(problem_search["results"][0]["id"] == "erdos_243", "cold-clone comprehension invariant")

    require(set(packets["claim_statuses"]) == set(summary["status_taxonomy"]), "cold-clone comprehension invariant")
    for status, packet in packets["claim_statuses"].items():
        require(packet["kind"] == "claim_status", "cold-clone comprehension invariant")
        require(packet["authority_posture"] == (
            "claim_registry_status_navigation_not_proof_authority"
        ), "cold-clone comprehension invariant")
        require(packet["status"] == status, "cold-clone comprehension invariant")
        require(packet["meaning"] == summary["status_taxonomy"][status], "cold-clone comprehension invariant")
        require(packet["claim_count"] >= len(packet["claims"]) > 0, "cold-clone comprehension invariant")
        require(packet["omitted_claim_count"] == (
            packet["claim_count"] - len(packet["claims"])
        ), "cold-clone comprehension invariant")
        require(all(row["status"] == status for row in packet["claims"]), "cold-clone comprehension invariant")
        require(all(row["statement_excerpt"] for row in packet["claims"]), "cold-clone comprehension invariant")
        if status == "conditional reduction":
            require(all(
                row.get("remaining_open_proposition_ids")
                for row in packet["claims"]
            ), "cold-clone comprehension invariant")
        if status == "verified finite instance":
            require(all(row.get("bounded_domain") for row in packet["claims"]), "cold-clone comprehension invariant")
        if status == "open":
            # Read the open set from the registry rather than a literal pair.
            # This was written when only #249 and #257 were registered; every
            # indexed problem now carries an open claim, and a pinned pair made
            # the packet look wrong for saying so.
            require({row["id"] for row in packet["claims"]} == {
                claim["id"]
                for claim in json.loads(safe_read_text("docs/claims.json"))["claims"]
                if claim["status"] == "open"
            }, "cold-clone comprehension invariant")
            require({
                row["id"] for row in packet["remaining_open_propositions"]
            } == {
                row["id"] for row in summary["remaining_open_propositions"]
            }, "cold-clone comprehension invariant")
        else:
            require(packet["remaining_open_propositions"] == [], "cold-clone comprehension invariant")
        require(encoded_bytes(packet) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")

    principal = {row["id"]: row for row in summary["principal_claims"]}
    require(any(row["status"] == "conditional reduction" for row in principal.values()), "cold-clone comprehension invariant")
    require(any(row["status"] == "verified finite instance" for row in principal.values()), "cold-clone comprehension invariant")

    for open_id, packet in packets["opens"].items():
        proposition = packet["open_proposition"]
        require(proposition["id"] == open_id, "cold-clone comprehension invariant")
        require(packet["authority_posture"] == "authored_open_boundary_navigation_not_proof_authority", "cold-clone comprehension invariant")
        require(proposition["paper_anchor"] is not None, "cold-clone comprehension invariant")
        require(packet["open_target"]["status"] == "open", "cold-clone comprehension invariant")

    for claim_id, packet in packets["claims"].items():
        claim = packet["claim"]
        require(claim["id"] == claim_id, "cold-clone comprehension invariant")
        require(claim["status"] == principal[claim_id]["status"], "cold-clone comprehension invariant")
        require(packet["authority_posture"] == "navigation_projection_not_proof_authority", "cold-clone comprehension invariant")
        if claim["status"] == "conditional reduction":
            require(claim["remaining_open_proposition_ids"], "cold-clone comprehension invariant")
        if claim["status"] == "verified finite instance":
            require(claim.get("bounded_domain"), "cold-clone comprehension invariant")
        paper_label = claim.get("paper_label")
        if paper_label:
            require(paper_label in packets["papers"], "cold-clone comprehension invariant")
            require(packets["papers"][paper_label]["paper"]["label"] == paper_label, "cold-clone comprehension invariant")
        for declaration in claim["declarations"][:1]:
            key = f"{declaration['module']}:{declaration['line']}"
            exact = [
                row
                for row in packets["declarations"][key]["matches"]
                if row["module"] == declaration["module"] and row["line"] == declaration["line"]
            ]
            require(len(exact) == 1, "cold-clone comprehension invariant")
            source = packets["sources"][key]["source"]
            require(source["source_ref"] == key, "cold-clone comprehension invariant")
            module = packets["modules"][declaration["module"]]
            require(module["module"]["path"] == declaration["module"], "cold-clone comprehension invariant")
            sigil = module.get("paper_sigil")
            if sigil:
                require(packets["sigil_modules"][sigil]["module"]["path"] == declaration["module"], "cold-clone comprehension invariant")

    artifact = packets["artifact"]["matches"]
    digest_matches = packets["artifact_digest"]["matches"]
    require(artifact and digest_matches, "cold-clone comprehension invariant")
    require(artifact[0]["artifact_handle"] in {
        row["artifact_handle"] for row in digest_matches
    }, "cold-clone comprehension invariant")
    require(packets["route"]["route"]["id"] == "instant_orientation", "cold-clone comprehension invariant")
    require(packets["route"]["proof_authority"] == PROOF_AUTHORITY, "cold-clone comprehension invariant")
    route = packets["route"]["route"]
    require("docs/claims.json" not in route["read"], "cold-clone comprehension invariant")
    require(route["query_steps"], "cold-clone comprehension invariant")
    require("python3 scripts/query_corpus.py --publication-architecture" in (
        route["query_steps"]
    ), "cold-clone comprehension invariant")
    require(route["authority_owners"], "cold-clone comprehension invariant")
    require(route["adjacent_handle_classes"], "cold-clone comprehension invariant")

    story_routes = packets["story_routes"]
    require(tuple(story_routes) == STORY_ROUTES, "cold-clone comprehension invariant")
    summary_programmes = {
        row["id"]: row for row in summary["mathematical_programmes"]
    }
    require(set(summary_programmes) == set(STORY_ROUTES), "cold-clone comprehension invariant")
    for route_id, packet in story_routes.items():
        route = packet["route"]
        programme = packet["programme"]
        require(route["route_kind"] == "mathematical_programme", "cold-clone comprehension invariant")
        require(route["id"] == route_id, "cold-clone comprehension invariant")
        require(programme["title"] == summary_programmes[route_id]["title"], "cold-clone comprehension invariant")
        require(programme["core_claims"], "cold-clone comprehension invariant")
        require(summary_programmes[route_id]["core_claim_count"] == len(
            programme["core_claims"]
        ), "cold-clone comprehension invariant")
        require(set(summary_programmes[route_id]["representative_claim_ids"]).issubset(
            {row["id"] for row in programme["core_claims"]}
        ), "cold-clone comprehension invariant")
        require(programme["problem_targets"], "cold-clone comprehension invariant")
        require(all(row["status"] == "open" for row in programme["problem_targets"]), "cold-clone comprehension invariant")
        require(programme["remaining_open_propositions"], "cold-clone comprehension invariant")
        require(any(
            token in programme["claim_ceiling"].casefold()
            for token in (
                "remain open",
                "not proved",
                "does not",
                "do not",
                "neither",
                "no ",
            )
        ), "cold-clone comprehension invariant")
        require({
            step.rsplit(" ", 1)[-1]
            for step in route["query_steps"]
            if " --claim " in step
        } == {row["id"] for row in programme["core_claims"]}, "cold-clone comprehension invariant")
        require({
            step.rsplit(" ", 1)[-1]
            for step in route["query_steps"]
            if " --open " in step
        } == {
            row["id"] for row in programme["remaining_open_propositions"]
        }, "cold-clone comprehension invariant")
        require(packet["release_provenance"] == summary["release_provenance"], "cold-clone comprehension invariant")
    for search_text, expected_route_id in DISCOVERY_ROUTE_QUERIES.items():
        search_packet = packets["discovery_searches"][search_text]
        require(search_packet["kind"] == "search", "cold-clone comprehension invariant")
        require(search_packet["query"] == search_text, "cold-clone comprehension invariant")
        require(search_packet["results"], "cold-clone comprehension invariant")
        require(search_packet["results"][0]["kind"] == "reading_route", "cold-clone comprehension invariant")
        require(search_packet["results"][0]["id"] == expected_route_id, "cold-clone comprehension invariant")
    for search_text, expected_route_ids in DISCOVERY_MULTI_ROUTE_QUERIES.items():
        search_packet = packets["discovery_multi_searches"][search_text]
        require(search_packet["kind"] == "search", "cold-clone comprehension invariant")
        require(search_packet["query"] == search_text, "cold-clone comprehension invariant")
        require({
            row["id"]
            for row in search_packet["results"]
            if row["kind"] == "reading_route"
        } >= expected_route_ids, "cold-clone comprehension invariant")
    portfolio_results = packets["discovery_searches"][
        "what other exact mathematics is there"
    ]["results"]
    require(portfolio_results[0]["kind"] == "reading_route", "cold-clone comprehension invariant")
    require(portfolio_results[0]["id"] == "instant_orientation", "cold-clone comprehension invariant")
    require([
        step.rsplit(" ", 1)[-1]
        for step in story_routes["erdos257_half_story"]["route"]["query_steps"]
    ] == [
        *STORY_CLAIMS[:10],
        "remaining_open.half_value_membership",
        "remaining_open.twenty_one_permanent_affine_supercapacity",
        "remaining_open.universal_257_all_infinite_supports",
    ], "cold-clone comprehension invariant")
    require([
        step.rsplit(" ", 1)[-1]
        for step in story_routes["erdos249_certificate_story"]["route"]["query_steps"]
    ] == [
        "denominator_exclusion",
        "certificate_reduction",
        "certificate_completeness",
        "certified_kill_instances",
        "first_harmonic_certificate_interface",
        "first_harmonic_pivot_decomposition",
        "remaining_open.erdos_249_irrationality",
        "remaining_open.unbounded_certificate_supply",
    ], "cold-clone comprehension invariant")

    story_claims = packets["story_claims"]
    band_claim = story_claims["half_greedy_two_thirds_band"]
    require(("builds_on", "greedy_achievement_geometry") in {
        (row["relation"], row["neighbour"]["id"])
        for row in band_claim["argument_neighbourhood"]["outgoing"]
    }, "cold-clone comprehension invariant")
    require("no theorem here says that the actual greedy orbit for 1/2 avoids a band"
        in band_claim["claim"]["statement"], "cold-clone comprehension invariant")
    half_membership = story_claims["half_membership_seam_classification"]
    require({
        (row["relation"], row["neighbour"]["id"])
        for row in half_membership["argument_neighbourhood"]["outgoing"]
    } >= {
        ("builds_on", "greedy_achievement_geometry"),
        ("builds_on", "fatal_gap_right_tail_classification"),
    }, "cold-clone comprehension invariant")
    last_producer = story_claims["last_producer_tail_escape_reduction"]
    require(("eliminates_case", "final_middle_cell_escape") in {
        (row["relation"], row["neighbour"]["id"])
        for row in last_producer["argument_neighbourhood"]["incoming"]
    }, "cold-clone comprehension invariant")
    require(("builds_on", "fatal_gap_right_tail_classification") in {
        (row["relation"], row["neighbour"]["id"])
        for row in last_producer["argument_neighbourhood"]["outgoing"]
    }, "cold-clone comprehension invariant")
    phase_sieve = story_claims["final_middle_neg_two_phase_sieve"]
    require("Exactly 412 of the 2730 joint residue classes survive" in phase_sieve["claim"]["statement"], "cold-clone comprehension invariant")
    require(("advances_open_target", "universal_257") in {
        (row["relation"], row["neighbour"]["id"])
        for row in phase_sieve["argument_neighbourhood"]["outgoing"]
    }, "cold-clone comprehension invariant")
    first_harmonic = story_claims["first_harmonic_certificate_interface"]
    require({
        row["neighbour"]["id"]
        for row in first_harmonic["argument_neighbourhood"]["outgoing"]
        if row["relation"] == "builds_on"
    } >= {"certificate_reduction", "certificate_completeness"}, "cold-clone comprehension invariant")
    harmonic_pivot = story_claims["first_harmonic_pivot_decomposition"]
    require("14X/25" in harmonic_pivot["claim"]["statement"], "cold-clone comprehension invariant")
    require("9X/10" in harmonic_pivot["claim"]["statement"], "cold-clone comprehension invariant")
    require({
        (row["relation"], row["neighbour"]["id"])
        for row in harmonic_pivot["argument_neighbourhood"]["outgoing"]
    } >= {
        ("builds_on", "first_harmonic_certificate_interface"),
        ("advances_open_target", "erdos_249"),
    }, "cold-clone comprehension invariant")

    def validate_compact_question(row: dict[str, Any]) -> None:
        require(isinstance(row.get("id"), str) and row["id"].strip(), "cold-clone comprehension invariant")
        require(row.get("status") == "OPEN", "cold-clone comprehension invariant")
        for field in ("exact_ask", "current_hypothesis"):
            require(isinstance(row.get(field), str) and row[field].strip(), "cold-clone comprehension invariant")
        require(row.get("hypothesis_confidence") in {"low", "medium", "high"}, "cold-clone comprehension invariant")
        alternatives = row.get("plausible_alternatives")
        require(isinstance(alternatives, list) and len(alternatives) >= 2, "cold-clone comprehension invariant")
        alternative_ids = [alternative.get("id") for alternative in alternatives]
        require(len(alternative_ids) == len(set(alternative_ids)), "cold-clone comprehension invariant")
        for alternative in alternatives:
            for field in ("id", "statement"):
                require(isinstance(alternative.get(field), str), "cold-clone comprehension invariant")
                require(alternative[field].strip(), "cold-clone comprehension invariant")
        for field in ("current_evidence", "discriminating_evidence"):
            evidence = row.get(field)
            require(isinstance(evidence, list) and len(evidence) >= 2, "cold-clone comprehension invariant")
            require(len(evidence) == len(set(evidence)), "cold-clone comprehension invariant")
            require(all(
                isinstance(item, str) and item.strip()
                for item in evidence
            ), "cold-clone comprehension invariant")

    def validate_full_question(row: dict[str, Any]) -> None:
        validate_compact_question(row)
        for field in ("payoff", "boundary", "known_obstruction"):
            require(isinstance(row.get(field), str) and row[field].strip(), "cold-clone comprehension invariant")
        for alternative in row["plausible_alternatives"]:
            require(isinstance(alternative.get("consequence"), str), "cold-clone comprehension invariant")
            require(alternative["consequence"].strip(), "cold-clone comprehension invariant")

    expert_questions = packets["expert_questions"]
    expert_questions_by_problem = packets["expert_questions_by_problem"]
    expert_question_details = packets["expert_question_details"]
    require(expert_questions["packet_kind"] == "compact_index", "cold-clone comprehension invariant")
    require(expert_questions["count"] == len(expert_questions["results"]) == 5, "cold-clone comprehension invariant")
    require(encoded_bytes(expert_questions) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")
    require(set(expert_questions_by_problem) == {"249", "257"}, "cold-clone comprehension invariant")
    require({
        problem: packet["count"]
        for problem, packet in expert_questions_by_problem.items()
    } == {"249": 3, "257": 2}, "cold-clone comprehension invariant")
    require({
        row["classification"] for row in expert_questions["results"]
    } == {
        "endpoint_equivalent",
        "sufficient_for_erdos_249",
        "sufficient_for_counterexample",
    }, "cold-clone comprehension invariant")
    require(set(expert_questions["classification_legend"]) == {
        "endpoint_equivalent",
        "sufficient_for_erdos_249",
        "sufficient_for_counterexample",
    }, "cold-clone comprehension invariant")
    semantic_index_by_id = {
        row["id"]: row for row in expert_questions["results"]
    }
    require(len(semantic_index_by_id) == 5, "cold-clone comprehension invariant")
    for row in semantic_index_by_id.values():
        require(row["problem"] in {"249", "257"}, "cold-clone comprehension invariant")
        validate_compact_question(row)
        require(row["detail_command"] == (
            "python3 scripts/query_semantic.py expert-questions "
            f"{row['id']}"
        ), "cold-clone comprehension invariant")
        require(isinstance(row.get("checked_consumers"), list), "cold-clone comprehension invariant")
        require(row["checked_consumers"], "cold-clone comprehension invariant")
        require(all(
            isinstance(consumer, str) and consumer.strip()
            for consumer in row["checked_consumers"]
        ), "cold-clone comprehension invariant")
    default_by_problem = {
        problem: [
            row for row in expert_questions["results"]
            if row["problem"] == problem
        ]
        for problem in ("249", "257")
    }
    for problem, packet in expert_questions_by_problem.items():
        require(packet["packet_kind"] == "compact_index", "cold-clone comprehension invariant")
        require(packet["results"] == default_by_problem[problem], "cold-clone comprehension invariant")
        require(all(row["problem"] == problem for row in packet["results"]), "cold-clone comprehension invariant")
        require(packet["classification_legend"] == (
            expert_questions["classification_legend"]
        ), "cold-clone comprehension invariant")
        require(packet["limits"] == expert_questions["limits"], "cold-clone comprehension invariant")
        require(encoded_bytes(packet) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")
    require({
        row["classification"]
        for row in expert_questions_by_problem["249"]["results"]
    } == {"endpoint_equivalent", "sufficient_for_erdos_249"}, "cold-clone comprehension invariant")
    require({
        row["classification"]
        for row in expert_questions_by_problem["257"]["results"]
    } == {"sufficient_for_counterexample"}, "cold-clone comprehension invariant")
    expert_limits = normalized(" ".join(expert_questions["limits"]))
    require(contains_any(
        expert_limits,
        [
            "The two #257 questions can produce a counterexample if answered "
            "positively; they cannot prove the universal positive statement."
        ],
    ), "cold-clone comprehension invariant")
    require(contains_any(
        expert_limits,
        [
            "No checked strictly weaker expert handoff currently implies "
            "universal Erdős #257 for every infinite support."
        ],
    ), "cold-clone comprehension invariant")
    require(set(expert_question_details) == set(semantic_index_by_id), "cold-clone comprehension invariant")
    semantic_detail_by_id: dict[str, dict[str, Any]] = {}
    compact_identity_fields = (
        "id",
        "problem",
        "classification",
        "status",
        "exact_ask",
        "current_hypothesis",
        "hypothesis_confidence",
        "current_evidence",
        "discriminating_evidence",
    )
    for question_id, packet in expert_question_details.items():
        require(packet["packet_kind"] == "full_question", "cold-clone comprehension invariant")
        require(packet["count"] == len(packet["results"]) == 1, "cold-clone comprehension invariant")
        require(packet["classification_legend"] == (
            expert_questions["classification_legend"]
        ), "cold-clone comprehension invariant")
        require(packet["limits"] == expert_questions["limits"], "cold-clone comprehension invariant")
        require(encoded_bytes(packet) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")
        row = packet["results"][0]
        require(row["id"] == question_id, "cold-clone comprehension invariant")
        validate_full_question(row)
        index_row = semantic_index_by_id[question_id]
        require(all(
            row[field] == index_row[field]
            for field in compact_identity_fields
        ), "cold-clone comprehension invariant")
        require([
            {
                "id": alternative["id"],
                "statement": alternative["statement"],
            }
            for alternative in row["plausible_alternatives"]
        ] == index_row["plausible_alternatives"], "cold-clone comprehension invariant")
        consumers = row.get("consumer_declarations")
        require(isinstance(consumers, list) and consumers, "cold-clone comprehension invariant")
        for consumer in consumers:
            require(isinstance(consumer.get("declaration"), str), "cold-clone comprehension invariant")
            require(consumer["declaration"].strip(), "cold-clone comprehension invariant")
            require(isinstance(consumer.get("module"), str), "cold-clone comprehension invariant")
            require(consumer["module"].strip(), "cold-clone comprehension invariant")
            require(isinstance(consumer.get("line"), int) and consumer["line"] > 0, "cold-clone comprehension invariant")
        require([
            f"{consumer['module']}:{consumer['line']}:{consumer['declaration']}"
            for consumer in consumers
        ] == index_row["checked_consumers"], "cold-clone comprehension invariant")
        for field in (
            "open_proposition_id",
            "source_claim_id",
            "verification_command",
        ):
            require(isinstance(row.get(field), str) and row[field].strip(), "cold-clone comprehension invariant")
        semantic_detail_by_id[question_id] = row

    expert_handoffs = packets["expert_handoffs"]
    expert_handoff_details = packets["expert_handoff_details"]
    require(expert_handoffs["packet_kind"] == "compact_index", "cold-clone comprehension invariant")
    require(expert_handoffs["count"] == len(expert_handoffs["results"]) == 6, "cold-clone comprehension invariant")
    require(expert_handoffs["domain_counts"] == {
        "mathematics": 5,
        "systems": 1,
    }, "cold-clone comprehension invariant")
    require(
        encoded_bytes(expert_handoffs) <= EXPERT_HANDOFF_INDEX_BUDGET_BYTES,
        f"expert-handoff index encodes {encoded_bytes(expert_handoffs)} bytes, "
        f"over the {EXPERT_HANDOFF_INDEX_BUDGET_BYTES}-byte chooser budget; "
        "densify a per-family or per-row enumeration rather than raising it",
    )
    validate_bounded_expert_handoff_supports(packets)
    validate_bounded_expert_handoff_navigation(packets)
    handoff_index_by_id = {
        row["id"]: row for row in expert_handoffs["results"]
    }
    require(len(handoff_index_by_id) == 6, "cold-clone comprehension invariant")
    require(set(expert_handoff_details) == set(handoff_index_by_id), "cold-clone comprehension invariant")
    shared_index_fields = (
        "id",
        "problem",
        "classification",
        "status",
        "exact_ask",
        "current_hypothesis",
        "hypothesis_confidence",
        "plausible_alternatives",
        "current_evidence",
        "discriminating_evidence",
    )
    for row in handoff_index_by_id.values():
        validate_compact_question(row)
        require(row["detail_command"] == (
            "python3 scripts/query_expert_handoffs.py --question "
            f"{row['id']}"
        ), "cold-clone comprehension invariant")
        if row["domain"] == "mathematics":
            semantic_row = semantic_index_by_id[row["id"]]
            require(all(
                row[field] == semantic_row[field]
                for field in shared_index_fields
            ), "cold-clone comprehension invariant")
    handoff_detail_by_id: dict[str, dict[str, Any]] = {}
    for question_id, packet in expert_handoff_details.items():
        require(packet["packet_kind"] == "full_question", "cold-clone comprehension invariant")
        require(packet["count"] == len(packet["results"]) == 1, "cold-clone comprehension invariant")
        require(encoded_bytes(packet) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")
        row = packet["results"][0]
        require(row["id"] == question_id, "cold-clone comprehension invariant")
        require(packet["domain_counts"] == {row["domain"]: 1}, "cold-clone comprehension invariant")
        validate_full_question(row)
        index_row = handoff_index_by_id[question_id]
        require(all(
            row.get(field) == index_row.get(field)
            for field in compact_identity_fields
        ), "cold-clone comprehension invariant")
        require([
            {
                "id": alternative["id"],
                "statement": alternative["statement"],
            }
            for alternative in row["plausible_alternatives"]
        ] == index_row["plausible_alternatives"], "cold-clone comprehension invariant")
        if row["domain"] == "mathematics":
            semantic_row = semantic_detail_by_id[question_id]
            require({
                key: value for key, value in row.items()
                if key != "domain"
            } == semantic_row, "cold-clone comprehension invariant")
        handoff_detail_by_id[question_id] = row

    mathematical_handoffs_by_id = {
        question_id: row
        for question_id, row in handoff_detail_by_id.items()
        if row["domain"] == "mathematics"
    }
    expected_257_consumers = {
        "XQ257-second-channel-separation": {
            "half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven",
            "positiveMersenneSupportValue_coe_finset_ne_half",
            "positiveMersenneSupportValue_eq_erdosSupportSeries",
        },
        "XQ257-middle-producer-tail-escape": {
            "half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree",
            "positiveMersenneSupportValue_coe_finset_ne_half",
            "positiveMersenneSupportValue_eq_erdosSupportSeries",
        },
    }
    for question_id, expected_consumers in expected_257_consumers.items():
        row = mathematical_handoffs_by_id[question_id]
        require(row["problem"] == "257", "cold-clone comprehension invariant")
        require({
            consumer["declaration"]
            for consumer in row["consumer_declarations"]
        } == expected_consumers, "cold-clone comprehension invariant")
    pivot = mathematical_handoffs_by_id["XQ249-pivot-decorrelation"]
    require("h <= L-s" in pivot["exact_ask"], "cold-clone comprehension invariant")
    require("all four 14/25, 1/100, 1/100 and 8/25 budgets"
        in pivot["current_hypothesis"], "cold-clone comprehension invariant")
    pivot_alternatives = {
        row["id"]: row for row in pivot["plausible_alternatives"]
    }
    require(set(pivot_alternatives) == {
        "cofinal_four_budget_socket",
        "no_cofinal_joint_witness",
    }, "cold-clone comprehension invariant")
    require(pivot_alternatives["cofinal_four_budget_socket"]["statement"] == (
        "All four budgets, overlap and room inequalities hold cofinally for "
        "every positive shift."
    ), "cold-clone comprehension invariant")
    require(pivot_alternatives["no_cofinal_joint_witness"]["statement"] == (
        "For some h > 0, every s > 0 and eta in (0,1) has a cutoff after "
        "which no X,L meet the complete structural and four-budget conjunction."
    ), "cold-clone comprehension invariant")

    adjacent = mathematical_handoffs_by_id[
        "XQ249-adjacent-phase-separation"
    ]
    require("16(2X+h+L+2) <= 2^L" in adjacent["exact_ask"], "cold-clone comprehension invariant")
    adjacent_alternatives = {
        row["id"]: row for row in adjacent["plausible_alternatives"]
    }
    require(adjacent_alternatives["phase_locking"]["statement"] == (
        "For some positive shift there is a cutoff beyond which no admissible "
        "block, depth and adjacent pair meet the 19/25 threshold."
    ), "cold-clone comprehension invariant")
    require(any(
        "Infinitely many bad blocks alone do not." in evidence
        for evidence in adjacent["discriminating_evidence"]
    ), "cold-clone comprehension invariant")

    second_channel = mathematical_handoffs_by_id[
        "XQ257-second-channel-separation"
    ]
    second_channel_text = " ".join(
        [
            second_channel["current_hypothesis"],
            second_channel["known_obstruction"],
            *second_channel["current_evidence"],
        ]
    )
    require("Theta(n^2)" not in second_channel_text, "cold-clone comprehension invariant")
    require("no matching reduced-denominator lower bound"
        in second_channel_text, "cold-clone comprehension invariant")
    require("1 <= n <= 1000" in second_channel_text, "cold-clone comprehension invariant")
    require("Rank 1001 onward is unmeasured" in second_channel_text, "cold-clone comprehension invariant")
    require("1033253069/8193024" in second_channel_text, "cold-clone comprehension invariant")
    require("All 128 branch words of length seven occur"
        in second_channel_text, "cold-clone comprehension invariant")
    require(second_channel["measured_evidence_artifact"] == (
        "docs/measurements/second_channel_separation_probe.json"
    ), "cold-clone comprehension invariant")
    require(second_channel["measurement_check_command"] == (
        "python3 scripts/probe_second_channel_separation.py --check"
    ), "cold-clone comprehension invariant")

    middle = mathematical_handoffs_by_id[
        "XQ257-middle-producer-tail-escape"
    ]
    require("Prove C_s = -3 or (1 <= C_s and Theta_s < C_s)."
        in middle["exact_ask"], "cold-clone comprehension invariant")
    middle_alternatives = {
        row["id"]: row for row in middle["plausible_alternatives"]
    }
    require(set(middle_alternatives) == {
        "full_middle_disjunction",
        "nonpositive_cell_counterexample",
        "positive_tail_counterexample",
    }, "cold-clone comprehension invariant")
    require(middle_alternatives["full_middle_disjunction"]["statement"] == (
        "Every actual middle row satisfies C_s = -3 or 1 <= C_s with "
        "Theta_s < C_s."
    ), "cold-clone comprehension invariant")
    require(middle_alternatives["nonpositive_cell_counterexample"][
        "statement"
    ] == "An actual middle row has C_s <= 0 with C_s != -3.", "cold-clone comprehension invariant")
    require(middle_alternatives["positive_tail_counterexample"]["statement"] == (
        "An actual middle row has 1 <= C_s and Theta_s >= C_s."
    ), "cold-clone comprehension invariant")
    systems_handoff = handoff_detail_by_id[SYSTEMS_EXPERT_QUESTION_ID]
    require(systems_handoff["domain"] == "systems", "cold-clone comprehension invariant")
    require(systems_handoff["classification"] == "external_validation", "cold-clone comprehension invariant")
    for field in (
        "exact_ask",
        "payoff",
        "boundary",
        "known_obstruction",
        "verification_command",
    ):
        require(isinstance(systems_handoff.get(field), str), "cold-clone comprehension invariant")
        require(systems_handoff[field].strip(), "cold-clone comprehension invariant")
    require(systems_handoff["input_template"]["question_id"] == (
        systems_handoff["id"]
    ), "cold-clone comprehension invariant")
    require("acceptance" not in systems_handoff, "cold-clone comprehension invariant")
    require("review_template" not in systems_handoff, "cold-clone comprehension invariant")
    rubric = systems_handoff.get("manual_review_rubric")
    require(isinstance(rubric, dict) and rubric, "cold-clone comprehension invariant")
    require(all(
        isinstance(key, str) and key.strip()
        and isinstance(value, str) and value.strip()
        for key, value in rubric.items()
    ), "cold-clone comprehension invariant")
    scalar_answer_fields = (
        "prior_project_context",
        "elapsed_seconds",
        "problem_249_status",
        "problem_257_status",
        "farey_bound_provenance",
        "farey_numerical_delta",
        "equivalent_antecedents",
        "substantial_antecedents",
    )
    require(all(
        systems_handoff["input_template"][field] is None
        for field in scalar_answer_fields
    ), "cold-clone comprehension invariant")
    require(systems_handoff["consumer"]["command"], "cold-clone comprehension invariant")
    require(systems_handoff["consumer"]["review_template_command"] == (
        "python3 scripts/query_expert_handoffs.py --review-template "
        f"{SYSTEMS_EXPERT_QUESTION_ID}"
    ), "cold-clone comprehension invariant")
    require(systems_handoff["consumer"]["final_review_command"], "cold-clone comprehension invariant")
    require(systems_handoff["verification_command"] == (
        "python3 scripts/query_expert_handoffs.py --check"
    ), "cold-clone comprehension invariant")
    require(packets["expert_handoff_protocol_check"] == (
        "expert handoff protocol: 5 mathematical questions and "
        "1 systems question(s) verified"
    ), "cold-clone comprehension invariant")
    review_template = packets["expert_handoff_review_template"]
    require(review_template["question_id"] == SYSTEMS_EXPERT_QUESTION_ID, "cold-clone comprehension invariant")
    require(review_template["response_sha256"] is None, "cold-clone comprehension invariant")
    require(review_template["evaluator_identity"] is None, "cold-clone comprehension invariant")
    require(review_template["evaluated_at"] is None, "cold-clone comprehension invariant")
    require(review_template["reviewer_provenance_verified"] is None, "cold-clone comprehension invariant")
    require(review_template["timing_provenance_verified"] is None, "cold-clone comprehension invariant")
    require(review_template["review_notes"] == "", "cold-clone comprehension invariant")
    require(review_template["final_outcome"] is None, "cold-clone comprehension invariant")
    require(set(review_template["criteria"]) == set(rubric), "cold-clone comprehension invariant")
    require(all(value is None for value in review_template["criteria"].values()), "cold-clone comprehension invariant")
    require("acceptance" not in review_template, "cold-clone comprehension invariant")
    require(encoded_bytes(review_template) <= PACKET_BUDGET_BYTES, "cold-clone comprehension invariant")


def run_quick_check() -> int:
    """Verify the zero-build first-contact path from committed projections."""
    semantic_receipt = check_semantic_corpus_freshness()
    check_route_memory_descriptor()
    summary = quick_summary()
    human_surfaces = {path: read(path) for path in HUMAN_SURFACES}
    validate_human_first_contact(summary, human_surfaces)
    validate_paper_library_first_contact(read(PAPER_LIBRARY_SURFACE))
    validate_public_semantic_census(
        semantic_census(semantic_receipt),
        {path: read(path) for path in CENSUS_SURFACES},
    )
    validate_gateway_opening(read(GATEWAY_PAPER))
    validate_cross_agent_entry(read("AGENTS.md"), read("CLAUDE.md"))
    validate_incremental_build_contract(
        {path: read(path) for path in INCREMENTAL_BUILD_SURFACES}
    )
    print(
        "cold-clone quick check: committed human and agent first-contact "
        "projections verified; no Lean build or corpus-query sweep run"
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verify bounded cold-clone comprehension."
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help=(
            "check committed first-contact projections only; performs no Lean "
            "build and no exhaustive typed-query sweep"
        ),
    )
    parser.add_argument(
        "--proof-plans-only",
        action="store_true",
        help=(
            "exercise the two bounded semantic proof plans without the wider "
            "claim, paper, and route projection sweep"
        ),
    )
    parser.add_argument(
        "--singleflight-worker",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    args = parser.parse_args(argv)
    if args.quick:
        return run_quick_check()
    if args.proof_plans_only:
        validate_proof_plan_packets(collect_proof_plan_packets())
        print(
            "cold-clone proof plans: blocked and context-ready application "
            "boundaries verified"
        )
        return 0

    if not args.singleflight_worker:
        state_root = singleflight.default_state_root()
        specification = singleflight.validator_spec(
            "cold-clone", [], None, state_root
        )
        receipt = singleflight.submit(specification, state_root)
        terminal, code = singleflight.collect(
            state_root,
            receipt["key"],
            True,
            singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
        )
        if terminal.get("state") != "terminal":
            print(json.dumps(terminal, sort_keys=True), file=sys.stderr)
            return code
        stdout = terminal.get("stdout", {}).get("tail")
        stderr = terminal.get("stderr", {}).get("tail")
        if stdout:
            print(stdout, end="" if stdout.endswith("\n") else "\n")
        if stderr:
            print(
                stderr,
                end="" if stderr.endswith("\n") else "\n",
                file=sys.stderr,
            )
        print(
            "cold-clone comprehension: shared validation "
            f"key={receipt['key'][:12]} reuse={receipt.get('reuse', 'owner')} "
            f"exit={code}",
            file=sys.stderr,
        )
        return code

    validate_query_cli_process_smoke()
    check_route_memory_descriptor()
    packets = collect_agent_packets()
    summary = packets["summary"]
    human_surfaces = {path: read(path) for path in HUMAN_SURFACES}
    validate_human_first_contact(summary, human_surfaces)
    validate_paper_library_first_contact(read(PAPER_LIBRARY_SURFACE))
    validate_public_semantic_census(
        semantic_census(),
        {path: read(path) for path in CENSUS_SURFACES},
    )
    validate_gateway_opening(read(GATEWAY_PAPER))
    validate_cross_agent_entry(read("AGENTS.md"), read("CLAUDE.md"))
    validate_incremental_build_contract(
        {path: read(path) for path in INCREMENTAL_BUILD_SURFACES}
    )
    validate_agent_packets(packets)
    query_count = (
        1
        + len(packets["opens"])
        + len(packets["claims"])
        + len(packets["papers"])
        + len(packets["declarations"])
        + len(packets["sources"])
        + len(packets["modules"])
        + len(packets["sigil_modules"])
        + 1
        + len(packets["publication_families"])
        + len(packets["claim_statuses"])
        + len(packets["story_routes"])
        + len(packets["discovery_searches"])
        + len(packets["discovery_multi_searches"])
        + len(packets["proof_plans"])
        + len(packets["story_claims"])
        + 2
        + 1
        + len(packets["expert_questions_by_problem"])
        + len(packets["expert_question_details"])
        + 1
        + len(packets["expert_handoff_details"])
        + 2
        + 3
    )
    print(
        "cold-clone comprehension: bounded human first contact and "
        f"{query_count} typed query packets verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
