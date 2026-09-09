#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the claim-owned External Verification Packet projections.

The semantic owner is ``docs/claims.json::external_verification_packet``.
Lean remains proof authority.  This builder validates the owner, checks the
statement-isolation boundary, and projects the small Comparator config, the
whole-eight-problem disclosure, and reviewer/outreach surfaces.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS_PATH = ROOT / "docs/claims.json"
PROBLEM_SOURCE_PATH = ROOT / "docs/problem_index_source.json"
PROBLEM_PROJECTION_PATH = ROOT / "docs/problems.json"
PALOMAR_SHOWCASE_PATH = ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json"
OUTPUTS = {
    "config": ROOT / "verification/comparator.json",
    "negative_config": ROOT / "verification/comparator-negative-mismatch.json",
    "formalization": ROOT / "formalization.yaml",
    "packet": ROOT / "docs/external_verification_packet.json",
    "human": ROOT / "docs/EXTERNAL_VERIFICATION.md",
    "outreach": ROOT / "docs/OUTREACH_EVIDENCE_CAPSULES.md",
}

IMPORT_LINE_RE = re.compile(r"^import\s+([^\n]+)$", re.M)
PRIOR_RESULT_RE = re.compile(
    r"formalisation of (?:an )?existing|known geometry",
    re.I,
)


def canonical_claim_status(result: dict) -> str:
    """Keep Comparator selection distinct from canonical claim registration."""
    return (
        f"supports_registered_claim_family:{result['claim_id']}"
        if result.get("claim_id")
        else "comparator_interface_not_registered_as_canonical_claim"
    )


def source_fidelity(packet: dict, row_id: str) -> dict | None:
    mapping = packet.get("source_fidelity", {}).get(row_id)
    return mapping if isinstance(mapping, dict) else None


def imports_in_text(text: str) -> list[str]:
    """Return every module token, including multi-module import lines."""
    return [token for body in IMPORT_LINE_RE.findall(text) for token in body.split()]


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


class UnsafeVerificationPath(ValueError):
    """A verification input or output escaped the asserted checkout boundary."""


def _safe_component(path: Path) -> Path:
    """Reject checkout escapes and symbolic-link components before I/O."""
    root = Path(os.path.abspath(ROOT))
    candidate = Path(os.path.abspath(path))
    if candidate != root and root not in candidate.parents:
        raise UnsafeVerificationPath(f"path escaped verification checkout: {candidate}")
    current = candidate
    while current != root:
        if current.is_symlink():
            raise UnsafeVerificationPath(
                f"symbolic-link verification path: {candidate}"
            )
        if current.parent == current:
            raise UnsafeVerificationPath(
                f"path escaped verification checkout: {candidate}"
            )
        current = current.parent
    return candidate


def safe_bytes(path: Path) -> bytes:
    """Read a verification file through a no-follow regular-file descriptor."""
    candidate = _safe_component(path)
    flags = os.O_RDONLY
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeVerificationPath(
            f"verification file could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeVerificationPath(
                f"verification file is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        return b"".join(chunks)
    except OSError as exc:
        raise UnsafeVerificationPath(
            f"verification file could not be read safely: {candidate}"
        ) from exc
    finally:
        os.close(descriptor)


def safe_text(path: Path) -> str:
    """Decode one descriptor-safe verification input as UTF-8."""
    return safe_bytes(path).decode("utf-8")


def safe_write_bytes(path: Path, content: bytes) -> None:
    """Write a generated verification artifact without following a symlink."""
    candidate = _safe_component(path)
    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(candidate, flags, 0o644)
    except OSError as exc:
        raise UnsafeVerificationPath(
            f"verification output could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeVerificationPath(
                f"verification output is not a regular file: {candidate}"
            )
        offset = 0
        while offset < len(content):
            written = os.write(descriptor, content[offset:])
            if written <= 0:
                raise UnsafeVerificationPath(
                    f"verification output write made no progress: {candidate}"
                )
            offset += written
        os.fsync(descriptor)
    except OSError as exc:
        raise UnsafeVerificationPath(
            f"verification output could not be written safely: {candidate}"
        ) from exc
    finally:
        os.close(descriptor)


def sha256_path(path: Path) -> str:
    return sha256_bytes(safe_bytes(path))


def load_owner() -> tuple[dict, dict, dict, dict]:
    claims = json.loads(safe_text(CLAIMS_PATH))
    packet = claims.get("external_verification_packet")
    if not isinstance(packet, dict):
        raise ValueError("docs/claims.json lacks external_verification_packet")
    if packet.get("scope") != "all_eight_public_problem_programmes":
        raise ValueError("external verification scope must cover all eight programmes")
    source = json.loads(safe_text(PROBLEM_SOURCE_PATH))
    projection = json.loads(safe_text(PROBLEM_PROJECTION_PATH))
    expected_ids = packet.get("problem_ids")
    source_ids = [row.get("problem_id") for row in source.get("problems", [])]
    projection_ids = [row.get("problem_id") for row in projection.get("problems", [])]
    if source_ids != expected_ids or projection_ids != expected_ids:
        raise ValueError("external verification problem_ids must match both canonical problem indexes")
    if source.get("problem_count", len(source_ids)) != 8 or projection.get("problem_count") != 8:
        raise ValueError("canonical problem indexes must cover exactly eight programmes")
    if any(row.get("status") != "open" for row in projection["problems"]):
        raise ValueError("every canonical problem-index row must retain status=open")
    return claims, packet, source, projection


def load_signal_authority() -> dict:
    """Read the existing mathematical-value judgement without copying it here."""
    showcase = json.loads(safe_text(PALOMAR_SHOWCASE_PATH))
    if showcase.get("schema") != "plectis-palomar-result-showcase/1":
        raise ValueError("Palomar result showcase has an unsupported schema")
    ranking = showcase.get("candidate_ranking")
    screening = showcase.get("candidate_screening")
    universe = showcase.get("candidate_universe")
    contract = showcase.get("selection_contract")
    if not isinstance(ranking, list) or not ranking:
        raise ValueError("Palomar result showcase lacks candidate_ranking")
    if not isinstance(contract, dict) or not contract.get("ranking_axes"):
        raise ValueError("Palomar result showcase lacks its selection contract")
    if not isinstance(screening, list) or not screening:
        raise ValueError("Palomar result showcase lacks candidate_screening")
    if not isinstance(universe, dict) or not universe.get("source_family_dispositions"):
        raise ValueError("Palomar result showcase lacks its candidate universe")
    ranks = [row.get("rank") for row in ranking]
    declarations = [row.get("declaration") for row in ranking]
    if sorted(ranks) != list(range(1, len(ranking) + 1)):
        raise ValueError("Palomar candidate_ranking must use unique contiguous ranks")
    if len(declarations) != len(set(declarations)) or any(
        not isinstance(name, str) or not name for name in declarations
    ):
        raise ValueError("Palomar candidate_ranking declarations must be unique")
    return {
        "selection_contract": contract,
        "candidate_ranking": ranking,
        "candidate_screening": screening,
        "candidate_universe": universe,
    }


def declaration_exists(source: str, full_name: str) -> bool:
    path = ROOT / source
    short = full_name.rsplit(".", 1)[-1]
    try:
        text = safe_text(path)
    except (OSError, UnicodeError, UnsafeVerificationPath):
        return False
    return re.search(
        rf"^\s*(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
        rf"(?:theorem|def|abbrev|structure|class)\s+{re.escape(short)}\b",
        text,
        re.M,
    ) is not None


def module_path(module: str) -> Path | None:
    path = ROOT / (module.replace(".", "/") + ".lean")
    return path if path.is_file() else None


def internal_import_closure(start_module: str) -> list[Path]:
    queue = [start_module]
    seen_modules: set[str] = set()
    paths: list[Path] = []
    while queue:
        module = queue.pop(0)
        if module in seen_modules:
            continue
        seen_modules.add(module)
        path = module_path(module)
        if path is None:
            continue
        paths.append(path)
        for imported in imports_in_text(safe_text(path)):
            if module_path(imported) is not None:
                queue.append(imported)
    return sorted(paths)


def validate(packet: dict, problem_source: dict) -> tuple[list[Path], list[str]]:
    errors: list[str] = []
    claims = json.loads(safe_text(CLAIMS_PATH))["claims"]
    claim_by_id = {row["id"]: row for row in claims}
    expected_problems = {68, 243, 249, 251, 257, 269, 1041, 1049}
    results = packet.get("main_results", [])
    if len(results) < len(expected_problems):
        errors.append("Comparator must expose at least one exact interface for every problem")
    if {row.get("problem") for row in results} != expected_problems:
        errors.append("Comparator result coverage must equal the eight-problem portfolio")
    matrix_by_problem = {
        row["problem"]: {family["id"]: family for family in row.get("families", [])}
        for row in packet.get("review_matrix", [])
    }
    if set(matrix_by_problem) != expected_problems:
        errors.append("review_matrix coverage must equal the eight-problem portfolio")
    wrapper_sources = {
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Solution.lean",
    }
    for result in results:
        family = matrix_by_problem.get(result["problem"], {}).get(result.get("review_family"))
        if family is None:
            errors.append(f"Comparator result {result['id']} lacks a review_matrix family owner")
        if "original theoretical result" in result.get("contribution_class", "").lower():
            errors.append(
                f"result {result['id']} infers originality from local proof provenance"
            )
        if PRIOR_RESULT_RE.search(result.get("contribution_class", "")):
            mapping = source_fidelity(packet, result["id"]) or source_fidelity(
                packet, result.get("review_family", "")
            )
            if not mapping or not mapping.get("source_statement") or not mapping.get("mapping"):
                errors.append(f"prior-result interface {result['id']} lacks source fidelity")
        claim_id = result.get("claim_id")
        claim = claim_by_id.get(claim_id) if claim_id else None
        if claim_id and claim is None:
            errors.append(f"unknown claim_id: {claim_id}")
        original = result["original_declaration"]
        source = result["original_source"]
        if not declaration_exists(source, original):
            errors.append(f"missing original declaration {original} in {source}")
        short_original = original.rsplit(".", 1)[-1]
        if claim is not None and not any(
            d.get("name") == short_original and d.get("module") == source
            for d in claim.get("declarations", [])
        ):
            errors.append(f"result {result['id']} is not owned by claim {claim_id}")
        wrapper = result["wrapper_declaration"]
        for wrapper_source in wrapper_sources:
            if not declaration_exists(wrapper_source, wrapper):
                errors.append(f"missing wrapper {wrapper} in {wrapper_source}")

    for problem, families in matrix_by_problem.items():
        for family_id, family in families.items():
            contribution_class = family.get("contribution_class", "")
            if "original theoretical result" in contribution_class.lower():
                errors.append(
                    f"family {problem}/{family_id} infers originality from local proof provenance"
                )
            if PRIOR_RESULT_RE.search(contribution_class):
                mapping = source_fidelity(packet, family_id)
                if not mapping or not mapping.get("source_statement") or not mapping.get("mapping"):
                    errors.append(f"prior-result family {problem}/{family_id} lacks source fidelity")

    for row in problem_source["problems"]:
        required = row.get("required_note_declarations", [])
        if not required:
            errors.append(f"problem {row['erdos_number']} has no required note declarations")
        for declaration in required:
            source = declaration["module"].replace(".", "/") + ".lean"
            full_name = declaration["module"].rsplit(".", 1)[0] + "." + declaration["declaration"]
            if not declaration_exists(source, full_name):
                errors.append(
                    f"problem {row['erdos_number']} required declaration is missing: "
                    f"{full_name} in {source}"
                )

    closure = internal_import_closure(packet["comparator"]["challenge_module"])
    closure_rel = [path.relative_to(ROOT).as_posix() for path in closure]
    expected = [
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Statements.lean",
    ]
    if closure_rel != expected:
        errors.append(f"challenge internal import closure drifted: {closure_rel!r}")
    for path in closure:
        text = safe_text(path)
        for imported in imports_in_text(text):
            if imported.startswith("Erdos249257.") or imported.startswith("ErdosProblems."):
                errors.append(f"proof-bearing import leaked into challenge closure: {path}: {imported}")
    workflow = safe_text(ROOT / ".github/workflows/lean.yml")
    for tool, revision in packet["comparator"]["pins"].items():
        if revision not in workflow:
            errors.append(f"workflow does not bind the claim-owned {tool} revision {revision}")
    return closure, errors


def load_comparator_source(packet: dict) -> tuple[dict, bytes]:
    """Consume the Comparator-owned roster without promoting it to claim source."""
    config_path = OUTPUTS["config"]
    config_bytes = safe_bytes(config_path)
    try:
        config = json.loads(config_bytes)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("Comparator config is not valid UTF-8 JSON") from exc
    if not isinstance(config, dict):
        raise ValueError("Comparator config must be a JSON object")
    required = {
        "challenge_module",
        "solution_module",
        "theorem_names",
        "permitted_axioms",
        "enable_nanoda",
    }
    if set(config) != required:
        raise ValueError(
            "Comparator config keys drifted: "
            f"expected={sorted(required)!r} actual={sorted(config)!r}"
        )
    names = config["theorem_names"]
    if not isinstance(names, list) or not names or not all(
        isinstance(name, str) and name for name in names
    ):
        raise ValueError("Comparator theorem_names must be a nonempty string array")
    if len(names) != len(set(names)):
        raise ValueError("Comparator theorem_names must be unique")
    packet_comparator = packet["comparator"]
    for field in ("challenge_module", "solution_module", "permitted_axioms", "enable_nanoda"):
        if config[field] != packet_comparator[field]:
            raise ValueError(f"Comparator {field} disagrees with packet authority")
    selected = [row["wrapper_declaration"] for row in packet["main_results"]]
    missing = [name for name in selected if name not in names]
    if missing:
        raise ValueError(
            "Comparator roster omits selected packet interfaces: " f"{missing!r}"
        )
    return config, config_bytes


def negative_config(packet: dict) -> dict:
    fixture = next(
        row for row in packet["main_results"]
        if row["id"] == "totient_kernel_finite_rank"
    )
    return {
        "challenge_module": packet["comparator"]["challenge_module"],
        "solution_module": "ExternalVerification.NegativeSolution",
        "theorem_names": [fixture["wrapper_declaration"]],
        "permitted_axioms": packet["comparator"]["permitted_axioms"],
        "enable_nanoda": False,
    }


def quote(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


SORRY_RE = re.compile(r"\bsorry\b")
CHALLENGE_FILENAME = "Challenge.lean"


def _lean_sources() -> list[Path]:
    """Every committed Lean source, excluding build output."""
    return sorted(p for p in ROOT.rglob("*.lean") if ".lake" not in p.parts)


def sorry_census() -> dict:
    """Derive the `sorry` accounting in `formalization.yaml` from the tree.

    These four numbers used to be hand-written literals here, and they drifted:
    the projection reported one `sorry` and said "The only sorry is ...", while
    two statement-isolated Challenge fixtures carried one each.  Counting them
    means the published number cannot disagree with the source again.

    The scan reuses the lexer in ``scripts/lean_source.py`` — the same one the
    release gate uses — so that prose in a docstring asserting the *absence* of
    `sorry` is not counted as one.  A second, divergent lexer here would be its
    own defect, and that module is stdlib-only precisely so this builder can
    reach it without importing the release gate's heavier dependencies.
    """
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from lean_source import LIBRARY_ROOTS, lean_code_without_comments_and_strings

    root_lean_files = {f"{root}.lean" for root in LIBRARY_ROOTS}
    challenge: dict[str, int] = {}
    corpus: dict[str, int] = {}
    other: dict[str, int] = {}
    for path in _lean_sources():
        text = path.read_text(encoding="utf-8")
        if "sorry" not in text:
            continue
        count = len(SORRY_RE.findall(lean_code_without_comments_and_strings(text)))
        if not count:
            continue
        rel = path.relative_to(ROOT).as_posix()
        if path.name == CHALLENGE_FILENAME:
            challenge[rel] = count
        elif path.parts[len(ROOT.parts)] in LIBRARY_ROOTS or rel in root_lean_files:
            corpus[rel] = count
        else:
            other[rel] = count

    # The guard, not just the count: a `sorry` anywhere other than a declared
    # Challenge fixture is a proof-trust failure, and must not be absorbed into
    # a total that still reads as "intentional".
    if corpus or other:
        offenders = ", ".join(sorted({**corpus, **other}))
        raise SystemExit(
            "build_external_verification: sorry outside a statement-isolated "
            f"Challenge fixture: {offenders}"
        )

    return {
        "challenge": challenge,
        "total": sum(challenge.values()),
        "corpus_total": 0,
    }


def render_sorry_boundary(census: dict) -> str:
    """Name the fixtures rather than asserting a count the reader cannot check."""
    files = sorted(census["challenge"])
    if not files:
        return (
            "No sorry anywhere in the repository, including the Comparator "
            "challenge fixtures."
        )
    listed = "; ".join(files)
    where = (
        f"the statement-isolated Comparator challenge fixture ({listed})"
        if len(files) == 1
        else f"one of the statement-isolated Comparator challenge fixtures ({listed})"
    )
    return (
        f"Every sorry is a trusted proposition package in {where}. Each is the "
        "fixture against which Comparator checks the proof-bearing solution; "
        "the proof corpus and every solution wrapper have sorry_count 0."
    )


def render_formalization(
    packet: dict, problem_projection: dict, comparator_source: dict
) -> str:
    schema_commit = packet["formalization_schema"]["commit"]
    census = sorry_census()
    lines = [
        f"# yaml-language-server: $schema=https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/{schema_commit}/schema/formalization.schema.json",
        "# Generated from docs/claims.json::external_verification_packet.",
        "# Refresh: python3 scripts/build_external_verification.py",
        f"version: {quote(packet['formalization_schema']['version'])}",
        "project:",
        "  name: \"Eight open Erdős problems: checked subsidiary mathematics\"",
        "  description: \"Lean 4 formalization of subsidiary mathematics for eight open Erdős problems, including unconditional irrationality theorems for structured Mersenne supports, exact conditional endpoint reductions, arithmetic classifications, and method barriers; none of the eight open problems is claimed solved.\"",
        "  authors:",
        "    - \"Will Cook\"",
        "  license: \"Apache-2.0\"",
        "  responsible_maintainers:",
        "    - \"Will Cook\"",
        "classification:",
        "  arxiv: [\"math.NT\", \"math.CO\"]",
        # Required by the Palomar submission spec, and empty here until now.
        # 11J72 (irrationality; linear independence over a field) is the code
        # the private source tree already carries for this corpus.
        "  msc2020: [\"11J72\"]",
        "sources:",
        "  - title: \"Erdős Problems 68, 243, 249, 251, 257, 269, 1041, and 1049\"",
        "    authors:",
        "      - \"Paul Erdős and collaborators\"",
        "    id: \"https://www.erdosproblems.com/\"",
        "    type: \"web discussion\"",
        "    relationship: \"background\"",
        "    license: \"external source; see source site\"",
        "    author_endorsement: \"n/a\"",
        "  - title: \"Repository problem notes and cited-source registry\"",
        "    authors:",
        "      - \"Will Cook\"",
        "    id: \"docs/papers/corpus.json\"",
        "    type: \"other\"",
        "    relationship: \"adapts\"",
        "    license: \"CC-BY-4.0\"",
        "    author_endorsement: \"n/a\"",
        "status:",
        "  scope: >-",
        "    All eight covered Erdős problems remain open. This repository checks",
        "    subsidiary theorems, formalises selected known results, verifies finite",
        "    instances, and records conditional reductions and method barriers.",
        f"  proof_corpus_sorry_count: {census['corpus_total']}",
        f"  sorry_count: {census['total']}",
        "  sorry_in_definitions: 0",
        f"  trusted_challenge_sorry_count: {census['total']}",
        f"  sorry_boundary: {quote(render_sorry_boundary(census))}",
        "  axioms:",
    ]
    for axiom in packet["comparator"]["permitted_axioms"]:
        lines.append(f"    - {quote(axiom)}")
    lines.append("  main_results:")
    for row in packet["main_results"]:
        lines.extend([
            f"    - declaration: {quote(row['original_declaration'])}",
            f"      file: {quote(row['original_source'])}",
            "      sorry_count: 0",
            "      axioms:",
        ])
        for axiom in packet["comparator"]["permitted_axioms"]:
            lines.append(f"        - {quote(axiom)}")
        lines.extend([
            f"      comparator_config: {quote(packet['comparator']['config'])}",
            f"      canonical_claim_status: {quote(canonical_claim_status(row))}",
            "      local_proof_provenance: \"proved_in_this_repository\"",
            "      novelty_status: \"unassessed_no_priority_claim\"",
            f"      contribution_class: {quote(row['contribution_class'])}",
            f"      statement: {quote(row['statement'])}",
            f"      boundary: {quote(row['boundary'])}",
            f"      comparator_declaration: {quote(row['wrapper_declaration'])}",
        ])
        fidelity = source_fidelity(packet, row["id"]) or source_fidelity(
            packet, row.get("review_family", "")
        )
        lines.append("      literature_dependencies:")
        if fidelity:
            for reference in fidelity.get("references", []):
                lines.append(f"        - source: {quote(reference)}")
            lines.extend([
                f"      source_statement: {quote(fidelity['source_statement'])}",
                f"      source_mapping: {quote(fidelity['mapping'])}",
                f"      historical_attribution: {quote(fidelity['historical_attribution'])}",
                f"      logical_dependency: {quote(fidelity['logical_dependency'])}",
            ])
        else:
            lines[-1] = "      literature_dependencies: []"
    lines.extend([
        "automation:",
        "  methods:",
        "    - method: \"agent\"",
        "      models: [\"OpenAI Codex and other disclosed agent systems\"]",
        "      framework: \"agent-assisted Lean formalisation and proof engineering\"",
        "      tool_setup: \"Repository-specific generators, release guards, and focused Lean builds\"",
        "    - method: \"other\"",
        "      framework: \"Pinned Lean kernel and statement-isolated Comparator CI\"",
        "comparator:",
        f"  config: {quote(packet['comparator']['config'])}",
        "  roster_source: \"verification/comparator.json\"",
        f"  theorem_name_count: {len(comparator_source['theorem_names'])}",
        "  theorem_names:",
        *[f"    - {quote(name)}" for name in comparator_source["theorem_names"]],
        "review:",
        "  status: \"self-assessed\"",
        "  reviewers: []",
        f"  notes: {quote(packet['review_status'])}",
        "fidelity:",
        "  divergences: >-",
        "    The checked results are subsidiary results or formalised prior mathematics; none is the open problem statement. Comparator checks formal statement identity and axioms, not informal significance, novelty, or source fidelity.",
        "alignment:",
        "  namespace: \"Erdos249257.ExternalVerification\"",
        "  statements:",
    ])
    for row in packet["main_results"]:
        lines.extend([
            f"    - source: {quote(row['statement'])}",
            f"      lean: {quote(row['original_declaration'])}",
            f"      module: {quote(row['original_source'])}",
            "      status: \"proved\"",
            f"      note: {quote(row['boundary'])}",
        ])
    lines.append("claim_review_matrix:")
    for problem in packet["review_matrix"]:
        lines.append(f"  - problem: {problem['problem']}")
        lines.append(f"    paper: {quote(problem['paper'])}")
        lines.append("    families:")
        for family in problem["families"]:
            lines.extend([
                f"      - id: {quote(family['id'])}",
                f"        contribution_class: {quote(family['contribution_class'])}",
                f"        evidence_mode: {quote(family['evidence_mode'])}",
                f"        comparator_disposition: {quote(family['comparator_disposition'])}",
                f"        summary: {quote(family['summary'])}",
                f"        boundary: {quote(family['boundary'])}",
            ])
            fidelity = source_fidelity(packet, family["id"])
            if fidelity:
                lines.extend([
                    f"        source_statement: {quote(fidelity['source_statement'])}",
                    f"        source_mapping: {quote(fidelity['mapping'])}",
                    f"        historical_attribution: {quote(fidelity['historical_attribution'])}",
                    f"        logical_dependency: {quote(fidelity['logical_dependency'])}",
                ])
    lines.extend([
        "external_verification:",
        "  owner: \"docs/claims.json::external_verification_packet\"",
        f"  problem_index: {quote(packet['problem_index_projection'])}",
        f"  problem_index_digest: {quote(sha256_path(PROBLEM_PROJECTION_PATH))}",
        f"  problem_count: {problem_projection['problem_count']}",
        "  problems:",
    ])
    for problem in problem_projection["problems"]:
        lines.extend([
            f"    - id: {quote(problem['problem_id'])}",
            f"      erdos_number: {problem['erdos_number']}",
            f"      status: {quote(problem['status'])}",
            f"      checked_frontier: {quote(problem['what_is_checked'][0])}",
            f"      open_frontier: {quote(problem['what_is_not_checked'][0])}",
            f"      claim_registry_status: {quote(problem['claim_registry_status'])}",
        ])
        research = problem.get("research_corpus")
        if isinstance(research, dict):
            files = research.get("files", {})
            strongest = research.get("strongest_result_summary", {})
            checkpoint = research.get("checkpoint_summary", {})
            lines.extend([
                "      research_frontier:",
                f"        directory: {quote(research['directory'])}",
                f"        authority_posture: {quote(research['authority_posture'])}",
                f"        reading_rule: {quote(research['reading_rule'])}",
                f"        frontier: {quote(files['frontier']['path'])}",
                f"        strongest_results: {quote(files['strongest_results']['path'])}",
                f"        manifest: {quote(files['manifest']['path'])}",
                f"        checkpoint: {quote(files['checkpoint']['path'])}",
                "        content_digests:",
                f"          frontier: {quote(files['frontier']['content_digest'])}",
                f"          strongest_results: {quote(files['strongest_results']['content_digest'])}",
                f"          manifest: {quote(files['manifest']['content_digest'])}",
                f"          checkpoint: {quote(files['checkpoint']['content_digest'])}",
                f"        activated_result_count: {strongest['result_count']}",
                f"        source_checkpoint: {quote(strongest['source_checkpoint'])}",
                f"        source_subtree_tree: {quote(checkpoint['source_subtree_tree'])}",
                "        promotion_boundary: \"This route is public research evidence only; it is not a reviewed claim-registry entry or a Comparator interface.\"",
            ])
    lines.extend([
        f"  trusted_challenge_holes: {census['total']}",
        "  packet: \"docs/EXTERNAL_VERIFICATION.md\"",
        "  receipt_contract: \"docs/external_verification_packet.json::receipt_contract\"",
        "",
    ])
    return "\n".join(lines)


def _md_code(name: str) -> str:
    """Render an identifier verbatim, so a reviewer can copy it and it still compiles.

    GitHub's HTML sanitiser strips <wbr>, and zero-width or soft-hyphen breaks
    survive but corrupt copy-paste, so no break markup is inserted at all.
    """
    escaped = (
        name.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
    )
    return "<code>" + escaped + "</code>"


def _programme_display_title(short_title: str) -> str:
    """Reuse the reviewed short title as a heading, without a leading article."""
    title = short_title.strip()
    if title[:4].lower() == "the ":
        title = title[4:]
    return title[:1].upper() + title[1:] if title else title


def _family_display_label(family_id: str) -> str:
    """Display-only sentence label for a snake_case family key (not a new claim title)."""
    words = family_id.replace("_", " ").strip()
    return words[:1].upper() + words[1:] if words else family_id


def _programme_anchor(erdos_number: int) -> str:
    return f"programme-{erdos_number}"


def _details_block(summary: str, body_lines: list[str]) -> list[str]:
    """Sibling <details> only; blank lines keep GitHub Markdown parsing stable."""
    return [
        "<details>",
        f"<summary>{summary}</summary>",
        "",
        *body_lines,
        "",
        "</details>",
        "",
    ]


def _render_family_item(family: dict) -> list[str]:
    """One Markdown list item = one family; explicit breaks keep fields grouped."""
    label = _family_display_label(family["id"])
    evidence = f"{family['contribution_class']} · {family['evidence_mode']}"
    return [
        f"- **{label}**<br>",
        f"  {family['summary']}<br>",
        f"  **Boundary.** {family['boundary']}<br>",
        f"  *Evidence.* {evidence}",
        "",
    ]


def _render_routing_item(family: dict) -> list[str]:
    """Sibling machine-routing lane; order matches the human family list."""
    return [
        f"- {_md_code(family['id'])}<br>",
        f"  Comparator: {_md_code(family['comparator_disposition'])}",
        "",
    ]


def _ranked_candidate_tier(candidate: dict) -> str:
    """Project the ranking into reader tiers without creating a second ranking."""
    if candidate["selection_status"] == "subordinate":
        return "structural"
    conditional_text = " ".join(
        str(candidate.get(key, ""))
        for key in (
            "consequence_and_endpoint_proximity",
            "mechanism_depth_and_natural_friction",
            "overclaim_risk",
            "why_not_ranked_first",
        )
    ).lower()
    if any(
        marker in conditional_text
        for marker in ("conditional", "unresolved", "missing producer", "not constructed")
    ):
        return "conditional"
    return "completed"


def _render_ranked_candidate(candidate: dict, result: dict) -> list[str]:
    """Keep consequence, hard step, evidence, and surviving boundary adjacent."""
    tier_labels = {
        "completed": "completed direct result",
        "conditional": "conditional endpoint route",
        "structural": "exact reduction or structural result",
    }
    return [
        (
            f"{candidate['rank']}. **{_family_display_label(candidate['family_id'])}** "
            f"({_md_code(candidate['declaration'])}; `{candidate['selection_status']}`)"
        ),
        f"   - **Reader tier.** {tier_labels[_ranked_candidate_tier(candidate)]}",
        f"   - **Consequence.** {candidate['consequence_and_endpoint_proximity']}",
        (
            "   - **Load-bearing mechanism.** "
            f"{candidate['mechanism_depth_and_natural_friction']}"
        ),
        (
            f"   - **Source and evidence.** [Lean source](../{result['original_source']}); "
            f"{candidate['evidence_certainty']}"
        ),
        (
            f"   - **Boundary.** {result['boundary']} "
            f"**Overclaim risk.** {candidate['overclaim_risk']}"
        ),
        "",
    ]


def _presentation_contract(signal_authority: dict) -> tuple[dict[str, dict], dict[str, dict]]:
    """Validate the authored reader tiers and explicit relational placements."""
    contract = signal_authority.get("selection_contract", {})
    tiers = contract.get("presentation_tiers")
    screening = signal_authority.get("candidate_screening")
    if not isinstance(tiers, list) or not tiers:
        raise ValueError("Palomar selection contract lacks presentation_tiers")
    if not isinstance(screening, list):
        raise ValueError("Palomar showcase lacks candidate_screening")

    orders = [tier.get("order") for tier in tiers]
    if sorted(orders) != list(range(1, len(tiers) + 1)):
        raise ValueError("Palomar presentation tiers must be unique and contiguous")
    tier_by_id = {tier["tier_id"]: tier for tier in tiers}
    if len(tier_by_id) != len(tiers):
        raise ValueError("Palomar presentation tier ids must be unique")

    tier_by_disposition: dict[str, dict] = {}
    for tier in tiers:
        for disposition in tier.get("candidate_screening_dispositions", []):
            if disposition in tier_by_disposition:
                raise ValueError(
                    f"Palomar screening disposition occurs in two tiers: {disposition}"
                )
            tier_by_disposition[disposition] = tier
    actual_dispositions = {row.get("disposition") for row in screening}
    missing = sorted(actual_dispositions - set(tier_by_disposition))
    if missing:
        raise ValueError(
            "Palomar presentation tiers must cover candidate_screening dispositions: "
            f"missing={missing!r}"
        )

    placements = contract.get("relational_placements")
    if not isinstance(placements, list):
        raise ValueError("Palomar selection contract lacks relational_placements")
    placement_by_family: dict[str, dict] = {}
    for placement in placements:
        family_id = placement["family_id"]
        if family_id in placement_by_family:
            raise ValueError(f"duplicate Palomar relational placement: {family_id}")
        if placement["tier_id"] not in tier_by_id:
            raise ValueError(
                f"Palomar relational placement has unknown tier: {family_id}"
            )
        placement_by_family[family_id] = placement
    return tier_by_disposition, placement_by_family


def _programme_signal_rows(packet: dict, signal_authority: dict) -> dict[int, list[dict]]:
    """Project one authored, order-independent signal spine for every programme."""
    tier_by_disposition, placement_by_family = _presentation_contract(signal_authority)
    result_by_declaration = {
        row["wrapper_declaration"]: row for row in packet["main_results"]
    }
    family_by_key = {
        (int(problem["problem"]), family["id"]): family
        for problem in packet["review_matrix"]
        for family in problem["families"]
    }
    family_by_id = {
        family_id: (problem, family)
        for (problem, family_id), family in family_by_key.items()
    }
    dispositions = signal_authority["candidate_universe"][
        "source_family_dispositions"
    ]
    expected_family_ids = {family_id for _, family_id in family_by_key}
    if set(dispositions) != expected_family_ids:
        raise ValueError(
            "Palomar source-family dispositions must cover the complete review matrix"
        )

    rows_by_key: dict[tuple[int, str], dict] = {}
    ranked_keys: set[tuple[int, str]] = set()
    matched_placements: set[str] = set()
    ranked_tier = next(
        tier
        for tier in signal_authority["selection_contract"]["presentation_tiers"]
        if tier["tier_id"] == "source_ranked_frontier"
    )
    for candidate in sorted(
        signal_authority["candidate_ranking"], key=lambda row: row["rank"]
    ):
        result = result_by_declaration[candidate["declaration"]]
        key = (int(result["problem"]), result["review_family"])
        family = family_by_key[key]
        rows_by_key[key] = {
            "tier_order": ranked_tier["order"],
            "tier_id": ranked_tier["tier_id"],
            "tier_label": ranked_tier["label"],
            "within_tier_order": candidate["rank"],
            "global_rank": candidate["rank"],
            "family_id": family["id"],
            "signal_family_id": candidate["family_id"],
            "source_disposition": dispositions[family["id"]],
            "declaration": candidate["declaration"],
            "source_file": result["original_source"],
            "why_here": candidate["consequence_and_endpoint_proximity"],
            "boundary": result["boundary"],
        }
        ranked_keys.add(key)

    for screening_row in signal_authority["candidate_screening"]:
        declaration = screening_row["declaration"]
        result = result_by_declaration.get(declaration)
        family_owner = family_by_id.get(screening_row["family_id"])
        if result is None and family_owner is None:
            raise ValueError(
                "Palomar candidate_screening row lacks a Comparator result and review "
                f"family owner: {declaration}"
            )
        if result is not None:
            key = (int(result["problem"]), result["review_family"])
        else:
            problem, family = family_owner
            key = (problem, family["id"])
        if key in ranked_keys:
            continue
        family = family_by_key[key]
        tier = tier_by_disposition[screening_row["disposition"]]
        placement = placement_by_family.get(family["id"])
        if placement is not None and placement["tier_id"] != tier["tier_id"]:
            placement = None
        if placement is not None:
            matched_placements.add(family["id"])
        within_tier_order = (
            placement["within_tier_order"] if placement is not None else 1_000_000
        )
        candidate_row = {
            "tier_order": tier["order"],
            "tier_id": tier["tier_id"],
            "tier_label": tier["label"],
            "within_tier_order": within_tier_order,
            "global_rank": None,
            "family_id": family["id"],
            "signal_family_id": screening_row["family_id"],
            "source_disposition": dispositions[family["id"]],
            "screening_disposition": screening_row["disposition"],
            "declaration": declaration,
            "source_file": (
                result["original_source"]
                if result is not None
                else "ExternalVerification/Statements.lean"
            ),
            "why_here": (
                placement["relative_judgement"]
                if placement is not None
                else screening_row["reason"]
            ),
            "boundary": family["boundary"],
        }
        previous = rows_by_key.get(key)
        candidate_key = (
            candidate_row["tier_order"],
            candidate_row["within_tier_order"],
            candidate_row["declaration"],
        )
        previous_key = (
            previous["tier_order"],
            previous["within_tier_order"],
            previous["declaration"],
        ) if previous is not None else None
        if previous is None or candidate_key < previous_key:
            rows_by_key[key] = candidate_row

    tiers_by_id = {
        tier["tier_id"]: tier
        for tier in signal_authority["selection_contract"]["presentation_tiers"]
    }
    represented_placements = signal_authority["selection_contract"].get(
        "represented_family_placements"
    )
    if not isinstance(represented_placements, list):
        raise ValueError("Palomar selection contract lacks represented-family placements")
    for placement in represented_placements:
        family_id = placement["family_id"]
        owner = family_by_id.get(family_id)
        if owner is None:
            raise ValueError(
                f"Palomar represented-family placement lacks review owner: {family_id}"
            )
        problem, family = owner
        key = (problem, family_id)
        if dispositions[family_id] != "represented":
            raise ValueError(
                f"Palomar represented-family placement is not represented: {family_id}"
            )
        tier = tiers_by_id.get(placement["tier_id"])
        if tier is None:
            raise ValueError(
                f"Palomar represented-family placement has unknown tier: {family_id}"
            )
        if key in rows_by_key:
            # A source family may gain a Comparator-screened declaration after
            # its authored represented-family placement was established. The
            # screening row supplies stronger evidence; the placement still
            # owns its reader tier and relative judgement. Coalesce the two
            # accounts instead of emitting a duplicate family or rejecting a
            # source-current Comparator roster.
            existing = rows_by_key[key]
            if existing["tier_id"] != tier["tier_id"]:
                raise ValueError(
                    "Palomar screened declaration conflicts with represented-family "
                    f"tier: {family_id} is screened into {existing['tier_id']!r} but "
                    f"placed in {tier['tier_id']!r}"
                )
            existing["why_here"] = placement["relative_judgement"]
            continue
        rows_by_key[key] = {
            "tier_order": tier["order"],
            "tier_id": tier["tier_id"],
            "tier_label": tier["label"],
            "within_tier_order": 1_000_000,
            "global_rank": None,
            "family_id": family_id,
            "signal_family_id": family_id,
            "source_disposition": dispositions[family_id],
            "declaration": f"review_family:{family_id}",
            "source_kind": "canonical_review_family",
            "source_file": "docs/claims.json",
            "why_here": placement["relative_judgement"],
            "boundary": family["boundary"],
        }

    missing_placements = sorted(set(placement_by_family) - matched_placements)
    if missing_placements:
        raise ValueError(
            "Palomar relational placements lack a matching screening tier: "
            f"{missing_placements!r}"
        )

    relations = signal_authority["selection_contract"].get("family_relations")
    if not isinstance(relations, list):
        raise ValueError("Palomar selection contract lacks family relations")
    relation_rows_by_family: dict[str, list[dict]] = {}
    for relation in relations:
        source_family = relation["from_family_id"]
        target_family = relation["to_family_id"]
        if source_family not in family_by_id or target_family not in family_by_id:
            raise ValueError("Palomar family relation names an unknown review family")
        relation_rows_by_family.setdefault(source_family, []).append(
            {**relation, "direction": "outgoing"}
        )
        relation_rows_by_family.setdefault(target_family, []).append(
            {**relation, "direction": "incoming"}
        )
    for row in rows_by_key.values():
        row["relations"] = relation_rows_by_family.get(row["family_id"], [])

    rows_by_problem: dict[int, list[dict]] = {}
    for (problem, _), row in rows_by_key.items():
        rows_by_problem.setdefault(problem, []).append(row)
    programme_order = signal_authority["selection_contract"].get(
        "programme_family_order"
    )
    if not isinstance(programme_order, list):
        raise ValueError("Palomar selection contract lacks programme-family order")
    order_by_problem = {
        int(row["problem"]): row["family_ids"] for row in programme_order
    }
    if len(order_by_problem) != len(programme_order):
        raise ValueError("Palomar programme-family order repeats a problem")
    if set(order_by_problem) != set(rows_by_problem):
        raise ValueError("Palomar programme-family order does not cover every dossier")
    for problem, rows in rows_by_problem.items():
        authored_order = order_by_problem[problem]
        if len(authored_order) != len(set(authored_order)):
            raise ValueError(
                f"Palomar programme-family order repeats a family for #{problem}"
            )
        emitted_ids = {row["family_id"] for row in rows}
        if set(authored_order) != emitted_ids:
            raise ValueError(
                f"Palomar programme-family order is not signal-complete for #{problem}"
            )
        order_index = {family_id: index for index, family_id in enumerate(authored_order)}
        rows.sort(key=lambda row: order_index[row["family_id"]])
        for local_rank, row in enumerate(rows, start=1):
            row["programme_order"] = local_rank
    return rows_by_problem


def _render_programme_signal(rows: list[dict]) -> list[str]:
    lines = [
        "### First-contact mathematical order",
        "",
        (
            "This is Palomar's source-current reader order, not review-matrix or "
            "Comparator roster order. Ranked results lead; conditional endpoint leverage, "
            "deep mechanisms, natural friction, and supporting rows follow unequally."
        ),
        "",
    ]
    for row in rows:
        rank_note = (
            f"; global rank {row['global_rank']}"
            if row["global_rank"] is not None
            else ""
        )
        source_line = (
            f"   - **Source authority.** Canonical review family "
            f"`{row['family_id']}` in [claims](../{row['source_file']})"
            if row.get("source_kind") == "canonical_review_family"
            else (
                f"   - **Source.** {_md_code(row['declaration'])} in "
                f"[Lean](../{row['source_file']})"
            )
        )
        lines.extend(
            [
                (
                    f"{row['programme_order']}. **{_family_display_label(row['family_id'])}** "
                    f"(`{row['family_id']}`; {row['tier_label']}{rank_note}; "
                    f"source disposition `{row['source_disposition']}`)"
                ),
                f"   - **Why here.** {row['why_here']}",
                source_line,
                f"   - **Boundary.** {row['boundary']}",
            ]
        )
        for relation in row.get("relations", []):
            other = (
                relation["to_family_id"]
                if relation["direction"] == "outgoing"
                else relation["from_family_id"]
            )
            lines.append(
                f"   - **Relation.** `{relation['relation']}` `{other}`: "
                f"{relation['reason']}"
            )
        lines.append("")
    return lines


def _render_complete_candidate_universe(packet: dict, signal_authority: dict) -> list[str]:
    universe = signal_authority["candidate_universe"]
    dispositions = universe["source_family_dispositions"]
    family_owner = {
        family["id"]: int(problem["problem"])
        for problem in packet["review_matrix"]
        for family in problem["families"]
    }
    if set(dispositions) != set(family_owner):
        raise ValueError("Palomar candidate universe is not review-matrix complete")
    disposition_order = signal_authority["selection_contract"].get(
        "source_family_disposition_order"
    )
    if not isinstance(disposition_order, list):
        raise ValueError("Palomar selection contract lacks source disposition order")
    lines = [
        "### Complete serious-result universe",
        "",
        (
            f"All {len(dispositions)} source-current review families are accounted for here. "
            "The categories preserve honest selection reasons while the programme dossiers "
            "below retain each family's exact mechanism and boundary. This inventory is "
            "complete but deliberately does not compete with the ranked frontier for attention."
        ),
        "",
    ]
    for disposition in disposition_order:
        family_ids = sorted(
            family_id
            for family_id, value in dispositions.items()
            if value == disposition
        )
        if not family_ids:
            continue
        linked = ", ".join(
            f"[#{family_owner[family_id]}](#{_programme_anchor(family_owner[family_id])}) "
            f"`{family_id}`"
            for family_id in family_ids
        )
        lines.extend(
            [
                f"- **{disposition.replace('_', ' ')} ({len(family_ids)}).** {linked}",
                "",
            ]
        )
    return lines


def _render_signal_spine(packet: dict, signal_authority: dict) -> list[str]:
    result_by_declaration = {
        row["wrapper_declaration"]: row for row in packet["main_results"]
    }
    ranked = sorted(signal_authority["candidate_ranking"], key=lambda row: row["rank"])
    missing = [
        row["declaration"]
        for row in ranked
        if row["declaration"] not in result_by_declaration
    ]
    if missing:
        raise ValueError(
            "Palomar candidate_ranking declarations lack Comparator interfaces: "
            + ", ".join(missing)
        )

    lines = [
        "## Mathematical signal spine",
        "",
        (
            "This order projects Palomar's mathematical `candidate_ranking`; it is independent "
            "of Comparator roster order, programme number, insertion time, theorem count, and "
            "qualification convenience. Comparator coverage is the exhaustive evidence inventory, "
            "not a significance ranking. Checked propositions are therefore given unequal reader "
            "attention: each promoted result keeps its hard step and surviving boundary adjacent."
        ),
        "",
        "### Reader tiers",
        "",
        (
            "- **Completed direct results:** unconditional checked consequences with their "
            "scope kept visible."
        ),
        (
            "- **Conditional endpoint routes:** target-facing routes whose explicit producer "
            "or selector remains open."
        ),
        (
            "- **Exact endpoint reductions and structural results:** results that sharpen the "
            "remaining problem without being presented as endpoint theorems."
        ),
        "",
        "### Source-ranked frontier",
        "",
    ]
    tiers = {_ranked_candidate_tier(row) for row in ranked}
    if tiers != {"completed", "conditional", "structural"}:
        raise ValueError("Palomar candidate_ranking must populate all three reader tiers")
    for candidate in ranked:
        lines.extend(
            _render_ranked_candidate(
                candidate, result_by_declaration[candidate["declaration"]]
            )
        )

    no_go_rows = sorted(
        (
            (int(problem["problem"]), family)
            for problem in packet["review_matrix"]
            for family in problem["families"]
            if "no-go" in family.get("contribution_class", "").lower()
            or "obstruction" in family.get("contribution_class", "").lower()
            or "no_go" in family["id"]
        ),
        key=lambda item: item[1]["id"],
    )
    if not no_go_rows:
        raise ValueError("review_matrix lacks natural-friction/no-go families")
    lines.extend(
        [
            "### Natural friction and no-go boundaries",
            "",
            (
                "These checked obstructions are an alphabetical, deliberately unranked tier. "
                "They show where natural proof friction survives without competing with direct "
                "endpoint results for headline position."
            ),
            "",
        ]
    )
    for problem, family in no_go_rows:
        lines.extend(
            [
                (
                    f"- **[#{problem}](#{_programme_anchor(problem)}) · "
                    f"{_family_display_label(family['id'])}** (`{family['id']}`)<br>"
                ),
                f"  {family['summary']}<br>",
                f"  **Boundary.** {family['boundary']}<br>",
                (
                    f"  *Evidence.* {family['contribution_class']} · "
                    f"{family['evidence_mode']}"
                ),
                "",
            ]
        )
    lines.extend(
        [
            "### Complete inventory, kept subordinate",
            "",
            (
                "Every contribution family and every statement-isolated interface remains "
                "queryable in the programme dossiers and the [Comparator interface appendix]"
                "(#comparator-interface-appendix). Subordination is a presentation judgement, "
                "not deletion or an adverse mathematical disposition."
            ),
            "",
        ]
    )
    lines.extend(_render_complete_candidate_universe(packet, signal_authority))
    return lines


def render_human(
    packet: dict,
    problem_source: dict,
    problem_projection: dict,
    signal_authority: dict,
) -> str:
    source_by_id = {row["problem_id"]: row for row in problem_source["problems"]}
    families_by_problem = {
        int(problem["problem"]): problem["families"] for problem in packet["review_matrix"]
    }
    interfaces_by_problem: dict[int, list[dict]] = {}
    for row in packet["main_results"]:
        interfaces_by_problem.setdefault(int(row["problem"]), []).append(row)
    programme_signal = _programme_signal_rows(packet, signal_authority)

    index_links: list[str] = []
    dossier_blocks: list[str] = []
    for row in problem_projection["problems"]:
        source = source_by_id[row["problem_id"]]
        number = int(row["erdos_number"])
        title = _programme_display_title(row["short_title"])
        anchor = _programme_anchor(number)
        index_links.append(f"[#{number}: {title}](#{anchor})")

        representative = source["required_note_declarations"][0]
        full_name = (
            representative["module"].rsplit(".", 1)[0] + "." + representative["declaration"]
        )
        source_path = representative["module"].replace(".", "/") + ".lean"
        paper = row["paper"]
        families = families_by_problem[number]
        family_items: list[str] = []
        routing_items: list[str] = []
        for family in families:
            family_items.extend(_render_family_item(family))
            routing_items.extend(_render_routing_item(family))
        if family_items and family_items[-1] == "":
            family_items.pop()
        if routing_items and routing_items[-1] == "":
            routing_items.pop()

        dossier_blocks.extend(
            [
                f'<a id="{anchor}"></a>',
                f"## #{number}: {title}",
                "",
                f"**Question.** {row['question']}",
                "",
                f"**Checked frontier.** {row['what_is_checked'][0]}",
                "",
                f"**Open boundary.** {row['what_is_not_checked'][0]}",
                "",
                (
                    f"**Read.** [Programme paper](../{paper['pdf']}) · "
                    f"[Lean source](../{source_path})"
                ),
                "",
            ]
        )
        priority_note = source.get("source_priority_note")
        if isinstance(priority_note, str) and priority_note.strip():
            dossier_blocks.extend(
                _details_block(
                    "Source and priority note",
                    [priority_note.strip()],
                )
            )
        research = row.get("research_corpus")
        if isinstance(research, dict):
            files = research.get("files", {})
            strongest = research.get("strongest_result_summary", {})
            dossier_blocks.extend(
                _details_block(
                    "Source-current research frontier",
                    [
                        (
                            f"[Dated frontier](../{files['frontier']['path']}) · "
                            f"[strongest-result map](../{files['strongest_results']['path']}) · "
                            f"[corpus manifest](../{files['manifest']['path']}) · "
                            f"[checkpoint](../{files['checkpoint']['path']})"
                        ),
                        "",
                        (
                            f"This source-fingerprinted route contains {strongest['result_count']} "
                            f"activated research results at source checkpoint "
                            f"`{strongest['source_checkpoint']}`. Read the dated frontier first: "
                            "the map preserves hypotheses, falsifiers, and open gaps."
                        ),
                        "",
                        (
                            "Authority boundary: these are public research evidence, not reviewed "
                            "claim-registry entries or Comparator interfaces. They do not close "
                            "Erdős #1041 or promote research-corpus rows into the checked result set."
                        ),
                    ],
                )
            )
        dossier_blocks.extend(
            _details_block(
                "Representative checked declaration",
                [_md_code(full_name)],
            )
        )
        dossier_blocks.extend(_render_programme_signal(programme_signal.get(number, [])))
        dossier_blocks.extend(
            _details_block(
                f"Contribution families ({len(families)})",
                [
                    "Exact registry keys and Comparator routing are listed separately.",
                    "",
                    *family_items,
                ],
            )
        )
        dossier_blocks.extend(
            _details_block(
                f"Technical registry and Comparator routing ({len(families)})",
                routing_items,
            )
        )
        dossier_blocks.append("---")
        dossier_blocks.append("")

    interface_body: list[str] = []
    for row in problem_projection["problems"]:
        number = int(row["erdos_number"])
        title = _programme_display_title(row["short_title"])
        interfaces = interfaces_by_problem.get(number, [])
        if not interfaces:
            continue
        interface_body.extend([f"**#{number}: {title}**", ""])
        for item in interfaces:
            status = canonical_claim_status(item)
            interface_body.extend(
                [
                    f"- {_md_code(item['wrapper_declaration'])}",
                    f"  - **Class.** {item['contribution_class']}",
                    f"  - **Statement.** {item['statement']}",
                    f"  - **Canonical claim status.** `{status}`",
                    "  - **Novelty.** unassessed; no priority claim",
                    f"  - **Boundary.** {item['boundary']}",
                    "",
                ]
            )

    human = "\n".join(
        [
            "<!-- Generated by scripts/build_external_verification.py; do not edit. -->",
            "# Plectis verification: eight open Erdős programmes",
            "",
            "> [!IMPORTANT]",
            "> **Status:** All eight public problem programmes remain open.",
            f"> **Review posture:** {packet['review_status'][0].upper() + packet['review_status'][1:]}.",
            "",
            (
                "**What this is.** Plectis is an AI-assisted research system. This public "
                "surface shows one checked frontier for each of eight open Erdős problems. "
                "For each programme, read the question, the exact checked object, and the "
                "remaining open step before opening the technical registry."
            ),
            "",
            # The dossiers below use "Comparator" from their first line onward.
            # Before this paragraph existed the term appeared roughly ninety
            # times and was only explained in the closing section, so a reviewer
            # met it as undefined jargon for the whole document. Define it once,
            # here, ahead of first use. (2026-08-15)
            (
                f"**How verification works.** The {len(packet['main_results'])} selected "
                "propositions are declared again without proofs. Comparator checks that the proof-bearing modules "
                "match those independent statements and a fixed axiom budget. A named "
                "altered statement must fail. This checks formal propositions only. It "
                "does not assess exposition, citations, intended meaning, novelty, or "
                "significance. Technical detail is in the [Comparator interface appendix]"
                "(#comparator-interface-appendix)."
            ),
            "",
            *_render_signal_spine(packet, signal_authority),
            "**Programmes.** " + " · ".join(index_links),
            "",
            "---",
            "",
            *dossier_blocks,
            "## Comparator interface appendix",
            "",
            *_details_block(
                f"Show all {len(packet['main_results'])} statement-isolated interfaces",
                interface_body,
            ),
            "## Verification contract and replay",
            "",
            (
                "Comparator is used only for exact Lean-owned propositions that can be isolated "
                "without importing their proofs; paper deductions, cited theorems, and external "
                "computations retain their own evidence classes."
            ),
            (
                "The `main_results` key in `formalization.yaml` is the format's list of selected "
                "executable interfaces. It is not the canonical claim registry and does not make "
                "an unregistered declaration a principal result."
            ),
            (
                f"The {len(packet['main_results'])} exact interfaces cover all eight programmes. "
                "Local proof provenance is recorded separately from novelty, which remains "
                "unassessed unless a source-fidelity row says otherwise. The trusted challenge "
                "contains one proposition-package fixture and imports only "
                "`ExternalVerification.Statements` and Mathlib."
            ),
            "The proof-bearing modules occur only in `ExternalVerification.Solution`.",
            "CI runs the pinned real Linux sandbox and uploads a commit-bound JSON receipt.",
            (
                "For a reviewer-run Linux check and the immutable release-asset contract, see "
                "`docs/EXTERNAL_VERIFICATION_REPLAY.md`."
            ),
            "",
            (
                "Use the precise phrase **Comparator-checked against a separately declared "
                "statement and axiom budget** only when the receipt for the displayed commit is "
                "green. Do not replace it with “independently verified”."
            ),
            "",
        ]
    )
    return human.replace("—", ":")


def render_outreach(packet: dict) -> str:
    return "\n".join([
        "<!-- Generated by scripts/build_external_verification.py; do not edit. -->",
        "# Outreach evidence capsules",
        "",
        "These are reusable evidence paragraphs only. Openings, mathematical motivation, and questions must remain recipient-specific and written in Will's own words.",
        "",
        "## Post-green generic capsule",
        "",
        "> To make the formal part easy to inspect, the repository includes a root `formalization.yaml` recording its provenance, automation, current review status, and the checked frontier for all eight covered problems. A small Comparator packet checks the theorem named above against a separately declared statement and axiom budget, then Lean's kernel checks the submitted proof. The attached CI receipt is bound to the repository commit. It does not claim that any of the eight Erdős problems is solved.",
        "",
        "## #249 boundary capsule",
        "",
        "> The checked local result is the exact rank `2^e+1` of the dyadic totient kernel through level `e`; the full-kernel infinite-dimensionality declaration is also kernel-checked, but is recorded as a formalised consequence of Coons rather than an independent contribution. For every base `k >= 2`, Lean separately checks the arithmetic reduction, exact finite residue coordinates, unconditional spanning by the canonical family, and exact rank `k^e+1` conditional on that family being linearly independent. Martin supplies the paper's all-base independence step externally and is not formalised. Comparator checks its selected statements and axiom budget. The missing rationality-to-finite-rank or unbounded-certificate bridge remains open, so Erdős #249 is not solved.",
        "",
        "## #257 boundary capsule",
        "",
        "> The checked result is the measure-one geometry of the Mersenne achievement set, plus a separate formalisation of the classical full-support Erdős–Borwein irrationality theorem. Comparator checks those statements and their axiom budget. Universal Erdős #257, including the rational targets `1/2` and `1/21`, remains open.",
        "",
    ])


def render_packet(
    packet: dict,
    problem_source: dict,
    problem_projection: dict,
    closure: list[Path],
    config_bytes: bytes,
    comparator_source: dict,
) -> str:
    result = json.loads(json.dumps(packet))
    for row in result["main_results"]:
        row["canonical_claim_status"] = canonical_claim_status(row)
        row["local_proof_provenance"] = "proved_in_this_repository"
        row["novelty_status"] = "unassessed_no_priority_claim"
    result["authority_posture"] = "generated_projection_not_proof_or_claim_authority"
    result["source_owner"] = "docs/claims.json::external_verification_packet"
    result["comparator"]["roster_source"] = "verification/comparator.json"
    result["comparator"]["theorem_name_count"] = len(
        comparator_source["theorem_names"]
    )
    result["comparator"]["theorem_names"] = comparator_source["theorem_names"]
    result["problem_index"] = {
        "owner": packet["problem_index_owner"],
        "owner_digest": sha256_path(PROBLEM_SOURCE_PATH),
        "projection": packet["problem_index_projection"],
        "projection_digest": sha256_path(PROBLEM_PROJECTION_PATH),
        "schema": problem_projection["schema"],
        "problem_count": problem_projection["problem_count"],
        "authority_posture": problem_projection["authority_posture"],
        "problems": problem_projection["problems"],
    }
    result["challenge_import_closure"] = {
        "internal_paths": [path.relative_to(ROOT).as_posix() for path in closure],
        "digest": sha256_bytes(
            b"".join(
                path.relative_to(ROOT).as_posix().encode()
                + b"\0"
                + safe_bytes(path)
                + b"\0"
                for path in closure
            )
        ),
        "proof_bearing_internal_import_count": 0,
    }
    result["trusted_build_inputs"] = {
        path: sha256_path(ROOT / path)
        for path in ("lakefile.toml", "lean-toolchain", "lake-manifest.json")
    }
    result["config_digest"] = sha256_bytes(config_bytes)
    result["solution_source_digest"] = sha256_path(ROOT / "ExternalVerification/Solution.lean")
    return json.dumps(result, indent=2, ensure_ascii=False) + "\n"


def build_outputs(
    packet: dict,
    problem_source: dict,
    problem_projection: dict,
    signal_authority: dict,
    closure: list[Path],
) -> dict[Path, bytes]:
    comparator_source, config_bytes = load_comparator_source(packet)
    negative_bytes = (json.dumps(negative_config(packet), indent=2) + "\n").encode()
    return {
        OUTPUTS["config"]: config_bytes,
        OUTPUTS["negative_config"]: negative_bytes,
        OUTPUTS["formalization"]: render_formalization(
            packet, problem_projection, comparator_source
        ).encode(),
        OUTPUTS["packet"]: render_packet(
            packet,
            problem_source,
            problem_projection,
            closure,
            config_bytes,
            comparator_source,
        ).encode(),
        OUTPUTS["human"]: render_human(
            packet, problem_source, problem_projection, signal_authority
        ).encode(),
        OUTPUTS["outreach"]: render_outreach(packet).encode(),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--only",
        choices=tuple(OUTPUTS),
        action="append",
        metavar="OUTPUT",
        help="check or write only the named projection(s); repeat for a disjoint refresh",
    )
    args = parser.parse_args()
    _, packet, problem_source, problem_projection = load_owner()
    signal_authority = load_signal_authority()
    closure, errors = validate(packet, problem_source)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    outputs = build_outputs(
        packet, problem_source, problem_projection, signal_authority, closure
    )
    selected = args.only or list(OUTPUTS)
    outputs = {OUTPUTS[name]: outputs[OUTPUTS[name]] for name in selected}
    stale: list[str] = []
    for path, content in outputs.items():
        if args.check:
            try:
                current = safe_bytes(path)
            except UnsafeVerificationPath:
                stale.append(path.relative_to(ROOT).as_posix())
            else:
                if current != content:
                    stale.append(path.relative_to(ROOT).as_posix())
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            safe_write_bytes(path, content)
            print(path.relative_to(ROOT).as_posix())
    if stale:
        print("stale external-verification projections: " + ", ".join(stale), file=sys.stderr)
        return 1
    if args.check:
        print("external-verification projections are current and challenge isolation is intact")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
