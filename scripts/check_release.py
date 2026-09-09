#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Cross-surface release checker.

The single owner of release identity and claim status is docs/claims.json.
This script verifies that every other public surface agrees with it:

  1. claims.json is well formed, every claim status is in the taxonomy, typed
     remaining-open propositions resolve, and the machine-readable paper graph
     resolves to real public files and claim ids.
  2. Release identity: lakefile.toml and CITATION.cff state the last tagged
     release, while the main exposition pin agrees with the exact committed
     formal-source checkpoint named in the registry.
  3. Every claimed Lean declaration exists in the stated module at the
     stated line.
  4. Every paper source link (\\lref / \\lrefx / \\lloc) resolves: the file
     exists and the named declaration appears at the stated line.
  5. SCOPE.md lists exactly the machine identifiers in claims.json.
  6. README.md carries the headline declarations, states the release tag,
     uses only taxonomy statuses in its status table, and contains none of
     the banned drift phrases.
  7. Licensing: every licence named in REUSE.toml or an SPDX header has its
     text under LICENSES/.
  8. AGENTS.md routes agent harnesses through the public machine-readable paper
     without weakening the proof or open-problem boundary; CONTRIBUTING.md
     describes the cold-clone baseline-plus-adversarial program as a release
     gate rather than an advisory diagnostic; and the public conduct standard
     remains present.
 9. Proof-trust guard: no sorry/admit/axiom or native evaluator in the
     Lean sources.
 10. The methodology source, generated root projection, claim-transition
     requirements, descriptor capsule, and entry routes agree.
 11. The systems paper's historical outcome and explicit evidence ceilings
     agree with the typed publication-evidence receipt.
 12. Digest-bound semantic review receipts remain attached to the exact
     statement or relation that was reviewed.
Stdlib only; run from the repository root:  python3 scripts/check_release.py
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
from pathlib import Path
from typing import Any

from check_problem_note_sources import note_pinned_commit, snapshot_lines_batch
from methodology_contract import mutation_fixture_errors, render_markdown, validate_contract
from lean_source import LIBRARY_ROOTS, lean_code_without_comments_and_strings
from publication_contract import (
    RepositoryReader,
    mutation_fixture_failures as publication_mutation_fixture_failures,
    validate_publication_contract,
)
from query_corpus import canonical_paper_anchor_key, paper_anchor_inventory
from systems_paper_evidence import (
    mutation_fixture_failures as systems_paper_mutation_fixture_failures,
    validate_systems_paper_evidence,
)
import validation_singleflight as singleflight
import refresh_projections

ROOT = Path(__file__).resolve().parent.parent
ERRORS: list[str] = []
CHECKS = 0
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
SUBPROCESS_TIMEOUT_SECONDS = singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS
SANITIZED_GIT_ENVIRONMENT_KEYS = tuple(sorted(singleflight.GIT_CONTEXT_KEYS))
_SUBPROCESS_RUN = subprocess.run
PROJECTION_CHECK_WORKERS = refresh_projections.CHECK_WORKERS
RELEASE_CHECK_WORKERS = 4
_PROJECTION_CHECK_RESULTS: dict[str, subprocess.CompletedProcess[str]] | None = None


def clean_environment() -> dict[str, str]:
    """Use the canonical isolated environment for every release-gate child."""
    return singleflight.command_environment()


def run(*args: Any, **kwargs: Any) -> subprocess.CompletedProcess[str]:
    """Run a release-gate subprocess with checkout-independent Git state."""
    kwargs["env"] = clean_environment()
    kwargs.setdefault("timeout", SUBPROCESS_TIMEOUT_SECONDS)
    builder = projection_check_builder(args, kwargs.get("cwd"))
    if builder is not None:
        return projection_check_results()[builder]
    return _SUBPROCESS_RUN(*args, **kwargs)


def projection_check_builder(args: tuple[Any, ...], cwd: Any) -> str | None:
    """Identify an exact read-only projection freshness invocation."""
    if len(args) != 1 or not isinstance(args[0], (list, tuple)) or Path(cwd) != ROOT:
        return None
    argv = list(args[0])
    if len(argv) != 3 or argv[0] != sys.executable or argv[2] != "--check":
        return None
    try:
        builder = Path(argv[1]).relative_to(ROOT).as_posix()
    except (TypeError, ValueError):
        return None
    return builder if builder in refresh_projections.BUILDERS else None


def projection_check_results() -> dict[str, subprocess.CompletedProcess[str]]:
    """Run the release gate's immutable projection checks once, in parallel."""
    global _PROJECTION_CHECK_RESULTS
    if _PROJECTION_CHECK_RESULTS is not None:
        return _PROJECTION_CHECK_RESULTS

    def check_builder(builder: str) -> tuple[str, subprocess.CompletedProcess[str]]:
        result = _SUBPROCESS_RUN(
            [sys.executable, str(ROOT / builder), "--check"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
            env=clean_environment(),
            timeout=SUBPROCESS_TIMEOUT_SECONDS,
        )
        return builder, result

    with ThreadPoolExecutor(
        max_workers=min(PROJECTION_CHECK_WORKERS, len(refresh_projections.BUILDERS))
    ) as executor:
        _PROJECTION_CHECK_RESULTS = dict(
            executor.map(check_builder, refresh_projections.BUILDERS)
        )
    return _PROJECTION_CHECK_RESULTS


def run_independent_checks(
    commands: dict[str, list[str]],
) -> dict[str, subprocess.CompletedProcess[str]]:
    """Run independent read-only release suites with bounded concurrency."""
    executor, futures = start_independent_checks(commands)
    return finish_independent_checks(executor, futures)


def _run_independent_check(argv: list[str]) -> subprocess.CompletedProcess[str]:
    return _SUBPROCESS_RUN(
        argv,
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        env=clean_environment(),
        timeout=SUBPROCESS_TIMEOUT_SECONDS,
    )


def start_independent_checks(
    commands: dict[str, list[str]],
    *,
    max_workers: int = RELEASE_CHECK_WORKERS,
) -> tuple[ThreadPoolExecutor, dict[str, Any]]:
    """Start bounded read-only checks whose results are consumed at a later barrier."""
    executor = ThreadPoolExecutor(max_workers=min(max_workers, len(commands)))
    return executor, {
        check_id: executor.submit(_run_independent_check, argv)
        for check_id, argv in commands.items()
    }


def finish_independent_checks(
    executor: ThreadPoolExecutor,
    futures: dict[str, Any],
) -> dict[str, subprocess.CompletedProcess[str]]:
    """Collect a previously started check batch and always close its workers."""
    try:
        return {check_id: future.result() for check_id, future in futures.items()}
    finally:
        executor.shutdown(wait=True, cancel_futures=True)


def late_check_commands() -> dict[str, list[str]]:
    """Read-only suites that may overlap the release gate's middle section."""
    return {
        # These are the two long readers in this two-worker pool. Start both
        # immediately; queuing cold-clone checks behind short diagnostics left
        # several seconds of avoidable work on the release critical path.
        "query": [sys.executable, str(ROOT / "scripts" / "test_query_corpus.py")],
        "cold_clone_adversarial": [
            sys.executable,
            str(ROOT / "scripts" / "test_cold_clone_comprehension.py"),
        ],
        "mutation_harness": [
            sys.executable,
            str(ROOT / "scripts" / "test_publication_mutation_harness.py"),
        ],
        "public_boundary": [
            sys.executable,
            str(ROOT / "scripts" / "test_public_artifact_boundary.py"),
        ],
        "primary_source_disposition": [
            sys.executable,
            str(ROOT / "scripts" / "check_primary_source_dispositions.py"),
        ],
        "proof_cockpit": [
            sys.executable,
            str(ROOT / "scripts" / "test_proof_cockpit.py"),
        ],
        "clone_footprint": [
            sys.executable,
            str(ROOT / "scripts" / "test_clone_footprint.py"),
        ],
    }


def publication_stage_check_results() -> dict[str, subprocess.CompletedProcess[str]]:
    """Share one bounded pool across projection and publication diagnostics.

    The projection freshness checks already form one parallel batch. Running
    the remaining independent publication diagnostics only after that batch
    left avoidable serial work on the release gate's critical path. Scheduling
    both groups together preserves every check and the projection result cache
    while keeping one four-worker ceiling.
    """
    global _PROJECTION_CHECK_RESULTS
    projection_prefix = "projection:"
    commands = {
        f"{projection_prefix}{builder}": [
            sys.executable,
            str(ROOT / builder),
            "--check",
        ]
        for builder in refresh_projections.BUILDERS
    }
    commands.update(
        {
            "external_verification_release": [
                sys.executable,
                str(ROOT / "scripts" / "test_external_verification_release.py"),
            ],
            "note_source": [
                sys.executable,
                str(ROOT / "scripts" / "check_problem_note_sources.py"),
                "--coverage",
            ],
            "paper_corpus": [
                sys.executable,
                str(ROOT / "docs" / "papers" / "check_paper_corpus.py"),
            ],
            "publication_taxonomy": [
                sys.executable,
                str(ROOT / "docs" / "papers" / "check_publication_taxonomy.py"),
            ],
        }
    )
    results = run_independent_checks(commands)
    _PROJECTION_CHECK_RESULTS = {
        builder: results[f"{projection_prefix}{builder}"]
        for builder in refresh_projections.BUILDERS
    }
    return results

ROOT_FILES = tuple(f"{root}.lean" for root in LIBRARY_ROOTS)
PROOF_PATHS = tuple(
    path
    for library_root, root_file in zip(LIBRARY_ROOTS, ROOT_FILES, strict=True)
    for path in (root_file, library_root)
)
INTERNAL_IMPORT_RE = re.compile(
    rf"^import ((?:{'|'.join(LIBRARY_ROOTS)})(?:\.[A-Za-z0-9_]+)+)\s*$",
    re.M,
)

LINE_WINDOW = 3  # declaration name must appear within this many lines of the stated line
MAX_ROUTE_FIRST_CONTACT_BYTES = 48_000

README_BANNED_PHRASES = [
    "Ramanujan Machine Challenge",
    "publication status",
    "ai_workflow` is a private",
]

PROOF_TRUST_RE = re.compile(
    r"\bsorry\b|\badmit\b|(?<![\w.])axiom\s+"
    r"|native_decide"
    r"|\+native\b|\bnative\s*:=\s*true\b"
    r"|^\s*(?:unsafe|partial)\s+(?:def|theorem|opaque|instance)\b"
    r"|^\s*set_option\s+(?:maxHeartbeats|maxRecDepth)\s+0\b",
    re.M,
)
PROOF_TRUST_LINE_DECL_RE = re.compile(
    r"(?:unsafe|partial)\s+(?:def|theorem|opaque|instance)\b"
)
PROOF_TRUST_OPTION_RE = re.compile(
    r"set_option\s+(?:maxHeartbeats|maxRecDepth)\s+0\b"
)
PROOF_TRUST_NATIVE_ASSIGN_RE = re.compile(r"native\s*:=\s*true\b")
PROOF_TRUST_LINE_DECL_BYTES_RE = re.compile(
    rb"(?:unsafe|partial)\s+(?:def|theorem|opaque|instance)\b"
)
PROOF_TRUST_OPTION_BYTES_RE = re.compile(
    rb"set_option\s+(?:maxHeartbeats|maxRecDepth)\s+0\b"
)
PROOF_TRUST_NATIVE_ASSIGN_BYTES_RE = re.compile(rb"native\s*:=\s*true\b")


def fail(msg: str) -> None:
    ERRORS.append(msg)


def check(ok: bool, msg: str) -> None:
    global CHECKS
    CHECKS += 1
    if not ok:
        fail(msg)


class UnsafeReleasePath(ValueError):
    """A release-gate input is outside the regular in-checkout file boundary."""


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


def _safe_release_component(path: Path) -> Path:
    """Reject checkout escapes and symbolic-link components."""
    root = Path(os.path.abspath(ROOT))
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeReleasePath(f"symlinked release path: {candidate}")
        if current == root:
            break
        if current.parent == current:
            raise UnsafeReleasePath(f"release path escaped checkout: {candidate}")
        current = current.parent

    return candidate


def safe_release_path(path: Path) -> Path:
    """Reject checkout escapes, symbolic-link components, and special files."""
    candidate = _safe_release_component(path)
    if not candidate.is_file():
        raise UnsafeReleasePath(f"release path is not a regular file: {candidate}")
    return candidate


def release_file_exists(path: Path) -> bool:
    """Return whether a path is a safe regular release file."""
    try:
        safe_release_path(path)
    except UnsafeReleasePath:
        return False
    return True


def _read_safe_bytes(path: Path) -> bytes:
    """Read a release file through a no-follow descriptor after admission."""
    candidate = _canonical_input_path(safe_release_path(path))
    directory_flags = os.O_RDONLY
    directory_flags |= getattr(os, "O_CLOEXEC", 0)
    directory_flags |= getattr(os, "O_DIRECTORY", 0)
    directory_flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        directory = os.open(os.sep, directory_flags)
    except OSError as exc:
        raise UnsafeReleasePath(
            f"release path could not be opened safely: {candidate}"
        ) from exc
    descriptor = -1
    try:
        for component in candidate.parts[1:-1]:
            child = os.open(component, directory_flags, dir_fd=directory)
            try:
                if not stat.S_ISDIR(os.fstat(child).st_mode):
                    raise OSError(
                        f"release path parent is not a directory: {candidate.parent}"
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
            raise UnsafeReleasePath(f"release path is not a regular file: {candidate}")
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            return stream.read()
    except OSError as exc:
        raise UnsafeReleasePath(
            f"release path could not be opened safely: {candidate}"
        ) from exc
    finally:
        os.close(directory)
        if descriptor >= 0:
            os.close(descriptor)


def file_digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(_read_safe_bytes(path)).hexdigest()


@lru_cache(maxsize=None)
def read(path: Path, *, errors: str = "strict") -> str:
    """Read each admitted immutable release input once per gate process."""
    return _read_safe_bytes(path).decode("utf-8", errors=errors)


def read_bytes(path: Path) -> bytes:
    """Read a release artifact only after applying the path boundary."""
    return _read_safe_bytes(path)


def flattened(text: str) -> str:
    """Collapse every run of whitespace so prose checks survive rewrapping.

    Markdown prose is rewrapped freely, so a required phrase that happens to
    straddle a line break stops matching a raw ``in`` test even though the
    sentence is still there — the gate then fails for a reason that has nothing
    to do with the claim it guards.  The same gap lets a *banned* phrase evade
    detection simply by wrapping.  Flattening fixes both directions: a phrase
    that is genuinely absent is still absent after flattening, so this can only
    remove false failures and add real detections, never mask a missing fence.
    """
    return " ".join(text.split())


def readme_open_boundary_present(readme: str, problem_count: int) -> bool:
    """Accept an explicit global open boundary without prescribing one sentence."""
    flat = flattened(readme).lower()
    if "does not solve" in flat:
        return True
    if problem_count < 1:
        return False
    words = {
        1: "one", 2: "two", 3: "three", 4: "four", 5: "five",
        6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten",
    }
    alternatives = [str(problem_count)]
    if problem_count in words:
        alternatives.append(words[problem_count])
    count = "|".join(re.escape(value) for value in alternatives)
    return bool(re.search(
        rf"\ball\s+(?:{count})\s+(?:original\s+)?(?:erd[őo]s\s+)?problems\s+remain\s+open\b",
        flat,
    ))


def contributor_gate_posture_errors(contributing: str) -> list[str]:
    """Reject contributor guidance that understates cold-reader validation."""
    flat = " ".join(contributing.split())
    errors: list[str] = []
    if "combined baseline-plus-adversarial release-gate check" not in flat:
        errors.append(
            "CONTRIBUTING.md must identify the cold-clone adversarial program "
            "as a release-gate check"
        )
    if "A failure therefore blocks the release gate" not in flat:
        errors.append(
            "CONTRIBUTING.md must state that cold-clone comprehension failures "
            "block the release gate"
        )
    if "diagnostic (not a gate)" in flat or "does not block a release" in flat:
        errors.append(
            "CONTRIBUTING.md still describes cold-clone comprehension as advisory"
        )
    return errors


def source_map_entry_errors(source_map: str) -> list[str]:
    """Keep source navigation bounded and subordinate to mathematical owners."""
    required = (
        "docs/orientation.json",
        "python3 scripts/query_corpus.py --route <programme_id>",
        "python3 scripts/query_corpus.py --claim <claim_id>",
        "python3 scripts/query_corpus.py --open <remaining_open.id>",
        "Lean source checked by the pinned Lean kernel is proof authority",
        "Erdős #249",
        "universal form of #257 remain open",
        "for every natural `t ≤ 82`",
        "supplies nothing at `t = 83`",
    )
    # Compare through flattened() on both sides. These are prose-presence
    # requirements, so the property is "the document still says this", not
    # "the document wraps this line where it wrapped in 2026". Matching raw
    # text pinned one requirement to an accidental markdown wrap position
    # ("for every\n  natural `t <= 82`"), which would have failed on a pure
    # reflow that changed no meaning. (2026-08-15)
    flat_source_map = flattened(source_map)
    errors = [
        f"docs/SOURCE_MAP.md lost bounded first-contact route: {phrase}"
        for phrase in required
        if flattened(phrase) not in flat_source_map
    ]
    if "Read `Erdos249257.lean` or `ErdosProblems.lean` only when package topology" not in flat_source_map:
        errors.append(
            "docs/SOURCE_MAP.md must not send first-contact readers directly "
            "into the full import graph"
        )
    if "currently assembled at 28 explicit scales through `t = 64`" in source_map:
        errors.append(
            "docs/SOURCE_MAP.md still presents the historical deposit list "
            "as the current certificate frontier"
        )
    return errors


def certified_kill_claim_errors(data: dict) -> list[str]:
    """Keep the registered finite #249 frontier aligned with its exact theorem."""
    claim = next(
        (
            row
            for row in data.get("claims", [])
            if row.get("id") == "certified_kill_instances"
        ),
        None,
    )
    if claim is None:
        return ["docs/claims.json lacks certified_kill_instances"]
    errors: list[str] = []
    statement = str(claim.get("statement", ""))
    bounded_domain = str(claim.get("bounded_domain", ""))
    declarations = {
        (row.get("module"), row.get("name"))
        for row in claim.get("declarations", [])
    }
    expected_band_declaration = (
        "ErdosProblems/Skip/LadderT67.lean",
        "exists_diagonalKill_le_82",
    )
    if "every lcm-diagonal scale t ≤ 82" not in statement:
        errors.append(
            "certified_kill_instances must state the contiguous t ≤ 82 band"
        )
    if "No certificate at t = 83" not in bounded_domain:
        errors.append(
            "certified_kill_instances must retain the explicit t = 83 ceiling"
        )
    if expected_band_declaration not in declarations:
        errors.append(
            "certified_kill_instances must cite "
            "ErdosProblems/Skip/LadderT67.exists_diagonalKill_le_82"
        )
    if claim.get("status") != "verified finite instance":
        errors.append(
            "certified_kill_instances must remain a verified finite instance"
        )
    if "remaining_open.unbounded_certificate_supply" not in claim.get(
        "remaining_open_proposition_ids", []
    ):
        errors.append(
            "certified_kill_instances must retain the unbounded-supply boundary"
        )
    return errors


def certified_kill_claim_mutation_fixture_failures(data: dict) -> list[str]:
    """Return mutations that escaped the finite-band claim contract."""
    fixtures: dict[str, dict] = {}
    historical = copy.deepcopy(data)
    historical_claim = next(
        row
        for row in historical["claims"]
        if row["id"] == "certified_kill_instances"
    )
    historical_claim["statement"] = (
        "Kernel-checked certificates at 28 scales through t = 64."
    )
    fixtures["historical_t64_understatement"] = historical

    missing_declaration = copy.deepcopy(data)
    missing_claim = next(
        row
        for row in missing_declaration["claims"]
        if row["id"] == "certified_kill_instances"
    )
    missing_claim["declarations"] = [
        row
        for row in missing_claim["declarations"]
        if row["name"] != "exists_diagonalKill_le_82"
    ]
    fixtures["t82_declaration_removed"] = missing_declaration

    ceiling_removed = copy.deepcopy(data)
    ceiling_claim = next(
        row
        for row in ceiling_removed["claims"]
        if row["id"] == "certified_kill_instances"
    )
    ceiling_claim["bounded_domain"] = "Every natural lcm-diagonal scale t."
    fixtures["finite_ceiling_removed"] = ceiling_removed

    return [
        fixture_id
        for fixture_id, mutated in fixtures.items()
        if not certified_kill_claim_errors(mutated)
    ]


def wave_index_entry_errors(wave_index: str) -> list[str]:
    """Keep development chronology downstream of bounded mathematical entry."""
    required = (
        "docs/orientation.json",
        "docs/SOURCE_MAP.md",
        "recover development chronology only when chronology is the",
        "inspect package topology only",
        "Lean source checked by the pinned Lean kernel is proof authority",
        "Erdős #249",
        "universal form of #257 remain open",
    )
    return [
        f"docs/WAVE_INDEX.md lost bounded chronology boundary: {phrase}"
        for phrase in required
        if phrase not in wave_index
    ]


def module_lines(
    cache: dict[tuple[str, str | None], list[str] | None],
    rel: str,
    source_ref: str | None = None,
) -> list[str] | None:
    """Read a module from the worktree or from the exact pinned Git tree."""
    key = (rel, source_ref)
    if key not in cache:
        if source_ref is None:
            path = ROOT / rel
            cache[key] = read(path).splitlines() if release_file_exists(path) else None
        else:
            completed = run(
                ["git", "show", f"{source_ref}:{rel}"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            cache[key] = completed.stdout.splitlines() if completed.returncode == 0 else None
    return cache[key]


def formal_source_matches_current_lean_tree(formal_ref: str) -> tuple[bool, str]:
    """Whether the current public proof sources are exactly ``formal_ref``.

    The source checkpoint owns the declarations named by the claim registry.
    Checking a declaration only with ``git show <formal_ref>:...`` is necessary,
    but it is not sufficient when a later Lean edit is present in the worktree:
    that would verify an older source while presenting the current tree.  The
    public root and library directory are the supported proof surface; papers,
    generated navigation, and release metadata may legitimately advance after
    that checkpoint.
    """
    comparison = run(
        ["git", "diff", "--quiet", formal_ref, "--", *PROOF_PATHS],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if comparison.returncode not in (0, 1):
        return False, comparison.stderr.strip() or "could not compare formal source to worktree"
    untracked = run(
        ["git", "ls-files", "--others", "--exclude-standard", "--", *PROOF_PATHS],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if untracked.returncode != 0:
        return False, untracked.stderr.strip() or "could not inspect untracked Lean sources"
    extras = [line for line in untracked.stdout.splitlines() if line.endswith(".lean")]
    if comparison.returncode == 0 and not extras:
        return True, ""
    detail = "current public Lean sources differ from formal-source checkpoint"
    if extras:
        detail += "; untracked Lean source(s): " + ", ".join(extras)
    return False, detail


def name_at_line(lines: list[str], name: str, line: int) -> bool:
    lo = max(0, line - 1 - LINE_WINDOW)
    hi = min(len(lines), line - 1 + LINE_WINDOW + 1)
    return any(name in lines[i] for i in range(lo, hi))


def internal_imports(path: Path) -> list[str]:
    """Return direct imports from either supported library in source order."""
    return INTERNAL_IMPORT_RE.findall(read(path))


def proof_trust_violation(text: str) -> str | None:
    """Return the first executable proof-trust violation, if any."""
    # The combined multiline expression is exact after lexical stripping, but
    # using it as a raw-corpus prefilter makes Python try its anchored branches
    # at nearly every character. On this 150 MB Lean tree that alone took over
    # ten seconds. Cheap literal searches identify the same candidate-bearing
    # files; only those files pay for the exact comment/string-aware scan.
    if not proof_trust_candidate(text):
        return None
    match = PROOF_TRUST_RE.search(lean_code_without_comments_and_strings(text))
    return match.group(0).strip() if match else None


def _is_word_character(character: str) -> bool:
    r"""Match the boundary alphabet used by Python's Unicode ``\w``."""
    return character == "_" or character.isalnum()


def _contains_delimited_token(
    text: str,
    token: str,
    *,
    check_start: bool = True,
    forbid_dot_before: bool = False,
    require_space_after: bool = False,
) -> bool:
    """Find a literal token with the proof-trust expression's boundaries."""
    position = 0
    while True:
        position = text.find(token, position)
        if position < 0:
            return False
        end = position + len(token)
        before = text[position - 1] if position else ""
        after = text[end] if end < len(text) else ""
        start_ok = (
            not check_start
            or not before
            or (
                not _is_word_character(before)
                and (not forbid_dot_before or before != ".")
            )
        )
        end_ok = not after or not _is_word_character(after)
        space_ok = not require_space_after or bool(after and after.isspace())
        if start_ok and end_ok and space_ok:
            return True
        position = end


def proof_trust_candidate(text: str) -> bool:
    """Cheaply over-approximate whether exact Lean lexing is required."""
    if _contains_delimited_token(text, "sorry"):
        return True
    if _contains_delimited_token(text, "admit"):
        return True
    if _contains_delimited_token(
        text,
        "axiom",
        forbid_dot_before=True,
        require_space_after=True,
    ):
        return True
    if "native_decide" in text:
        return True
    if _contains_delimited_token(text, "+native", check_start=False):
        return True

    position = 0
    while True:
        position = text.find("native", position)
        if position < 0:
            break
        if (
            (position == 0 or not _is_word_character(text[position - 1]))
            and PROOF_TRUST_NATIVE_ASSIGN_RE.match(text, position)
        ):
            return True
        position += len("native")

    for token in ("unsafe", "partial"):
        position = 0
        while True:
            position = text.find(token, position)
            if position < 0:
                break
            if PROOF_TRUST_LINE_DECL_RE.match(text, position):
                return True
            position += len(token)

    position = 0
    while True:
        position = text.find("set_option", position)
        if position < 0:
            return False
        if PROOF_TRUST_OPTION_RE.match(text, position):
            return True
        position += len("set_option")


def _is_word_byte(value: int) -> bool:
    """Conservatively approximate Unicode word boundaries before decoding."""

    return (
        value >= 128
        or value == ord("_")
        or ord("0") <= value <= ord("9")
        or ord("A") <= value <= ord("Z")
        or ord("a") <= value <= ord("z")
    )


def _contains_delimited_token_bytes(
    data: bytes,
    token: bytes,
    *,
    check_start: bool = True,
    forbid_dot_before: bool = False,
    require_space_after: bool = False,
) -> bool:
    """Apply the cheap trust-token boundary test without Unicode decoding."""

    position = 0
    while True:
        position = data.find(token, position)
        if position < 0:
            return False
        end = position + len(token)
        before = data[position - 1] if position else None
        after = data[end] if end < len(data) else None
        start_ok = (
            not check_start
            or before is None
            or (
                not _is_word_byte(before)
                and (not forbid_dot_before or before != ord("."))
            )
        )
        end_ok = after is None or not _is_word_byte(after)
        space_ok = (
            not require_space_after
            or after in {ord(" "), ord("\t"), ord("\n"), ord("\r"), ord("\f"), ord("\v")}
        )
        if start_ok and end_ok and space_ok:
            return True
        position = end


def proof_trust_candidate_bytes(data: bytes) -> bool:
    """Conservatively select sources that need exact lexical decoding."""

    if _contains_delimited_token_bytes(data, b"sorry"):
        return True
    if _contains_delimited_token_bytes(data, b"admit"):
        return True
    if _contains_delimited_token_bytes(
        data,
        b"axiom",
        forbid_dot_before=True,
        require_space_after=True,
    ):
        return True
    if b"native_decide" in data:
        return True
    if _contains_delimited_token_bytes(data, b"+native", check_start=False):
        return True

    position = 0
    while True:
        position = data.find(b"native", position)
        if position < 0:
            break
        if (
            (position == 0 or not _is_word_byte(data[position - 1]))
            and PROOF_TRUST_NATIVE_ASSIGN_BYTES_RE.match(data, position)
        ):
            return True
        position += len(b"native")

    for token in (b"unsafe", b"partial"):
        position = 0
        while True:
            position = data.find(token, position)
            if position < 0:
                break
            if PROOF_TRUST_LINE_DECL_BYTES_RE.match(data, position):
                return True
            position += len(token)

    position = 0
    while True:
        position = data.find(b"set_option", position)
        if position < 0:
            return False
        if PROOF_TRUST_OPTION_BYTES_RE.match(data, position):
            return True
        position += len(b"set_option")


def proof_trust_violation_bytes(data: bytes) -> str | None:
    """Decode only sources whose byte prefilter can contain a violation."""

    if not proof_trust_candidate_bytes(data):
        return None
    text = data.decode("utf-8")
    match = PROOF_TRUST_RE.search(lean_code_without_comments_and_strings(text))
    return match.group(0).strip() if match else None


def check_proof_trust() -> None:
    """Run the cheap proof-trust gate before any expensive release checks."""
    # Pin the lexical boundary: prose and strings are harmless, executable
    # native reduction is not.  These fixtures keep future scanner edits from
    # silently weakening or over-broadening the release contract.
    check(proof_trust_violation("theorem bad : True := by sorry\n") == "sorry",
          "proof-trust scanner must reject inline sorry")
    check(proof_trust_violation("theorem bad : True := by admit\n") == "admit",
          "proof-trust scanner must reject inline admit")
    check(proof_trust_violation("namespace Bad\naxiom hidden : True\nend Bad\n") == "axiom",
          "proof-trust scanner must reject project-defined axioms")
    check(proof_trust_violation("theorem bad : True := by native_decide\n") == "native_decide",
          "proof-trust scanner must reject executable native reduction")
    check(proof_trust_violation("theorem bad : True := by decide +native\n") == "+native",
          "proof-trust scanner must reject the native decide alias")
    check(proof_trust_violation(
        "theorem bad : True := by decide (config := { native := true })\n"
    ) == "native := true",
          "proof-trust scanner must reject native evaluation through configuration")
    check(proof_trust_violation("unsafe def bad : Nat := 1\n") == "unsafe def",
          "proof-trust scanner must reject unsafe declarations")
    check(proof_trust_violation("partial def bad : Nat -> Nat := fun n => bad n\n") == "partial def",
          "proof-trust scanner must reject partial declarations")
    check(proof_trust_violation(
        "/- prefix comment -/ unsafe def bad : Nat := 1\n"
    ) == "unsafe def",
          "proof-trust prefilter must retain declarations after inline comments")
    check(proof_trust_violation(
        "set_option maxHeartbeats 0\nexample : True := by trivial\n"
    ) == "set_option maxHeartbeats 0",
          "proof-trust scanner must reject unbounded heartbeat limits")
    check(proof_trust_violation(
        "/- prefix comment -/ set_option maxHeartbeats 0 in\n"
        "example : True := by trivial\n"
    ) == "set_option maxHeartbeats 0",
          "proof-trust prefilter must retain options after inline comments")
    check(proof_trust_violation(
        "set_option maxRecDepth 0 in\nexample : True := by trivial\n"
    ) == "set_option maxRecDepth 0",
          "proof-trust scanner must reject unbounded recursion limits")
    check(proof_trust_violation("/- native_decide -/\ntheorem ok : True := by trivial\n") is None,
          "proof-trust scanner must ignore comments")
    check(proof_trust_violation('def label := "native_decide"\n') is None,
          "proof-trust scanner must ignore strings")
    check(
        not proof_trust_candidate_bytes(
            b"#print axioms safe\nset_option maxRecDepth 10000\n"
        ),
        "byte prefilter must skip common safe trust-adjacent forms",
    )
    check(
        proof_trust_violation_bytes(
            b"/- prefix comment -/ unsafe def bad : Nat := 1\n"
        )
        == "unsafe def",
        "byte prefilter must retain executable declarations after comments",
    )
    check(
        proof_trust_violation_bytes(
            b"/- outer /- nested -/ sorry -/\ntheorem ok : True := by trivial\n"
        )
        is None,
        "chunked lexer must preserve nested-comment exclusion",
    )
    check(
        proof_trust_violation_bytes(
            b'def label := "escaped \\\" sorry"\ntheorem ok : True := by trivial\n'
        )
        is None,
        "chunked lexer must preserve escaped-string exclusion",
    )
    example_sources = sorted((ROOT / "examples").rglob("*.lean")) if (ROOT / "examples").is_dir() else []
    lean_sources = (
        [
            path
            for library_root, root_file in zip(LIBRARY_ROOTS, ROOT_FILES, strict=True)
            for path in (
                *sorted((ROOT / library_root).rglob("*.lean")),
                ROOT / root_file,
            )
        ]
        + example_sources
    )
    for lean in lean_sources:
        violation = proof_trust_violation_bytes(read_bytes(lean))
        check(violation is None,
              f"proof-trust violation in {lean.relative_to(ROOT)}: {violation or ''}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--singleflight-worker",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    args = parser.parse_args(argv)
    if not args.singleflight_worker:
        state_root = singleflight.default_state_root()
        specification = singleflight.validator_spec(
            "release-worktree", [], None, state_root
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
            "check_release: shared validation "
            f"key={receipt['key'][:12]} reuse={receipt.get('reuse', 'owner')} "
            f"exit={code}",
            file=sys.stderr,
        )
        return code

    # ``read`` is a per-run immutable snapshot, not a cross-run file cache.
    # Clearing here keeps repeated in-process invocations source-current while
    # letting the thousands of consumers below share one admitted read.
    read.cache_clear()
    cache: dict[tuple[str, str | None], list[str] | None] = {}

    # Fail fast on the cheapest high-severity invariant.  In particular, do
    # not spend the corpus-query budget before rejecting untrusted proof code.
    check_proof_trust()
    if ERRORS:
        print(f"check_release: {len(ERRORS)} proof-trust failure(s) across {CHECKS} checks")
        for err in ERRORS:
            print(f"  FAIL {err}")
        return 1

    # --- 1. claims.json ---------------------------------------------------
    claims_path = ROOT / "docs" / "claims.json"
    data = json.loads(read(claims_path))
    check(data.get("schema") == "erdos249257-claims/3",
          "docs/claims.json must use schema erdos249257-claims/3")
    publication_reader = RepositoryReader(ROOT)
    publication_errors = validate_publication_contract(publication_reader)
    check(
        not publication_errors,
        "publication artifact contract failed: " + "; ".join(publication_errors),
    )
    publication_fixture_failures = publication_mutation_fixture_failures(
        publication_reader
    )
    check(
        not publication_fixture_failures,
        "publication artifact mutation fixtures stopped rejecting: "
        + ", ".join(publication_fixture_failures),
    )
    systems_paper_errors = validate_systems_paper_evidence()
    check(
        not systems_paper_errors,
        "systems paper evidence crosswalk failed: "
        + "; ".join(systems_paper_errors),
    )
    systems_paper_fixture_failures = systems_paper_mutation_fixture_failures()
    check(
        not systems_paper_fixture_failures,
        "systems paper evidence fixtures stopped rejecting: "
        + ", ".join(systems_paper_fixture_failures),
    )
    # Reject a stale formal-source checkpoint before starting the expensive
    # projection, query, and adversarial pools. A split or moved Lean module
    # otherwise makes the answer inevitable but used to keep CPU-heavy readers
    # alive for another 20-30 seconds before reporting it.
    release = data["release"]
    formal_source = release.get("formal_source")
    check(isinstance(formal_source, dict), "release must name a formal_source checkpoint")
    formal_ref = formal_source.get("ref") if isinstance(formal_source, dict) else None
    check(isinstance(formal_ref, str) and re.fullmatch(r"[0-9a-f]{40}", formal_ref or "") is not None,
          "release.formal_source.ref must be a full lowercase Git commit id")
    if isinstance(formal_ref, str) and re.fullmatch(r"[0-9a-f]{40}", formal_ref):
        formal_ref_resolves = run(
            ["git", "rev-parse", "--verify", f"{formal_ref}^{{commit}}"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        check(
            formal_ref_resolves.returncode == 0,
            f"release.formal_source.ref {formal_ref!r} does not resolve to a local commit",
        )
        if formal_ref_resolves.returncode == 0:
            formal_tree_matches, formal_tree_detail = formal_source_matches_current_lean_tree(
                formal_ref
            )
            check(
                formal_tree_matches,
                formal_tree_detail
                or "current public Lean sources differ from formal-source checkpoint",
            )
    if ERRORS:
        print(
            "check_release: "
            f"{len(ERRORS)} release-identity failure(s) across {CHECKS} checks"
        )
        for err in ERRORS:
            print(f"  FAIL {err}")
        return 1
    publication_stage_results = publication_stage_check_results()
    problem_index_check = _PROJECTION_CHECK_RESULTS[
        "scripts/build_problem_index.py"
    ]
    check(
        problem_index_check.returncode == 0,
        "generated problem-index freshness failed: "
        f"{problem_index_check.stdout.strip() or problem_index_check.stderr.strip()}",
    )
    external_verification_check = _PROJECTION_CHECK_RESULTS[
        "scripts/build_external_verification.py"
    ]
    check(
        external_verification_check.returncode == 0,
        "external-verification projection or statement-isolation check failed: "
        f"{external_verification_check.stdout.strip() or external_verification_check.stderr.strip()}",
    )
    external_verification_release_check = publication_stage_results[
        "external_verification_release"
    ]
    check(
        external_verification_release_check.returncode == 0,
        "external-verification replay or immutable release-identity contract failed: "
        f"{external_verification_release_check.stdout.strip() or external_verification_release_check.stderr.strip()}",
    )
    note_source_check = publication_stage_results["note_source"]
    check(
        note_source_check.returncode == 0,
        "problem-note pinned-source contract failed: "
        f"{note_source_check.stdout.strip() or note_source_check.stderr.strip()}",
    )
    paper_corpus_check = publication_stage_results["paper_corpus"]
    check(
        paper_corpus_check.returncode == 0,
        "generated paper-corpus freshness failed: "
        f"{paper_corpus_check.stdout.strip() or paper_corpus_check.stderr.strip()}",
    )
    # Freshness is not the only way the corpus can mislead. Nothing here has
    # been externally reviewed and nothing carries an archival identifier; a
    # field claiming either would read as a credential at publication stage.
    publication_taxonomy_check = publication_stage_results[
        "publication_taxonomy"
    ]
    check(
        publication_taxonomy_check.returncode == 0,
        "paper publication-taxonomy honesty failed: "
        f"{publication_taxonomy_check.stdout.strip() or publication_taxonomy_check.stderr.strip()}",
    )
    publication_taxonomy_current = _PROJECTION_CHECK_RESULTS[
        "docs/papers/build_publication_taxonomy.py"
    ]
    check(
        publication_taxonomy_current.returncode == 0,
        "paper publication-taxonomy projection is stale: "
        f"{publication_taxonomy_current.stdout.strip() or publication_taxonomy_current.stderr.strip()}",
    )
    if ERRORS:
        print(
            "check_release: "
            f"{len(ERRORS)} publication-stage failure(s) across {CHECKS} checks"
        )
        for err in ERRORS:
            print(f"  FAIL {err}")
        return 1
    # The publication-stage contract is the last prerequisite for the larger
    # query and cold-clone suites. Start those two CPU-heavy readers here with
    # a two-worker cap, then consume them at the existing final barrier while
    # the main thread advances the remaining release checks.
    late_executor, late_futures = start_independent_checks(
        late_check_commands(), max_workers=2
    )
    taxonomy = set(data["status_taxonomy"])
    version, tag = release["version"], release["tag"]
    check(tag == f"v{version}", f"release tag {tag} does not match version {version}")
    if isinstance(formal_source, dict):
        check(formal_source.get("ref_kind") == "commit",
              "release.formal_source.ref_kind must be 'commit'")
        check(formal_source.get("publication_state") in {
            "committed_checkpoint_pending_remote_publication",
            "published_committed_checkpoint",
        }, "release.formal_source has an unsupported publication_state")
        check(formal_source.get("relationship_to_last_tag") in {
            "at_last_tag", "post_tag_checkpoint",
        }, "release.formal_source has an unsupported relationship_to_last_tag")
        public_tag = formal_source.get("public_tag")
        check(
            isinstance(public_tag, str)
            and re.fullmatch(
                r"formal-source-\d{4}-\d{2}-\d{2}(?:-r[1-9]\d*)?",
                public_tag,
            )
            is not None,
            "release.formal_source.public_tag must be a dated formal-source "
            "tag, optionally with a positive correction revision",
        )
        if isinstance(public_tag, str):
            tag_kind = run(
                ["git", "cat-file", "-t", public_tag],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            check(
                tag_kind.returncode == 0 and tag_kind.stdout.strip() == "tag",
                "release.formal_source.public_tag must resolve to an annotated tag",
            )
            resolved_tag = run(
                ["git", "rev-parse", f"{public_tag}^{{}}"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            check(
                resolved_tag.returncode == 0
                and resolved_tag.stdout.strip() == formal_ref,
                "release.formal_source.public_tag does not peel to formal_source.ref",
            )
            check(
                formal_source.get("publication_state")
                == "published_committed_checkpoint",
                "a public formal-source tag requires published_committed_checkpoint state",
            )
    public_projection = release.get("public_projection")
    check(isinstance(public_projection, dict),
          "release must name its public_projection provenance posture")
    if isinstance(public_projection, dict):
        check(
            public_projection.get("posture")
            == "self_contained_public_projection_from_a_larger_ongoing_research_workflow",
            "release.public_projection posture drifted",
        )
        check(bool(public_projection.get("meaning"))
              and bool(public_projection.get("public_evidence"))
              and bool(public_projection.get("boundary")),
              "release.public_projection needs meaning, evidence, and a boundary")
        boundary = str(public_projection.get("boundary", "")).casefold()
        check("does not imply hidden proof authority" in boundary
              and "private work" in boundary,
              "release.public_projection boundary must reject hidden proof authority "
              "and private-work equivalence")
    claim_ids = [claim["id"] for claim in data["claims"]]
    check(len(claim_ids) == len(set(claim_ids)), "docs/claims.json contains duplicate claim ids")
    claim_id_set = set(claim_ids)
    claim_index = {claim["id"]: claim for claim in data["claims"]}
    finite_band_errors = certified_kill_claim_errors(data)
    check(
        not finite_band_errors,
        "certified-kill claim contract: " + "; ".join(finite_band_errors),
    )
    for fixture_id in certified_kill_claim_mutation_fixture_failures(data):
        check(
            False,
            "certified-kill claim mutation fixture escaped: " + fixture_id,
        )
    remaining_open_id_set = {
        row["id"] for row in data["remaining_open_propositions"]
    }
    for claim in data["claims"]:
        check(claim["status"] in taxonomy,
              f"claim {claim['id']}: status {claim['status']!r} not in taxonomy")
        if claim["status"] in ("cited only", "open"):
            check(not claim["declarations"],
                  f"claim {claim['id']}: {claim['status']!r} claims must not carry declarations")
        else:
            check(bool(claim["declarations"]),
                  f"claim {claim['id']}: formal claim carries no declaration")

    machine_paper = data["machine_readable_paper"]
    check(machine_paper.get("schema") == "erdos249257-machine-readable-paper/1",
          "machine_readable_paper has an unsupported schema")
    publication_assembly = machine_paper.get("publication_assembly")
    check(isinstance(publication_assembly, dict),
          "machine_readable_paper must own a publication_assembly")
    if isinstance(publication_assembly, dict):
        families = publication_assembly.get("contribution_families", [])
        check(isinstance(families, list) and bool(families),
              "publication_assembly must contain contribution families")
        family_ids = [family.get("id") for family in families]
        check(len(family_ids) == len(set(family_ids)),
              "publication contribution families contain duplicate ids")
        required_family_fields = {
            "id",
            "claim_ids",
            "status_summary",
            "prior_art_posture",
            "primary_narrative_owner",
            "source_route",
            "consumer_or_open_obligation",
            "view_decision",
        }
        assembled_claim_ids: list[str] = []
        for family in families:
            missing_fields = required_family_fields - set(family)
            check(not missing_fields,
                  f"publication family {family.get('id')!r} lacks fields: "
                  f"{sorted(missing_fields)}")
            family_claim_ids = family.get("claim_ids", [])
            check(isinstance(family_claim_ids, list) and bool(family_claim_ids),
                  f"publication family {family.get('id')!r} has no claims")
            check(not (set(family_claim_ids) - claim_id_set),
                  f"publication family {family.get('id')!r} has unknown claims: "
                  f"{sorted(set(family_claim_ids) - claim_id_set)}")
            assembled_claim_ids.extend(family_claim_ids)
            owner_path = str(family.get("primary_narrative_owner", "")).split("::", 1)[0]
            check(release_file_exists(ROOT / owner_path),
                  f"publication family {family.get('id')!r} owner does not exist: "
                  f"{owner_path}")
            check(str(family.get("source_route", "")).startswith(
                "python3 scripts/query_corpus.py --"),
                f"publication family {family.get('id')!r} lacks a typed source route")
            check(bool(family.get("status_summary"))
                  and bool(family.get("prior_art_posture"))
                  and bool(family.get("consumer_or_open_obligation"))
                  and bool(family.get("view_decision")),
                  f"publication family {family.get('id')!r} has an empty editorial field")
        duplicate_assembled_claims = sorted(
            claim_id
            for claim_id in set(assembled_claim_ids)
            if assembled_claim_ids.count(claim_id) > 1
        )
        check(not duplicate_assembled_claims,
              "publication contribution families overlap on claims: "
              f"{duplicate_assembled_claims}")
        check(set(assembled_claim_ids) == claim_id_set,
              "publication contribution census drifted: missing="
              f"{sorted(claim_id_set - set(assembled_claim_ids))}, extra="
              f"{sorted(set(assembled_claim_ids) - claim_id_set)}")
        architecture = publication_assembly.get("publication_architecture", {})
        canonical_gateway = architecture.get("canonical_gateway", {})
        check(canonical_gateway.get("source") == machine_paper["paper"]["source"],
              "publication architecture canonical gateway drifted from paper owner")
        for companion in architecture.get("retained_companions", []):
            check(any(
                row.get("source") == companion.get("source")
                for row in machine_paper["paper"].get("companion_sources", [])
            ), f"retained publication companion is not registered: "
               f"{companion.get('source')}")
        editorial_state = publication_assembly.get("editorial_state")
        check(isinstance(editorial_state, dict),
              "publication_assembly must own an editorial_state")
        if isinstance(editorial_state, dict):
            required_editorial_fields = {
                "schema",
                "scope",
                "current_priority",
                "last_verified_wave",
                "active_inconsistencies",
                "blocked_decisions",
            }
            check(not (required_editorial_fields - set(editorial_state)),
                  "publication editorial_state lacks fields: "
                  f"{sorted(required_editorial_fields - set(editorial_state))}")
            check(editorial_state.get("schema") == "erdos249257-editorial-state/1",
                  "publication editorial_state has an unsupported schema")
            for field in ("current_priority", "last_verified_wave"):
                row = editorial_state.get(field, {})
                check(isinstance(row, dict) and bool(row.get("id"))
                      and bool(row.get("surface")),
                      f"publication editorial_state {field} lacks an id or surface")
                owner_path = str(row.get("surface", "")).split("::", 1)[0]
                check(release_file_exists(ROOT / owner_path),
                      f"publication editorial_state {field} owner does not exist: "
                      f"{owner_path}")
            inconsistencies = editorial_state.get("active_inconsistencies", [])
            check(isinstance(inconsistencies, list),
                  "publication active_inconsistencies must be a list")
            inconsistency_ids = [
                row.get("id") for row in inconsistencies if isinstance(row, dict)
            ]
            check(len(inconsistency_ids) == len(set(inconsistency_ids)),
                  "publication active_inconsistencies contain duplicate ids")
            for row in inconsistencies:
                check(isinstance(row, dict)
                      and bool(row.get("id"))
                      and row.get("severity") in {"high", "medium", "low"}
                      and bool(row.get("surface"))
                      and bool(row.get("statement"))
                      and bool(row.get("next_action")),
                      "publication active inconsistency lacks a typed complete record")
                owner_path = str(row.get("surface", "")).split("::", 1)[0]
                check(release_file_exists(ROOT / owner_path),
                      f"publication active inconsistency owner does not exist: "
                      f"{owner_path}")
            check(isinstance(editorial_state.get("blocked_decisions"), list),
                  "publication blocked_decisions must be a list")
    route_ids = [route.get("id") for route in machine_paper["entrypoints"]]
    check(len(route_ids) == len(set(route_ids)),
          "machine-readable-paper entrypoints contain duplicate route ids")
    route_id_set = set(route_ids)
    route_index = {route["id"]: route for route in machine_paper["entrypoints"]}
    exhaustive_route_reads = {"docs/claims.json", "docs/declaration_atlas.json", "docs/methodology.json"}
    for route in machine_paper["entrypoints"]:
        check(bool(route.get("id")) and bool(route.get("intent")) and bool(route.get("read")),
              "every machine-readable-paper entrypoint needs id, intent, and read paths")
        check(bool(route.get("query_steps")) and bool(route.get("authority_owners"))
              and bool(route.get("adjacent_handle_classes")),
              f"route {route.get('id')!r} lacks bounded query, authority-owner, or adjacent-handle data")
        check(not (set(route.get("read", [])) & exhaustive_route_reads),
              f"route {route.get('id')!r} sends first contact to an exhaustive owner")
        first_contact_bytes = 0
        for rel in route.get("read", []):
            path = ROOT / rel
            check(release_file_exists(path), f"machine-readable-paper entrypoint path does not exist: {rel}")
            if release_file_exists(path):
                first_contact_bytes += path.stat().st_size
        check(first_contact_bytes <= MAX_ROUTE_FIRST_CONTACT_BYTES,
              f"route {route.get('id')!r} first-contact bundle is {first_contact_bytes} bytes "
              f"(budget {MAX_ROUTE_FIRST_CONTACT_BYTES})")
        for owner in route.get("authority_owners", []):
            rel = str(owner).split("::", 1)[0]
            check(release_file_exists(ROOT / rel),
                  f"route {route.get('id')!r} authority owner does not exist: {rel}")
        for step in route.get("query_steps", []):
            check(step.startswith("python3 scripts/query_corpus.py --"),
                  f"route {route.get('id')!r} query step is not a typed corpus query: {step}")
        for step in route.get("action_steps", []):
            match = re.match(r"^python3 (scripts/[A-Za-z0-9_.-]+\.py)(?:\s|$)", step)
            action_path = match.group(1) if match else ""
            check(
                bool(match)
                and action_path != "scripts/query_corpus.py"
                and release_file_exists(ROOT / action_path),
                f"route {route.get('id')!r} has an invalid executable action handoff: {step}",
            )
        discovery_terms = route.get("discovery_terms", [])
        check(
            isinstance(discovery_terms, list)
            and all(isinstance(term, str) and term.strip() for term in discovery_terms),
            f"route {route.get('id')!r} has invalid discovery terms",
        )
        route_kind = route.get("route_kind", "reading_route")
        check(route_kind in {"reading_route", "mathematical_programme"},
              f"route {route.get('id')!r} has unsupported route_kind {route_kind!r}")
        if route_kind == "mathematical_programme":
            required_fields = (
                "title",
                "mathematical_focus",
                "claim_ceiling",
                "problem_target_claim_ids",
                "core_claim_ids",
                "remaining_open_proposition_ids",
                "related_route_ids",
            )
            check(all(route.get(field) for field in required_fields),
                  f"programme route {route.get('id')!r} lacks a required programme field")
            target_ids = set(route.get("problem_target_claim_ids", []))
            core_ids = set(route.get("core_claim_ids", []))
            open_ids = set(route.get("remaining_open_proposition_ids", []))
            related_ids = set(route.get("related_route_ids", []))
            check(not (target_ids - claim_id_set),
                  f"programme route {route.get('id')!r} has unknown problem targets: "
                  f"{sorted(target_ids - claim_id_set)}")
            check(
                all(claim_index[target_id]["status"] == "open"
                    for target_id in target_ids if target_id in claim_index),
                f"programme route {route.get('id')!r} target claims must remain open",
            )
            check(not (core_ids - claim_id_set),
                  f"programme route {route.get('id')!r} has unknown core claims: "
                  f"{sorted(core_ids - claim_id_set)}")
            check(not (open_ids - remaining_open_id_set),
                  f"programme route {route.get('id')!r} has unknown open propositions: "
                  f"{sorted(open_ids - remaining_open_id_set)}")
            check(not (related_ids - route_id_set),
                  f"programme route {route.get('id')!r} has unknown related routes: "
                  f"{sorted(related_ids - route_id_set)}")
            check(
                all(
                    route_index[related_id].get("route_kind")
                    == "mathematical_programme"
                    for related_id in related_ids
                    if related_id in route_index
                ),
                f"programme route {route.get('id')!r} relates to a non-programme route",
            )
            check(route.get("id") not in related_ids,
                  f"programme route {route.get('id')!r} relates to itself")
            steps = set(route.get("query_steps", []))
            check(
                all(
                    f"python3 scripts/query_corpus.py --claim {claim_id}" in steps
                    for claim_id in core_ids
                ),
                f"programme route {route.get('id')!r} does not expose every core claim",
            )
            check(
                all(
                    f"python3 scripts/query_corpus.py --open {open_id}" in steps
                    for open_id in open_ids
                ),
                f"programme route {route.get('id')!r} does not expose every open proposition",
            )
            ceiling = str(route.get("claim_ceiling", "")).casefold()
            check(
                any(
                    token in ceiling
                    for token in (
                        "remain open",
                        "not proved",
                        "does not",
                        "do not",
                        "neither",
                        "no ",
                    )
                ),
                f"programme route {route.get('id')!r} lacks an explicit negative claim ceiling",
            )

    module_nodes = machine_paper["module_graph"]["nodes"]
    module_ids = [node["id"] for node in module_nodes]
    check(len(module_ids) == len(set(module_ids)), "machine-readable module graph contains duplicate ids")
    module_id_set = set(module_ids)
    module_paths = {node["path"] for node in module_nodes}
    for node in module_nodes:
        path = ROOT / node["path"]
        check(release_file_exists(path), f"machine-readable module path does not exist: {node['path']}")
        unknown_imports = set(node["imports"]) - module_id_set
        check(not unknown_imports,
              f"module {node['id']} has unknown internal imports: {sorted(unknown_imports)}")
        if release_file_exists(path):
            observed = internal_imports(path)
            check(observed == node["imports"],
                  f"module {node['id']} imports drifted: registry={node['imports']} source={observed}")
    graph = machine_paper["module_graph"]
    roots = [graph["root"], *graph.get("additional_roots", [])]
    check(roots == list(ROOT_FILES),
          f"machine-readable module graph roots drifted: {roots}")
    root_imports: list[str] = []
    for root in roots:
        root_path = ROOT / root
        check(release_file_exists(root_path), f"machine-readable module graph root does not exist: {root}")
        if release_file_exists(root_path):
            observed = internal_imports(root_path)
            root_imports.extend(observed)
            unknown_root_imports = set(observed) - module_id_set
            check(not unknown_root_imports,
                  f"{root} has imports missing from the machine-readable module graph: {sorted(unknown_root_imports)}")
    imports_by_id = {node["id"]: node["imports"] for node in module_nodes}
    auxiliary_roots = graph.get("auxiliary_roots", [])
    auxiliary_contract = graph.get("auxiliary_root_contract", {})
    allowed_auxiliary_prefixes = tuple(
        auxiliary_contract.get("allowed_prefixes", [])
    )
    check(
        auxiliary_contract.get("posture")
        == "exhaustive_inventory_forest_not_compact_reading_root",
        "machine-readable module graph lost its auxiliary-root posture",
    )
    check(
        len(auxiliary_roots) == len(set(auxiliary_roots)),
        "machine-readable module graph contains duplicate auxiliary roots",
    )
    check(
        all(root_id in module_id_set for root_id in auxiliary_roots),
        "machine-readable module graph names an unknown auxiliary root",
    )
    check(
        bool(allowed_auxiliary_prefixes)
        and all(
            root_id.startswith(allowed_auxiliary_prefixes)
            for root_id in auxiliary_roots
        ),
        "machine-readable module graph has an auxiliary root outside the "
        "explicit experimental namespaces",
    )
    supported_root_reachable = set(root_imports)
    supported_frontier = list(supported_root_reachable)
    while supported_frontier:
        current = supported_frontier.pop()
        for dependency in imports_by_id.get(current, []):
            if dependency not in supported_root_reachable:
                supported_root_reachable.add(dependency)
                supported_frontier.append(dependency)
    check(
        "ErdosProblems.Skip.LadderT67" in supported_root_reachable,
        "the reviewed t ≤ 82 finite-certificate theorem is outside the "
        "supported-root build closure",
    )
    reachable = set([*root_imports, *auxiliary_roots])
    frontier = list(reachable)
    while frontier:
        current = frontier.pop()
        for dependency in imports_by_id.get(current, []):
            if dependency not in reachable:
                reachable.add(dependency)
                frontier.append(dependency)
    check(
        reachable == module_id_set,
        "machine-readable module graph has nodes unreachable from supported "
        f"roots or the validated auxiliary forest: {sorted(module_id_set - reachable)}",
    )

    edge_types = set(machine_paper["argument_graph"]["edge_semantics"])
    for edge in machine_paper["argument_graph"]["edges"]:
        check(edge.get("from") in claim_id_set,
              f"argument edge has unknown source claim: {edge.get('from')}")
        check(edge.get("to") in claim_id_set,
              f"argument edge has unknown target claim: {edge.get('to')}")
        check(edge.get("relation") in edge_types,
              f"argument edge has unknown relation: {edge.get('relation')}")
    for claim in data["claims"]:
        for decl in claim["declarations"]:
            check(decl["module"] in module_paths,
                  f"claim {claim['id']}: declaration module missing from machine-readable module graph: {decl['module']}")
    for projection in machine_paper.get("projections", []):
        check(release_file_exists(ROOT / projection["path"]),
              f"machine-readable paper projection does not exist: {projection['path']}")

    # --- methodology source and typed claim transitions -------------------
    methodology_path = ROOT / "docs" / "methodology.json"
    methodology = json.loads(read(methodology_path))
    methodology_errors = validate_contract(data, methodology)
    check(not methodology_errors,
          "methodology contract invalid: " + "; ".join(methodology_errors))

    methodology_projection = ROOT / "METHODOLOGY.md"
    expected_methodology_projection = render_markdown(methodology, data)
    check(release_file_exists(methodology_projection), "METHODOLOGY.md is missing")
    if release_file_exists(methodology_projection):
        check(read(methodology_projection) == expected_methodology_projection,
              "METHODOLOGY.md does not exactly match docs/methodology.json")

    for fixture_id, fixture_errors in mutation_fixture_errors(data, methodology).items():
        check(bool(fixture_errors),
              f"methodology mutation fixture escaped validation: {fixture_id}")

    # --- 2. release identity ----------------------------------------------
    lakefile = read(ROOT / "lakefile.toml")
    m = re.search(r'^version\s*=\s*"([^"]+)"', lakefile, re.M)
    check(m is not None and m.group(1) == version,
          f"lakefile.toml version {m.group(1) if m else '<missing>'} != claims.json {version}")

    cff = read(ROOT / "CITATION.cff")
    check(re.search(r"^type: software\s*$", cff, re.M) is not None,
          "CITATION.cff: top-level type must be exactly 'software' (CFF 1.2.0)")
    check(re.search(rf'^version: "?{re.escape(version)}"?\s*$', cff, re.M) is not None,
          f"CITATION.cff: version does not state {version}")
    check(re.search(rf"""^date-released: ["']?{re.escape(release['date'])}["']?\s*$""", cff, re.M) is not None,
          f"CITATION.cff: date-released does not state {release['date']}")
    check("Erdős" in cff, "CITATION.cff: title/keywords should use Unicode 'Erdős'")

    toolchain = read(ROOT / "lean-toolchain").strip()
    check(toolchain == release["lean_toolchain"],
          f"lean-toolchain {toolchain} != claims.json {release['lean_toolchain']}")

    main_paper_row = machine_paper["paper"]
    paper_rows = [main_paper_row, *main_paper_row.get("companion_sources", [])]
    paper_sources = [(row["source"], read(ROOT / row["source"])) for row in paper_rows]
    paper = paper_sources[0][1]
    all_paper = "\n".join(text for _path, text in paper_sources)
    for paper_path, paper_text in paper_sources:
        m = re.search(
            r"\\(?:re)?newcommand\{\\commit\}\{([^}]+)\}", paper_text
        )
        expected_pin = next(row for row in paper_rows if row["source"] == paper_path).get("formal_source_ref", formal_ref)
        check(m is not None and m.group(1) == expected_pin,
              f"{paper_path} \\commit pin {m.group(1) if m else '<missing>'} != expected {expected_pin}")
        if paper_path == main_paper_row["source"]:
            # At most one, not exactly one. The rule is that no reader-facing
            # link may float on a branch; the gateway paper was allowed a single
            # root-navigation base because it once pointed at blob/main. That
            # base now resolves through \commit, so the paper carries no floating
            # link at all, which is the stronger state the rule wanted.
            check(paper_text.count("blob/main") <= 1 and "\\newcommand{\\rootbase}" in paper_text,
                  f"{paper_path} may use blob/main only for the explicit \\rref root-navigation base")
        else:
            check("blob/main" not in paper_text,
                  f"{paper_path} links a floating branch (blob/main)")
    for claim in data["claims"]:
        label = claim.get("paper_label")
        if label:
            check(re.search(rf"\\label\{{{re.escape(label)}\}}", all_paper) is not None,
                  f"claim {claim['id']}: paper label {label!r} does not exist")
    paper_anchors = paper_anchor_inventory()
    anchor_labels = [row["label"] for row in paper_anchors if row["label"]]
    check(len(anchor_labels) == len(set(anchor_labels)),
          "authored papers contain duplicate semantic-anchor labels")
    check(all(row.get("anchor_class") for row in paper_anchors),
          "every authored paper semantic anchor must have an explicit classification")
    check(all(
        row["anchor_class"] in {
            "registered_claim_anchor",
            "remaining_open_proposition_anchor",
            "authored_formal_anchor_without_registered_claim",
            "section_navigation_anchor",
        }
        for row in paper_anchors
    ), "authored paper semantic anchor has an unsupported classification")
    claim_ids_by_label: dict[str, set[str]] = {}
    for claim in data["claims"]:
        if claim.get("paper_label"):
            claim_ids_by_label.setdefault(claim["paper_label"], set()).add(claim["id"])
    for anchor in paper_anchors:
        observed_claim_ids = {row["id"] for row in anchor["attached_claims"]}
        expected_claim_ids = claim_ids_by_label.get(anchor["label"], set())
        check(observed_claim_ids == expected_claim_ids,
              f"paper anchor {anchor['canonical_handle']}: attached claim set drifted")
        observed_open_ids = {row["id"] for row in anchor["attached_open_propositions"]}
        # Key both sides through the one function the repository owns for this.
        # Raw field equality cannot succeed here: a sectioning anchor carries
        # environment None and resolves its environment from its anchor kind,
        # and a registry title is authored in reader form ("Erdős #68") while
        # the scanned title is the TeX source form ("Erd\H{o}s \#68"). Comparing
        # the raw fields made six anchors permanently red while the inventory
        # they are checked against had already attached the right propositions.
        anchor_key = canonical_paper_anchor_key(
            anchor["paper"]["source"],
            anchor["environment"],
            anchor["title"],
            anchor["anchor_kind"],
        )
        expected_open_ids = {
            row["id"]
            for row in data["remaining_open_propositions"]
            if row.get("paper_anchor")
            and canonical_paper_anchor_key(
                row["paper_anchor"]["source"],
                row["paper_anchor"]["environment"],
                row["paper_anchor"]["title"],
            )
            == anchor_key
        }
        check(observed_open_ids == expected_open_ids,
              f"paper anchor {anchor['canonical_handle']}: open proposition set drifted")
        if anchor["environment"] == "problem":
            check(anchor["anchor_class"] == "remaining_open_proposition_anchor",
                  f"problem paper anchor {anchor['canonical_handle']} is not typed as remaining open")
        if anchor["anchor_kind"] == "formal_environment":
            check(anchor["anchor_class"] != "section_navigation_anchor",
                  f"formal paper anchor {anchor['canonical_handle']} classified as navigation-only")
    routed_open_ids = {
        row["id"]
        for anchor in paper_anchors
        for row in anchor["attached_open_propositions"]
    }
    check(routed_open_ids == {row["id"] for row in data["remaining_open_propositions"]},
          "every remaining-open proposition must resolve to exactly one authored problem anchor")
    index_label = machine_paper["paper"]["principal_declaration_index_label"]
    check(re.search(rf"\\label\{{{re.escape(index_label)}\}}", paper) is not None,
          f"machine-readable paper index label {index_label!r} does not exist")

    pinned_requests = {
        (formal_ref, decl["module"])
        for claim in data["claims"]
        for decl in claim["declarations"]
    }
    for _paper_path, paper_text in paper_sources:
        for _macro, fname, _line_s, _name in re.findall(
            r"\\((?:[lm](?:refx?|word|loc)|rootword))\{([^}]+)\}\{(\d+)\}(?:\{([^}]*)\})?(?:\{[^}]*\})?",
            paper_text,
        ):
            if fname.startswith(("Erdos249257/", "ErdosProblems/")):
                rel = fname
            elif "\\input{problem-note-preamble}" in paper_text:
                rel = f"ErdosProblems/{fname}"
            else:
                rel = f"Erdos249257/{fname}"
            pinned_requests.add((note_pinned_commit(paper_text, formal_ref), rel))
    pinned_cache: dict[tuple[str, str], list[str]] = {}
    snapshot_lines_batch(
        pinned_requests,
        pinned_cache,
    )
    cache.update(
        {
            (rel, ref): lines or None
            for (ref, rel), lines in pinned_cache.items()
        }
    )

    # --- 3. claimed declarations -------------------------------------------
    for claim in data["claims"]:
        for decl in claim["declarations"]:
            lines = module_lines(cache, decl["module"], formal_ref)
            if lines is None:
                fail(f"claim {claim['id']}: module {decl['module']} not found")
                continue
            check(name_at_line(lines, decl["name"], decl["line"]),
                  f"claim {claim['id']}: {decl['name']} not at "
                  f"{decl['module']}:{decl['line']} (±{LINE_WINDOW})")

    # --- 4. paper source links ----------------------------------------------
    for paper_path, paper_text in paper_sources:
        source_ref = note_pinned_commit(paper_text, formal_ref)
        for macro, fname, line_s, name in re.findall(
                r"\\((?:[lm](?:refx?|word|loc)|rootword))\{([^}]+)\}\{(\d+)\}(?:\{([^}]*)\})?(?:\{[^}]*\})?", paper_text):
            if fname.startswith(("Erdos249257/", "ErdosProblems/")):
                rel = fname
            elif "\\input{problem-note-preamble}" in paper_text:
                rel = f"ErdosProblems/{fname}"
            else:
                rel = f"Erdos249257/{fname}"
            lines = module_lines(cache, rel, source_ref)
            if lines is None:
                fail(f"{paper_path} \\{macro}: file {rel} not found at {source_ref}")
                continue
            line = int(line_s)
            check(line <= len(lines), f"{paper_path} \\{macro}: {rel}:{line} beyond end of file")
            if macro in ("lref", "lrefx", "lword", "mref", "mword", "rootword") and name and line <= len(lines):
                check(name_at_line(lines, name, line),
                      f"{paper_path} \\{macro}: {name} not at {rel}:{line} (±{LINE_WINDOW})")

    # --- 5. SCOPE.md ----------------------------------------------------------
    scope = read(ROOT / "SCOPE.md")
    declared = {nc["id"] for nc in data["non_claims"]}
    listed = set(re.findall(r"`(not_[a-z0-9_]+)`", scope))
    check(declared == listed,
          f"SCOPE.md identifiers {sorted(listed)} != claims.json {sorted(declared)}")
    check("does not prove" in flattened(scope),
          "SCOPE.md must state the open boundary in plain language")

    # --- 6. README ------------------------------------------------------------
    readme = read(ROOT / "README.md")
    check(tag in readme, f"README does not state the release tag {tag}")
    check("METHODOLOGY.md" in readme and "SOURCE_MAP.md" in readme,
          "README must route readers to the methodology and source map")
    check(
        "formalization.yaml" in readme and "docs/EXTERNAL_VERIFICATION.md" in readme,
        "README must route readers to the external verification packet",
    )
    # Derive the scope sentence from the problem registry rather than pinning
    # one fixed English sentence. The property is "the README states that the
    # manifest and packet cover every indexed problem programme". Matching the
    # literal "cover all eight problem programmes" both broke on an honest
    # rewording ("covers") and would have stayed silent if a ninth problem were
    # indexed while the sentence still said eight. (2026-08-15)
    indexed_problem_count = int(
        json.loads(read(ROOT / "docs" / "problems.json")).get("problem_count", 0)
    )
    count_words = {
        1: "one", 2: "two", 3: "three", 4: "four", 5: "five",
        6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten",
    }
    check(readme_open_boundary_present(readme, indexed_problem_count),
          "README must state the open boundary in plain language")
    count_word = count_words.get(indexed_problem_count, "")
    count_pattern = "|".join(
        re.escape(token) for token in (count_word, str(indexed_problem_count)) if token
    )
    check(
        bool(
            re.search(
                rf"covers?\s+all\s+(?:{count_pattern})\s+problem\s+programmes",
                flattened(readme),
            )
        ),
        "README must state that the external-verification packet covers all "
        f"{indexed_problem_count} indexed problem programmes",
    )
    leaked_identifier = re.search(r"method_axiom\.|anti_principle\.|principle\.[a-z_]|transition\.[a-z_]", readme)
    check(leaked_identifier is None,
          f"README leaks a methodology machine identifier: {leaked_identifier.group(0) if leaked_identifier else ''}")
    for phrase in README_BANNED_PHRASES:
        check(phrase not in flattened(readme),
              f"README contains banned drift phrase: {phrase!r}")
    # docs/external_verification_packet.json already declares the wording that
    # must never describe Comparator, and docs/EXTERNAL_VERIFICATION.md repeats
    # it as guidance, but nothing enforced it: the README could have claimed
    # "independently verified" and passed every release check. Source the phrase
    # from the packet so the gate tracks the contract instead of duplicating it.
    # A negation ("this is not independently verified") is an honest disclaimer
    # and stays legal; only an affirmative claim fails. (2026-08-15)
    #
    # The contract governs how Comparator may be described, not where. Scanning
    # only the README left every other surface a reader meets first -- the agent
    # entries, the architecture guide, the whole of docs/ -- free to make the
    # claim the README could not. Widened to the repository's own prose.
    # (2026-08-16)
    #
    # Authored manuscripts are excluded on purpose rather than by oversight:
    # paper/ and docs/papers/ use "independently verified" in its ordinary
    # mathematical sense, for finite tables of separately checked rows, and one
    # paper discusses NASA's IV&V criteria by name. That prose is authored
    # exposition under its own review, and this gate does not rewrite it.
    forbidden_wording = (
        json.loads(read(ROOT / "docs" / "external_verification_packet.json"))
        .get("receipt_contract", {})
        .get("forbidden_wording", "")
    )
    if forbidden_wording:
        negations = ("not", "never", "no", "without", "cannot", "nor", "neither")
        own_prose = [
            ROOT / name
            for name in (
                "README.md",
                "AGENTS.md",
                "AGENTS.override.md",
                "CLAUDE.md",
                "CODEX.md",
                "CURSOR.md",
                "GEMINI.md",
                ".github/copilot-instructions.md",
                "ARCHITECTURE.md",
                "METHODOLOGY.md",
                "SCOPE.md",
                "CODE_OF_CONDUCT.md",
                "CONTRIBUTING.md",
                "SECURITY.md",
            )
        ]
        own_prose.extend(sorted((ROOT / "docs").glob("*.md")))
        for path in own_prose:
            if not release_file_exists(path):
                check(False, f"release prose path is not a safe regular file: {path.relative_to(ROOT)}")
                continue
            flat = flattened(read(path))
            asserted = [
                match.start()
                for match in re.finditer(re.escape(forbidden_wording), flat, re.I)
                if not any(
                    re.search(rf"\b{negation}\b", flat[max(0, match.start() - 40):match.start()], re.I)
                    for negation in negations
                )
            ]
            check(
                not asserted,
                f"{path.relative_to(ROOT)} asserts the forbidden "
                f"external-verification wording {forbidden_wording!r}; Comparator "
                "is a second checker, not an independent verification of the "
                "mathematics",
            )
    # When the human-first README uses a Status/Result reference table, check
    # only its first column. The table itself is optional: current first contact
    # explains evidence classes in prose and routes exhaustive status to the
    # claim registry. Other README tables legitimately bold problem numbers.
    status_table = re.search(
        r"(?ms)^\| Status \| Result \|\n^\|---\|---\|\n"
        r"(?P<body>(?:^\|.*\n)+)",
        readme,
    )
    status_table_body = status_table.group("body") if status_table else ""
    for status in re.findall(r"\|\s*\*\*([^*\n]+)\*\*\s*\|", status_table_body):
        check(status in taxonomy,
              f"README status table uses {status!r}, which is not in the taxonomy")

    # --- 7. licensing -----------------------------------------------------------
    import os

    # REUSE-IgnoreStart — the strings below are scanner patterns, not licence tags.
    reuse = read(ROOT / "REUSE.toml")
    spdx_ids = set(re.findall(r'SPDX-License-Identifier\s*=\s*"([^"]+)"', reuse))
    license_scan_excluded_dirs = {
        ".git",
        ".lake",
        ".venv",
        "LICENSES",
        "__pycache__",
        "venv",
    }
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames if d not in license_scan_excluded_dirs]
        for dirname in dirnames:
            _safe_release_component(Path(dirpath) / dirname)
        for fname in filenames:
            path = Path(dirpath) / fname
            head = read(path, errors="ignore")[:2000]
            spdx_ids.update(re.findall(r"SPDX-License-Identifier: ([A-Za-z0-9.\-]+)", head))
    # REUSE-IgnoreEnd
    for lic in sorted(spdx_ids):
        check(release_file_exists(ROOT / "LICENSES" / f"{lic}.txt"),
              f"licence {lic} is used but LICENSES/{lic}.txt is missing")

    # --- 8. agent entry ------------------------------------------------------------
    agents = read(ROOT / "AGENTS.md")
    for required in (
        "ARCHITECTURE.md",
        "docs/orientation.json",
        "docs/ORIENTATION.md",
        "docs/claims.json",
        "docs/corpus_descriptor.json",
        "docs/methodology.json",
        "METHODOLOGY.md",
        "SCOPE.md",
        "Erdos249257.lean",
        "ErdosProblems.lean",
        "scripts/check_release.py",
        "scripts/check_architecture_guide.py",
        "scripts/test_architecture_guide.py",
            "scripts/agent_entry.py",
            "scripts/agent_skill_catalog.py",
            "scripts/test_agent_entry.py",
            "skills/maintain-public-infrastructure/SKILL.md",
        "scripts/query_corpus.py",
    ):
        check(required in agents, f"AGENTS.md does not route through {required}")
    flat_agents = flattened(agents)
    check("remain open" in flat_agents,
          "AGENTS.md must preserve the open-problem boundary")
    check("proof authority" in flat_agents,
          "AGENTS.md must state the proof-authority boundary")
    check("larger ongoing formal-mathematics workflow" in flat_agents,
          "AGENTS.md must preserve the public-projection provenance boundary")
    check("mathematical programme" in flat_agents,
          "AGENTS.md must expose mathematical programme routes")

    mid_checks = run_independent_checks(
        {
            "architecture": [
                sys.executable,
                str(ROOT / "scripts" / "check_architecture_guide.py"),
            ],
            "architecture_fixtures": [
                sys.executable,
                str(ROOT / "scripts" / "test_architecture_guide.py"),
            ],
            "agent_entry": [
                sys.executable,
                str(ROOT / "scripts" / "test_agent_entry.py"),
            ],
            "agent_skill_catalog": [
                sys.executable,
                str(ROOT / "scripts" / "agent_skill_catalog.py"),
                "--check",
            ],
            "clone_skills": [
                sys.executable,
                str(ROOT / "scripts" / "test_clone_skills.py"),
            ],
            "contribution_entry": [
                sys.executable,
                str(ROOT / "scripts" / "test_contribution_entry.py"),
            ],
            "human_first_contact": [
                sys.executable,
                str(ROOT / "scripts" / "test_human_first_contact.py"),
            ],
            "agent_navigation_paper": [
                sys.executable,
                str(ROOT / "scripts" / "check_agent_navigation_paper.py"),
            ],
            "certificate_probe": [
                sys.executable,
                str(ROOT / "scripts" / "probe_certificate_supply.py"),
                "--check",
            ],
            "second_channel_probe": [
                sys.executable,
                str(ROOT / "scripts" / "probe_second_channel_separation.py"),
                "--check",
            ],
            "semantic_contract": [
                sys.executable,
                str(ROOT / "scripts" / "check_semantic_corpus.py"),
            ],
            "semantic_review": [
                sys.executable,
                str(ROOT / "scripts" / "semantic_review.py"),
                "--check",
            ],
            "semantic_review_fixtures": [
                sys.executable,
                str(ROOT / "scripts" / "test_semantic_review.py"),
            ],
            "theory_lab_contract": [
                sys.executable,
                str(ROOT / "scripts" / "check_theory_lab.py"),
            ],
            "reasoning_coordinates": [
                sys.executable,
                str(ROOT / "scripts" / "test_reasoning_source_coordinates.py"),
            ],
            "reasoning_assembly": [
                sys.executable,
                str(ROOT / "scripts" / "assemble_reasoning_surfaces.py"),
                "--check",
            ],
            "paper_boundary": [
                sys.executable,
                str(ROOT / "scripts" / "check_rendered_paper_boundary.py"),
                "--source-only",
            ],
        }
    )
    architecture_check = mid_checks["architecture"]
    check(
        architecture_check.returncode == 0,
        "newcomer architecture guide failed: "
        f"{architecture_check.stdout.strip() or architecture_check.stderr.strip()}",
    )
    architecture_fixture_check = mid_checks["architecture_fixtures"]
    check(
        architecture_fixture_check.returncode == 0,
        "newcomer architecture guide fixtures failed: "
        f"{architecture_fixture_check.stdout.strip() or architecture_fixture_check.stderr.strip()}",
    )
    agent_entry_check = mid_checks["agent_entry"]
    check(
        agent_entry_check.returncode == 0,
        "clone-local agent entry failed: "
        f"{agent_entry_check.stdout.strip() or agent_entry_check.stderr.strip()}",
    )
    agent_skill_catalog_check = mid_checks["agent_skill_catalog"]
    check(
        agent_skill_catalog_check.returncode == 0,
        "clone-local skill catalog failed: "
        f"{agent_skill_catalog_check.stdout.strip() or agent_skill_catalog_check.stderr.strip()}",
    )
    clone_skills_check = mid_checks["clone_skills"]
    check(
        clone_skills_check.returncode == 0,
        "clone-local skill installation and discovery failed: "
        f"{clone_skills_check.stdout.strip() or clone_skills_check.stderr.strip()}",
    )
    contribution_entry_check = mid_checks["contribution_entry"]
    check(
        contribution_entry_check.returncode == 0,
        "public contribution and credit entry failed: "
        f"{contribution_entry_check.stdout.strip() or contribution_entry_check.stderr.strip()}",
    )
    agent_navigation_paper_check = mid_checks["agent_navigation_paper"]
    check(
        agent_navigation_paper_check.returncode == 0,
        "agent-navigation paper failed: "
        f"{agent_navigation_paper_check.stdout.strip() or agent_navigation_paper_check.stderr.strip()}",
    )

    contributing = read(ROOT / "CONTRIBUTING.md")
    contributing_errors = contributor_gate_posture_errors(contributing)
    check(not contributing_errors, "; ".join(contributing_errors))

    source_map = read(ROOT / "docs" / "SOURCE_MAP.md")
    source_map_errors = source_map_entry_errors(source_map)
    check(not source_map_errors, "; ".join(source_map_errors))

    wave_index = read(ROOT / "docs" / "WAVE_INDEX.md")
    wave_index_errors = wave_index_entry_errors(wave_index)
    check(not wave_index_errors, "; ".join(wave_index_errors))

    methodology_check = run(
        [sys.executable, str(ROOT / "scripts" / "build_methodology.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(methodology_check.returncode == 0,
          f"methodology projection drift: {methodology_check.stdout.strip() or methodology_check.stderr.strip()}")

    module_graph_check = run(
        [sys.executable, str(ROOT / "scripts" / "build_module_graph.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(module_graph_check.returncode == 0,
          f"module graph drift: {module_graph_check.stdout.strip() or module_graph_check.stderr.strip()}")

    atlas_check = run(
        [sys.executable, str(ROOT / "scripts" / "build_declaration_atlas.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(atlas_check.returncode == 0,
          f"declaration atlas drift: {atlas_check.stdout.strip() or atlas_check.stderr.strip()}")

    certificate_probe_check = mid_checks["certificate_probe"]
    check(certificate_probe_check.returncode == 0,
          f"certificate-supply probe drift: {certificate_probe_check.stdout.strip() or certificate_probe_check.stderr.strip()}")

    second_channel_probe_check = mid_checks["second_channel_probe"]
    check(second_channel_probe_check.returncode == 0,
          f"second-channel separation probe drift: {second_channel_probe_check.stdout.strip() or second_channel_probe_check.stderr.strip()}")

    off_diagonal_roster_check = run(
        [
            sys.executable,
            str(ROOT / "scripts" / "build_off_diagonal_certificate_roster.py"),
            "--check",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(off_diagonal_roster_check.returncode == 0,
          f"off-diagonal certificate roster drift: {off_diagonal_roster_check.stdout.strip() or off_diagonal_roster_check.stderr.strip()}")

    diagonal_depth_roster_check = run(
        [
            sys.executable,
            str(ROOT / "scripts" / "build_checked_diagonal_depth_roster.py"),
            "--check",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(diagonal_depth_roster_check.returncode == 0,
          f"checked diagonal depth roster drift: {diagonal_depth_roster_check.stdout.strip() or diagonal_depth_roster_check.stderr.strip()}")

    # The semantic corpus is what makes "what does this prove" a query rather
    # than a reread.  Its coverage contract is what stops a barrier from being
    # described as closing a family of engines while a weaker sibling engine
    # survives it, which has happened here once already.
    semantic_build = run(
        [sys.executable, str(ROOT / "scripts" / "build_semantic_corpus.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(semantic_build.returncode == 0,
          f"semantic corpus drift: {semantic_build.stdout.strip() or semantic_build.stderr.strip()}")

    semantic_contract = mid_checks["semantic_contract"]
    check(semantic_contract.returncode == 0,
          f"semantic coverage contract: {semantic_contract.stdout.strip() or semantic_contract.stderr.strip()}")
    semantic_review_check = mid_checks["semantic_review"]
    check(
        semantic_review_check.returncode == 0,
        "semantic review receipt contract: "
        f"{semantic_review_check.stdout.strip() or semantic_review_check.stderr.strip()}",
    )
    semantic_review_fixtures = mid_checks["semantic_review_fixtures"]
    check(
        semantic_review_fixtures.returncode == 0,
        "semantic review mutation fixtures: "
        f"{semantic_review_fixtures.stdout.strip() or semantic_review_fixtures.stderr.strip()}",
    )

    # The theory lab is the layer that makes predictive claims -- which mechanism
    # explains a proof, what survives an intervention, whether an explanation
    # transfers.  Its contract is stricter than the corpus contract because the
    # failure mode is worse: a plausible mechanism laid over a proof that works
    # for another reason, or a barrier written up without naming the sibling
    # engines it leaves alive.
    lab_build = run(
        [sys.executable, str(ROOT / "scripts" / "build_theory_lab.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(lab_build.returncode == 0,
          f"theory lab drift: {lab_build.stdout.strip() or lab_build.stderr.strip()}")

    lab_contract = mid_checks["theory_lab_contract"]
    check(lab_contract.returncode == 0,
          f"theory lab contract: {lab_contract.stdout.strip() or lab_contract.stderr.strip()}")
    theory_lab = json.loads(read(ROOT / "docs" / "theory_lab.json"))
    check(
        theory_lab.get("schema") == "erdos249257-theory-lab/2",
        "theory lab must use content-addressed schema erdos249257-theory-lab/2",
    )
    check(
        "source_revision" not in theory_lab
        and theory_lab.get("source_provenance", {}).get("identity_kind")
        == "content_addressed_input_set",
        "theory lab retains self-invalidating Git-derived provenance",
    )

    # The authored semantic zones pin Lean line numbers by hand. Nothing checked
    # them until 2026-08-31, by which point 3722 pinned rows across 39 of the 94
    # zones named a line their declaration had moved off, and the only surface
    # that noticed was one digest test for one zone.
    zone_coordinate_check = run(
        [
            sys.executable,
            str(ROOT / "scripts" / "refresh_zone_source_coordinates.py"),
            "--check",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(
        zone_coordinate_check.returncode == 0,
        "semantic zone source-coordinate drift: "
        + (
            zone_coordinate_check.stdout.strip()
            or zone_coordinate_check.stderr.strip()
        ),
    )

    # docs/module_synopsis_index.json carries its own freshness check and was
    # in neither this gate nor the refresh pipeline, so nothing ran the check
    # and nothing rebuilt the file. query_corpus rejects the index outright
    # when its fingerprint disagrees with the atlas, so the rot showed up only
    # as an empty index behind a bare assert.
    synopsis_check = run(
        [
            sys.executable,
            str(ROOT / "scripts" / "build_module_synopsis_index.py"),
            "--check",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(
        synopsis_check.returncode == 0,
        "module synopsis index freshness: "
        + (synopsis_check.stdout.strip() or synopsis_check.stderr.strip()),
    )

    coordinate_check = run(
        [sys.executable, str(ROOT / "scripts" / "refresh_source_coordinates.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(coordinate_check.returncode == 0,
          f"source-coordinate drift: {coordinate_check.stdout.strip() or coordinate_check.stderr.strip()}")

    reasoning_coordinate_check = run(
        [
            sys.executable,
            str(ROOT / "scripts" / "refresh_reasoning_source_coordinates.py"),
            "--check",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(
        reasoning_coordinate_check.returncode == 0,
        "reasoning source-coordinate drift: "
        + (
            reasoning_coordinate_check.stdout.strip()
            or reasoning_coordinate_check.stderr.strip()
        ),
    )
    reasoning_coordinate_test = mid_checks["reasoning_coordinates"]
    check(
        reasoning_coordinate_test.returncode == 0,
        "reasoning source-coordinate regression: "
        + (
            reasoning_coordinate_test.stdout.strip()
            or reasoning_coordinate_test.stderr.strip()
        ),
    )

    corpus_check = run(
        [sys.executable, str(ROOT / "scripts" / "build_corpus_descriptor.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(corpus_check.returncode == 0,
          f"corpus descriptor drift: {corpus_check.stdout.strip() or corpus_check.stderr.strip()}")

    paper_alias_check = run(
        [sys.executable, str(ROOT / "scripts" / "build_paper_module_aliases.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(paper_alias_check.returncode == 0,
          f"paper module alias drift: {paper_alias_check.stdout.strip() or paper_alias_check.stderr.strip()}")
    reasoning_assembly_check = mid_checks["reasoning_assembly"]
    check(
        reasoning_assembly_check.returncode == 0,
        "reasoning-surface assembly drift: "
        + (
            reasoning_assembly_check.stdout.strip()
            or reasoning_assembly_check.stderr.strip()
        ),
    )
    boundary = mid_checks["paper_boundary"]
    check(
        boundary.returncode == 0,
        "human-facing paper boundary failed: "
        f"{boundary.stdout.strip() or boundary.stderr.strip()}",
    )

    descriptor = json.loads(read(ROOT / "docs" / "corpus_descriptor.json"))
    check(descriptor.get("schema") == "erdos249257-corpus-descriptor/5",
          "corpus descriptor must use schema erdos249257-corpus-descriptor/5")
    check(descriptor.get("release_provenance") == public_projection,
          "corpus descriptor release provenance drifted from docs/claims.json")
    descriptor_path = ROOT / "docs" / "corpus_descriptor.json"
    check(len(read_bytes(descriptor_path)) <= 64_000,
          "corpus descriptor exceeds the 64 KB registration-envelope budget")
    compact_graph = descriptor.get("compact_graph", {})
    check("module_graph" not in compact_graph and "high_salience_declarations" not in compact_graph,
          "corpus descriptor re-embedded an exhaustive graph removed in schema 3")
    module_topology = compact_graph.get("module_topology", {})
    check(module_topology.get("node_count") == len(machine_paper["module_graph"]["nodes"]),
          "corpus descriptor module count drifted from the machine-readable paper")
    check(module_topology.get("full_graph") == "docs/claims.json::machine_readable_paper.module_graph",
          "corpus descriptor does not route to the complete module graph")
    expected_compact_programmes = [
        {
            "id": route["id"],
            "title": route["title"],
            "core_claim_count": len(route["core_claim_ids"]),
            "representative_claim_ids": route["core_claim_ids"][:2],
            "remaining_open_proposition_ids": route[
                "remaining_open_proposition_ids"
            ],
        }
        for route in machine_paper["entrypoints"]
        if route.get("route_kind") == "mathematical_programme"
    ]
    check(compact_graph.get("mathematical_programmes") == expected_compact_programmes,
          "corpus descriptor mathematical programme index drifted")
    check(
        compact_graph.get("mathematical_programme_query")
        == "python3 scripts/query_corpus.py --route <programme_route_id>",
        "corpus descriptor mathematical programme query route drifted",
    )
    check(descriptor.get("capabilities", {}).get("typed_mathematical_programme_routes") is True,
          "corpus descriptor does not advertise typed mathematical programme routes")
    methodology_content = descriptor.get("identity", {}).get("content", {}).get("methodology_contract", {})
    check(methodology_content.get("path") == "docs/methodology.json",
          "corpus descriptor does not register docs/methodology.json")
    check(descriptor.get("schemas", {}).get("methodology") == methodology.get("schema"),
          "corpus descriptor methodology schema does not match docs/methodology.json")
    methodology_capsule = descriptor.get("compact_graph", {}).get("methodology_capsule", {})
    check(methodology_capsule.get("human_capsule") == methodology.get("human_capsule"),
          "corpus descriptor methodology capsule drifted from docs/methodology.json")
    check(methodology_capsule.get("change_classes") == methodology.get("change_classes"),
          "corpus descriptor methodology capsule does not carry the change-class matrix")
    descriptor_content = descriptor.get("identity", {}).get("content", {})
    paper_aliases = json.loads(read(ROOT / "paper" / "module-aliases.json"))
    paper_artifacts = {
        "human_exposition": (
            "paper/erdos249-257-main-paper.tex",
            "erdos249-257-main-paper.pdf",
        ),
    }
    for content_id, (source_path, rendered_path) in paper_artifacts.items():
        content = descriptor_content.get(content_id, {})
        check(content.get("source_path") == source_path,
              f"corpus descriptor {content_id} source path is missing or incorrect")
        check(content.get("rendered_path") == rendered_path,
              f"corpus descriptor {content_id} rendered path is missing or incorrect")
        check(content.get("source_content_digest") == file_digest(ROOT / source_path),
              f"corpus descriptor {content_id} source digest drifted")
        check(content.get("rendered_content_digest") == file_digest(ROOT / rendered_path),
              f"corpus descriptor {content_id} rendered digest drifted")
        check(content.get("authority_posture") == "authored_editorial_surface_not_Lean_proof_authority",
              f"corpus descriptor {content_id} does not preserve the proof-authority boundary")
    sigils = descriptor_content.get("paper_source_sigils", {})
    check(sigils.get("path") == "paper/module-aliases.json",
          "corpus descriptor does not register the paper source-sigil crosswalk")
    check(sigils.get("content_digest") == file_digest(ROOT / "paper" / "module-aliases.json"),
          "corpus descriptor paper source-sigil digest drifted")
    check(descriptor.get("schemas", {}).get("paper_module_aliases") == paper_aliases.get("schema"),
          "corpus descriptor paper source-sigil schema drifted")

    orientation_path = ROOT / "docs" / "orientation.json"
    orientation = json.loads(read(orientation_path))
    declaration_atlas = json.loads(read(ROOT / "docs" / "declaration_atlas.json"))
    check(orientation.get("schema") == "erdos249257-orientation/1",
          "orientation projection must use schema erdos249257-orientation/1")
    check(orientation.get("scale") == declaration_atlas.get("summary"),
          "orientation scale drifted from the declaration atlas")
    check(orientation.get("release_provenance") == public_projection,
          "orientation release provenance drifted from docs/claims.json")
    expected_principal_ids = [
        claim["id"] for claim in data["claims"] if claim.get("readme_headline")
    ]
    actual_principal_ids = [
        claim.get("id") for claim in orientation.get("principal_claims", [])
    ]
    check(actual_principal_ids == expected_principal_ids,
          "orientation principal claims drifted from README-headline claims")
    expected_programmes = [
        {
            "id": route["id"],
            "title": route["title"],
            "mathematical_focus": route["mathematical_focus"],
            "claim_ceiling": route["claim_ceiling"],
            "core_claim_count": len(route["core_claim_ids"]),
            "representative_claim_ids": route["core_claim_ids"][:2],
            "remaining_open_proposition_ids": route[
                "remaining_open_proposition_ids"
            ],
        }
        for route in machine_paper["entrypoints"]
        if route.get("route_kind") == "mathematical_programme"
    ]
    check(orientation.get("mathematical_programmes") == expected_programmes,
          "orientation mathematical programmes drifted from machine-readable-paper entrypoints")
    publication_assembly = machine_paper["publication_assembly"]
    architecture = publication_assembly["publication_architecture"]
    expected_editorial_architecture = {
        "canonical_gateway": {
            key: architecture["canonical_gateway"][key]
            for key in ("source", "decision")
        },
        "retained_companions": [
            {"source": companion["source"]}
            for companion in architecture.get("retained_companions", [])
        ],
        "qualified_future_companion": {
            key: architecture["qualified_future_companion"][key]
            for key in ("id", "decision")
        },
    }
    check(orientation.get("editorial_architecture")
          == expected_editorial_architecture,
          "orientation editorial architecture drifted from publication_assembly")
    editorial_state = publication_assembly["editorial_state"]
    expected_editorial_state = {
        "current_priority": editorial_state["current_priority"],
        "active_inconsistencies": editorial_state["active_inconsistencies"],
        "blocked_decisions": editorial_state["blocked_decisions"],
    }
    check(orientation.get("editorial_state") == expected_editorial_state,
          "orientation editorial state drifted from publication_assembly")
    expected_source_provenance = {
        "formal_source_ref": data["release"]["formal_source"]["ref"],
        "main_paper_source_digest": file_digest(
            ROOT / "paper" / "erdos249-257-main-paper.tex"
        ),
        "navigation_projection_identity": (
            "content digests; no checkout commit embedded"
        ),
    }
    check(orientation.get("source_provenance") == expected_source_provenance,
          "orientation source provenance differs from its canonical claims or paper")
    check(
        "navigation_snapshot" not in descriptor.get("identity", {}),
        "corpus descriptor retains the ambiguous historical navigation snapshot",
    )
    check(len(read_bytes(orientation_path)) <= 36_000,
          "orientation JSON exceeds the 36 KB bounded first-read budget")
    for target in orientation.get("drilldowns", {}).values():
        targets = target if isinstance(target, list) else [target]
        for item in targets:
            rel = str(item).split("::", 1)[0]
            check(
                release_file_exists(ROOT / rel),
                f"orientation drilldown path does not exist: {rel}",
            )
    late_checks = finish_independent_checks(late_executor, late_futures)
    query_check = late_checks["query"]
    check(query_check.returncode == 0,
          f"corpus query surface failed: {query_check.stdout.strip() or query_check.stderr.strip()}")
    mutation_harness_check = late_checks["mutation_harness"]
    check(
        mutation_harness_check.returncode == 0,
        "publication mutation harness self-test failed: "
        f"{mutation_harness_check.stdout.strip() or mutation_harness_check.stderr.strip()}",
    )
    public_boundary_check = late_checks["public_boundary"]
    check(
        public_boundary_check.returncode == 0,
        "public-artifact boundary contract failed: "
        f"{public_boundary_check.stdout.strip() or public_boundary_check.stderr.strip()}",
    )
    primary_source_disposition_check = late_checks["primary_source_disposition"]
    check(
        primary_source_disposition_check.returncode == 0,
        "third-party source redistribution disposition contract failed: "
        f"{primary_source_disposition_check.stdout.strip() or primary_source_disposition_check.stderr.strip()}",
    )
    # The adversarial program starts by running the complete baseline against
    # one collected packet set, then mutates that same set.  Running the
    # standalone diagnostic here as well would repeat every bounded query.
    # Keep the diagnostic as a user-facing command, but execute the combined
    # baseline-plus-adversarial program once in the release gate.
    cold_clone_adversarial = late_checks["cold_clone_adversarial"]
    check(cold_clone_adversarial.returncode == 0,
          "bounded cold-clone baseline/adversarial check failed: "
          f"{cold_clone_adversarial.stdout.strip() or cold_clone_adversarial.stderr.strip()}")

    proof_cockpit_check = late_checks["proof_cockpit"]
    check(
        proof_cockpit_check.returncode == 0,
        "cold-clone proof cockpit check failed: "
        f"{proof_cockpit_check.stdout.strip() or proof_cockpit_check.stderr.strip()}",
    )
    clone_footprint_check = late_checks["clone_footprint"]
    check(
        clone_footprint_check.returncode == 0,
        "clone-footprint budget check failed: "
        f"{clone_footprint_check.stdout.strip() or clone_footprint_check.stderr.strip()}",
    )

    # --- report ---------------------------------------------------------------------
    if ERRORS:
        print(f"check_release: {len(ERRORS)} failure(s) across {CHECKS} checks")
        for err in ERRORS:
            print(f"  FAIL {err}")
        return 1
    print(f"check_release: all {CHECKS} checks passed for release {tag}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except UnsafeReleasePath as exc:
        print(f"check_release: unsafe release path: {exc}", file=sys.stderr)
        sys.exit(1)
