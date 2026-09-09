#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the public checkout from silently regressing into a giant clone."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
MIB = 1024 * 1024
FULL_CHECKOUT_LIMIT_BYTES = 420 * MIB
QUICK_LEAN_CHECKOUT_LIMIT_BYTES = 8 * MIB
LEAN_CHECKOUT_LIMIT_BYTES = 160 * MIB
READER_CHECKOUT_LIMIT_BYTES = 32 * MIB
SINGLE_BLOB_LIMIT_BYTES = 100 * MIB
MINIMUM_LEAN_CHECKOUT_REDUCTION = 0.50
QUICK_LEAN_TARGET = "ErdosProblems.Erdos249.PeriodMultipleEscape"
QUICK_LEAN_SPARSE_MANIFEST_PATH = ROOT / "scripts/lean-quick-sparse-checkout"
QUICK_LEAN_COMMON_PATTERNS = (
    "/scripts/lean-quick-sparse-checkout",
    "/scripts/lean-sparse-checkout",
    "/scripts/lean_fast_build.py",
    "/scripts/lean_build_share.py",
    "/scripts/lean_package_share.py",
    "/scripts/validation_singleflight.py",
    "/*.md",
    "/.gitignore",
    "/CITATION.cff",
    "/LICENSE",
    "/REUSE.toml",
    "/formalization.yaml",
    "/lake-manifest.json",
    "/lakefile.toml",
    "/lean-toolchain",
)
LEAN_SPARSE_MANIFEST_PATH = ROOT / "scripts/lean-sparse-checkout"
LEAN_SPARSE_PATTERNS = (
    "/Erdos249257/",
    "/ErdosProblems/",
    "/scripts/lean_fast_build.py",
    "/scripts/lean_build_share.py",
    "/scripts/lean_package_share.py",
    "/scripts/lean-sparse-checkout",
    "/scripts/validation_singleflight.py",
    "/.gitignore",
    "/AGENTS.md",
    "/AGENTS.override.md",
    "/ARCHITECTURE.md",
    "/CITATION.cff",
    "/CLAUDE.md",
    "/CODEX.md",
    "/CONTRIBUTING.md",
    "/CURSOR.md",
    "/Erdos249257.lean",
    "/ErdosProblems.lean",
    "/GEMINI.md",
    "/HUMAN_ENTRY.md",
    "/LICENSE",
    "/METHODOLOGY.md",
    "/PRIVACY.md",
    "/README.md",
    "/REUSE.toml",
    "/SCOPE.md",
    "/SECURITY.md",
    "/docs/repository_identity.json",
    "/formalization.yaml",
    "/lake-manifest.json",
    "/lakefile.toml",
    "/lean-toolchain",
    "!/ErdosProblems/FreePosition/data.jsonl",
)
LEAN_SPARSE_MANIFEST_TEXT = "\n".join(LEAN_SPARSE_PATTERNS) + "\n"
READER_SPARSE_MANIFEST_PATH = ROOT / "scripts/reader-sparse-checkout"
READER_SPARSE_PATTERNS = (
    "/.github/banner.png",
    "/.github/system-map.png",
    "/docs/AGENT_WORKBENCH.md",
    "/docs/ARCHITECTURE.md",
    "/docs/CONTRIBUTOR_PATH.md",
    "/docs/CORRECTIONS.md",
    "/docs/ORIENTATION.md",
    "/docs/PAPER_LIBRARY.md",
    "/docs/PROOF_COCKPIT.md",
    "/docs/REPRODUCIBILITY.md",
    "/docs/SOURCE_MAP.md",
    "/docs/claims.json",
    "/docs/problems.json",
    "/docs/problem_library.json",
    "/docs/PROBLEM_LIBRARY.md",
    "/docs/papers/",
    "/paper/",
    "/scripts/reader-sparse-checkout",
    "/*.md",
    "/*.pdf",
    "/CITATION.cff",
    "/LICENSE",
    "/REUSE.toml",
    "/SCOPE.md",
)
READER_SPARSE_MANIFEST_TEXT = "\n".join(READER_SPARSE_PATTERNS) + "\n"
REPRODUCIBILITY_PATH = ROOT / "docs" / "REPRODUCIBILITY.md"
REPRODUCIBILITY_LINK_TARGET = "docs/REPRODUCIBILITY.md"
RUNBOOK_CLONE_COMMAND = (
    "git clone --filter=blob:none "
    "https://github.com/wcook04/plectis-erdos.git"
)
RUNBOOK_CD_COMMAND = "cd plectis-erdos"
RUNBOOK_FETCH_COMMAND = "git fetch --tags --force"
RUNBOOK_QUICK_CHECK_COMMAND = (
    "python3 scripts/check_cold_clone_comprehension.py --quick"
)
LEAN_BUILD_COMMAND = "python3 scripts/lean_fast_build.py --jobs 2"


def quick_lean_sparse_patterns(root: Path = ROOT) -> tuple[str, ...]:
    """Derive the first proof check's exact local import cone."""

    import lean_fast_build as planner

    modules = planner.discover(root)
    graph = planner.local_graph(modules)
    if QUICK_LEAN_TARGET not in modules:
        raise RuntimeError(f"quick Lean target is absent: {QUICK_LEAN_TARGET}")
    source_patterns = tuple(
        f"/{modules[name].relative_to(root).as_posix()}"
        for name in sorted(planner.reachable([QUICK_LEAN_TARGET], graph))
    )
    return source_patterns + QUICK_LEAN_COMMON_PATTERNS


QUICK_LEAN_SPARSE_PATTERNS = quick_lean_sparse_patterns()
QUICK_LEAN_SPARSE_MANIFEST_TEXT = "\n".join(QUICK_LEAN_SPARSE_PATTERNS) + "\n"


def committed_entries(root: Path = ROOT, revision: str = "HEAD") -> list[dict[str, Any]]:
    """Read checkout-relevant blob sizes without opening their contents."""

    result = subprocess.run(
        ["git", "-C", str(root), "ls-tree", "-r", "-l", "-z", revision],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    entries: list[dict[str, Any]] = []
    for raw_record in result.stdout.split(b"\0"):
        if not raw_record:
            continue
        metadata, raw_path = raw_record.split(b"\t", 1)
        mode, object_type, object_id, raw_size = metadata.split()
        if object_type != b"blob":
            continue
        entries.append(
            {
                "mode": mode.decode("ascii"),
                "object_id": object_id.decode("ascii"),
                "size_bytes": 0 if raw_size == b"-" else int(raw_size),
                "path": raw_path.decode("utf-8"),
            }
        )
    return entries


def belongs_to_lean_sparse_checkout(path: str) -> bool:
    """Match the versioned non-cone proof-build checkout manifest."""

    rooted = f"/{path}"
    included = False
    for raw_pattern in LEAN_SPARSE_PATTERNS:
        excluded = raw_pattern.startswith("!")
        pattern = raw_pattern.removeprefix("!")
        if rooted == pattern or (pattern.endswith("/") and rooted.startswith(pattern)):
            included = not excluded
    return included


def belongs_to_quick_lean_sparse_checkout(path: str) -> bool:
    """Match the exact first-proof import cone and its build tooling."""

    rooted = f"/{path}"
    return any(
        rooted == pattern
        or (pattern == "/*.md" and "/" not in path and path.endswith(".md"))
        for pattern in QUICK_LEAN_SPARSE_PATTERNS
    )


def belongs_to_reader_sparse_checkout(path: str) -> bool:
    rooted = f"/{path}"
    return any(
        rooted == pattern
        or (pattern.endswith("/") and rooted.startswith(pattern))
        or (pattern == "/*.md" and "/" not in path and path.endswith(".md"))
        or (pattern == "/*.pdf" and "/" not in path and path.endswith(".pdf"))
        for pattern in READER_SPARSE_PATTERNS
    )


def build_report(entries: Iterable[dict[str, Any]]) -> dict[str, Any]:
    rows = list(entries)
    full_bytes = sum(int(row["size_bytes"]) for row in rows)
    quick_lean_bytes = sum(
        int(row["size_bytes"])
        for row in rows
        if belongs_to_quick_lean_sparse_checkout(str(row["path"]))
    )
    lean_bytes = sum(
        int(row["size_bytes"])
        for row in rows
        if belongs_to_lean_sparse_checkout(str(row["path"]))
    )
    reader_bytes = sum(
        int(row["size_bytes"])
        for row in rows
        if belongs_to_reader_sparse_checkout(str(row["path"]))
    )
    largest = max(rows, key=lambda row: int(row["size_bytes"]), default=None)
    reduction = (full_bytes - lean_bytes) / full_bytes if full_bytes else 0.0
    return {
        "schema": "plectis_clone_footprint_v1",
        "full_checkout_bytes": full_bytes,
        "full_checkout_limit_bytes": FULL_CHECKOUT_LIMIT_BYTES,
        "quick_lean_sparse_checkout_bytes": quick_lean_bytes,
        "quick_lean_sparse_checkout_limit_bytes": QUICK_LEAN_CHECKOUT_LIMIT_BYTES,
        "lean_sparse_checkout_bytes": lean_bytes,
        "lean_sparse_checkout_limit_bytes": LEAN_CHECKOUT_LIMIT_BYTES,
        "reader_sparse_checkout_bytes": reader_bytes,
        "reader_sparse_checkout_limit_bytes": READER_CHECKOUT_LIMIT_BYTES,
        "lean_sparse_omitted_bytes": full_bytes - lean_bytes,
        "lean_sparse_reduction_fraction": round(reduction, 6),
        "minimum_lean_sparse_reduction_fraction": MINIMUM_LEAN_CHECKOUT_REDUCTION,
        "single_blob_limit_bytes": SINGLE_BLOB_LIMIT_BYTES,
        "largest_blob": largest,
        "tracked_blob_count": len(rows),
        "scope": "committed_tree_checkout_bytes_not_network_pack_bytes",
    }


def contract_errors(
    report: dict[str, Any],
    readme: str,
    sparse_manifest: str = LEAN_SPARSE_MANIFEST_TEXT,
    reader_sparse_manifest: str = READER_SPARSE_MANIFEST_TEXT,
    quick_sparse_manifest: str = QUICK_LEAN_SPARSE_MANIFEST_TEXT,
    reproducibility: str = "",
) -> list[str]:
    errors: list[str] = []
    if int(report["full_checkout_bytes"]) > FULL_CHECKOUT_LIMIT_BYTES:
        errors.append("committed full checkout exceeds the 420 MiB clone budget")
    if int(report["quick_lean_sparse_checkout_bytes"]) > QUICK_LEAN_CHECKOUT_LIMIT_BYTES:
        errors.append("versioned quick Lean checkout exceeds the 8 MiB budget")
    if int(report["lean_sparse_checkout_bytes"]) > LEAN_CHECKOUT_LIMIT_BYTES:
        errors.append("versioned Lean sparse checkout exceeds the 160 MiB budget")
    if int(report["reader_sparse_checkout_bytes"]) > READER_CHECKOUT_LIMIT_BYTES:
        errors.append("versioned reader sparse checkout exceeds the 32 MiB budget")
    largest = report.get("largest_blob")
    if isinstance(largest, dict) and int(largest["size_bytes"]) > SINGLE_BLOB_LIMIT_BYTES:
        errors.append(
            f"committed blob exceeds the 100 MiB budget: {largest['path']}"
        )
    if float(report["lean_sparse_reduction_fraction"]) < MINIMUM_LEAN_CHECKOUT_REDUCTION:
        errors.append("Lean sparse checkout no longer omits at least half the full tree")
    if f"]({REPRODUCIBILITY_LINK_TARGET})" not in readme:
        errors.append("README is missing its local reproducibility-runbook link")
    runbook_commands = (
        RUNBOOK_CLONE_COMMAND,
        RUNBOOK_CD_COMMAND,
        RUNBOOK_FETCH_COMMAND,
        RUNBOOK_QUICK_CHECK_COMMAND,
        LEAN_BUILD_COMMAND,
    )
    for command in runbook_commands:
        if command not in reproducibility:
            errors.append(f"reproducibility runbook is missing required route: {command}")
    positions = [reproducibility.find(command) for command in runbook_commands]
    if any(position < 0 for position in positions) or positions != sorted(positions):
        errors.append(
            "reproducibility runbook must order clone, repository entry, history "
            "fetch, quick navigation check, then bounded Lean build"
        )
    if quick_sparse_manifest != QUICK_LEAN_SPARSE_MANIFEST_TEXT:
        errors.append("versioned quick Lean sparse manifest has drifted from its import cone")
    if sparse_manifest != LEAN_SPARSE_MANIFEST_TEXT:
        errors.append("versioned Lean sparse manifest has drifted from the checked contract")
    if reader_sparse_manifest != READER_SPARSE_MANIFEST_TEXT:
        errors.append("versioned reader sparse manifest has drifted from the checked contract")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail when a clone budget regresses")
    parser.add_argument("--revision", default="HEAD")
    args = parser.parse_args(argv)
    report = build_report(committed_entries(ROOT, args.revision))
    errors = contract_errors(
        report,
        (ROOT / "README.md").read_text(encoding="utf-8"),
        LEAN_SPARSE_MANIFEST_PATH.read_text(encoding="utf-8"),
        READER_SPARSE_MANIFEST_PATH.read_text(encoding="utf-8"),
        QUICK_LEAN_SPARSE_MANIFEST_PATH.read_text(encoding="utf-8"),
        REPRODUCIBILITY_PATH.read_text(encoding="utf-8"),
    )
    report["status"] = "pass" if not errors else "fail"
    report["errors"] = errors
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if args.check and errors else 0


if __name__ == "__main__":
    sys.exit(main())
