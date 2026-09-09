#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for bounded cold-clone comprehension."""

from __future__ import annotations

import argparse
import copy
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

import check_cold_clone_comprehension as diagnostic
import query_route_memory as route_memory
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
ROUTE_MEMORY_SCRIPT = ROOT / "scripts" / "query_route_memory.py"
FROZEN_PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)
HOSTILE_ENVIRONMENT = {
    "GIT_DIR": "/tmp/not-this-checkout/.git",
    "GIT_NAMESPACE": "refs/namespaces/not-this-cold-clone",
    "GIT_REPLACE_REF_BASE": "refs/replace/",
    "PYTHONPATH": "/tmp/not-this-python-path",
    "LC_ALL": "C",
    "LANG": "C",
}


def require(condition: bool, message: str) -> None:
    """Keep the environment contract active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def run(args: list[str]) -> subprocess.CompletedProcess[str]:
    """Run cold-clone children without ambient checkout or interpreter state."""
    return subprocess.run(
        args,
        cwd=ROOT,
        env=singleflight.command_environment(),
        check=False,
        capture_output=True,
        text=True,
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )


def assert_rejected(packets: dict, label: str) -> None:
    try:
        diagnostic.validate_agent_packets(packets)
    except AssertionError:
        return
    raise AssertionError(f"semantic mutation escaped: {label}")


def copy_packet_sections(packets: dict, *section_names: str) -> dict:
    """Copy only the top-level packet sections an adversarial case mutates.

    The collected cold-clone packet is intentionally exhaustive.  Deep-copying
    that entire graph for each of dozens of one-field rejection checks made
    fixture setup dominate the suite, even though validators never mutate the
    untouched sections.
    """
    copied = packets.copy()
    for section_name in section_names:
        copied[section_name] = copy.deepcopy(packets[section_name])
    return copied


def assert_proof_plan_rejected(proof_plans: dict, label: str) -> None:
    try:
        diagnostic.validate_proof_plan_packets(proof_plans)
    except AssertionError:
        return
    raise AssertionError(f"proof-plan mutation escaped: {label}")


def check_proof_plan_mutations(proof_plans: dict) -> int:
    mutated = copy.deepcopy(proof_plans)
    mutated["blocked_integer_tail"]["application"]["obligations"] = [
        row
        for row in mutated["blocked_integer_tail"]["application"][
            "obligations"
        ]
        if row["name"] != "hdvd"
    ]
    assert_proof_plan_rejected(
        mutated, "proof-plan missing-obligation boundary"
    )

    mutated = copy.deepcopy(proof_plans)
    mutated["context_ready_curvature"]["exact_dependency_spine"][
        "steps"
    ] = []
    assert_proof_plan_rejected(
        mutated, "proof-plan exact dependency spine"
    )
    return 2


def assert_human_rejected(
    summary: dict,
    surfaces: dict[str, str],
    label: str,
    *,
    routed_surfaces: dict[str, str] | None = None,
) -> None:
    """Require rejection after mutating direct or README-routed surfaces."""
    original_safe_read_text = diagnostic.safe_read_text

    def read_with_routed_mutations(path: str | Path) -> str:
        route = str(path)
        if routed_surfaces is not None and route in routed_surfaces:
            return routed_surfaces[route]
        return original_safe_read_text(path)

    try:
        with patch.object(
            diagnostic,
            "safe_read_text",
            side_effect=read_with_routed_mutations,
        ):
            diagnostic.validate_human_first_contact(summary, surfaces)
    except AssertionError:
        return
    raise AssertionError(f"human first-contact mutation escaped: {label}")


def assert_census_rejected(
    census: dict, surfaces: dict[str, str], label: str
) -> None:
    try:
        diagnostic.validate_public_semantic_census(census, surfaces)
    except AssertionError:
        return
    raise AssertionError(f"public census mutation escaped: {label}")


def remove_semantic_anchor(text: str, token: str) -> str:
    """Delete every case-insensitive occurrence seen by the production check."""
    return re.sub(
        re.escape(diagnostic.normalized(token)),
        "",
        text,
        flags=re.IGNORECASE,
    )


def check_route_memory_cold_clone() -> int:
    """Exercise the tracked-only route-memory entry for every selector."""
    descriptor = json.loads(
        (ROOT / "docs" / "corpus_descriptor.json").read_text(encoding="utf-8")
    )
    diagnostic.validate_route_memory_descriptor(descriptor)
    mutated = copy.deepcopy(descriptor)
    mutated["compact_graph"]["route_memory_contract"]["problem_selectors"] = [249]
    try:
        diagnostic.validate_route_memory_descriptor(mutated)
    except AssertionError:
        pass
    else:
        raise AssertionError("descriptor route-memory selector mutation was accepted")
    # ``--all`` is the production batch entry for the complete frozen roster.
    # Spawning one fresh interpreter for every problem repeated the same source
    # loads eight times and tested process startup more than selector coverage.
    batch = run(
        [
            sys.executable,
            str(ROUTE_MEMORY_SCRIPT),
            "--all",
        ]
    )
    if batch.returncode != 0:
        raise AssertionError(f"route-memory --all failed: {batch.stderr}")
    batch_packets = json.loads(batch.stdout)
    require(isinstance(batch_packets, list), "route-memory --all did not return a list")
    require(
        {packet["problem"]["erdos_number"] for packet in batch_packets}
        == set(FROZEN_PROBLEMS),
        "route-memory --all crossed or omitted a frozen selector",
    )
    require(
        len({packet["source_snapshot"]["commit"] for packet in batch_packets}) == 1,
        "route-memory --all mixed source commits",
    )
    for packet in batch_packets:
        problem_number = packet["problem"]["erdos_number"]
        require(
            route_memory.validate_packet(packet)["resume_state"]
            == packet["resume_state"],
            f"route-memory --all resume identity drifted for #{problem_number}",
        )

    # Keep one scalar-selector process smoke so --problem parsing cannot drift
    # behind the faster batch coverage.
    scalar = run(
        [sys.executable, str(ROUTE_MEMORY_SCRIPT), "--problem", "249"]
    )
    if scalar.returncode != 0:
        raise AssertionError(f"route-memory selector #249 failed: {scalar.stderr}")
    scalar_packet = json.loads(scalar.stdout)
    if scalar_packet["problem"]["erdos_number"] != 249:
        raise AssertionError("route-memory crossed selector #249")

    cross_problem = run(
        [
            sys.executable,
            str(ROUTE_MEMORY_SCRIPT),
            "--problem",
            "249",
            "--route",
            "erdos257_half_story",
        ]
    )
    if cross_problem.returncode != 2 or cross_problem.stdout:
        raise AssertionError("cross-problem route was not rejected by the CLI")
    if "cross_problem_route" not in cross_problem.stderr:
        raise AssertionError("cross-problem rejection lost its machine-readable code")
    return len(batch_packets) + 2


def check_checker_child_environment() -> None:
    """Prove comprehension subprocesses ignore ambient checkout selectors."""
    hostile_environment = {
        **HOSTILE_ENVIRONMENT,
        "PATH": "/tmp/not-this-bin",
    }
    completed = subprocess.CompletedProcess(
        [sys.executable, "-c", "pass"], 0, stdout="", stderr=""
    )
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(
            diagnostic.subprocess, "run", return_value=completed
        ) as run_child:
            observed = diagnostic.run_child(
                [sys.executable, "-c", "pass"], cwd=ROOT.parent
            )

    require(observed is completed, "child result was not returned")
    require(len(run_child.call_args_list) == 1, "child process was not exercised")
    kwargs = run_child.call_args.kwargs
    sanitized = kwargs["env"]
    for key in (
        "GIT_DIR",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "PYTHONPATH",
    ):
        require(key not in sanitized, f"ambient {key} leaked into child")
    require(sanitized["LC_ALL"] == "C.UTF-8", "canonical locale missing")
    require(sanitized["LANG"] == "C.UTF-8", "canonical LANG missing")
    require(sanitized["PATH"] == os.defpath, "ambient PATH leaked into child")
    require(
        kwargs["timeout"] == diagnostic.singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "child timeout drifted",
    )
    require(
        diagnostic.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "cold-clone environment contract drifted",
    )


def check_public_surface_file_boundary() -> None:
    """The cold-clone evaluator must reject non-regular public surfaces."""
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        regular = root / "regular.txt"
        regular.write_text("public fixture\n", encoding="utf-8")
        directory = root / "directory"
        directory.mkdir()
        link = root / "link.txt"
        link.symlink_to(regular)
        fifo = root / "fifo"
        try:
            os.mkfifo(fifo)
        except AttributeError:
            fifo = None

        with patch.object(diagnostic, "ROOT", root):
            require(
                diagnostic.safe_read_text("regular.txt") == "public fixture\n",
                "cold-clone regular file could not be read",
            )
            for path in ("directory", "link.txt"):
                try:
                    diagnostic.safe_read_text(path)
                except diagnostic.UnsafeColdCloneInput:
                    pass
                else:
                    raise AssertionError(f"cold-clone {path} boundary escaped")
            if fifo is not None:
                try:
                    diagnostic.safe_read_text("fifo")
                except diagnostic.UnsafeColdCloneInput:
                    pass
                else:
                    raise AssertionError("cold-clone FIFO boundary escaped")

            raced_parent = root / "input-parent"
            raced_parent.mkdir()
            original_parent = root / "input-parent-original"
            outside = root / "outside"
            outside.mkdir()
            raced_input = raced_parent / "surface.txt"
            raced_input.write_text("inside\n", encoding="utf-8")
            (outside / raced_input.name).write_text("outside\n", encoding="utf-8")
            original_open = diagnostic.os.open

            def swap_parent(
                path: Path,
                flags: int,
                mode: int = 0o777,
                *,
                dir_fd: int | None = None,
            ) -> int:
                if dir_fd is not None and Path(path).name == raced_input.name:
                    raced_parent.rename(original_parent)
                    raced_parent.symlink_to(outside, target_is_directory=True)
                if dir_fd is not None:
                    return original_open(path, flags, mode, dir_fd=dir_fd)
                return original_open(path, flags, mode)

            with patch.object(diagnostic.os, "open", side_effect=swap_parent):
                observed = diagnostic.safe_read_text("input-parent/surface.txt")
            require(
                observed == "inside\n",
                "cold-clone reader followed a swapped parent directory",
            )
            require(
                (original_parent / raced_input.name).is_file(),
                "cold-clone reader did not use the held parent descriptor",
            )


def main() -> int:
    check_checker_child_environment()
    check_public_surface_file_boundary()
    with patch.dict(os.environ, HOSTILE_ENVIRONMENT):
        route_memory_checks = check_route_memory_cold_clone()
    packets = diagnostic.collect_agent_packets()
    summary = packets["summary"]
    quick_summary = diagnostic.quick_summary()
    human_surfaces = {
        path: diagnostic.read(path) for path in diagnostic.HUMAN_SURFACES
    }
    routed_human_surfaces = {
        path: diagnostic.read(path)
        for path in diagnostic.FIRST_CONTACT_ROUTED_SURFACES
    }
    paper_library = diagnostic.read(diagnostic.PAPER_LIBRARY_SURFACE)
    # The generated shelf may be one exporter turn behind while this focused
    # consumer test is being landed. Build a minimal compliant fixture from
    # the live Palomar ranking so the positive contract remains executable,
    # while the real shelf is still checked for stale/reordered content.
    showcase = json.loads(diagnostic.read("docs/PALOMAR_RESULT_SHOWCASE.json"))
    ranked_rows = list(reversed(showcase["candidate_ranking"]))
    ranked_fixture = "\n\n".join(
        "\n".join(
            (
                f"#### {row['rank']}. fixture — `{row['family_id']}`",
                f"- **Checked interface:** `{row['declaration']}`",
                "- **Source declaration:** fixture source",
                "- **Hard mechanism:** fixture friction",
                "- **Evidence:** fixture evidence",
                "- **Boundary:** fixture boundary",
            )
        )
        for row in sorted(ranked_rows, key=lambda row: row["rank"])
    )
    compliant_paper_library = (
        "## Mathematical signal first\n\n"
        "This reader order projects the canonical Palomar `candidate_ranking`; "
        "it is not a proof, novelty, review, or closure claim.\n\n"
        "### Ranked frontier\n\n"
        + ranked_fixture
        + "\n\n### Represented natural friction\n\n- fixture friction\n\n"
        "### Explicitly subordinate, rejected, and long tail\n\n"
        "- fixture long tail\n\n"
        "## Problem portfolio (complete 15-paper inventory)\n"
    )
    diagnostic.validate_human_first_contact(quick_summary, human_surfaces)
    diagnostic.validate_human_first_contact(summary, human_surfaces)
    checks = 4

    clone_command = (
        "git clone --filter=blob:none "
        "https://github.com/wcook04/plectis-erdos.git"
    )
    require(
        clone_command in routed_human_surfaces["docs/REPRODUCIBILITY.md"],
        "clone-command mutation fixture lost its routed-source anchor",
    )
    mutated_shallow_clone_routes = routed_human_surfaces.copy()
    mutated_shallow_clone_routes["docs/REPRODUCIBILITY.md"] = (
        mutated_shallow_clone_routes["docs/REPRODUCIBILITY.md"].replace(
            clone_command,
            clone_command.replace("git clone ", "git clone --depth=1 "),
            1,
        )
    )
    assert_human_rejected(
        summary,
        human_surfaces,
        "shallow clone substituted for the complete-history route",
        routed_surfaces=mutated_shallow_clone_routes,
    )
    checks += 1

    mutated_unfiltered_clone_routes = routed_human_surfaces.copy()
    mutated_unfiltered_clone_routes["docs/REPRODUCIBILITY.md"] = (
        mutated_unfiltered_clone_routes["docs/REPRODUCIBILITY.md"].replace(
            clone_command,
            clone_command.replace("--filter=blob:none ", ""),
            1,
        )
    )
    assert_human_rejected(
        summary,
        human_surfaces,
        "blob filter removed from the complete-history route",
        routed_surfaces=mutated_unfiltered_clone_routes,
    )
    checks += 1

    try:
        diagnostic.validate_paper_library_first_contact(paper_library)
    except AssertionError:
        checks += 1
    else:
        # A concurrently refreshed exporter may already have repaired the
        # committed shelf; the positive contract below still exercises it.
        pass
    diagnostic.validate_paper_library_first_contact(
        compliant_paper_library, ranking=ranked_rows
    )
    census = diagnostic.semantic_census()
    census_surfaces = {
        path: diagnostic.read(path) for path in diagnostic.CENSUS_SURFACES
    }
    diagnostic.validate_public_semantic_census(census, census_surfaces)
    gateway_paper = diagnostic.read(diagnostic.GATEWAY_PAPER)
    diagnostic.validate_gateway_opening(gateway_paper)
    agents = diagnostic.read("AGENTS.md")
    claude = diagnostic.read("CLAUDE.md")
    diagnostic.validate_cross_agent_entry(agents, claude)
    incremental_surfaces = {
        path: diagnostic.read(path)
        for path in diagnostic.INCREMENTAL_BUILD_SURFACES
    }
    diagnostic.validate_incremental_build_contract(incremental_surfaces)
    diagnostic.validate_agent_packets(packets)

    mutated_paper_library = compliant_paper_library.replace(
        "## Mathematical signal first", "## Problem portfolio", 1
    )
    try:
        diagnostic.validate_paper_library_first_contact(mutated_paper_library)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("paper-library signal heading deletion escaped")

    mutated_paper_library = compliant_paper_library.replace(
        "## Mathematical signal first",
        "## Problem portfolio (complete 15-paper inventory)\n\n## Mathematical signal first",
        1,
    )
    try:
        diagnostic.validate_paper_library_first_contact(mutated_paper_library)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("paper-library inventory reordering escaped")

    first_family = showcase["candidate_ranking"][0]["family_id"]
    mutated_paper_library = compliant_paper_library.replace(f"`{first_family}`", "`invented_family`", 1)
    try:
        diagnostic.validate_paper_library_first_contact(mutated_paper_library)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("paper-library invented ranked family escaped")

    mutated_paper_library = compliant_paper_library.replace(
        "**Source declaration:**", "**Unbound source:**", 1
    )
    try:
        diagnostic.validate_paper_library_first_contact(
            mutated_paper_library, ranking=ranked_rows
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("paper-library exact-source deletion escaped")

    mutated_paper_library = compliant_paper_library.replace(
        "**Hard mechanism:**", "**Mechanism:**", 1
    )
    try:
        diagnostic.validate_paper_library_first_contact(
            mutated_paper_library, ranking=ranked_rows
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("paper-library natural-friction deletion escaped")

    mutated_paper_library = compliant_paper_library.replace(
        "**Evidence:**", "**Evidence note:**", 1
    )
    try:
        diagnostic.validate_paper_library_first_contact(
            mutated_paper_library, ranking=ranked_rows
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("paper-library evidence-ceiling deletion escaped")

    mutated_paper_library = compliant_paper_library.replace(
        "**Boundary:**", "**Conclusion:**", 1
    )
    try:
        diagnostic.validate_paper_library_first_contact(
            mutated_paper_library, ranking=ranked_rows
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("paper-library boundary deletion escaped")

    duplicate_rank_rows = copy.deepcopy(ranked_rows)
    duplicate_rank_rows[1]["rank"] = duplicate_rank_rows[0]["rank"]
    try:
        diagnostic.validate_paper_library_first_contact(
            compliant_paper_library, ranking=duplicate_rank_rows
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("duplicate Palomar rank escaped")

    mutated = copy.deepcopy(human_surfaces)
    mutated["README.md"] = (
        "## Corpus at a glance\n\nRaw inventory fixture.\n\n" + mutated["README.md"]
    )
    assert_human_rejected(
        summary, mutated, "raw inventory before all-problem discovery"
    )
    checks += 1

    for task_id, requirements in diagnostic.human_tasks(summary).items():
        for alternatives in requirements:
            mutated = copy.deepcopy(human_surfaces)
            mutated_routes = copy.deepcopy(routed_human_surfaces)
            changed = False
            for token in alternatives:
                for path in (*diagnostic.HUMAN_SURFACES, *diagnostic.FIRST_CONTACT_ROUTED_SURFACES):
                    owner = mutated if path in mutated else mutated_routes
                    original = owner[path]
                    normalized_original = diagnostic.normalized(original)
                    normalized_token = diagnostic.normalized(token)
                    if normalized_token.casefold() in normalized_original.casefold():
                        owner[path] = remove_semantic_anchor(
                            normalized_original, normalized_token
                        )
                        changed = True
            require(
                changed,
                f"human-task mutation fixture lost its source anchor: {task_id}: {alternatives}",
            )
            assert_human_rejected(
                summary,
                mutated,
                f"{task_id}: {alternatives}",
                routed_surfaces=mutated_routes,
            )
            checks += 1

    mutated = copy.deepcopy(human_surfaces)
    # Rename a heading the section contract actually pins. "What remains open"
    # is no longer one of them: the open boundary now sits in the line that
    # names each problem's paper, so renaming that heading mutated nothing and
    # the fixture stopped testing the contract it is named for.
    mutated["README.md"] = mutated["README.md"].replace(
        "## What the checks establish", "## Deferred questions"
    )
    assert_human_rejected(summary, mutated, "first-contact section contract")
    checks += 1

    mutated_incremental = copy.deepcopy(incremental_surfaces)
    mutated_incremental[".github/workflows/lean.yml"] = mutated_incremental[
        ".github/workflows/lean.yml"
    ].replace("uses: actions/cache@", "uses: actions/cache-bypassed@", 1)
    try:
        diagnostic.validate_incremental_build_contract(mutated_incremental)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("project-cache workflow deletion escaped")

    mutated_incremental = copy.deepcopy(incremental_surfaces)
    mutated_incremental["scripts/lean_fast_build.py"] = mutated_incremental[
        "scripts/lean_fast_build.py"
    ].replace('"--changed-from"', '"--all-from-scratch"', 1)
    try:
        diagnostic.validate_incremental_build_contract(mutated_incremental)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("changed-cone planner deletion escaped")

    mutated_incremental = copy.deepcopy(incremental_surfaces)
    mutated_incremental["README.md"] = mutated_incremental["README.md"].replace(
        "python3 scripts/lean_fast_build.py --jobs 2",
        "lake build",
        1,
    )
    try:
        diagnostic.validate_incremental_build_contract(mutated_incremental)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("raw Lake command bypassed the public build wrapper")

    mutated_incremental = copy.deepcopy(incremental_surfaces)
    mutated_incremental["README.md"] = mutated_incremental["README.md"].replace(
        "ErdosProblems.Erdos249.PeriodMultipleEscape",
        "Erdos249257",
        1,
    )
    try:
        diagnostic.validate_incremental_build_contract(mutated_incremental)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("full-corpus-first README regression escaped")

    mutated_incremental = copy.deepcopy(incremental_surfaces)
    mutated_incremental["docs/REPRODUCIBILITY.md"] = mutated_incremental[
        "docs/REPRODUCIBILITY.md"
    ].replace(
        "python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness",
        "lake build",
        1,
    )
    try:
        diagnostic.validate_incremental_build_contract(mutated_incremental)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("runbook raw Lake command bypass escaped")

    mutated_incremental = copy.deepcopy(incremental_surfaces)
    mutated_incremental[".github/workflows/lean.yml"] = mutated_incremental[
        ".github/workflows/lean.yml"
    ].replace(
        "python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness",
        "python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness\n"
        "      - name: Duplicate build\n"
        "        run: lake build ErdosProblems",
        1,
    )
    try:
        diagnostic.validate_incremental_build_contract(mutated_incremental)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("duplicate raw Lake CI build escaped")

    mutated_incremental = copy.deepcopy(incremental_surfaces)
    mutated_incremental[".github/workflows/lean.yml"] = mutated_incremental[
        ".github/workflows/lean.yml"
    ].replace(
        "run: python3 scripts/check_release.py",
        "run: python3 scripts/check_release.py\n"
        "        run: python3 scripts/check_cold_clone_comprehension.py",
        1,
    )
    try:
        diagnostic.validate_incremental_build_contract(mutated_incremental)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("duplicate standalone cold-clone CI step escaped")

    mutated = copy.deepcopy(human_surfaces)
    mutated["README.md"] = (
        "This is an exceptional and impressive research-grade achievement.\n"
        + mutated["README.md"]
    )
    assert_human_rejected(summary, mutated, "self-appraisal language")
    checks += 1

    mutated_census = copy.deepcopy(census_surfaces)
    mutated_census["docs/RESULTS.md"] = mutated_census[
        "docs/RESULTS.md"
    ].replace(
        "| mechanically nonrecurring candidates |",
        "| mechanically nonrecurring candidates CORRUPTED |",
        1,
    )
    assert_census_rejected(
        census, mutated_census, "live semantic census synchronization"
    )
    checks += 1

    mutated_census = copy.deepcopy(census_surfaces)
    mutated_census["docs/TRUTH_AUDIT.md"] = mutated_census[
        "docs/TRUTH_AUDIT.md"
    ].replace(
        (
            f"The `{census['demand_equivalent_total']}/"
            f"{census['demand_lattice_counts']['substantial']}` count"
        ),
        "The `0/0` count",
        1,
    )
    assert_census_rejected(
        census, mutated_census, "demand-lattice population distinction"
    )
    checks += 1

    mutated_paper = remove_semantic_anchor(
        gateway_paper, "An unbounded certificate supply"
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway exact-open-edge deletion escaped")

    mutated_paper = gateway_paper.replace(
        r"for every infinite $A\subseteq\Npos$ (\#257)",
        r"for every infinite $A\subseteq\N$ (\#257)",
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway positive-support notation mutation escaped")

    mutated_paper = gateway_paper.replace(
        "Open; exact reductions", "Proved"
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway half-value status inflation escaped")

    mutated_paper = gateway_paper.replace(
        r"\paragraph{Reading map.}",
        r"\paragraph{Reading map.} Fake.lean module inventory",
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway source-inventory leak escaped")

    # Delete the import the contract actually requires. This mutated
    # "@AGENTS.md", which is not a substring of "@AGENTS.override.md", so once
    # CLAUDE.md imported the compact entry the replace became a no-op and the
    # harness was asserting against an unmutated file.
    try:
        diagnostic.validate_cross_agent_entry(
            agents, claude.replace("@AGENTS.override.md", "")
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("Claude shared-instruction import deletion escaped")

    for token, label in (
        ("## Eight-problem cold-start card", "agent direct fleet card"),
        (r"\sum_{n\ge1}p_n/2^n", "agent #251 mathematical statement"),
        ("`ai_workflow`", "agent standalone boundary"),
    ):
        try:
            diagnostic.validate_cross_agent_entry(
                agents.replace(token, "", 1), claude
            )
        except AssertionError:
            checks += 1
        else:
            raise AssertionError(f"{label} deletion escaped")

    mutated = copy_packet_sections(packets, "summary")
    mutated["summary"]["proof_authority"] = "unverified"
    assert_rejected(mutated, "proof authority")
    checks += 1

    mutated = copy_packet_sections(packets, "summary")
    mutated["summary"]["remaining_open_propositions"] = []
    assert_rejected(mutated, "open boundary")
    checks += 1

    mutated = copy_packet_sections(packets, "summary")
    mutated["summary"]["publication_family_count"] = 0
    assert_rejected(mutated, "contribution-family scale")
    checks += 1

    mutated = copy_packet_sections(packets, "route")
    mutated["route"]["route"]["query_steps"].remove(
        "python3 scripts/query_corpus.py --publication-architecture"
    )
    assert_rejected(mutated, "contribution-family first-read route")
    checks += 1

    mutated = copy_packet_sections(packets, "agent_native_navigation_route")
    mutated["agent_native_navigation_route"]["route"]["action_steps"] = [
        step
        for step in mutated["agent_native_navigation_route"]["route"]["action_steps"]
        if "proof_workbench.py open" not in step
    ]
    assert_rejected(mutated, "agent-native navigation workbench handoff")
    checks += 1

    mutated = copy_packet_sections(packets, "agent_native_navigation_route")
    mutated["agent_native_navigation_route"]["route"]["cold_clone_contract"][
        "navigation_requires_lean_build"
    ] = True
    assert_rejected(mutated, "agent-native zero-build navigation contract")
    checks += 1

    mutated = copy_packet_sections(packets, "agent_native_navigation_route")
    mutated["agent_native_navigation_route"]["route"]["query_steps"].remove(
        "python3 scripts/query_corpus.py --search <ordinary-language-query>"
    )
    assert_rejected(mutated, "agent-native ordinary-language first drilldown")
    checks += 1

    mutated = copy_packet_sections(packets, "agent_native_navigation_route")
    mutated["agent_native_navigation_route"]["route"]["query_steps"] = [
        step
        for step in mutated["agent_native_navigation_route"]["route"][
            "query_steps"
        ]
        if "--publication-artifact agent_native_navigation_guide" not in step
    ]
    assert_rejected(mutated, "agent-native publication handoff")
    checks += 1

    mutated = copy_packet_sections(packets, "agent_tour")
    mutated["agent_tour"]["intent_lenses"] = [
        row
        for row in mutated["agent_tour"]["intent_lenses"]
        if row["intent"] != "begin_a_checked_change"
    ]
    assert_rejected(mutated, "agent tour checked-change intent")
    checks += 1

    mutated = copy_packet_sections(packets, "agent_tour")
    del mutated["agent_tour"]["cold_reader_contracts"]["ai_lab_researcher"]
    assert_rejected(mutated, "agent tour AI-lab reader contract")
    checks += 1

    mutated = copy_packet_sections(packets, "agent_native_navigation_route")
    mutated["agent_native_navigation_route"]["route"]["action_steps"] = [
        step
        for step in mutated["agent_native_navigation_route"]["route"]["action_steps"]
        if "lean_fast_build.py" not in step
    ]
    assert_rejected(mutated, "agent-native focused incremental build handoff")
    checks += 1

    mutated = copy_packet_sections(packets, "discovery_searches")
    mutated["discovery_searches"]["what other exact mathematics is there"][
        "results"
    ].insert(0, {"kind": "declaration", "name": "shadow_result"})
    assert_rejected(mutated, "contribution-family search priority")
    checks += 1

    mutated = copy_packet_sections(packets, "discovery_searches")
    mutated["discovery_searches"][
        "what else is formally checked besides Erdos 249 and 257"
    ]["results"] = []
    assert_rejected(mutated, "ordinary corpus-breadth route discovery")
    checks += 1

    mutated = copy_packet_sections(packets, "publication_families")
    removed_family = next(iter(mutated["publication_families"]))
    mutated["publication_families"].pop(removed_family)
    assert_rejected(mutated, "contribution-family coverage")
    checks += 1

    mutated = copy_packet_sections(packets, "story_routes")
    mutated["story_routes"]["erdos257_half_story"]["route"]["query_steps"].pop()
    assert_rejected(mutated, "#257 story route")
    checks += 1

    mutated = copy_packet_sections(packets, "story_routes")
    mutated["story_routes"]["erdos249_diagonal_arithmetic"]["programme"][
        "claim_ceiling"
    ] = "This solves Erdős #249."
    assert_rejected(mutated, "programme claim ceiling")
    checks += 1

    mutated = copy_packet_sections(packets, "story_routes")
    mutated["story_routes"]["boolean_mobius_constraints"]["programme"][
        "core_claims"
    ].pop()
    assert_rejected(mutated, "programme claim-route completeness")
    checks += 1

    mutated = copy_packet_sections(packets, "story_routes")
    mutated["story_routes"]["transport_curvature_programme"][
        "release_provenance"
    ]["boundary"] = "Private work may supply proof authority."
    assert_rejected(mutated, "public-projection provenance boundary")
    checks += 1

    mutated = copy_packet_sections(packets, "discovery_searches")
    mutated["discovery_searches"]["what remains open for 257"]["results"] = []
    assert_rejected(mutated, "natural-language route discovery")
    checks += 1

    mutated = copy_packet_sections(packets, "discovery_searches")
    mutated["discovery_searches"]["what is reduced"]["results"].insert(
        0, {"kind": "declaration", "name": "shadow_reduction"}
    )
    assert_rejected(mutated, "claim-status route priority")
    checks += 1

    mutated = copy_packet_sections(packets, "discovery_searches")
    mutated["discovery_searches"]["which claims are cited only"]["results"] = []
    assert_rejected(mutated, "cited-only status route")
    checks += 1

    mutated = copy_packet_sections(packets, "discovery_searches")
    mutated["discovery_searches"]["list open claims"]["results"].insert(
        0, {"kind": "reading_route", "id": "shadow_open_route"}
    )
    assert_rejected(mutated, "open-claim status route priority")
    checks += 1

    mutated = copy_packet_sections(packets, "discovery_multi_searches")
    mutated["discovery_multi_searches"]["what is ruled out"]["results"] = []
    assert_rejected(mutated, "no-go programme route coverage")
    checks += 1

    checks += check_proof_plan_mutations(packets["proof_plans"])

    mutated = copy_packet_sections(packets, "claim_statuses")
    mutated["claim_statuses"]["conditional reduction"]["claims"][0][
        "remaining_open_proposition_ids"
    ] = []
    assert_rejected(mutated, "conditional status packet open boundary")
    checks += 1

    mutated = copy_packet_sections(packets, "claim_statuses")
    mutated["claim_statuses"]["verified finite instance"]["claims"][0].pop(
        "bounded_domain", None
    )
    assert_rejected(mutated, "finite status packet bounded domain")
    checks += 1

    mutated = copy_packet_sections(packets, "claim_statuses")
    mutated["claim_statuses"]["open"]["remaining_open_propositions"] = []
    assert_rejected(mutated, "open status packet proposition distinction")
    checks += 1

    mutated = copy_packet_sections(packets, "story_claims")
    mutated["story_claims"]["half_greedy_two_thirds_band"]["claim"]["statement"] = (
        "The actual greedy orbit for 1/2 avoids the band."
    )
    assert_rejected(mutated, "#257 band orbit boundary")
    checks += 1

    mutated = copy_packet_sections(packets, "story_claims")
    last_producer = mutated["story_claims"]["last_producer_tail_escape_reduction"]
    last_producer["argument_neighbourhood"]["incoming"] = [
        row
        for row in last_producer["argument_neighbourhood"]["incoming"]
        if row["relation"] != "eliminates_case"
    ]
    assert_rejected(mutated, "#257 eliminated-case edge")
    checks += 1

    mutated = copy_packet_sections(packets, "story_claims")
    first_harmonic = mutated["story_claims"]["first_harmonic_certificate_interface"]
    first_harmonic["argument_neighbourhood"]["outgoing"] = [
        row
        for row in first_harmonic["argument_neighbourhood"]["outgoing"]
        if row["neighbour"]["id"] != "certificate_completeness"
    ]
    assert_rejected(mutated, "#249 completeness-consumer edge")
    checks += 1

    mutated = copy_packet_sections(packets, "story_claims")
    harmonic_pivot = mutated["story_claims"]["first_harmonic_pivot_decomposition"]
    harmonic_pivot["argument_neighbourhood"]["outgoing"] = [
        row
        for row in harmonic_pivot["argument_neighbourhood"]["outgoing"]
        if row["neighbour"]["id"] != "first_harmonic_certificate_interface"
    ]
    assert_rejected(mutated, "#249 harmonic-pivot consumer edge")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_questions")
    mutated["expert_questions"]["results"][0]["status"] = "PROVED"
    assert_rejected(mutated, "expert-question OPEN boundary")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_questions")
    mutated["expert_questions"]["results"][0]["exact_ask"] = ""
    assert_rejected(mutated, "expert-question exact ask")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_questions")
    first_question_id = mutated["expert_questions"]["results"][0]["id"]
    mutated["expert_question_details"][first_question_id]["results"][0][
        "consumer_declarations"
    ] = []
    assert_rejected(mutated, "expert-question checked consumer")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_questions")
    mutated["expert_questions"]["packet_kind"] = "full_question"
    assert_rejected(mutated, "expert-question compact index")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_question_details")
    first_question_id = next(iter(mutated["expert_question_details"]))
    mutated["expert_question_details"][first_question_id]["packet_kind"] = (
        "compact_index"
    )
    assert_rejected(mutated, "expert-question full drill-down")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_questions_by_problem")
    mutated["expert_questions_by_problem"]["249"]["results"].pop()
    mutated["expert_questions_by_problem"]["249"]["count"] = 2
    assert_rejected(mutated, "expert-question 5/3/2 problem split")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_questions")
    mutated["expert_questions"]["results"][0]["classification"] = (
        "sufficient_for_counterexample"
    )
    assert_rejected(mutated, "expert-question classification partition")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_questions")
    mutated["expert_questions"]["limits"] = [
        limit
        for limit in mutated["expert_questions"]["limits"]
        if "strictly weaker expert handoff" not in limit
    ]
    assert_rejected(mutated, "universal #257 expert-handoff boundary")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoffs")
    mutated["expert_handoffs"]["domain_counts"] = {
        "mathematics": 6,
        "systems": 0,
    }
    assert_rejected(mutated, "cross-domain expert-handoff 5/1 split")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    mutated["expert_handoff_details"][diagnostic.SYSTEMS_EXPERT_QUESTION_ID][
        "results"
    ][0]["boundary"] = ""
    assert_rejected(mutated, "systems expert-handoff boundary")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoffs")
    mutated["expert_handoffs"]["packet_kind"] = "full_question"
    assert_rejected(mutated, "cross-domain compact index")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    first_handoff_id = next(iter(mutated["expert_handoff_details"]))
    mutated["expert_handoff_details"][first_handoff_id]["packet_kind"] = (
        "compact_index"
    )
    assert_rejected(mutated, "cross-domain full drill-down")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    first_handoff_id = next(iter(mutated["expert_handoff_details"]))
    mutated["expert_handoff_details"][first_handoff_id]["results"][0][
        "plausible_alternatives"
    ][0]["consequence"] = ""
    assert_rejected(mutated, "full handoff alternative consequence")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_protocol_check")
    mutated["expert_handoff_protocol_check"] = "unchecked"
    assert_rejected(mutated, "expert-handoff protocol self-check")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoffs")
    mutated["expert_handoffs"]["results"][0]["current_hypothesis"] = ""
    assert_rejected(mutated, "expert-handoff current hypothesis")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoffs")
    mutated["expert_handoffs"]["results"][0]["hypothesis_confidence"] = (
        "certain"
    )
    assert_rejected(mutated, "expert-handoff hypothesis confidence")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoffs")
    alternatives = mutated["expert_handoffs"]["results"][0][
        "plausible_alternatives"
    ]
    alternatives[1]["id"] = alternatives[0]["id"]
    assert_rejected(mutated, "expert-handoff distinct alternatives")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoffs")
    mutated["expert_handoffs"]["results"][0]["current_evidence"].pop()
    assert_rejected(mutated, "expert-handoff current evidence")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoffs")
    mutated["expert_handoffs"]["results"][0]["discriminating_evidence"].pop()
    assert_rejected(mutated, "expert-handoff discriminating evidence")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    second_channel = mutated["expert_handoff_details"][
        "XQ257-second-channel-separation"
    ]["results"][0]
    second_channel["consumer_declarations"].pop()
    assert_rejected(mutated, "#257 dual-consumer handoff")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    pivot = mutated["expert_handoff_details"][
        "XQ249-pivot-decorrelation"
    ]["results"][0]
    pivot["exact_ask"] = pivot["exact_ask"].replace("h <= L-s", "h may exceed L-s")
    assert_rejected(mutated, "#249 pivot overlap condition")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    pivot = mutated["expert_handoff_details"][
        "XQ249-pivot-decorrelation"
    ]["results"][0]
    pivot_negative = next(
        row for row in pivot["plausible_alternatives"]
        if row["id"] == "no_cofinal_joint_witness"
    )
    pivot_negative["statement"] = (
        "Infinitely many blocks fail one clause of the socket."
    )
    assert_rejected(mutated, "#249 pivot exact complement")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    adjacent = mutated["expert_handoff_details"][
        "XQ249-adjacent-phase-separation"
    ]["results"][0]
    phase_locking = next(
        row for row in adjacent["plausible_alternatives"]
        if row["id"] == "phase_locking"
    )
    phase_locking["statement"] = (
        "Infinitely many blocks contain no good adjacent pair."
    )
    assert_rejected(mutated, "#249 adjacent eventual negation")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    adjacent = mutated["expert_handoff_details"][
        "XQ249-adjacent-phase-separation"
    ]["results"][0]
    adjacent["exact_ask"] = adjacent["exact_ask"].replace(
        "16(2X+h+L+2) <= 2^L",
        "the dyadic-room inequality",
    )
    assert_rejected(mutated, "#249 adjacent explicit room inequality")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    second_channel = mutated["expert_handoff_details"][
        "XQ257-second-channel-separation"
    ]["results"][0]
    second_channel["current_evidence"].append(
        "The reduced denominator height is on the scale 2^(Theta(n^2))."
    )
    assert_rejected(mutated, "#257 unproved height law")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    second_channel = mutated["expert_handoff_details"][
        "XQ257-second-channel-separation"
    ]["results"][0]
    second_channel["current_evidence"][1] = (
        second_channel["current_evidence"][1]
        .replace("1 <= n <= 1000", "1 <= n <= 100")
        .replace("Rank 1001 onward", "Rank 101 onward")
    )
    assert_rejected(mutated, "#257 measured range contraction")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    second_channel = mutated["expert_handoff_details"][
        "XQ257-second-channel-separation"
    ]["results"][0]
    second_channel["current_evidence"][2] = (
        "The finite orbit looks symbolically constrained."
    )
    assert_rejected(mutated, "#257 short-word discriminator")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    middle = mutated["expert_handoff_details"][
        "XQ257-middle-producer-tail-escape"
    ]["results"][0]
    middle["exact_ask"] = middle["exact_ask"].replace(
        "C_s = -3 or (1 <= C_s and Theta_s < C_s)",
        "Theta_s < C_s whenever C_s != -3",
    )
    assert_rejected(mutated, "#257 middle exact disjunction")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    middle = mutated["expert_handoff_details"][
        "XQ257-middle-producer-tail-escape"
    ]["results"][0]
    middle["plausible_alternatives"][1]["id"] = "old_cell_partition"
    assert_rejected(mutated, "#257 middle alternative partition")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    systems = mutated["expert_handoff_details"][
        diagnostic.SYSTEMS_EXPERT_QUESTION_ID
    ]["results"][0]
    systems["acceptance"] = {"problem_status": "OPEN"}
    assert_rejected(mutated, "respondent packet evaluator-answer leak")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    systems = mutated["expert_handoff_details"][
        diagnostic.SYSTEMS_EXPERT_QUESTION_ID
    ]["results"][0]
    systems.pop("manual_review_rubric")
    assert_rejected(mutated, "respondent packet manual rubric")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_details")
    systems = mutated["expert_handoff_details"][
        diagnostic.SYSTEMS_EXPERT_QUESTION_ID
    ]["results"][0]
    systems["input_template"]["farey_numerical_delta"] = 0
    assert_rejected(mutated, "respondent packet scalar answer key")
    checks += 1

    mutated = copy_packet_sections(packets, "expert_handoff_review_template")
    mutated["expert_handoff_review_template"]["criteria"].pop(
        next(iter(mutated["expert_handoff_review_template"]["criteria"]))
    )
    assert_rejected(mutated, "expert-handoff review-template shape")
    checks += 1

    conditional = next(
        claim_id for claim_id, packet in packets["claims"].items()
        if packet["claim"]["status"] == "conditional reduction"
    )
    mutated = copy_packet_sections(packets, "claims")
    mutated["claims"][conditional]["claim"]["remaining_open_proposition_ids"] = []
    assert_rejected(mutated, "conditional-open link")
    checks += 1

    finite = next(
        claim_id for claim_id, packet in packets["claims"].items()
        if packet["claim"]["status"] == "verified finite instance"
    )
    mutated = copy_packet_sections(packets, "claims")
    mutated["claims"][finite]["claim"].pop("bounded_domain", None)
    assert_rejected(mutated, "finite bound")
    checks += 1

    source_key = next(iter(packets["sources"]))
    mutated = copy_packet_sections(packets, "sources")
    mutated["sources"][source_key]["source"]["source_ref"] = "wrong.lean:1"
    assert_rejected(mutated, "source coordinate")
    checks += 1

    print(
        "test_cold_clone_comprehension: bounded baseline passed; "
        f"{checks - 3} semantic mutations were rejected; "
        f"route-memory cold-clone checks={route_memory_checks}"
    )
    return 0


def cli() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof-plans-only", action="store_true")
    args = parser.parse_args()
    if args.proof_plans_only:
        proof_plans = diagnostic.collect_proof_plan_packets()
        diagnostic.validate_proof_plan_packets(proof_plans)
        rejected = check_proof_plan_mutations(proof_plans)
        print(
            "test_cold_clone_comprehension: proof-plan baseline passed; "
            f"{rejected} semantic mutations were rejected"
        )
        return 0
    return main()


if __name__ == "__main__":
    raise SystemExit(cli())
