#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep public navigation from treating unpublished work as corpus authority."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

import validation_singleflight as singleflight
from check_release import readme_open_boundary_present


ROOT = Path(__file__).resolve().parent.parent
QUERY = ROOT / "scripts" / "query_corpus.py"
PUBLIC_PROBLEM_IDS = (68, 243, 249, 251, 257, 269, 1041, 1049)
UNSUPPORTED_RESULT_CLAIM_PHRASES = (
    "proves irrationality",
    "establishes irrationality",
    "proving the #",
    "proves the #",
    "proves #",
    "solves erdos",
    "settles erdos",
    "proves the problem",
    "settles #",
    "solves #",
    "proves universal erdos",
    "proves universal erdős",
    "novel result",
    "novel contribution",
    "first proof",
    "first to prove",
    "new theorem",
)


def safe_read_path(root: Path, relative: str) -> Path:
    """Resolve a public-boundary input only through regular in-tree files."""
    root = Path(os.path.abspath(root))
    path = root / relative
    current = Path(os.path.abspath(path))
    while True:
        if current.is_symlink():
            raise AssertionError(
                f"public-boundary path must not traverse symbolic links: {relative}"
            )
        if current == root:
            break
        if current.parent == current:
            raise AssertionError(f"public-boundary path escaped checkout: {relative}")
        current = current.parent
    require(path.is_file(), f"public-boundary path must be a regular file: {relative}")
    return path


def read(rel: str) -> str:
    return safe_read_path(ROOT, rel).read_text(encoding="utf-8")


def require(condition: bool, message: str) -> None:
    """Keep contract failures active when the test runs with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def summary_packet() -> dict[str, object]:
    completed = subprocess.run(
        [sys.executable, str(QUERY)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )
    return json.loads(completed.stdout)


def check_summary_packet_environment() -> None:
    """Prove the public query subprocess ignores ambient runner state."""
    hostile_environment = {
        "GIT_DIR": str(ROOT / "not-a-git-directory"),
        "GIT_WORK_TREE": "/private/wrong-work-tree",
        "GIT_INDEX_FILE": "/private/wrong-index",
        "GIT_NAMESPACE": "wrong-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    completed = subprocess.CompletedProcess(
        [], 0, stdout=json.dumps({"non_claims": []}), stderr=""
    )
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(subprocess, "run", return_value=completed) as run:
            observed = summary_packet()

    require(observed == {"non_claims": []}, "public query result was not returned")
    require(len(run.call_args_list) == 1, "public query subprocess was not exercised")
    kwargs = run.call_args.kwargs
    sanitized = kwargs["env"]
    for key in (
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "PYTHONPATH",
    ):
        require(key not in sanitized, f"ambient {key} leaked into public query")
    require(sanitized["GIT_CONFIG_GLOBAL"] == os.devnull, "global Git config was not disabled")
    require(sanitized["GIT_OPTIONAL_LOCKS"] == "0", "optional Git locks were not disabled")
    require(sanitized["GIT_NO_REPLACE_OBJECTS"] == "1", "replacement objects were not disabled")
    require(sanitized["GIT_ASKPASS"] == "/bin/false", "Git askpass was not disabled")
    require(sanitized["PYTHONNOUSERSITE"] == "1", "user Python site was not disabled")
    require(sanitized["PATH"] == os.defpath, "ambient PATH leaked into public query")
    require(sanitized["LC_ALL"] == "C.UTF-8", "canonical locale was not pinned")
    require(sanitized["LANG"] == "C.UTF-8", "canonical language was not pinned")
    require(
        kwargs["timeout"] == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "public query subprocess timeout drifted",
    )


def check_read_path_boundary() -> None:
    """Prove public-boundary inputs cannot redirect outside the checkout."""
    with tempfile.TemporaryDirectory(
        prefix="public-artifact-boundary-", dir=ROOT
    ) as temporary:
        root = Path(temporary) / "checkout"
        outside = Path(temporary) / "outside"
        root.mkdir()
        outside.mkdir()
        (outside / "README.md").write_text("private fixture\n", encoding="utf-8")
        (root / "docs").symlink_to(outside, target_is_directory=True)
        try:
            safe_read_path(root, "docs/README.md")
        except AssertionError as exc:
            require("symbolic links" in str(exc), str(exc))
        else:
            raise AssertionError("public-boundary reader followed a symlink")

        (root / "directory").mkdir()
        try:
            safe_read_path(root, "directory")
        except AssertionError as exc:
            require("regular file" in str(exc), str(exc))
        else:
            raise AssertionError("public-boundary reader accepted a directory")


def flowed(text: str) -> str:
    """Collapse every run of whitespace, so line wrapping stops being content."""
    return " ".join(text.split())


def boundary_errors(
    agents: str,
    scope: str,
    readme: str,
    claims: dict[str, object],
    methodology: dict[str, object],
    summary: dict[str, object],
) -> list[str]:
    """Return every missing public-proof boundary required at first contact."""
    errors: list[str] = []
    # Compare on collapsed whitespace. What these phrases assert is a boundary,
    # and a boundary is the same boundary whichever column its sentence wraps
    # at; matching raw text made a paragraph reflow look like a lost promise.
    flowed_agents = flowed(agents)
    flowed_scope = flowed(scope)
    flowed_readme = flowed(readme)
    for phrase in (
        "not an entrypoint into any private development system",
        "Work only from the files in this repository",
        "never infer unpublished results or private machinery",
    ):
        if flowed(phrase) not in flowed_agents:
            errors.append(f"agent entry lost public-boundary phrase: {phrase}")
    for phrase in (
        "Unreleased work, private repositories",
        "not public proof artefact",
    ):
        if flowed(phrase) not in flowed_scope:
            errors.append(f"scope lost public-boundary phrase: {phrase}")
    if not readme_open_boundary_present(readme, len(PUBLIC_PROBLEM_IDS)):
        errors.append("README lost the global open-problem boundary")

    non_claims = {row["id"] for row in claims["non_claims"]}
    required_non_claims = {
        "not_private_root_equivalence",
        "not_hidden_proof_body_authority",
        "not_provider_proof_authority",
    }
    missing_non_claims = sorted(required_non_claims - non_claims)
    if missing_non_claims:
        errors.append(f"claim registry lost public-boundary non-claims: {missing_non_claims}")

    anti_principles = {row["id"]: row["statement"] for row in methodology["anti_principles"]}
    private_work_rule = anti_principles.get(
        "anti_principle.do_not_treat_graph_model_or_private_work_as_proof", ""
    )
    if "private proof sketch is not public proof authority" not in private_work_rule:
        errors.append("methodology lost private-proof authority boundary")

    projected_non_claims = {row["id"] for row in summary["non_claims"]}
    missing_projected = sorted(required_non_claims - projected_non_claims)
    if missing_projected:
        errors.append(f"bounded query lost public-boundary non-claims: {missing_projected}")
    return errors


def prior_art_errors(prior_art: str) -> list[str]:
    """Keep bibliography navigation subordinate to exact claim evidence."""
    required = (
        "python3 scripts/query_corpus.py --route trace_prior_art",
        "python3 scripts/query_corpus.py --claim <claim_id>",
        "remaining-open links",
        "is an evidence statement, not a novelty",
        "Failure to identify a matching source is\nnot evidence of novelty",
        "Lean source checked by the pinned Lean kernel remains\nproof authority",
    )
    return [
        f"prior-art map lost claim-faithful comparison boundary: {phrase}"
        for phrase in required
        if phrase not in prior_art
    ]


def related_problem_errors(related: str) -> list[str]:
    """Reject collapse between catalogue status and local mathematical effect."""
    required = (
        "external catalogue status and the local release status are separate facts",
        "--open remaining_open.erdos_249_irrationality",
        "--open remaining_open.universal_257_all_infinite_supports",
        "--claim prime_support_irrationality",
        "--claim sigma_transcendence",
        "records an `advances_open_target` edge",
        "untouched analogy",
    )
    return [
        f"related-problem map lost typed relation boundary: {phrase}"
        for phrase in required
        if phrase not in related
    ]


def portfolio_visibility_errors(packet: dict[str, object]) -> list[str]:
    """Require broad, source-bound result visibility without freezing a shortlist."""
    errors: list[str] = []
    expected = set(PUBLIC_PROBLEM_IDS)
    expected_labels = {f"erdos_{problem}" for problem in PUBLIC_PROBLEM_IDS}
    problem_ids = packet.get("problem_ids")
    if set(problem_ids or []) != expected_labels:
        errors.append("external-verification packet must cover exactly the eight public problems")

    results = packet.get("main_results")
    if not isinstance(results, list):
        return ["external-verification packet must expose a main_results portfolio"]

    by_problem: dict[int, list[dict[str, object]]] = {problem: [] for problem in PUBLIC_PROBLEM_IDS}
    seen_ids: set[object] = set()
    for row in results:
        if not isinstance(row, dict):
            errors.append("external-verification portfolio contains a non-record result")
            continue
        problem = row.get("problem")
        if problem not in expected:
            errors.append(f"external-verification result names an unknown problem: {problem!r}")
            continue
        result_id = row.get("id")
        if not isinstance(result_id, str) or not result_id:
            errors.append(f"problem {problem} result lacks a stable id")
        elif result_id in seen_ids:
            errors.append(f"external-verification result id is duplicated: {result_id}")
        else:
            seen_ids.add(result_id)
        for field in (
            "statement",
            "boundary",
            "original_declaration",
            "original_source",
            "wrapper_declaration",
        ):
            if not isinstance(row.get(field), str) or not row[field].strip():
                errors.append(f"problem {problem} result lacks source-bound {field}")
        for field in ("review_family", "contribution_class"):
            if not isinstance(row.get(field), str) or not row[field].strip():
                errors.append(f"problem {problem} result lacks high-signal {field}")
        source = row.get("original_source", "")
        wrapper = row.get("wrapper_declaration", "")
        if isinstance(source, str) and not source.startswith(("Erdos249257/", "ErdosProblems/")):
            errors.append(f"problem {problem} result has a non-public source route")
        if isinstance(wrapper, str) and not wrapper.startswith("Erdos249257.ExternalVerification."):
            errors.append(f"problem {problem} result has an unbound verification wrapper")
        boundary = str(row.get("boundary", "")).casefold()
        if not any(token in boundary for token in ("does not", "remain", "not ", "no ", "only ")):
            errors.append(f"problem {problem} result boundary lacks an explicit claim ceiling")
        if any(token in boundary for token in ("solves erdos", "settles erdos", "proves the problem")):
            errors.append(f"problem {problem} result boundary overclaims closure")
        for field in ("statement", "boundary"):
            claim_text = str(row.get(field, "")).casefold()
            if any(phrase in claim_text for phrase in UNSUPPORTED_RESULT_CLAIM_PHRASES):
                errors.append(
                    f"problem {problem} result {result_id} overclaims endpoint or novelty "
                    f"in {field}"
                )
        by_problem[problem].append(row)

    for problem, rows in by_problem.items():
        if not rows:
            errors.append(
                f"problem {problem} portfolio lacks source-bound result visibility"
            )
        content_signatures = {
            (
                row.get("statement"),
                row.get("boundary"),
                row.get("original_declaration"),
                row.get("original_source"),
                row.get("wrapper_declaration"),
            )
            for row in rows
        }
        if len(content_signatures) != len(rows):
            errors.append(
                f"problem {problem} portfolio contains duplicate source-bound result content"
            )
        source_families = {
            (
                row.get("original_declaration"),
                row.get("original_source"),
                row.get("wrapper_declaration"),
            )
            for row in rows
        }
        if len(source_families) != len(rows):
            errors.append(
                f"problem {problem} portfolio repeats a source-bound result family"
            )
    return errors


def main() -> int:
    """Assert that every first-contact surface preserves the public membrane."""
    check_read_path_boundary()
    agents = read("AGENTS.md")
    scope = read("SCOPE.md")
    readme = read("README.md")
    claims = json.loads(read("docs/claims.json"))
    methodology = json.loads(read("docs/methodology.json"))
    prior_art = read("docs/PRIOR_ART.md")
    related = read("docs/RELATED_PROBLEMS.md")
    summary = summary_packet()
    require(
        not boundary_errors(agents, scope, readme, claims, methodology, summary),
        "live first-contact boundary contract is invalid",
    )
    open_boundary_fixtures = (
        ("All eight problems remain open.", True),
        ("All eight\nproblems remain open.", True),
        ("All 8 problems remain open.", True),
        ("All seven problems remain open.", False),
        ("Some problems remain open.", False),
        ("All 8 problems are solved.", False),
        ("This repository does not solve these problems.", True),
    )
    for fixture, expected in open_boundary_fixtures:
        require(
            readme_open_boundary_present(fixture, len(PUBLIC_PROBLEM_IDS)) is expected,
            f"README open-boundary fixture was misclassified: {fixture!r}",
        )
    require(not prior_art_errors(prior_art), "live prior-art boundary contract is invalid")
    require(
        not related_problem_errors(related),
        "live related-problem boundary contract is invalid",
    )
    verification_packet = claims["external_verification_packet"]
    require(
        not portfolio_visibility_errors(verification_packet),
        "live portfolio visibility contract is invalid",
    )

    missing_agent_rule = agents.replace(
        "never infer unpublished results or private machinery", "", 1
    )
    require(
        any(
            "agent entry lost public-boundary phrase" in error
            for error in boundary_errors(
                missing_agent_rule, scope, readme, claims, methodology, summary
            )
        ),
        "missing agent boundary rule was accepted",
    )
    missing_projection = deepcopy(summary)
    missing_projection["non_claims"] = [
        row for row in summary["non_claims"] if row["id"] != "not_hidden_proof_body_authority"
    ]
    require(
        any(
            "bounded query lost public-boundary non-claims" in error
            for error in boundary_errors(
                agents, scope, readme, claims, methodology, missing_projection
            )
        ),
        "missing projected boundary was accepted",
    )
    novelty_from_absence = prior_art.replace(
        "Failure to identify a matching source is\nnot evidence of novelty.",
        "Failure to identify a matching source establishes novelty.",
        1,
    )
    require(
        any(
            "prior-art map lost claim-faithful comparison boundary" in error
            for error in prior_art_errors(novelty_from_absence)
        ),
        "novelty-from-absence mutation was accepted",
    )
    missing_claim_route = prior_art.replace(
        "python3 scripts/query_corpus.py --claim <claim_id>", "", 1
    )
    require(
        any(
            "prior-art map lost claim-faithful comparison boundary" in error
            for error in prior_art_errors(missing_claim_route)
        ),
        "missing claim route mutation was accepted",
    )
    collapsed_relation = related.replace(
        "external catalogue status and the local release status are separate facts",
        "catalogue status closes every local target directly",
        1,
    )
    require(
        any(
            "related-problem map lost typed relation boundary" in error
            for error in related_problem_errors(collapsed_relation)
        ),
        "collapsed related-problem relation was accepted",
    )
    order_neutral_relation = related.replace(
        "The first two packets are `open`; the latter two are `cited only`.",
        "Each local target and cited neighbour retains its independently recorded status.",
        1,
    )
    require(
        not related_problem_errors(order_neutral_relation),
        "related-problem validation must not require a first-two/latter-two row order",
    )
    missing_open_handle = related.replace(
        "--open remaining_open.universal_257_all_infinite_supports", "", 1
    )
    require(
        any(
            "related-problem map lost typed relation boundary" in error
            for error in related_problem_errors(missing_open_handle)
        ),
        "missing open-target handle was accepted",
    )
    missing_problem_portfolio = deepcopy(verification_packet)
    missing_problem_portfolio["main_results"] = [
        row
        for row in verification_packet["main_results"]
        if row["problem"] != 1049
    ]
    require(
        any(
            "problem 1049 portfolio lacks source-bound result visibility" in error
            for error in portfolio_visibility_errors(missing_problem_portfolio)
        ),
        "missing public-problem visibility mutation was accepted",
    )
    single_result_portfolio = deepcopy(verification_packet)
    single_result_portfolio["main_results"] = [
        row
        for row in verification_packet["main_results"]
        if row["problem"] != 1049
        or row["id"] == "three_halves_corridor_no_go"
    ]
    require(
        not portfolio_visibility_errors(single_result_portfolio),
        "portfolio validation must not require a fixed number of results per problem",
    )
    for field in ("review_family", "contribution_class"):
        missing_signal_portfolio = deepcopy(verification_packet)
        del missing_signal_portfolio["main_results"][0][field]
        require(
            any(
                f"result lacks high-signal {field}" in error
                for error in portfolio_visibility_errors(missing_signal_portfolio)
            ),
            f"missing high-signal {field} mutation was accepted",
        )
    duplicate_portfolio = deepcopy(verification_packet)
    duplicate_portfolio["main_results"][1] = deepcopy(duplicate_portfolio["main_results"][0])
    require(
        any(
            "result id is duplicated" in error
            for error in portfolio_visibility_errors(duplicate_portfolio)
        ),
        "duplicate portfolio identity mutation was accepted",
    )
    duplicate_content_portfolio = deepcopy(verification_packet)
    first_result = duplicate_content_portfolio["main_results"][0]
    second_result_index = next(
        index
        for index, row in enumerate(duplicate_content_portfolio["main_results"])
        if index != 0 and row["problem"] == first_result["problem"]
    )
    duplicate_content_result = deepcopy(first_result)
    duplicate_content_result["id"] = f"{first_result['id']}__renamed"
    duplicate_content_portfolio["main_results"][second_result_index] = duplicate_content_result
    require(
        any(
            "duplicate source-bound result content" in error
            for error in portfolio_visibility_errors(duplicate_content_portfolio)
        ),
        "renamed duplicate result content was accepted",
    )
    overclaiming_portfolio = deepcopy(verification_packet)
    overclaiming_portfolio["main_results"][0]["boundary"] = (
        "This result solves Erdos 68 and supplies independent proof authority."
    )
    require(
        any(
            "boundary overclaims closure" in error
            for error in portfolio_visibility_errors(overclaiming_portfolio)
        ),
        "overclaiming portfolio mutation was accepted",
    )
    private_source_portfolio = deepcopy(verification_packet)
    private_source_portfolio["main_results"][0]["original_source"] = (
        "/private/development/hidden.lean"
    )
    require(
        any(
            "non-public source route" in error
            for error in portfolio_visibility_errors(private_source_portfolio)
        ),
        "private portfolio source mutation was accepted",
    )


    expanded_portfolio = deepcopy(verification_packet)
    expanded_result = deepcopy(
        next(row for row in verification_packet["main_results"] if row["problem"] == 68)
    )
    expanded_result["id"] = "factorial_independent_carry_certificate"
    expanded_result["statement"] = (
        "An independent finite factorial-successor certificate records another bounded carry mechanism."
    )
    expanded_result["boundary"] = (
        "This finite certificate remains bounded and does not supply cofinally many non-unit carries."
    )
    expanded_result["original_declaration"] = (
        "ErdosProblems.Erdos68.factorial_independent_carry_certificate"
    )
    expanded_result["original_source"] = "ErdosProblems/Erdos68/FactorialCarry.lean"
    expanded_result["wrapper_declaration"] = (
        "Erdos249257.ExternalVerification.factorial_independent_carry_certificate"
    )
    expanded_portfolio["main_results"].append(expanded_result)
    require(
        not portfolio_visibility_errors(expanded_portfolio),
        "portfolio validation must permit additional distinct source-bound result families",
    )

    repeated_family_portfolio = deepcopy(verification_packet)
    repeated_family_result = deepcopy(
        next(row for row in verification_packet["main_results"] if row["problem"] == 68)
    )
    repeated_family_result["id"] = "factorial_rephrased_duplicate_family"
    repeated_family_result["statement"] = "A rephrased statement for the same source-bound result."
    repeated_family_result["boundary"] = (
        "This remains an exact reformulation and does not settle Erdős #68."
    )
    repeated_family_portfolio["main_results"].append(repeated_family_result)
    require(
        any(
            "problem 68 portfolio repeats a source-bound result family" in error
            for error in portfolio_visibility_errors(repeated_family_portfolio)
        ),
        "rephrased duplicate source family was accepted",
    )

    legacy_selector_metadata = deepcopy(verification_packet)
    legacy_selector_metadata["headline_results"] = []
    legacy_selector_metadata["representative_result"] = None
    legacy_selector_metadata["selected_rows"] = []
    legacy_selector_metadata["main_results"] = list(
        reversed(legacy_selector_metadata["main_results"])
    )
    require(
        not portfolio_visibility_errors(legacy_selector_metadata),
        "portfolio validation must not depend on headline, representative, or selected-row metadata",
    )
    targeted_endpoint_mutations = {
        "factorial_nonunit_carry_equivalence": (
            "The factorial-denominator series is irrational, proving the #68 endpoint."
        ),
        "prime_gap_irrationality_equivalence": (
            "The prime-value series is irrational, proving the #251 endpoint."
        ),
        "erdos_support_pairwise_coprime": (
            "This proves universal Erdos #257 for every infinite support."
        ),
        "totient_kernel_finite_rank": (
            "The finite-rank identity proves irrationality of the binary totient series "
            "and settles #249."
        ),
        "bounded_negative_exclusion": (
            "The reduced-tail exclusion proves irrationality of the #243 series."
        ),
    }
    for result_id, statement in targeted_endpoint_mutations.items():
        mutated = deepcopy(verification_packet)
        target = next(row for row in mutated["main_results"] if row["id"] == result_id)
        target["statement"] = statement
        require(
            any(
                f"result {result_id} overclaims endpoint or novelty" in error
                for error in portfolio_visibility_errors(mutated)
            ),
            f"endpoint mutation for {result_id} was accepted",
        )

    newly_landed_endpoint_mutations = {
        "small_mismatch_criterion": "This proves #251 irrationality.",
        "conditional_carry_escape": "This proves #269 irrationality.",
    }
    for result_id, statement in newly_landed_endpoint_mutations.items():
        mutated = deepcopy(verification_packet)
        target = next(row for row in mutated["main_results"] if row["id"] == result_id)
        target["statement"] = statement
        require(
            any(
                f"result {result_id} overclaims endpoint or novelty" in error
                for error in portfolio_visibility_errors(mutated)
            ),
            f"newly landed endpoint mutation for {result_id} was accepted",
        )

    novel_mutation = deepcopy(verification_packet)
    novel_target = next(
        row
        for row in novel_mutation["main_results"]
        if row["id"] == "totient_kernel_finite_rank"
    )
    novel_target["statement"] = "This is a novel contribution to the #249 endpoint."
    require(
        any(
            "result totient_kernel_finite_rank overclaims endpoint or novelty" in error
            for error in portfolio_visibility_errors(novel_mutation)
        ),
        "unsupported novelty mutation was accepted",
    )

    print(
        "test_public_artifact_boundary: first-contact surfaces reject "
        "private or unpublished proof authority and novelty inference; "
        "portfolio visibility preserves all eight problems and distinct "
        "source-bound result families without shortlist proxies"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
