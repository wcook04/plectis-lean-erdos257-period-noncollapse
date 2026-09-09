#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for the public clone-footprint contract."""

from __future__ import annotations

import unittest
from pathlib import Path

import check_clone_footprint as footprint


ROOT = Path(__file__).resolve().parents[1]


class CloneFootprintTests(unittest.TestCase):
    def test_current_repository_stays_within_clone_budgets(self) -> None:
        report = footprint.build_report(footprint.committed_entries(ROOT))
        readme = (ROOT / "README.md").read_text(encoding="utf-8")
        manifest = footprint.LEAN_SPARSE_MANIFEST_PATH.read_text(encoding="utf-8")
        reader_manifest = footprint.READER_SPARSE_MANIFEST_PATH.read_text(
            encoding="utf-8"
        )
        quick_manifest = footprint.QUICK_LEAN_SPARSE_MANIFEST_PATH.read_text(
            encoding="utf-8"
        )
        reproducibility = footprint.REPRODUCIBILITY_PATH.read_text(encoding="utf-8")
        self.assertEqual(
            footprint.contract_errors(
                report,
                readme,
                manifest,
                reader_manifest,
                quick_manifest,
                reproducibility,
            ),
            [],
        )
        self.assertGreater(report["lean_sparse_omitted_bytes"], 200 * footprint.MIB)
        self.assertLess(
            report["quick_lean_sparse_checkout_bytes"],
            report["lean_sparse_checkout_bytes"] / 20,
        )

    def test_quick_lean_checkout_is_the_exact_focused_import_cone(self) -> None:
        patterns = footprint.QUICK_LEAN_SPARSE_PATTERNS
        source_patterns = tuple(
            pattern for pattern in patterns if pattern.endswith(".lean")
        )
        self.assertEqual(len(source_patterns), 43)
        self.assertIn(
            "/ErdosProblems/Erdos249/PeriodMultipleEscape.lean", source_patterns
        )
        self.assertNotIn(
            "/Erdos249257/DiagonalPincerPrimeCertificates/ClosureT64.lean",
            source_patterns,
        )

    def test_oversized_full_checkout_is_rejected(self) -> None:
        entries = [
            {"path": "Erdos249257/A.lean", "size_bytes": 150 * footprint.MIB},
            {"path": "docs/generated.json", "size_bytes": 271 * footprint.MIB},
        ]
        report = footprint.build_report(entries)
        errors = footprint.contract_errors(
            report, self.valid_readme(), reproducibility=self.valid_runbook()
        )
        self.assertTrue(any("full checkout" in error for error in errors))

    def test_oversized_lean_checkout_is_rejected(self) -> None:
        entries = [
            {"path": "Erdos249257/A.lean", "size_bytes": 161 * footprint.MIB},
            {"path": "docs/generated.json", "size_bytes": 200 * footprint.MIB},
        ]
        report = footprint.build_report(entries)
        errors = footprint.contract_errors(
            report, self.valid_readme(), reproducibility=self.valid_runbook()
        )
        self.assertTrue(any("Lean sparse checkout" in error for error in errors))

    def test_readme_cannot_drop_reproducibility_route(self) -> None:
        report = footprint.build_report(
            [
                {"path": "Erdos249257/A.lean", "size_bytes": 1},
                {"path": "docs/generated.json", "size_bytes": 2},
            ]
        )
        errors = footprint.contract_errors(
            report, "# README\n", reproducibility=self.valid_runbook()
        )
        self.assertTrue(any("reproducibility-runbook link" in error for error in errors))

    def test_runbook_keeps_blob_filtered_clone(self) -> None:
        entries = [
            {"path": "Erdos249257/A.lean", "size_bytes": 1},
            {"path": "docs/generated.json", "size_bytes": 2},
        ]
        runbook = self.valid_runbook().replace("--filter=blob:none ", "", 1)
        errors = footprint.contract_errors(
            footprint.build_report(entries),
            self.valid_readme(),
            reproducibility=runbook,
        )
        self.assertTrue(any("blob:none" in error for error in errors))

    def test_runbook_keeps_history_fetch(self) -> None:
        entries = [
            {"path": "Erdos249257/A.lean", "size_bytes": 1},
            {"path": "docs/generated.json", "size_bytes": 2},
        ]
        runbook = self.valid_runbook().replace(footprint.RUNBOOK_FETCH_COMMAND, "")
        errors = footprint.contract_errors(
            footprint.build_report(entries),
            self.valid_readme(),
            reproducibility=runbook,
        )
        self.assertTrue(any("fetch --tags --force" in error for error in errors))

    def test_lean_sparse_checkout_keeps_its_build_wrapper(self) -> None:
        entries = [
            {"path": "Erdos249257/A.lean", "size_bytes": 10},
            {"path": "scripts/lean_fast_build.py", "size_bytes": 20},
            {"path": "docs/generated.json", "size_bytes": 40},
        ]
        report = footprint.build_report(entries)
        self.assertEqual(report["lean_sparse_checkout_bytes"], 30)
        runbook = self.valid_runbook().replace(footprint.LEAN_BUILD_COMMAND, "")
        self.assertTrue(
            any(
                footprint.LEAN_BUILD_COMMAND in error
                for error in footprint.contract_errors(
                    report,
                    self.valid_readme(),
                    reproducibility=runbook,
                )
            )
        )

    def test_runbook_orders_lightweight_check_before_lean_build(self) -> None:
        entries = [{"path": "Erdos249257/A.lean", "size_bytes": 1}]
        runbook = self.valid_runbook().replace(
            footprint.RUNBOOK_QUICK_CHECK_COMMAND,
            "placeholder",
        ).replace(
            footprint.LEAN_BUILD_COMMAND,
            footprint.RUNBOOK_QUICK_CHECK_COMMAND,
        ).replace("placeholder", footprint.LEAN_BUILD_COMMAND)
        errors = footprint.contract_errors(
            footprint.build_report(entries),
            self.valid_readme(),
            reproducibility=runbook,
        )
        self.assertTrue(any("must order" in error for error in errors))

    def test_lean_sparse_checkout_omits_unneeded_scripts_and_root_pdfs(self) -> None:
        entries = [
            {"path": "scripts/lean_fast_build.py", "size_bytes": 10},
            {"path": "scripts/query_corpus.py", "size_bytes": 20},
            {"path": "erdos249-257-main-paper.pdf", "size_bytes": 40},
        ]
        report = footprint.build_report(entries)
        self.assertEqual(report["lean_sparse_checkout_bytes"], 10)

    def test_lean_sparse_checkout_omits_historical_certificate_input(self) -> None:
        entries = [
            {"path": "ErdosProblems/FreePosition/Proof.lean", "size_bytes": 10},
            {"path": "ErdosProblems/FreePosition/data.jsonl", "size_bytes": 20},
        ]
        report = footprint.build_report(entries)
        self.assertEqual(report["lean_sparse_checkout_bytes"], 10)

    def test_sparse_manifest_drift_is_rejected(self) -> None:
        report = footprint.build_report(
            [{"path": "Erdos249257/A.lean", "size_bytes": 1}]
        )
        errors = footprint.contract_errors(
            report,
            self.valid_readme(),
            "/README.md\n",
            reproducibility=self.valid_runbook(),
        )
        self.assertTrue(any("manifest has drifted" in error for error in errors))

    def test_reader_sparse_checkout_omits_machine_scale_corpora(self) -> None:
        entries = [
            {"path": "README.md", "size_bytes": 10},
            {"path": "paper/main.tex", "size_bytes": 20},
            {"path": "docs/claims.json", "size_bytes": 30},
            {"path": "docs/semantic_corpus.json", "size_bytes": 1000},
        ]
        report = footprint.build_report(entries)
        self.assertEqual(report["reader_sparse_checkout_bytes"], 60)

    @staticmethod
    def valid_readme() -> str:
        return "[Reproduce the release](docs/REPRODUCIBILITY.md)\n"

    @staticmethod
    def valid_runbook() -> str:
        return "\n".join(
            (
                footprint.RUNBOOK_CLONE_COMMAND,
                footprint.RUNBOOK_CD_COMMAND,
                footprint.RUNBOOK_FETCH_COMMAND,
                footprint.RUNBOOK_QUICK_CHECK_COMMAND,
                footprint.LEAN_BUILD_COMMAND,
            )
        )


if __name__ == "__main__":
    unittest.main()
