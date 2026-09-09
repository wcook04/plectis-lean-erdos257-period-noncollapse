#!/usr/bin/env python3
"""Enforce the dedicated #249 all-base totient-kernel Comparator replay."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PINS = {
    "comparator": "789279735fe44c1c05dc54bb9f46ba4d9b8c7611",
    "lean4export": "6f4e21dd70c3c11d7fbd07d39e3192792c657448",
    "landrun": "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4",
}
INPUTS = {
    "ExternalVerification249TotientKernelBasis/Challenge.lean": "a3a4e82608e3acb54f271df7b1afd3704c5ff855c995ee3b4c37db0ebed0d683",
    "Solutions/ExternalVerification249TotientKernelBasis.lean": "4d797b6c29feec7425ff4b8cebb277492ed82f025aed5c15014c9a3a31d3316b",
    "NegativeSolutions/ExternalVerification249TotientKernelBasis.lean": "e60202f6caf4bdc20e75b7f3689b524d2a68795b9a7f824313eed654ce8323a0",
    "ExternalVerification249TotientKernelBasis/comparator.json": "56b6b5ad7bcb2add1306f0d5ba809e4c104d37b393701d7c3ee8f0663fcffb2d",
    "ExternalVerification249TotientKernelBasis/comparator-negative-mismatch.json": "ca4adbdeac59ac0f08307b267d7ac7858cad9e024ee93644f8d89a57bed17948",
    "Erdos249257/AllBaseTotientKernel.lean": "83b32e134e206a012e4c4e189ff780922dc10b18fb4edf340de6c749a72488cd",
    "ErdosProblems/Erdos249/PaperCompleteR7/KernelIntegral.lean": "7e6260206db9907976f95ce347229965f585f7e3c517da8b13ad074e501c9268",
    "ErdosProblems/Erdos249/PaperCompleteR8/UnitPivotBasis.lean": "e11b92bf486db8d8d8059931bdf3a1424278071b74d4f590e4231902ee020965",
    "ErdosProblems/Erdos249/PaperCompleteR8/KernelRelationBasis.lean": "3bdc0a97c931c8ceca6e5f46e5b9d013b0fb50505bfda05f8cc512f66a4a0dbd",
}
EXPECTED_MISMATCH = (
    "Challenge and solution theorem statement do not match: "
    "'Erdos249257.ExternalVerification249TotientKernelBasis."
    "allSlopeAffineTotientFormsLinearIndependent'"
)
INFRASTRUCTURE_EXITS = {124, 125, 126, 127, -999}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def negative_is_semantic(exit_code: int, log: str) -> bool:
    return exit_code != 0 and exit_code not in INFRASTRUCTURE_EXITS and EXPECTED_MISMATCH in log


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--positive-exit", type=int, required=True)
    parser.add_argument("--negative-exit", type=int, required=True)
    parser.add_argument("--positive-log", type=Path, required=True)
    parser.add_argument("--negative-log", type=Path, required=True)
    parser.add_argument("--comparator-rev", required=True)
    parser.add_argument("--lean4export-rev", required=True)
    parser.add_argument("--landrun-rev", required=True)
    parser.add_argument("--comparator-bin", type=Path, required=True)
    parser.add_argument("--lean4export-bin", type=Path, required=True)
    parser.add_argument("--landrun-bin", type=Path, required=True)
    parser.add_argument("--sandbox-mode", required=True)
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/erdos249-totient-kernel-comparator-receipt.json")
    args = parser.parse_args()

    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    observed_inputs = {name: digest(ROOT / name) for name in INPUTS}
    input_match = observed_inputs == INPUTS
    observed_pins = {
        "comparator": args.comparator_rev,
        "lean4export": args.lean4export_rev,
        "landrun": args.landrun_rev,
    }
    binary_digests = {}
    for name, path in {
        "comparator": args.comparator_bin,
        "lean4export": args.lean4export_bin,
        "landrun": args.landrun_bin,
    }.items():
        binary_digests[name] = digest(path) if path.is_file() else None
    negative_log = args.negative_log.read_text(encoding="utf-8", errors="replace")
    checks = {
        "repository_commit_matches": head == args.expected_commit,
        "pinned_inputs_match": input_match,
        "pinned_tool_revisions_match": observed_pins == PINS,
        "tool_binaries_recorded": all(binary_digests.values()),
        "network_restricted_systemd_sandbox": args.sandbox_mode in {"user-manager", "system-manager-nonprivileged-unit"},
        "positive_comparator_accepted": args.positive_exit == 0,
        "deliberate_negative_semantically_rejected": negative_is_semantic(args.negative_exit, negative_log),
    }
    passed = all(checks.values())
    receipt = {
        "schema": "erdos249-totient-kernel-comparator-receipt/1",
        "result": "pass" if passed else "fail",
        "generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "repository_commit": head,
        "expected_repository_commit": args.expected_commit,
        "inputs": observed_inputs,
        "tool_revisions": observed_pins,
        "binary_sha256": binary_digests,
        "sandbox_mode": args.sandbox_mode,
        "positive": {"exit": args.positive_exit, "log_sha256": digest(args.positive_log)},
        "deliberate_negative": {"exit": args.negative_exit, "log_sha256": digest(args.negative_log)},
        "checks": checks,
        "boundary": "This certifies statement isolation for the three named all-base totient-kernel theorems. It does not solve Erdős #249.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(args.output)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
