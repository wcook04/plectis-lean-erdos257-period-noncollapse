#!/usr/bin/env python3
"""Check reciprocal, named-destination links across the public paper family."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"

CORE = {
    "claim-faithful-publication-systems-paper.pdf": (
        "claim-faithful-publication-systems-paper.tex",
        {"systems-lifecycle", "systems-public", "systems-trust", "systems-scaling"},
    ),
    "cold-clone-to-proof-receipt.pdf": (
        "cold-clone-to-proof-receipt.tex",
        {"cold-clone-problem", "cold-clone-authority", "cold-clone-limits"},
    ),
    "open-source-mathematics-strategy.pdf": (
        "open-source-mathematics-strategy.tex",
        {
            "strategy-protocol",
            "strategy-credit",
            "strategy-security",
            "strategy-limits",
            "strategy-entry-routes",
        },
    ),
}

NOTES = (
    "erdos-68-factorial-denominator-irrationality.tex",
    "erdos-243-reciprocal-tail-rigidity.tex",
    "erdos-249-binary-totient-series.tex",
    "erdos-251-prime-gap-dyadic-series.tex",
    "erdos-257-mersenne-support-subseries.tex",
    "erdos-269-three-prime-running-lcm.tex",
    "erdos-1041-lemniscate-newton-flow.tex",
    "erdos-1049-rational-base-lambert.tex",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def source(name: str) -> str:
    return (PAPER / name).read_text(encoding="utf-8")


def links(text: str) -> set[tuple[str, str]]:
    return set(
        re.findall(
            r"\\papersectionlink\{([^}]+\.pdf)\}%?\s*\{([^}]+)\}",
            text,
        )
    )


def main() -> int:
    style = source("paper-house-style.sty")
    require("#1\\#nameddest=#2" in style, "paper link macro is not destination-based")

    target_owner: dict[tuple[str, str], str] = {}
    for pdf, (tex, expected) in CORE.items():
        text = source(tex)
        actual = set(re.findall(r"\\papersectiontarget\{([^}]+)\}", text))
        require(expected <= actual, f"{tex} omits targets {sorted(expected - actual)}")
        require("31 August 2026" in text, f"{tex} omits the dated prototype boundary")
        require("external" in text.lower(), f"{tex} omits the external-use boundary")
        for target in actual:
            key = (pdf, target)
            require(key not in target_owner, f"duplicate destination owner for {key}")
            target_owner[key] = tex

    combined = "\n".join(source(tex) for tex, _ in CORE.values())
    core_links = links(combined)
    for pdf in CORE:
        outbound = {link for link in core_links if link[0] == pdf}
        require(outbound, f"no core paper links to {pdf}")

    preamble = source("problem-note-preamble.tex")
    note_links = links(preamble)
    for pdf in CORE:
        require(any(link[0] == pdf for link in note_links), f"problem notes do not link {pdf}")
    require("Those descriptions do not change the mathematical status" in preamble,
            "problem-note links omit the authority boundary")

    for note in NOTES:
        text = source(note)
        require("\\input{problem-note-preamble}" in text, f"{note} bypasses shared paper links")
        require("\\companionpapercontext" in text,
                f"{note} does not emit shared paper links independently")

    for link in core_links | note_links:
        require(link in target_owner, f"cross-paper link has no declared destination: {link}")

    all_sources = combined + "\n" + preamble
    require("#page=" not in all_sources, "cross-paper navigation uses fragile page numbers")
    print("paper crosslinks: reciprocal core links, eight note routes, and named targets PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
