#!/usr/bin/env python3
"""Acceptance checks for the public human-first documentation surface."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HUMAN_ENTRY = ROOT / "HUMAN_ENTRY.md"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def words(text: str) -> list[str]:
    return re.findall(r"[A-Za-z0-9][A-Za-z0-9'’+#./−≥≤]*", text)


def prose_words(text: str) -> list[str]:
    """Count reader prose without charging the separately bounded code block."""

    return words(re.sub(r"```.*?```", "", text, flags=re.DOTALL))


def local_markdown_targets(path: Path) -> list[Path]:
    """Resolve clone-local Markdown links from the document that owns them."""

    targets: list[Path] = []
    for raw in re.findall(r"\[[^]]+\]\(([^)]+)\)", path.read_text(encoding="utf-8")):
        target = raw.split("#", 1)[0]
        if not target or "://" in target or target.startswith("mailto:"):
            continue
        targets.append((path.parent / target).resolve())
    return targets


def authored_prose_blocks(text: str) -> list[str]:
    """Return ordinary prose blocks, excluding metadata and navigation syntax."""
    blocks: list[str] = []
    for raw in re.split(r"\n\s*\n", text):
        lines = [
            line.strip()
            for line in raw.splitlines()
            if line.strip() and not line.lstrip().startswith("<!--")
        ]
        if not lines or lines[0].startswith("#"):
            continue
        if any(
            line.startswith(("- ", "* ", "+ ", "> ", "|"))
            or re.match(r"\d+[.)]\s", line)
            for line in lines
        ):
            continue
        blocks.append(" ".join(lines))
    return blocks


def main() -> None:
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    human_entry = HUMAN_ENTRY.read_text(encoding="utf-8")
    results = (ROOT / "docs/RESULTS.md").read_text(encoding="utf-8")
    docs_index = (ROOT / "docs/README.md").read_text(encoding="utf-8")

    reader_surfaces = (
        ROOT / "README.md",
        HUMAN_ENTRY,
        ROOT / "docs/README.md",
        ROOT / "docs/RESULTS.md",
        ROOT / "docs/AGENT_WORKBENCH.md",
        *sorted((ROOT / "docs/papers/full-text").glob("*.md")),
    )
    for source in reader_surfaces:
        for target in local_markdown_targets(source):
            require(target.is_file(), f"{source.relative_to(ROOT)} has a dead local link: {target}")

    require(
        "../README.md#problem-papers" in results,
        "RESULTS does not route readers to the current README paper anchor",
    )

    require(
        len(prose_words(readme)) <= 1_400,
        "README prose exceeds the human front-door budget",
    )
    require(readme.count("```") <= 2, "README contains more than one command block")
    require(
        "All eight problems remain open" in readme,
        "README does not state the global open boundary near the front",
    )
    require(
        "docs/PALOMAR_RESULT_SHOWCASE.json" in readme and "docs/claims.json" in readme,
        "README must defer ranking and claim status to their canonical owners",
    )
    require(
        "archive and provenance" in readme,
        "README does not label the combined manuscript as archive/provenance",
    )
    require(
        "AGENTS.override.md" in readme and "docs/AGENT_WORKBENCH.md" in readme,
        "README must route agents to the separate workbench",
    )
    first_screen = readme.split("## Problem papers", 1)[0]
    require(
        "[A reader's way in](HUMAN_ENTRY.md)" in first_screen,
        "README does not lead human readers to the prose-first entry",
    )
    require(
        not re.search(r"(?m)^\|.+\|$", first_screen),
        "README first screen uses a routing table instead of prose",
    )
    require("```" not in first_screen and "git clone" not in first_screen,
        "README asks a cold reader to choose a checkout before showing the papers")
    require(
        "![Eight open problems:" in first_screen
        and "](.github/system-map.png)" in first_screen,
        "README opening lost the mathematical research-record banner",
    )
    for token in (
        "routes that stopped",
        "later models",
        "human judgement",
        "independent, AI-assisted prototype",
    ):
        require(token in first_screen, f"README opening lost its project-purpose boundary: {token}")
    require(
        "query_semantic.py" not in readme and "--publication-architecture" not in readme,
        "README exposes machine drilldowns that belong in agent documentation",
    )

    human_words = words(human_entry)
    prose_blocks = authored_prose_blocks(human_entry)
    prose_word_count = sum(len(words(block)) for block in prose_blocks)
    require(
        450 <= len(human_words) <= 1_200,
        "HUMAN_ENTRY must be a substantial but bounded prose introduction",
    )
    require(
        len(prose_blocks) >= 10 and prose_word_count / len(human_words) >= 0.9,
        "HUMAN_ENTRY is not predominantly authored explanatory prose",
    )
    require(
        len(words(prose_blocks[0])) >= 35,
        "HUMAN_ENTRY does not explain the project before routing the reader",
    )
    require("All eight problems remain open" in human_entry, "human entry blurs the open boundary")
    require(
        "Comparator" in human_entry and "Palomar" in human_entry,
        "human entry does not explain the two public review surfaces",
    )
    require("AGENTS.override.md" not in human_entry, "human entry leaks the agent router")
    require("python3 " not in human_entry, "human entry exposes shell commands")
    require("scripts/" not in human_entry, "human entry exposes implementation paths")
    require("```" not in human_entry, "human entry contains a code block")
    require(
        not re.search(r"(?m)^\|.+\|$", human_entry),
        "human entry contains a machine-like routing table",
    )
    require(
        not re.search(r"(?<![A-Za-z])--[a-z][a-z0-9-]*", human_entry),
        "human entry exposes command-line flags",
    )
    require(
        not re.search(r"\b(?:route|claim|problem|statement|family)_id\b", human_entry),
        "human entry exposes machine-readable identifiers",
    )
    require(
        not re.search(
            r"(?i)(?:^|[\s(])(?:[\w.-]+/)+[\w.-]+|"
            r"\b[\w-]+\.(?:json|py|lean|toml|ya?ml)\b|::",
            human_entry,
        ),
        "human entry exposes implementation coordinates instead of explaining them",
    )

    paper_slugs = (
        "erdos-68-factorial-denominator-irrationality",
        "erdos-243-reciprocal-tail-rigidity",
        "erdos-249-binary-totient-series",
        "erdos-251-prime-gap-dyadic-series",
        "erdos-257-mersenne-support-subseries",
        "erdos-269-three-prime-running-lcm",
        "erdos-1041-lemniscate-newton-flow",
        "erdos-1049-rational-base-lambert",
    )
    for slug in paper_slugs:
        require(f"{slug}.pdf" in readme, f"README omits the {slug} paper")
        require((ROOT / f"{slug}.pdf").is_file(), f"missing PDF for {slug}")
        require(
            (ROOT / f"docs/papers/full-text/{slug}.md").is_file(),
            f"missing Markdown paper for {slug}",
        )

    first_command_block = readme.find("```")
    last_short_paper = max(readme.find(f"{slug}.pdf") for slug in paper_slugs)
    require(
        first_command_block > last_short_paper,
        "README puts a command block before the complete eight-paper index",
    )

    details_at = results.find("<details>")
    guide_at = results.find("### Problem-by-problem guide")
    require(guide_at >= 0 and details_at > guide_at, "RESULTS does not lead with the human guide")
    require("</details>" in results, "RESULTS technical inventory is not closed")
    require(
        "<!-- BEGIN semantic_public_census -->" in results
        and "<!-- END semantic_public_census -->" in results,
        "RESULTS lost the generated semantic census contract",
    )
    require(
        "PALOMAR_RESULT_SHOWCASE.json" in results and "claims.json" in results,
        "RESULTS does not defer ranking and status to canonical data",
    )

    for heading in (
        "## Read",
        "## Check",
        "## Contribute",
        "## Where things live",
    ):
        require(heading in docs_index, f"documentation guide omits {heading}")
    require(
        "Generated technical navigation" in docs_index,
        "documentation guide does not classify generated orientation correctly",
    )

    print("human-first-contact: PASS")


if __name__ == "__main__":
    main()
