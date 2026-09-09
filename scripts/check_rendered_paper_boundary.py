#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep implementation coordinates exact but visually subordinate in the papers.

The authored TeX deliberately retains exact Lean coordinates inside hyperlink
arguments so release tooling can validate them.  A source link must print
ordinary mathematical words, not an indistinguishable glyph or a raw Lean
identifier.  Module names, source paths, registry paths, commit hashes, and
unlinked Lean identifiers remain outside the rendered narrative.  The one
exception is the public Farey reproduction script named below: it is part of
the mathematical audit trail, not an internal proof coordinate.

Run from the repository root:

    python3 scripts/check_rendered_paper_boundary.py

The full check extracts text from both PDFs with ``pdftotext``.  The
``--source-only`` mode checks the TeX rendering contract without requiring
Poppler and is suitable for the stdlib-only release gate.
"""

from __future__ import annotations

import argparse
import html
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import unicodedata
from pathlib import Path

import validation_singleflight as singleflight

ROOT = Path(__file__).resolve().parent.parent
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
EXTERNAL_TOOL_TIMEOUT_SECONDS = 120
PAPERS = (
    (
        ROOT / "paper" / "erdos249-257-main-paper.tex",
        ROOT / "erdos249-257-main-paper.pdf",
    ),
)
ARCHITECTURE_PAPERS = (
    ROOT / "claim-faithful-publication-systems-paper.pdf",
    ROOT / "cold-clone-to-proof-receipt.pdf",
)
ALIASES = ROOT / "paper" / "module-aliases.json"
# Page bands are the reach a limiting statement must keep, not a layout record.
# The gateway's compressed abstract now spends page one on exact contribution
# and non-contribution clauses for both problems; anchors therefore follow its
# semantic statements rather than historical wording. One later limiting
# sentence remains permitted on page two, but every headline boundary below
# must still be visible before the reader leaves page one.
FIRST_MINUTE_CONTRACT = {
    "erdos249-257-main-paper.pdf": {
        (1, 1): (
            "both remain open",
            "q-basis of the full 2-kernel span",
            "rank through level e ≥ 1 is exactly 2e + 1",
            "lcm-diagonal certificates for every t ≤ 82",
            "nowhere-dense achievement set with unique coding",
            "both memberships remain open",
            "this is not an irrationality theorem",
        ),
        (1, 2): ("neither problem is settled",),
        (2, 4): (
            "tail differences and finite certificates",
            "membership of 1/2",
            "no proof covers every infinite support",
            "the band is contiguous but bounded, not an unbounded family",
        ),
    },
    "claim-faithful-publication-systems-paper.pdf": {
        (1, 3): (
            "problem-sized lean worlds",
            "the contribution is an implemented architecture that connects research state",
            "six things that are commonly collapsed",
            "more reasoning cannot buy a write lease",
            "lean verifies that a proof establishes the formal statement written in the source",
            "eight problems remain open",
        ),
        (3, 6): (
            "type a and type b",
            "313 visible progress updates and 3,491 command events",
            "compressed trace has an observation boundary",
            "authority-bearing artefact and receipt",
        ),
        (6, 9): (
            "experiments are route selectors",
            "a lean no-go theorem",
            "three oracles, not one",
            "problem-sized lean worlds and bounded theorem neighbourhoods",
            "1,024 lean modules and 153,396 declarations",
        ),
        # The three ranges below each moved one page later when the
        # comprehension-packet section was added ahead of them. Every anchor was
        # confirmed still present in the source and in the rendered PDF before
        # its pin was moved: the section carrying it did not change, its
        # position did.
        (11, 12): (
            "comparator: an exact-statement firewall",
            "review selection, and what the palomar registry is not",
            "proof generation, verification, exposition, publication and community digestion",
            "natural friction",
            "paper authoring itself participates in this loop",
        ),
        (13, 13): (
            "finite range to the unbounded statement",
            "a larger cutoff exists",
            "relationship had not been registered",
            "nine of the ten edits were rejected",
        ),
        (15, 16): (
            "semantic single-flight queue",
            # Was "host-wide mathlib resource", which no layout could satisfy:
            # TeX breaks the line at the hyphen, the extracted text reads
            # "hostwide", and normalisation cannot put the hyphen back. This
            # phrase pins the same sentence and cannot break at a hyphen.
            "mathlib resource are serialized",
            "four separate scaling limits",
            "only an accepted receipt enters",
            "no-go graph as a new mathematical object",
        ),
    },
    "cold-clone-to-proof-receipt.pdf": {
        (1, 1): (
            "from a cold clone to a proof receipt",
            "153,253 declarations",
            "navigation does not receive proof authority",
            "verdicts come from the pinned lean process",
            "not an autonomous theorem prover",
        ),
    },
}

# \rootword has the same four-argument shape as \lword and, like it, prints only
# its fourth argument; the module path sits inside the href. Leaving it out of
# this list made the gateway paper's root-navigation links read as visible
# implementation paths that no reader of the PDF can see.
LINK_MACRO_RE = re.compile(
    r"""\\(?:lword|rootword)\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}
        |\\(?:lref|lrefx)\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}
        |\\lloc\{[^{}]*\}\{[^{}]*\}""",
    re.X,
)
SOURCE_LINK_COORD_RE = re.compile(
    r"""\\(?:lref|lrefx)\{(?P<ref_file>[^{}]+)\}\{(?P<ref_line>\d+)\}\{[^{}]+\}
        |\\lword\{(?P<word_file>[^{}]+)\}\{(?P<word_line>\d+)\}\{[^{}]+\}\{[^{}]+\}
        |\\lloc\{(?P<loc_file>[^{}]+)\}\{(?P<loc_line>\d+)\}""",
    re.X,
)
HREF_RE = re.compile(r'href="([^"]+)"')
VISIBLE_HREF_RE = re.compile(r"\\href\{[^{}]*\}\{")
COMMENT_RE = re.compile(r"(?<!\\)%.*$")
HIDDEN_RE = re.compile(r"\\iffalse.*?\\fi", re.S)
NEWCOMMAND_RE = re.compile(r"^\s*\\newcommand.*$", re.M)
VISIBLE_PATH_RE = re.compile(
    r"\b[A-Za-z0-9_./-]+\.(?:lean|json|py|md)\b",
    re.I,
)
COMMIT_RE = re.compile(r"\b[0-9a-f]{40}\b", re.I)
LEAN_IDENTIFIER_RE = re.compile(r"\b[A-Za-z][A-Za-z0-9]*_[A-Za-z0-9_]{8,}\b")
PUBLIC_REPRODUCIBILITY_PATHS = (
    "scripts/check_farey_denominator_scaling.py",
)


class UnsafeRenderedInput(ValueError):
    """A rendered-boundary input escaped the checkout or is not a file."""


def safe_rendered_file(path: Path) -> Path:
    """Read only regular, non-symlink files beneath the release checkout."""
    root = Path(os.path.abspath(ROOT))
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeRenderedInput(f"symlinked rendered-boundary input: {candidate}")
        if current == root:
            break
        if current.parent == current:
            raise UnsafeRenderedInput(
                f"rendered-boundary input escaped checkout: {candidate}"
            )
        current = current.parent
    if not candidate.is_file():
        raise UnsafeRenderedInput(
            f"rendered-boundary input is not a regular file: {candidate}"
        )
    return candidate


def safe_rendered_text(path: Path) -> str:
    """Read a rendered-boundary text input through a no-follow descriptor."""
    candidate = safe_rendered_file(path)
    flags = os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeRenderedInput(
            f"rendered-boundary input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeRenderedInput(
                f"rendered-boundary input is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        try:
            return b"".join(chunks).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise UnsafeRenderedInput(
                f"rendered-boundary input is not UTF-8: {candidate}"
            ) from exc
    finally:
        os.close(descriptor)


def visible_tex(text: str) -> str:
    """Approximate the material that can contribute visible prose."""
    text = "\n".join(COMMENT_RE.sub("", line) for line in text.splitlines())
    text = HIDDEN_RE.sub("", text)
    text = LINK_MACRO_RE.sub("", text)
    # Keep the human-facing label while removing the implementation coordinate
    # carried only by the hyperlink argument.
    text = VISIBLE_HREF_RE.sub("{", text)
    return NEWCOMMAND_RE.sub("", text)


def source_errors(path: Path) -> list[str]:
    try:
        path = safe_rendered_file(path)
        text = safe_rendered_text(path)
    except UnsafeRenderedInput as error:
        return [str(error)]
    visible = visible_tex(text)
    for public_path in PUBLIC_REPRODUCIBILITY_PATHS:
        visible = visible.replace(public_path, "")
    errors: list[str] = []

    if r"\newcommand{\sourceglyph}" in text:
        errors.append("obsolete source-glyph definition is still present")
    gateway = path.name == "erdos249-257-main-paper.tex"
    for macro in ("lref", "lrefx"):
        definitions = re.findall(
            rf"\\newcommand\{{\\{macro}\}}.*$", text, flags=re.M
        )
        if gateway:
            if definitions and any(r"\leanlabel{#3}" not in row for row in definitions):
                errors.append(
                    f"\\{macro} does not print its theorem-specific declaration label"
                )
        elif definitions and any("{Lean proof}" not in row for row in definitions):
            errors.append(f"\\{macro} does not print the textual fallback 'Lean proof'")
    if gateway and r"\newcommand{\leanlabel}" not in text:
        errors.append(r"\leanlabel is missing from the gateway paper")
    lword_definitions = re.findall(r"\\newcommand\{\\lword\}.*$", text, flags=re.M)
    if lword_definitions and any("{#4}" not in row for row in lword_definitions):
        errors.append(r"\lword does not print its semantic label")
    lloc_definitions = re.findall(r"\\newcommand\{\\lloc\}.*$", text, flags=re.M)
    if lloc_definitions and any("{Lean source}" not in row for row in lloc_definitions):
        errors.append(r"\lloc does not print a distinguishable textual source link")
    if r"\modulesigil" in "\n".join(
        re.findall(
            r"\\newcommand\{\\(?:lref|lrefx|lword|lloc)\}.*$",
            text,
            flags=re.M,
        )
    ):
        errors.append("a paper link macro still prints a module sigil")
    if r"\idn{" in visible:
        errors.append("visible TeX still prints a Lean identifier")
    if r"\rref{" in visible:
        errors.append("visible TeX still prints a repository path")

    for pattern, label in (
        (VISIBLE_PATH_RE, "implementation path"),
        (COMMIT_RE, "full commit hash"),
    ):
        match = pattern.search(visible)
        if match:
            errors.append(f"visible TeX contains {label}: {match.group(0)!r}")
    return [f"{path.relative_to(ROOT)}: {error}" for error in errors]


def run_render_tool(
    executable: str, arguments: list[str]
) -> subprocess.CompletedProcess[str]:
    """Run Poppler without ambient checkout state or an unbounded hang."""
    environment = singleflight.command_environment()
    executable_directory = str(Path(executable).resolve().parent)
    environment["PATH"] = os.pathsep.join(
        (executable_directory, environment["PATH"])
    )
    return subprocess.run(
        [executable, *arguments],
        cwd=ROOT,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
        timeout=EXTERNAL_TOOL_TIMEOUT_SECONDS,
    )


def rendered_text(pdf: Path, pdftotext: str) -> str:
    pdf = safe_rendered_file(pdf)
    completed = run_render_tool(pdftotext, [str(pdf), "-"])
    if completed.returncode != 0:
        detail = completed.stderr.strip() or "pdftotext failed"
        raise RuntimeError(f"{pdf.relative_to(ROOT)}: {detail}")
    return completed.stdout


def rendered_hrefs(pdf: Path, pdftohtml: str) -> set[str]:
    """Extract the actual URI annotations emitted into the rendered PDF."""
    pdf = safe_rendered_file(pdf)
    completed = run_render_tool(
        pdftohtml, ["-q", "-xml", "-hidden", "-stdout", str(pdf)]
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or "pdftohtml failed"
        raise RuntimeError(f"{pdf.relative_to(ROOT)}: {detail}")
    return {html.unescape(value) for value in HREF_RE.findall(completed.stdout)}


def rendered_source_link_errors(
    tex: Path,
    pdf: Path,
    pdftohtml: str,
) -> list[str]:
    """Require every authored Lean coordinate to survive as the pinned PDF URI."""
    try:
        tex = safe_rendered_file(tex)
        pdf = safe_rendered_file(pdf)
        source = safe_rendered_text(tex)
    except UnsafeRenderedInput as error:
        return [str(error)]
    commit_match = re.search(
        r"\\(?:re)?newcommand\{\\commit\}\{([0-9a-f]{40})\}", source
    )
    if commit_match is None:
        return [f"{tex.relative_to(ROOT)}: pinned source commit is missing"]
    commit = commit_match.group(1)
    prefix = (
        "https://github.com/wcook04/plectis-lean-erdos249-257/blob/"
        f"{commit}/Erdos249257/"
    )
    allowed_source_prefixes = (
        prefix,
        "https://github.com/wcook04/plectis-lean-erdos249-257/blob/"
        f"{commit}/ErdosProblems/",
    )
    expected: set[str] = set()
    for match in SOURCE_LINK_COORD_RE.finditer(source):
        file_name = (
            match.group("ref_file")
            or match.group("word_file")
            or match.group("loc_file")
        )
        line = (
            match.group("ref_line")
            or match.group("word_line")
            or match.group("loc_line")
        )
        expected.add(f"{prefix}{file_name}#L{line}")
    try:
        hrefs = rendered_hrefs(pdf, pdftohtml)
    except RuntimeError as error:
        return [str(error)]
    errors: list[str] = []
    missing = sorted(expected - hrefs)
    if missing:
        errors.append(
            f"{pdf.relative_to(ROOT)}: {len(missing)} authored Lean source "
            f"target(s) missing from rendered URI annotations; first is {missing[0]!r}"
        )
    repository_blob_prefix = (
        "https://github.com/wcook04/plectis-lean-erdos249-257/blob/"
    )
    stale = sorted(
        href
        for href in hrefs
        if href.startswith(repository_blob_prefix)
        and not any(href.startswith(allowed) for allowed in allowed_source_prefixes)
    )
    if stale:
        errors.append(
            f"{pdf.relative_to(ROOT)}: {len(stale)} stale or unpinned rendered "
            f"repository blob target(s); first is {stale[0]!r}"
        )
    return errors


def rendered_pages(pdf: Path, pdftotext: str, first: int, last: int) -> str:
    pdf = safe_rendered_file(pdf)
    completed = run_render_tool(
        pdftotext, ["-f", str(first), "-l", str(last), str(pdf), "-"]
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or "pdftotext failed"
        raise RuntimeError(
            f"{pdf.relative_to(ROOT)} pages {first}-{last}: {detail}"
        )
    return completed.stdout


def semantic_text(text: str) -> str:
    # Fold font-specific extraction forms (mathematical-alphanumeric letters,
    # ligature glyphs) to their plain equivalents so the anchor contract tests
    # wording and page placement rather than the ToUnicode map of the current
    # font choice.
    text = unicodedata.normalize("NFKC", text)
    replacements = {
        "ﬁ": "fi",
        "ﬂ": "fl",
        "ﬀ": "ff",
        "ﬃ": "ffi",
        "ﬄ": "ffl",
        "−": "-",
        "–": "-",
        "—": "-",
    }
    for source, target in replacements.items():
        text = text.replace(source, target)
    return re.sub(r"\s+", " ", text).lower()


def first_minute_errors(pdf: Path, pdftotext: str) -> list[str]:
    errors: list[str] = []
    contract = FIRST_MINUTE_CONTRACT.get(pdf.name, {})
    for (first, last), anchors in contract.items():
        try:
            text = semantic_text(rendered_pages(pdf, pdftotext, first, last))
        except RuntimeError as error:
            errors.append(str(error))
            continue
        for anchor in anchors:
            if anchor not in text:
                errors.append(
                    f"{pdf.relative_to(ROOT)} pages {first}-{last}: "
                    f"missing first-minute anchor {anchor!r}"
                )
    return errors


def rendered_errors(
    pdf: Path,
    text: str,
    aliases: dict[str, object],
) -> list[str]:
    errors: list[str] = []
    compact = re.sub(r"_\s+(?=[a-z0-9])", "_", text)
    compact = re.sub(r"(?<=[a-z0-9])\s+_", "_", compact)
    compact = re.sub(r"\s+", " ", compact)
    for public_path in PUBLIC_REPRODUCIBILITY_PATHS:
        compact = compact.replace(public_path, "")

    fixed_terms = (
        "docs/claims.json",
        "scripts/check_release.py",
        "METHODOLOGY.md",
        "lake-manifest.json",
        "native_decide",
        "Erdos249257/",
    )
    for term in fixed_terms:
        if term.lower() in compact.lower():
            errors.append(f"prints internal term {term!r}")

    for match in VISIBLE_PATH_RE.finditer(compact):
        errors.append(f"prints implementation path {match.group(0)!r}")
    for match in COMMIT_RE.finditer(compact):
        errors.append(f"prints full commit hash {match.group(0)!r}")
    for match in LEAN_IDENTIFIER_RE.finditer(compact):
        errors.append(f"prints raw Lean identifier {match.group(0)!r}")
    alias_rows = aliases.get("aliases", [])
    if isinstance(alias_rows, list):
        for row in alias_rows:
            if not isinstance(row, dict):
                continue
            sigil = row.get("sigil")
            module = row.get("module")
            terms = []
            if isinstance(sigil, str) and len(sigil) >= 6:
                terms.append(sigil)
            if isinstance(module, str):
                stem = module.rsplit("/", 1)[-1].removesuffix(".lean")
                if len(stem) >= 8:
                    terms.append(stem)
            for term in terms:
                if re.search(rf"\b{re.escape(term)}\b", compact):
                    errors.append(f"prints source-module name or sigil {term!r}")

    return [f"{pdf.relative_to(ROOT)}: {error}" for error in sorted(set(errors))]


def architecture_rendered_errors(pdf: Path, text: str) -> list[str]:
    """Reject a rebuilt architecture paper that regresses to private scorekeeping."""
    compact = semantic_text(text)
    errors: list[str] = []
    banned = (
        re.compile(r"\bm(?:10|[1-9])\b"),
        re.compile(r"\b9/10\b"),
        re.compile(r"\b5,207\b"),
        re.compile(r"\bunbounded quantifier\b"),
    )
    for pattern in banned:
        if pattern.search(compact):
            errors.append(
                f"prints private or score-like shorthand {pattern.pattern!r}"
            )
    if len(re.findall(r"\bsentence\b", compact)) > 4:
        errors.append("has regressed to a sentence-centred case study")
    return [f"{pdf.relative_to(ROOT)}: {error}" for error in errors]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--source-only",
        action="store_true",
        help="check only the TeX rendering contract; do not inspect PDFs",
    )
    args = parser.parse_args()

    errors = [error for tex, _pdf in PAPERS for error in source_errors(tex)]
    if not args.source_only:
        pdftotext = shutil.which("pdftotext")
        pdftohtml = shutil.which("pdftohtml")
        if pdftotext is None:
            errors.append("pdftotext is required for the rendered-paper check")
        if pdftohtml is None:
            errors.append("pdftohtml is required for the rendered-link check")
        if pdftotext is not None and pdftohtml is not None:
            try:
                aliases = json.loads(safe_rendered_text(ALIASES))
            except UnsafeRenderedInput as error:
                errors.append(str(error))
                aliases = {}
            for tex, pdf in PAPERS:
                try:
                    safe_rendered_file(pdf)
                except UnsafeRenderedInput as error:
                    errors.append(str(error))
                    continue
                try:
                    text = rendered_text(pdf, pdftotext)
                except RuntimeError as error:
                    errors.append(str(error))
                    continue
                errors.extend(rendered_errors(pdf, text, aliases))
                errors.extend(first_minute_errors(pdf, pdftotext))
                errors.extend(rendered_source_link_errors(tex, pdf, pdftohtml))
            for pdf in ARCHITECTURE_PAPERS:
                try:
                    safe_rendered_file(pdf)
                except UnsafeRenderedInput as error:
                    errors.append(str(error))
                    continue
                try:
                    text = rendered_text(pdf, pdftotext)
                except RuntimeError as error:
                    errors.append(str(error))
                    continue
                errors.extend(architecture_rendered_errors(pdf, text))
                errors.extend(first_minute_errors(pdf, pdftotext))

    if errors:
        print(f"check_rendered_paper_boundary: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1

    mode = "source contract" if args.source_only else "source contract and rendered PDFs"
    print(f"check_rendered_paper_boundary: {mode} passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
