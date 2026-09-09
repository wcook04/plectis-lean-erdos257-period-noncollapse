#!/usr/bin/env python3
"""Test clone-local skill discovery, installation, and first-action routes."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
INSTALLER = ROOT / "scripts" / "install_agent_skills.py"
PYTHON_COMMAND_RE = re.compile(
    r"python3\s+(scripts/[A-Za-z0-9_./-]+\.py)([^`\n]*)"
)
OPTION_RE = re.compile(r"(?<![A-Za-z0-9_-])(--[a-z][a-z0-9-]*)")


def local_skill_references(source: str) -> set[str]:
    """Return exact clone-local paths advertised in Markdown links or code spans."""
    candidates = set(re.findall(r"\[[^]]+\]\(([^)]+)\)", source))
    candidates.update(re.findall(r"`([^`\n]+)`", source))
    prefixes = (
        ".github/",
        "AGENTS",
        "ARCHITECTURE",
        "CONTRIBUTING",
        "HUMAN_ENTRY",
        "METHODOLOGY",
        "README",
        "docs/",
        "scripts/",
        "skills/",
    )
    result: set[str] = set()
    for candidate in candidates:
        value = candidate.split("#", 1)[0].strip().rstrip(".,:;")
        if not value.startswith(prefixes):
            continue
        if any(marker in value for marker in ("<", ">", "*", " ", "://", "::")):
            continue
        result.add(value)
    return result


def links_to(source: str, target: str) -> bool:
    """Accept any human label while requiring the exact clone-local target."""
    return any(
        destination.split("#", 1)[0].strip() == target
        for destination in re.findall(r"\[[^]]+\]\(([^)]+)\)", source)
    )


def advertised_python_commands(source: str) -> list[tuple[str, str | None, set[str]]]:
    """Extract tracked Python CLIs and options from runnable documentation."""
    joined = re.sub(r"\\\s*\n\s*", " ", source)
    commands: list[tuple[str, str | None, set[str]]] = []
    for match in PYTHON_COMMAND_RE.finditer(joined):
        script = match.group(1)
        tail = match.group(2).strip()
        first = tail.split(maxsplit=1)[0] if tail else ""
        positional = first if re.fullmatch(r"[a-z][a-z0-9_-]*", first) else None
        commands.append((script, positional, set(OPTION_RE.findall(tail))))
    return commands


def validate_advertised_python_commands(documents: dict[str, str]) -> None:
    """Require every advertised CLI selector to exist in that command's help."""
    help_cache: dict[tuple[str, str | None], str] = {}
    for document, source in documents.items():
        for script, positional, options in advertised_python_commands(source):
            path = ROOT / script
            assert path.is_file(), (document, script)
            if not options:
                continue
            cache_key = (script, None)
            if cache_key not in help_cache:
                result = subprocess.run(
                    [sys.executable, str(path), "--help"],
                    cwd=ROOT,
                    text=True,
                    capture_output=True,
                    check=False,
                )
                assert result.returncode == 0, (document, script, result.stderr)
                help_cache[cache_key] = result.stdout + result.stderr
            help_text = help_cache[cache_key]
            if positional is not None:
                assert positional in help_text, (document, script, positional)
            missing = options - set(OPTION_RE.findall(help_text))
            if missing and positional is not None:
                cache_key = (script, positional)
                if cache_key not in help_cache:
                    result = subprocess.run(
                        [sys.executable, str(path), positional, "--help"],
                        cwd=ROOT,
                        text=True,
                        capture_output=True,
                        check=False,
                    )
                    assert result.returncode == 0, (document, script, positional, result.stderr)
                    help_cache[cache_key] = result.stdout + result.stderr
                missing -= set(OPTION_RE.findall(help_cache[cache_key]))
            assert not missing, (document, script, sorted(missing))


def run(*args: str, expected: int = 0) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        ["python3", str(INSTALLER), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != expected:
        raise AssertionError(
            f"command returned {result.returncode}, expected {expected}:\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def main() -> int:
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    skill_index = (ROOT / "skills" / "README.md").read_text(encoding="utf-8")
    entry = (ROOT / "AGENTS.override.md").read_text(encoding="utf-8")
    registry = json.loads((ROOT / "skills" / "registry.json").read_text(encoding="utf-8"))
    registered = {row["id"] for row in registry["skills"]}
    skills = tuple(row["id"] for row in registry["skills"])
    command_documents: dict[str, str] = {}

    listed = run("--list").stdout
    for name in skills:
        skill = ROOT / "skills" / name / "SKILL.md"
        assert skill.is_file(), skill
        source = skill.read_text(encoding="utf-8")
        command_documents[str(skill.relative_to(ROOT))] = source
        assert f"name: {name}" in source, name
        assert name in listed, name
        description = next(
            line.removeprefix("description: ")
            for line in source.splitlines()
            if line.startswith("description: ")
        )
        assert description in listed, name
        assert name in skill_index, name
        assert name in registered, name
        assert "/Users/" not in source and "src/ai_workflow" not in source, name
        for reference in local_skill_references(source):
            assert (ROOT / reference).exists(), (name, reference)
        for reference in set(
            re.findall(r"(?<![A-Za-z0-9_.-])(scripts/[A-Za-z0-9_./-]+\.py)", source)
        ):
            assert (ROOT / reference).is_file(), (name, reference)

    return_template = "docs/research-commons/RETURN_PACKAGE_TEMPLATE.md"
    command_documents[return_template] = (ROOT / return_template).read_text(encoding="utf-8")
    validate_advertised_python_commands(command_documents)

    assert "[`AGENTS.override.md`](AGENTS.override.md)" in readme
    assert links_to(readme, "CONTRIBUTING.md")
    assert links_to("[Contribute](CONTRIBUTING.md)", "CONTRIBUTING.md")
    assert not links_to("[Contribute](docs/CONTRIBUTING.md)", "CONTRIBUTING.md")
    assert 'agent_entry.py --entry "<task in ordinary language>"' in entry
    assert "agent_entry.py --skills" in entry

    with tempfile.TemporaryDirectory(prefix="plectis-skill-test-") as temp:
        target = Path(temp) / "skills"
        preview = run("--target-dir", str(target), "--skill", "explain-public-system")
        assert "preview only" in preview.stdout
        assert not target.exists(), "preview mutated the destination"

        run(
            "--target-dir",
            str(target),
            "--skill",
            "explain-public-system",
            "--apply",
        )
        installed = target / "explain-public-system" / "SKILL.md"
        assert installed.is_file()
        run(
            "--target-dir",
            str(target),
            "--skill",
            "explain-public-system",
            "--check",
        )

        installed.write_text(installed.read_text(encoding="utf-8") + "\nchanged\n")
        collision = run(
            "--target-dir",
            str(target),
            "--skill",
            "explain-public-system",
            "--apply",
            expected=1,
        )
        assert "already contains different material" in collision.stderr

        link_target = Path(temp) / "links"
        run(
            "--target-dir",
            str(link_target),
            "--skill",
            "mine-open-problem",
            "--mode",
            "symlink",
            "--apply",
        )
        link = link_target / "mine-open-problem"
        assert link.is_symlink()
        run(
            "--target-dir",
            str(link_target),
            "--skill",
            "mine-open-problem",
            "--mode",
            "symlink",
            "--check",
        )

    print(
        "clone skills: discovery, live CLI grammar, preview, copy, symlink, "
        "collision, and routes PASS"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
