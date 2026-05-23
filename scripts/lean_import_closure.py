#!/usr/bin/env python3
"""Compute the deterministic import-closure for a Lean module/file.

Given a target module name (e.g. `PrimeNumberTheoremAnd.Lcm`) or a path to a
`.lean` file, this script:

- Traces `import ...` statements (purely syntactic; no Lean elaboration).
- Computes the transitive closure of internal dependencies (modules that resolve
  to `.lean` files inside the repo).
- Prints:
  - required `.lean` files (internal modules needed for compilation)
  - external modules (imports that do not resolve to a repo file)
  - safe-to-delete `.lean` files (repo `.lean` files not in the closure)

Notes / limitations:
- This is a best-effort *deterministic* parser. It ignores comments and then
  tokenizes; it does not run Lean.
- It only follows `import` statements.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple


EXCLUDED_DIRS = {
    ".git",
    ".lake",
    ".venv",
    ".vscode",
    "build",
    "deps",  # keep deterministic + avoid vendored sources
}


_MODULE_TOKEN_RE = re.compile(
    r"^(?:[A-Za-z_][A-Za-z0-9_]*|«[^»]+»)(?:\.(?:[A-Za-z_][A-Za-z0-9_]*|«[^»]+»))*$"
)


@dataclass(frozen=True)
class RepoIndex:
    repo_root: Path
    module_to_file: Dict[str, Path]
    file_to_module: Dict[Path, str]


def _iter_lean_files(repo_root: Path) -> Iterator[Path]:
    for dirpath, dirnames, filenames in os.walk(repo_root):
        # prune excluded dirs
        dirnames[:] = [
            d
            for d in dirnames
            if d not in EXCLUDED_DIRS and not d.startswith(".")
        ]
        for name in filenames:
            if name.endswith(".lean"):
                yield Path(dirpath) / name


def build_repo_index(repo_root: Path) -> RepoIndex:
    module_to_file: Dict[str, Path] = {}
    file_to_module: Dict[Path, str] = {}

    # Make file discovery deterministic.
    lean_files = sorted(_iter_lean_files(repo_root), key=lambda p: str(p))
    for lean_path in lean_files:
        rel = lean_path.relative_to(repo_root)
        module = ".".join(rel.with_suffix("").parts)
        # If duplicates occur, keep the first one in sorted order.
        module_to_file.setdefault(module, lean_path)
        file_to_module[lean_path] = module

    module_to_file = dict(sorted(module_to_file.items(), key=lambda kv: kv[0]))
    file_to_module = dict(sorted(file_to_module.items(), key=lambda kv: str(kv[0])))
    return RepoIndex(repo_root=repo_root, module_to_file=module_to_file, file_to_module=file_to_module)


def detect_repo_config_files(repo_root: Path) -> List[str]:
    """Return repo-relative paths of common files needed to build with Lake."""

    candidates = [
        "lakefile.toml",
        "lakefile.lean",
        "lean-toolchain",
        "lake-manifest.json",
    ]
    found: List[str] = []
    for rel in candidates:
        p = repo_root / rel
        if p.exists():
            found.append(rel)
    return found


def _strip_comments(text: str) -> str:
    """Remove Lean line comments (`-- ...`) and nested block comments (`/- ... -/`).

    This is a deterministic, best-effort stripper. It does not attempt to be a
    complete Lean lexer, but it handles nested block comments.
    """

    # First remove nested block comments.
    out_chars: List[str] = []
    i = 0
    n = len(text)
    depth = 0

    while i < n:
        if depth == 0 and text.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            i += 1
            continue

        out_chars.append(text[i])
        i += 1

    no_block = "".join(out_chars)

    # Then remove line comments.
    lines = []
    for line in no_block.splitlines(True):
        idx = line.find("--")
        if idx != -1:
            lines.append(line[:idx] + ("\n" if line.endswith("\n") else ""))
        else:
            lines.append(line)
    return "".join(lines)


def _tokenize(text: str) -> List[str]:
    """Tokenize enough to recognize `import` commands.

    Strategy: after stripping comments, split on whitespace and on common
    separators. We keep `.` inside module tokens.
    """

    # Replace some separators with whitespace, but keep '.'
    cleaned = re.sub(r"[(){}\[\],;]", " ", text)
    return cleaned.split()


def parse_imported_modules(file_path: Path) -> List[str]:
    try:
        text = file_path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        text = file_path.read_text(encoding="utf-8", errors="replace")

    text = _strip_comments(text)
    tokens = _tokenize(text)

    imported: List[str] = []
    i = 0
    while i < len(tokens):
        if tokens[i] != "import":
            i += 1
            continue

        i += 1
        while i < len(tokens) and _MODULE_TOKEN_RE.match(tokens[i]):
            imported.append(tokens[i])
            i += 1

    # Deterministic order, de-dupe preserving first appearance
    seen: Set[str] = set()
    result: List[str] = []
    for m in imported:
        if m not in seen:
            seen.add(m)
            result.append(m)
    return result


def resolve_target(index: RepoIndex, target: str) -> Tuple[str, Path]:
    """Return (module_name, file_path)."""

    # Treat as path if it looks like one.
    if target.endswith(".lean") or "/" in target or target.startswith(".") or target.startswith("/"):
        p = Path(target)
        if not p.is_absolute():
            p = (index.repo_root / p).resolve()
        try:
            rel = p.relative_to(index.repo_root)
        except ValueError:
            raise SystemExit(f"Target path is outside repo: {p}")
        if p.suffix != ".lean":
            raise SystemExit(f"Target file must be a .lean file: {p}")
        if not p.exists():
            raise SystemExit(f"Target file does not exist: {p}")
        module = ".".join(rel.with_suffix("").parts)
        return module, p

    # Otherwise treat as module name.
    module = target
    if module not in index.module_to_file:
        # heuristic: allow missing leading package name by trying to find a unique suffix
        matches = [m for m in index.module_to_file.keys() if m.endswith("." + module) or m == module]
        if len(matches) == 1:
            module = matches[0]
        else:
            hint = "\n".join(matches[:20])
            extra = "" if len(matches) <= 20 else f"\n... ({len(matches)} matches)"
            raise SystemExit(
                f"Module not found in repo: {target}\n"
                f"Tried suffix matches, got {len(matches)} candidates.\n{hint}{extra}"
            )
    return module, index.module_to_file[module]


def compute_import_closure(index: RepoIndex, start_module: str) -> Tuple[Set[str], Set[str]]:
    """Return (internal_modules, external_modules)."""

    internal: Set[str] = set()
    external: Set[str] = set()
    stack: List[str] = [start_module]

    while stack:
        mod = stack.pop()
        if mod in internal:
            continue
        internal.add(mod)

        file_path = index.module_to_file.get(mod)
        if file_path is None:
            # start_module should always exist; but keep logic robust.
            external.add(mod)
            continue

        for imported in parse_imported_modules(file_path):
            if imported in index.module_to_file:
                if imported not in internal:
                    stack.append(imported)
            else:
                external.add(imported)

    return internal, external


def _rel(index: RepoIndex, path: Path) -> str:
    return str(path.relative_to(index.repo_root))


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Trace Lean `import` closure for a target module/file and compute deletable files.",
    )
    parser.add_argument(
        "target",
        help="Target Lean module name (e.g. PrimeNumberTheoremAnd.Lcm) or a path to a .lean file.",
    )
    parser.add_argument(
        "--repo",
        default=str(Path.cwd()),
        help="Path to Lean repo root (default: current directory).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output JSON (otherwise human-readable text).",
    )
    parser.add_argument(
        "--include-external",
        action="store_true",
        help="Include external modules list in text output.",
    )

    args = parser.parse_args(argv)

    repo_root = Path(args.repo).resolve()
    if not repo_root.exists():
        raise SystemExit(f"Repo path does not exist: {repo_root}")

    index = build_repo_index(repo_root)
    start_module, start_file = resolve_target(index, args.target)

    internal_modules, external_modules = compute_import_closure(index, start_module)

    build_config_files = detect_repo_config_files(repo_root)

    required_files = sorted((_rel(index, index.module_to_file[m]) for m in internal_modules))
    all_files = sorted((_rel(index, p) for p in index.file_to_module.keys()))
    required_set = set(required_files)
    deletable_files = [p for p in all_files if p not in required_set]

    payload = {
        "repo": str(repo_root),
        "target": {
            "module": start_module,
            "file": _rel(index, start_file),
        },
        "build_config_files": build_config_files,
        "required": {
            "modules": sorted(internal_modules),
            "files": required_files,
            "count": len(required_files),
        },
        "external": {
            "modules": sorted(external_modules),
            "count": len(external_modules),
        },
        "deletable": {
            "files": deletable_files,
            "count": len(deletable_files),
        },
    }

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 0

    print(f"Repo: {repo_root}")
    print(f"Target: {start_module}  ({_rel(index, start_file)})")
    if build_config_files:
        print("Build config files (not import-traced):")
        for p in build_config_files:
            print(p)
    print("")
    print(f"Required internal .lean files ({len(required_files)}):")
    for p in required_files:
        print(p)

    if args.include_external:
        print("")
        print(f"External modules (not resolved in repo) ({len(external_modules)}):")
        for m in sorted(external_modules):
            print(m)

    print("")
    print(f"Safe-to-delete internal .lean files ({len(deletable_files)}):")
    for p in deletable_files:
        print(p)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
