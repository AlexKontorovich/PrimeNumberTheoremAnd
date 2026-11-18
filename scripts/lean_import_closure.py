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
  - unreachable `.lean` files (repo `.lean` files not in the closure)

Notes / limitations:
- This is a best-effort *deterministic* parser. It reads header tokens without elaborating
  Lean. A file outside the closure may still be used by another build target.
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


_MODULE_COMPONENT = r"(?:[^\W\d][\w']*|«[^»]+»)"
_MODULE_TOKEN_RE = re.compile(_MODULE_COMPONENT + r"(?:\." + _MODULE_COMPONENT + r")*")


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


def _header_tokens(text: str) -> Iterator[str]:
    """Lex only as much of the header as the caller consumes.

    Lean comments are whitespace, may nest, and line comments take precedence
    over block-comment delimiters on that line. Escaped identifiers are atomic.
    """
    i = 0
    while i < len(text):
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end + 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < len(text):
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("Unterminated block comment in Lean import header")
        else:
            match = _MODULE_TOKEN_RE.match(text, i)
            if match:
                yield match.group()
                i = match.end()
            else:
                yield text[i]
                i += 1


def parse_imported_modules(file_path: Path) -> List[str]:
    """Read Lean's header grammar, stopping at the first body command.

    Each import command has one module, optionally preceded by public/meta
    and followed by the import-all modifier before the module name.
    """
    tokens = iter(_header_tokens(file_path.read_text(encoding="utf-8")))
    token = next(tokens, None)
    if token == "module":
        token = next(tokens, None)
    if token == "prelude":
        token = next(tokens, None)
    imported: List[str] = []
    while token is not None:
        if token == "public":
            token = next(tokens, None)
        if token == "meta":
            token = next(tokens, None)
        if token != "import":
            break
        token = next(tokens, None)
        if token == "all":
            token = next(tokens, None)
        if token is None or not _MODULE_TOKEN_RE.fullmatch(token):
            raise ValueError(f"Missing module name in import header: {file_path}")
        imported.append(token)
        token = next(tokens, None)
    return list(dict.fromkeys(imported))


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
            # Escapes belong to Lean syntax, not filesystem component names.
            imported = re.sub(r"«([^»]+)»", r"\1", imported)
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
        description="Trace Lean `import` closure for a target module/file and report files outside that closure.",
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

    parser.add_argument(
        "--check-prefix", action="append", default=[], metavar="MODULE",
        help="Fail if a module in this namespace is outside the closure (repeatable).",
    )
    parser.add_argument(
        "--exclude-prefix", action="append", default=[], metavar="MODULE",
        help="Exclude an intentional namespace from the coverage check (repeatable).",
    )

    args = parser.parse_args(argv)

    repo_root = Path(args.repo).resolve()
    if not repo_root.exists():
        raise SystemExit(f"Repo path does not exist: {repo_root}")

    index = build_repo_index(repo_root)
    start_module, start_file = resolve_target(index, args.target)

    internal_modules, external_modules = compute_import_closure(index, start_module)

    if args.check_prefix:
        def matches(module: str, prefixes: Sequence[str]) -> bool:
            return any(module == prefix or module.startswith(prefix + ".") for prefix in prefixes)

        missing = sorted(
            module for module in index.module_to_file
            if matches(module, args.check_prefix)
            and not matches(module, args.exclude_prefix)
            and module not in internal_modules
        )
        if args.json:
            print(json.dumps({"missing": missing}, indent=2))
        elif missing:
            print("Modules outside the root import closure:", file=sys.stderr)
            for module in missing:
                print(module, file=sys.stderr)
        else:
            print("Import coverage check passed.")
        return 1 if missing else 0

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
    print(f"Internal .lean files outside this closure ({len(deletable_files)}):")
    for p in deletable_files:
        print(p)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
