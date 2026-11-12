"""Prepared, UNRUN independent RS62 Comparator runner.

Adapted from run_psi_check.py. A default invocation only prints a plan and writes
nothing. Do not execute until residual has confirmed both fresh solution audits
and allocated a compiler slot. No additional user permission is required.

After that scheduling decision, use --execute --compiler-slot-allocated. The
two prerequisite audit records must independently pass the source/object/log
checks below. This runner never builds a mathematical solution module or invokes
Lake dependency resolution: only the independent challenge and import-only
solution wrapper are compiled, using the pinned compiler and explicit LEAN_PATH.
Fresh exports are passed to the pinned Comparator with both from-export flags.

The optional --inadvisably-no-sandbox flag is for the previously documented
bwrap limitation in this workspace. It disables process isolation, not statement
comparison or native kernel replay; the run record distinguishes that mode.
No definition holes or nonstandard solution axioms are allowed. These local
records are not IEANTN verification receipts. The prerequisite audit runners
record source/object hashes but no earlier log hashes: this runner validates
their current log entries and freezes those bytes as new evidence. It does not
claim that those logs have a digest from the earlier proof build.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.35.0"
DEFAULT_TOOLCHAIN_DIR = (
    ROOT.parent / ".tools/elan-home/toolchains/leanprover--lean4---v4.35.0"
)
CONFIG = ROOT / "comparator-rs62-global.json"
THEOREMS = [
    "TernaryGoldbach.RSBounds.RS62MertensFromFiniteRH.mertens_lower_of_finiteRH",
    "TernaryGoldbach.RSBounds.RS62TotientFromFiniteRH.totient_bound_of_finiteRH",
]
SOLUTION_MODULES = ["RSBounds.RS62MertensFromFiniteRH", "RSBounds.RS62TotientFromFiniteRH"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PACKAGE_ORDER = [
    "Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph",
    "LeanSearchClient", "plausible", "mathlib", "TernaryGoldbach",
]
AUDITS = [
    ("rs62-mertens-from-finite-rh", "RS62MertensFromFiniteRH", 1, THEOREMS[0]),
    ("rs62-totient-from-finite-rh", "RS62TotientFromFiniteRH", 7, THEOREMS[1]),
]
# The same builtin and primitive roots as Lake.CLI.Check.compareIt in this pin.
BUILTINS = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
    "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def label(path: Path) -> str:
    return str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)


def snapshot(paths: set[Path]) -> dict[str, str]:
    return {label(path): sha(path) for path in sorted(paths)}


def unchanged(hashes: dict[str, str], category: str) -> None:
    for name, expected in hashes.items():
        require(sha(ROOT / name) == expected, f"Changed {category}: {name}")


def mask_comments_and_strings(text: str) -> str:
    """Keep line positions while masking nested Lean comments and string contents."""
    out = list(text)
    i, depth = 0, 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i + 1] != "\n": out[i + 1] = " "
                i += 2
            else:
                if text[i] == '"': quoted = False
                if text[i] != "\n": out[i] = " "
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i); i = end
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "; depth = 1; i += 2
        elif text[i] == "'" and (character := re.match(
                r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4}|.)|[^\\'\n])'",
                text[i:])):
            # A character literal such as '"' must not open a string. Apostrophes
            # in ordinary Lean identifiers do not match this literal grammar.
            end = i + len(character.group())
            out[i:end] = " " * (end - i); i = end
        elif text[i] == '"':
            out[i] = " "; quoted = True; i += 1
        else:
            i += 1
    require(depth == 0 and not quoted, "Unterminated source comment/string")
    return "".join(out)


def imports(path: Path) -> list[str]:
    text = mask_comments_and_strings(path.read_text())
    lines = re.findall(r"^\s*(?:(?:public|private|meta)\s+)?import[ \t]+([^\n]+)", text, re.M)
    return [module for line in lines for module in line.split()]


def axiom_entries(text: str) -> dict[str, set[str]]:
    matches = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    require(len({name for name, _ in matches}) == len(matches), "Duplicate axiom audit entry")
    return {name: {a.strip() for a in group.split(",") if a.strip()} for name, group in matches}


def validate_audits() -> tuple[dict, set[Path]]:
    evidence, files = {}, set()
    for prefix, module, count, theorem in AUDITS:
        record_path = ROOT / "verification" / (prefix + "-run.json")
        require(record_path.is_file(), f"Prerequisite audit has not completed: {record_path}")
        prior = json.loads(record_path.read_text())
        require(prior.get("exit_code") == 0 and prior.get("build_exit_code") == 0
                and bool(prior.get("finished_utc")), f"Incomplete/failed prerequisite: {prefix}")
        require(prior.get("axiom_audit") == {"declarations": count, "only_standard_axioms": True},
                f"Missing standard-three audit: {prefix}")
        hashes = prior.get("source_sha256", {})
        require(bool(hashes), f"Missing prerequisite source hashes: {prefix}")
        for name in hashes:
            require(not Path(name).is_absolute() and ".." not in Path(name).parts,
                    f"Unsafe prerequisite source path: {name}")
        unchanged(hashes, "prerequisite source")
        audit_path = ROOT / "verification" / (module + "Audit.lean")
        source_path = ROOT / "RSBounds" / (module + ".lean")
        require(all(label(path) in hashes for path in [audit_path, source_path]),
                f"Prerequisite does not cover the target/audit source: {prefix}")
        expected = re.findall(r"^#print axioms\s+(\S+)", audit_path.read_text(), re.M)
        require(len(expected) == count and len(set(expected)) == count and theorem in expected,
                f"Unexpected prerequisite audit declarations: {prefix}")
        audit_commands = [line for line in audit_path.read_text().splitlines()
                          if line.startswith("#print axioms ")]
        prior_stdin = source_path.read_text() + "\n" + "\n".join(audit_commands) + "\n"
        require(prior.get("stdin_sha256") == hashlib.sha256(prior_stdin.encode()).hexdigest(),
                f"Prerequisite input does not match the current source/audit: {prefix}")
        runs = prior.get("runs", [])
        require(bool(runs) and all(run.get("exit_code") == 0 for run in runs),
                f"Incomplete prerequisite stages: {prefix}")
        logs = []
        for run in runs:
            name = run.get("log", "")
            require(bool(name) and not Path(name).is_absolute() and ".." not in Path(name).parts,
                    f"Invalid prerequisite log path: {prefix}")
            logs.append(ROOT / name)
            if "log_sha256" in run:
                require(run["log_sha256"] == sha(logs[-1]),
                        f"Changed previously hashed prerequisite log: {prefix}")
        entries = axiom_entries("\n".join(path.read_text() for path in logs))
        require(set(entries) == set(expected) and all(a <= ALLOWED for a in entries.values()),
                f"Prerequisite transitive axioms do not match the policy: {prefix}")
        obj = ROOT / ".lake/build/lib/lean/RSBounds" / (module + ".olean")
        require(prior.get("object_sha256") == sha(obj), f"Changed prerequisite object: {module}")
        files.update([record_path, audit_path, *logs, *(ROOT / name for name in hashes)])
        evidence[prefix] = {"record": label(record_path), "record_sha256": sha(record_path),
                            "object": label(obj), "object_sha256": sha(obj),
                            "current_log_sha256": snapshot(set(logs)),
                            "log_hash_provenance": "Current log bytes validated against the exact "
                                "audit declarations and frozen now; no earlier log digest is "
                                "claimed unless present in the prerequisite run entry.",
                            "axioms": {name: sorted(a) for name, a in entries.items()}}
    return evidence, files


def object_artifacts(module: str, search: list[Path]) -> set[Path]:
    relative = Path(module.replace(".", "/") + ".olean")
    for base in search:
        obj = base / relative
        if obj.is_file():
            candidates = [obj, Path(str(obj) + ".private"), Path(str(obj) + ".server"),
                          obj.with_suffix(".ir")]
            return {path for path in candidates if path.is_file()}
    raise RuntimeError(f"Missing already-built dependency object: {module}; no rebuild was attempted")


def source_inventory(search: list[Path], tc: Path) -> tuple[set[Path], set[Path], dict]:
    local_roots = [ROOT, ROOT / "vendor/rh100", ROOT / ".lake/packages/TernaryGoldbach"]
    local_prefixes = {"RSBounds", "TernaryGoldbach", "Zeta23", "ZetaLean", "RHHeight",
                      "RHHeight100", "HardyFirstZero", "HardyTenZeros"}
    external_roots = [ROOT / ".lake/packages" / p for p in PACKAGE_ORDER]
    external_roots += [tc / "src/lean", tc / "src/lean/lake"]
    sources, objects, visited, external = set(), set(), set(), set()
    mapping = {}

    def visit(module: str) -> None:
        if module in visited: return
        visited.add(module)
        relative = Path(module.replace(".", "/") + ".lean")
        is_local = module.split(".")[0] in local_prefixes
        roots = local_roots if is_local else external_roots
        path = next((root / relative for root in roots if (root / relative).is_file()), None)
        require(path is not None, f"Unresolved source module: {module}")
        sources.add(path)
        artifacts = object_artifacts(module, search)
        objects.update(artifacts)
        mapping[module] = {"source": label(path), "objects": sorted(label(p) for p in artifacts)}
        if is_local:
            for dependency in imports(path): visit(dependency)
        else:
            external.add(module)

    for module in [*SOLUTION_MODULES, "Mathlib"]: visit(module)
    return sources, objects, {"modules": mapping, "direct_external_modules": sorted(external)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true", help="Run only after both proof audits pass")
    parser.add_argument("--compiler-slot-allocated", action="store_true",
                        help="Record the internal scheduler's allocation; not a user-approval request")
    parser.add_argument("--inadvisably-no-sandbox", action="store_true",
                        help="Use only for the documented bwrap limitation; kernel checking stays on")
    parser.add_argument("--toolchain-dir", type=Path, default=DEFAULT_TOOLCHAIN_DIR)
    parser.add_argument("--timeout-seconds", type=float, default=0,
                        help="Per-command timeout; 0 means no limit")
    args = parser.parse_args()
    require(args.timeout_seconds >= 0, "Timeout must be nonnegative")
    cfg = json.loads(CONFIG.read_text())
    require(set(cfg) == {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"},
            "Unexpected configuration field; definition holes/external kernels are not enabled")
    require(cfg["challenge_module"] == "RS62GlobalChallenge"
            and cfg["solution_module"] == "RS62GlobalSolution" and cfg["theorem_names"] == THEOREMS,
            "Comparator target/module mismatch")
    require(len(cfg["permitted_axioms"]) == 3 and set(cfg["permitted_axioms"]) == ALLOWED,
            "The permitted axioms must be exactly the standard three")
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Toolchain pin changed")
    challenge = ROOT / "comparator/RS62GlobalChallenge.lean"
    solution = ROOT / "comparator/RS62GlobalSolution.lean"
    require(imports(challenge) == ["Mathlib"], "Challenge must import Mathlib only")
    require(imports(solution) == SOLUTION_MODULES, "Solution must import only the two audited modules")
    if not args.execute:
        print(json.dumps({"status": "preparation-only; Comparator not run", "writes_files": False,
              "prerequisites": [p + "-run.json" for p, _, _, _ in AUDITS],
              "required_next_step": "Residual confirms both audits and allocates one compiler slot.",
              "execute_flags": "--execute --compiler-slot-allocated", "theorem_names": THEOREMS}, indent=2))
        return 0
    require(args.compiler_slot_allocated, "Wait for an allocated compiler slot before execution")
    prior_audits, audit_files = validate_audits()
    tc = args.toolchain_dir.resolve()
    binaries = {name: tc / "bin" / name for name in ["lean", "lake", "leanexport", "leanchecker"]}
    require(all(path.is_file() for path in binaries.values()), "Pinned toolchain binaries are incomplete")
    package_roots = [ROOT / ".lake/packages" / name for name in PACKAGE_ORDER]
    search = [root / ".lake/build/lib/lean" for root in package_roots]
    search += [ROOT / ".lake/build/lib/lean", tc / "lib/lean"]
    # Lean normally ignores nonexistent optional package build directories.
    # Record and omit them; source_inventory still requires an existing object
    # for every actually used module, so no missing dependency is bypassed.
    absent_search = [path for path in search if not path.is_dir()]
    search = [path for path in search if path.is_dir()]
    env = os.environ.copy()
    env.update(LEAN_SYSROOT=str(tc), ELAN="", LEAN_NUM_THREADS="1", RAYON_NUM_THREADS="1")
    env["PATH"] = str(tc / "bin") + os.pathsep + env.get("PATH", "")
    env["LEAN_PATH"] = os.pathsep.join(str(path.resolve()) for path in search)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = {item["name"]: item for item in manifest["packages"]}
    require(set(packages) == set(PACKAGE_ORDER), "Package inventory differs from explicit LEAN_PATH")
    require(packages["mathlib"]["rev"] == "56a005855ea17e0b0958f73ec801ae140b0a1679"
            and packages["TernaryGoldbach"]["rev"] == "ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0",
            "Recorded mathematical dependency pins changed")
    for name, package in packages.items():
        root = ROOT / ".lake/packages" / name
        result = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], env=env,
                                capture_output=True, text=True, check=True)
        require(result.stdout.strip() == package["rev"], f"Package revision differs from manifest: {name}")
        require(subprocess.run(["git", "-C", str(root), "diff", "--quiet", "HEAD", "--"],
                               env=env, capture_output=True).returncode == 0,
                f"Tracked package sources are modified: {name}")
    sources, objects, inventory = source_inventory(search, tc)
    for module in SOLUTION_MODULES:
        expected_object = ROOT / ".lake/build/lib/lean" / Path(module.replace(".", "/") + ".olean")
        require(expected_object in object_artifacts(module, search),
                f"The audited solution object is shadowed in LEAN_PATH: {module}")
    sources.update(audit_files | {challenge, solution, CONFIG, Path(__file__).resolve(),
                   ROOT / "lean-toolchain", ROOT / "lakefile.lean", ROOT / "lake-manifest.json"})
    for root in package_roots:
        sources.update(path for path in [root / "lake-manifest.json", root / "lean-toolchain"]
                       if path.is_file())
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = ROOT / "verification/rs62-global-comparator" / run_id
    exports = ROOT / ".lake/rs62-global-exports" / run_id
    fresh_objects = exports / "objects"
    output.mkdir(parents=True, exist_ok=False)
    fresh_objects.mkdir(parents=True, exist_ok=False)
    env["LEAN_PATH"] = str(fresh_objects) + os.pathsep + env["LEAN_PATH"]
    export_targets = BUILTINS + THEOREMS + cfg["permitted_axioms"] + PRIMITIVES
    data = {"kind": "local-independent-rs62-global-comparator", "status": "running",
            "official_ieantn_receipt": False, "started_utc": datetime.now(timezone.utc).isoformat(),
            "sandbox_disabled": args.inadvisably_no_sandbox, "definition_holes_permitted": False,
            "permitted_axioms": sorted(ALLOWED), "prerequisite_audits": prior_audits,
            "lean_path": env["LEAN_PATH"], "toolchain": TOOLCHAIN,
            "absent_optional_search_directories": [label(path) for path in absent_search],
            "tool_binary_sha256": snapshot(set(binaries.values())),
            "package_revisions": {name: item["rev"] for name, item in packages.items()},
            "source_sha256": snapshot(sources), "imported_object_sha256": snapshot(objects),
            "hash_scope": "Full project/vendor/TernaryGoldbach source and object closure, directly "
                          "imported external sources/objects, package manifests/pins and tool binaries. "
                          "External objects beyond direct imports are not individually hashed; the complete "
                          "exported proof is hashed and independently replayed.",
            "module_inventory": inventory, "export_targets": export_targets, "runs": []}
    record = output / "run.json"

    def save() -> None:
        temporary = record.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(data, indent=2) + "\n")
        temporary.replace(record)

    def run(command: list[str], name: str, stdin: bytes | None = None,
            export: Path | None = None) -> None:
        log = output / (name + ".log")
        started = time.monotonic()
        outcome, code = "exited", None
        print("START", name, flush=True)
        with log.open("wb") as errors:
            stream = export.open("wb") if export is not None else errors
            try:
                process = subprocess.Popen(command, cwd=ROOT, env=env,
                    stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
                    stdout=stream, stderr=errors if export is not None else subprocess.STDOUT,
                    start_new_session=True)
                try:
                    process.communicate(stdin, timeout=args.timeout_seconds or None)
                    code = process.returncode
                except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
                    outcome = "timeout" if isinstance(error, subprocess.TimeoutExpired) else "interrupted"
                    os.killpg(process.pid, signal.SIGTERM)
                    try: process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL); process.wait()
            finally:
                if export is not None: stream.close()
        entry = {"command": command, "log": label(log), "log_sha256": sha(log),
                 "outcome": outcome, "exit_code": code, "seconds": time.monotonic() - started}
        if stdin is not None: entry["stdin_sha256"] = hashlib.sha256(stdin).hexdigest()
        if export is not None:
            entry.update(export=label(export), export_sha256=sha(export), export_bytes=export.stat().st_size)
        data["runs"].append(entry)
        save()
        print("END", name, code, flush=True)
        require(code == 0, f"Stage did not complete successfully: {name} ({outcome}, {code})")

    save()
    print("Local run record:", record, flush=True)
    try:
        run([str(binaries["lean"]), "--version"], "toolchain-version")
        require(re.search(r"\bversion 4\.35\.0(?:[, )]|$)",
                          (output / "toolchain-version.log").read_text()) is not None,
                "Direct compiler does not report the pinned Lean version")
        for module, source in [(cfg["challenge_module"], challenge), (cfg["solution_module"], solution)]:
            obj = fresh_objects / (module + ".olean")
            command = [str(binaries["lean"]), "-j1", "-R", str(ROOT / "comparator"), "-o", str(obj)]
            stdin = None
            if source == solution:
                stdin = (source.read_text() + "\n" + "\n".join(
                    "#print axioms " + name for name in THEOREMS) + "\n").encode()
                command.append("--stdin")
            run([*command, str(source)], module + "-build", stdin)
            artifacts = object_artifacts(module, [fresh_objects])
            data.setdefault("fresh_object_sha256", {}).update(snapshot(artifacts))
            save()
            if source == solution:
                entries = axiom_entries((output / (module + "-build.log")).read_text())
                require(set(entries) == set(THEOREMS) and all(a <= ALLOWED for a in entries.values()),
                        "Fresh solution-wrapper transitive axiom audit failed")
                data["solution_axiom_audit"] = {name: sorted(a) for name, a in entries.items()}
                save()
            run([str(binaries["leanexport"]), module, "--", *export_targets],
                module + "-export", export=exports / (module + ".export"))
        for category in ["source_sha256", "imported_object_sha256", "fresh_object_sha256", "tool_binary_sha256"]:
            unchanged(data[category], category)
        validate_audits()
        command = [str(binaries["lake"]), "comparator", "--config", str(CONFIG),
                   "--challenge-from-export", str(exports / (cfg["challenge_module"] + ".export")),
                   "--solution-from-export", str(exports / (cfg["solution_module"] + ".export"))]
        if args.inadvisably_no_sandbox: command.append("--inadvisably-no-sandbox")
        run(command, "comparator")
        require("Your solution is okay!" in (output / "comparator.log").read_text(),
                "Comparator returned without its successful comparison verdict")
        for category in ["source_sha256", "imported_object_sha256", "fresh_object_sha256", "tool_binary_sha256"]:
            unchanged(data[category], category)
        for stage in data["runs"]:
            if "export" in stage:
                require(sha(ROOT / stage["export"]) == stage["export_sha256"], "Export changed during comparison")
        validate_audits()
        data.update(status="passed", exit_code=0)
    except (Exception, KeyboardInterrupt) as error:
        data.update(status="failed-or-incomplete", exit_code=1, error=str(error) or "Interrupted")
        raise
    finally:
        data["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
    print("Independent RS62 comparison and native kernel replay passed:", record, flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print("RS62 comparator not completed:", error, file=sys.stderr)
        raise SystemExit(1)
