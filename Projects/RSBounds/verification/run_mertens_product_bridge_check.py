"""Fresh source check for the actual prime-product bridge.

Usage: python3 verification/run_mertens_product_bridge_check.py
Checks all three public exports and their transitive axiom footprints.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[1]
settings = {
    "MertensProductBridge": ("mertens-product-bridge", 3),
}
requested = sys.argv[1:] or list(settings)
assert all(name in settings for name in requested)
sha = lambda data: hashlib.sha256(data).hexdigest()
for name in requested:
    stem, count = settings[name]
    source = f"RSBounds/{name}.lean"
    audit_path = f"verification/{name}Audit.lean"
    inputs = [source, audit_path, str(Path(__file__).relative_to(root))]
    if name == "MertensProductBridge":
        inputs += ["RSBounds/MertensProductCorrection.lean", "RSBounds/MertensSecondSigned.lean", "RSBounds/Totient.lean"]
    commands = [line for line in (root / audit_path).read_text().splitlines()
                if line.startswith("#print axioms ")]
    assert len(commands) == count
    declarations = [line.removeprefix("#print axioms ") for line in commands]
    stdin = (root / source).read_text() + "\n" + "\n".join(commands) + "\n"
    receipt = root / f"verification/{stem}-run.json"
    data = {
        "kind": f"fresh-{stem}-source-with-in-process-transitive-axiom-audit",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "source_sha256": {path: sha((root / path).read_bytes()) for path in inputs},
        "stdin_recipe": f"Exact source plus {count} fully qualified #print axioms commands.",
        "stdin_sha256": sha(stdin.encode()),
        "runs": [],
    }
    receipt.write_text(json.dumps(data, indent=2) + "\n")
    object_name = f".lake/build/lib/lean/RSBounds/{name}.olean"
    command = ["lean", "-j1", "-Dprofiler=true", "--stdin", "-o", object_name, source]
    log_path = root / f"verification/{stem}-build.log"
    start = time.monotonic()
    with log_path.open("wb") as out:
        result = subprocess.run(command, cwd=root, input=stdin.encode(), stdout=out,
                                stderr=subprocess.STDOUT)
    data["runs"].append({"command": command, "log": str(log_path.relative_to(root)),
                         "exit_code": result.returncode, "seconds": time.monotonic() - start})
    data["exit_code"] = result.returncode
    data["build_exit_code"] = result.returncode
    receipt.write_text(json.dumps(data, indent=2) + "\n")
    if result.returncode:
        print(log_path.read_text())
        raise SystemExit(result.returncode)
    log = log_path.read_text()
    audit = []
    raw = []
    for declaration in declarations:
        pattern = ("'" + re.escape(declaration) + "' "
                   + r"(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)")
        matches = list(re.finditer(pattern, log, re.S))
        assert len(matches) == 1, (declaration, len(matches))
        match = matches[0]
        axioms = sorted({a.strip() for a in (match.group(1) or "").split(",") if a.strip()})
        assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, (declaration, axioms)
        audit.append({"declaration": declaration, "axioms": axioms})
        raw.append(match.group())
    assert all(sha((root / path).read_bytes()) == digest
               for path, digest in data["source_sha256"].items()), "Source changed during check"
    data["axiom_audit"] = {"declarations": count, "only_standard_axioms": True,
                           "per_declaration": audit}
    data["object_sha256"] = sha((root / object_name).read_bytes())
    data["build_log_sha256"] = sha(log_path.read_bytes())
    data["finished_utc"] = datetime.now(timezone.utc).isoformat()
    receipt.write_text(json.dumps(data, indent=2) + "\n")
    (root / f"verification/{stem}-axioms.log").write_text("\n".join(raw) + "\n")
    print(f"{name}: source and {count} standard-axiom audits passed.", flush=True)
