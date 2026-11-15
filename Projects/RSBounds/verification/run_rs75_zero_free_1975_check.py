"""Compile and audit the complete RS75 zero-free-region assembly."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

root = Path(__file__).resolve().parent.parent
output = root / "verification/rs75-zero-free-1975-run.json"
record = {
    "kind": "fresh-local-compilation-and-public-transitive-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in [
            "RSBounds/RS75ZeroFree1975.lean",
            "RSBounds/RS75DirichletPositivity.lean",
            "RSBounds/RS75RealAxisLogDerivative.lean",
            "RSBounds/RS75GoldenRatio.lean",
            "RSBounds/RS75Frequency.lean",
            "RSBounds/RS75ZeroFreeOptimization.lean",
            "RSBounds/RS75ZeroFreeScalars.lean",
            "RSBounds/RS75Parameters.lean",
            "RSBounds/RS75FiniteHandoff.lean",
            "verification/RS75ZeroFree1975Audit.lean",
            "verification/run_rs75_zero_free_1975_check.py",
            "lean-toolchain", "lake-manifest.json",
        ]
    },
    "runs": [],
}

def save():
    output.write_text(json.dumps(record, indent=2) + "\n")

save()
jobs = [
    (["lake", "env", "lean", "-j1", "-o",
      ".lake/build/lib/lean/RSBounds/RS75ZeroFree1975.olean",
      "RSBounds/RS75ZeroFree1975.lean"], "rs75-zero-free-1975-build.log"),
    (["lake", "env", "lean", "-j1", "verification/RS75ZeroFree1975Audit.lean"],
     "rs75-zero-free-1975-axioms.log"),
]
for command, name in jobs:
    path = root / "verification" / name
    started = time.monotonic()
    with path.open("w") as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record["runs"].append({
        "command": command, "log": name, "exit_code": result.returncode,
        "elapsed_seconds": time.monotonic() - started,
    })
    save()
    if result.returncode:
        record["exit_code"] = result.returncode
        save()
        raise SystemExit(result.returncode)

groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]",
    (root / "verification/rs75-zero-free-1975-axioms.log").read_text(), re.S)
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert len(groups) == 4 and all(
    {a.strip() for a in group.split(",") if a.strip()} <= allowed for group in groups
), "Public transitive axiom audit failed"
record["axiom_audit"] = {"declarations": 4, "only_standard_axioms": True}
record["object_sha256"] = hashlib.sha256((root /
    ".lake/build/lib/lean/RSBounds/RS75ZeroFree1975.olean").read_bytes()).hexdigest()
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = 0
save()
print(json.dumps(record, indent=2))
