"""Compile and audit the RS75 real-axis RS75RealAxisGamma (one Lean process at a time)."""
from datetime import datetime, timezone
import hashlib
import json
import re
import time
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in [
            "RSBounds/RS75RealAxisGamma.lean",
            "RSBounds/IEANTNDigammaDifference.lean",
            "RSBounds/RS75RealAxisNumerics.lean",
            "verification/RS75RealAxisGammaAudit.lean",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "env", "lean", "-j1", "RSBounds/RS75RealAxisGamma.lean", "-o", ".lake/build/lib/lean/RSBounds/RS75RealAxisGamma.olean"], "rs75-real-axis-gamma-build.log"),
    (["lake", "env", "lean", "-j1", "verification/RS75RealAxisGammaAudit.lean"],
     "rs75-real-axis-gamma-axioms.log"),
]
for command, name in jobs:
    path = root / "verification" / name
    started = time.monotonic()
    with path.open("w") as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name, "exit_code": result.returncode, "elapsed_seconds": time.monotonic() - started})
    if result.returncode:
        break
if result.returncode == 0:
    axioms = re.findall(r"depends on axioms:\s*\[([^]]*)\]", (root / "verification/rs75-real-axis-gamma-axioms.log").read_text(), re.S)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    assert len(axioms) == 3 and all({x.strip() for x in a.split(",") if x.strip()} <= allowed for a in axioms), "Unexpected axiom audit"
    record["axiom_audit"] = {"declarations": 3, "only_standard_axioms": True}
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = result.returncode
(root / "verification/rs75-real-axis-gamma-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
