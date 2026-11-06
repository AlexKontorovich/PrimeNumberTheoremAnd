"""Compile and audit the Rosser elementary tail integrals (one Lean process at a time)."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in [
            "RSBounds/RosserTailIntegrals.lean",
            "RSBounds/WeightedZeroSums.lean",
            "verification/RosserTailIntegralsAudit.lean",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "env", "lean", "-j1", "RSBounds/RosserTailIntegrals.lean", "-o", ".lake/build/lib/lean/RSBounds/RosserTailIntegrals.olean"], "rosser-tail-integrals-build.log"),
    (["lake", "env", "lean", "-j1", "verification/RosserTailIntegralsAudit.lean"],
     "rosser-tail-integrals-axioms.log"),
]
for command, name in jobs:
    path = root / "verification" / name
    with path.open("w") as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name, "exit_code": result.returncode})
    if result.returncode:
        break
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = result.returncode
(root / "verification/rosser-tail-integrals-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
