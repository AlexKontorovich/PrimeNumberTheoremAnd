"""Compile and audit the Backlund inclusive zero-count endpoint extension (one Lean process at a time)."""
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
            "RSBounds/BacklundCountEndpoint.lean",
            "RSBounds/BacklundCountIdentity.lean",
            "verification/BacklundCountEndpointAudit.lean",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "env", "lean", "-j1", "RSBounds/BacklundCountEndpoint.lean", "-o", ".lake/build/lib/lean/RSBounds/BacklundCountEndpoint.olean"], "backlund-count-endpoint-build.log"),
    (["lake", "env", "lean", "-j1", "verification/BacklundCountEndpointAudit.lean"],
     "backlund-count-endpoint-axioms.log"),
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
(root / "verification/backlund-count-endpoint-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
