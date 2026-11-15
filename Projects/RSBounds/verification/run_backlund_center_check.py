"""Compile/audit the exact Euler-product center bound, sequentially."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent.parent
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in ["RSBounds/BacklundCenter.lean", "verification/BacklundCenterAudit.lean"]
    },
    "runs": [],
}
jobs = [
    (["lake", "build", "RSBounds.BacklundCenter"], "backlund-center-build.log"),
    (["lake", "env", "lean", "verification/BacklundCenterAudit.lean"],
     "backlund-center-axioms.log"),
]
for command, name in jobs:
    with (root / "verification" / name).open("w") as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name, "exit_code": result.returncode})
    if result.returncode:
        break
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = result.returncode
(root / "verification/backlund-center-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
