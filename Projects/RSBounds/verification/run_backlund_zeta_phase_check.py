"""Compile and audit the Backlund continuous zeta phase and reflected Jensen bridge (one Lean process at a time)."""
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
            "RSBounds/BacklundZetaPhase.lean",
            "verification/BacklundZetaPhaseAudit.lean",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "env", "lean", "-j1", "-o", ".lake/build/lib/lean/RSBounds/BacklundZetaPhase.olean", "RSBounds/BacklundZetaPhase.lean"], "backlund-zeta-phase-build.log"),
    (["lake", "env", "lean", "-j1", "verification/BacklundZetaPhaseAudit.lean"],
     "backlund-zeta-phase-axioms.log"),
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
(root / "verification/backlund-zeta-phase-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
