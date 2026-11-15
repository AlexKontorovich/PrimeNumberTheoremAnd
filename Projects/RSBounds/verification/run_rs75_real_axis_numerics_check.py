"""Compile and audit the RS75 real-axis numerical inputs."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import time

root = Path(__file__).resolve().parent.parent
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in [
            "RSBounds/RS75RealAxisNumerics.lean",
            "RSBounds/ZetaZeroTableHead.lean",
            "RSBounds/ZetaZeroTable.lean",
            "verification/RS75RealAxisNumericsAudit.lean",
            "lean-toolchain",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "env", "lean", "-j1", "-Dprofiler=true", "-o",
      ".lake/build/lib/lean/RSBounds/RS75RealAxisNumerics.olean",
      "RSBounds/RS75RealAxisNumerics.lean"], "rs75-real-axis-numerics-build.log"),
    (["lake", "env", "lean", "-j1", "verification/RS75RealAxisNumericsAudit.lean"],
     "rs75-real-axis-numerics-axioms.log"),
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
    if result.returncode:
        break
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = result.returncode
(root / "verification/rs75-real-axis-numerics-run.json").write_text(
    json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
