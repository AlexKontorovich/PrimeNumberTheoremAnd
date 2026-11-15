"""Compile and audit the second-order EM and Backlund right-edge bound sequentially."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent.parent
modules = ["BacklundEulerMaclaurin", "BacklundZetaRegularization", "BacklundZetaBoundary"]
sources = ["RSBounds/" + name + ".lean" for name in modules]
sources += ["verification/BacklundZetaBoundaryAudit.lean"]
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in sources
    },
    "runs": [],
}
jobs = [(["lake", "env", "lean", "-j1", "-o",
          ".lake/build/lib/lean/RSBounds/" + name + ".olean", "RSBounds/" + name + ".lean"],
         "backlund-zeta-" + name + "-build.log") for name in modules]
jobs += [(["lake", "env", "lean", "-j1", "verification/BacklundZetaBoundaryAudit.lean"],
          "backlund-zeta-boundary-axioms.log")]
for command, name in jobs:
    with (root / "verification" / name).open("w") as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name, "exit_code": result.returncode})
    if result.returncode:
        break
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = result.returncode
(root / "verification/backlund-zeta-boundary-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
