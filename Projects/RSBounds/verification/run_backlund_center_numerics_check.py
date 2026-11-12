"""Freshly compile all three numerical-center modules, then audit axioms."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent.parent
modules = ["BacklundCenterNumericsBase", "BacklundCenterNumericsData", "BacklundCenterNumerics"]
sources = [f"RSBounds/{name}.lean" for name in modules] + [
    "verification/BacklundCenterNumericsAudit.lean",
    "scripts/gen_backlund_center_numerics.py",
]
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {s: hashlib.sha256((root / s).read_bytes()).hexdigest() for s in sources},
    "runs": [],
}
jobs = [(["lake", "env", "lean", f"RSBounds/{m}.lean", "-o",
          f".lake/build/lib/lean/RSBounds/{m}.olean"],
         f"backlund-center-numerics-{m}-build.log") for m in modules]
jobs.append((["lake", "env", "lean", "verification/BacklundCenterNumericsAudit.lean"],
             "backlund-center-numerics-axioms.log"))
for command, name in jobs:
    with (root / "verification" / name).open("w") as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name, "exit_code": result.returncode})
    if result.returncode:
        break
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = result.returncode
(root / "verification/backlund-center-numerics-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
