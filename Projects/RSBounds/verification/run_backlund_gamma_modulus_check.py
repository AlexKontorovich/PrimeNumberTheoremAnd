"""Freshly compile the Gamma-modulus chain, then audit transitive axioms."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent.parent
modules = ["BacklundDigammaSeriesAdapter", "BacklundDigammaStirling", "BacklundGammaModulusDigamma", "BacklundGammaModulusHorizontal", "BacklundGammaModulusAbsorption"]
sources = [f"RSBounds/{name}.lean" for name in modules] + [
    "verification/BacklundGammaModulusAudit.lean",
]
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {s: hashlib.sha256((root / s).read_bytes()).hexdigest() for s in sources},
    "runs": [],
}
jobs = [(["lake", "env", "lean", f"RSBounds/{m}.lean", "-o",
          f".lake/build/lib/lean/RSBounds/{m}.olean"],
         f"backlund-gamma-modulus-{m}-build.log") for m in modules]
jobs.append((["lake", "env", "lean", "verification/BacklundGammaModulusAudit.lean"],
             "backlund-gamma-modulus-axioms.log"))
for command, name in jobs:
    with (root / "verification" / name).open("w") as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name, "exit_code": result.returncode})
    if result.returncode:
        break
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = result.returncode
(root / "verification/backlund-gamma-modulus-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
