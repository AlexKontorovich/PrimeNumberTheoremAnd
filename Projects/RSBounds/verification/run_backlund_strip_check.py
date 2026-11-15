"""Fresh direct compilation and axiom audit of unconditional Backlund (56)."""
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
            "RSBounds/BacklundStrip.lean",
            "RSBounds/BacklundHalfStrip.lean",
            "RSBounds/BacklundStripNormalizer.lean",
            "RSBounds/BacklundBottomCertificates.lean",
            "RSBounds/BacklundBottomData.lean",
            "RSBounds/BacklundBottomFiniteSum.lean",
            "verification/BacklundStripAudit.lean",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "env", "lean", "-j1", "-o",
      ".lake/build/lib/lean/RSBounds/BacklundStrip.olean",
      "RSBounds/BacklundStrip.lean"], "backlund-strip-build.log"),
    (["lake", "env", "lean", "-j1", "verification/BacklundStripAudit.lean"],
     "backlund-strip-axioms.log"),
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
(root / "verification/backlund-strip-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
