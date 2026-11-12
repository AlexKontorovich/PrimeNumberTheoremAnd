"""Compile and audit the pointwise quartic zero-coefficient majorants."""
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
            "RSBounds/PolynomialZeroMajorants.lean",
            "RSBounds/PolynomialKernelScaling.lean",
            "RSBounds/PolynomialZeroKernel.lean",
            "RSBounds/PolynomialLowerKernel.lean",
            "RSBounds/PolynomialZeroCancellation.lean",
            "RSBounds/PolynomialLeftKernel.lean",
            "verification/PolynomialZeroMajorantsAudit.lean",
            "lean-toolchain",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "env", "lean", "-j1", "-Dprofiler=true", "-o",
      ".lake/build/lib/lean/RSBounds/PolynomialZeroMajorants.olean",
      "RSBounds/PolynomialZeroMajorants.lean"], "polynomial-zero-majorants-build.log"),
    (["lake", "env", "lean", "-j1", "verification/PolynomialZeroMajorantsAudit.lean"],
     "polynomial-zero-majorants-axioms.log"),
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
(root / "verification/polynomial-zero-majorants-run.json").write_text(
    json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
