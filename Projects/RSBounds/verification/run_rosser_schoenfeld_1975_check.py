"""Compile and audit the Rosser-Schoenfeld b23 psi theorem (one Lean process at a time)."""
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
            "RSBounds/RosserSchoenfeld1975.lean",
            "RSBounds/PolynomialZeroPairing.lean",
            "RSBounds/PolynomialZeroMajorants.lean",
            "RSBounds/QuarticFirst29BudgetBridges.lean",
            "RSBounds/RosserWeightedBounds.lean",
            "RSBounds/QuarticLowZeroBounds.lean",
            "RSBounds/QuarticFirst29BudgetApplication.lean",
            "RSBounds/PolynomialPsiFromZeroSums.lean",
            "verification/RosserSchoenfeld1975Audit.lean",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "env", "lean", "-j1", "RSBounds/RosserSchoenfeld1975.lean", "-o", ".lake/build/lib/lean/RSBounds/RosserSchoenfeld1975.olean"], "rosser-schoenfeld-1975-build.log"),
    (["lake", "env", "lean", "-j1", "verification/RosserSchoenfeld1975Audit.lean"],
     "rosser-schoenfeld-1975-axioms.log"),
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
(root / "verification/rosser-schoenfeld-1975-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
