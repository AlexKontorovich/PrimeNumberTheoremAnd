"""Compile and audit the actual psi reduction from averaged zero sums (one Lean process at a time)."""
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
            "RSBounds/PolynomialPsiFromZeroSums.lean",
            "RSBounds/PolynomialAveragedFormula.lean",
            "RSBounds/PolynomialRemainderBound.lean",
            "RSBounds/PolynomialPsi.lean",
            "verification/PolynomialPsiFromZeroSumsAudit.lean",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "env", "lean", "-j1", "RSBounds/PolynomialPsiFromZeroSums.lean", "-o", ".lake/build/lib/lean/RSBounds/PolynomialPsiFromZeroSums.olean"], "polynomial-psi-from-zero-sums-build.log"),
    (["lake", "env", "lean", "-j1", "verification/PolynomialPsiFromZeroSumsAudit.lean"],
     "polynomial-psi-from-zero-sums-axioms.log"),
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
(root / "verification/polynomial-psi-from-zero-sums-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
