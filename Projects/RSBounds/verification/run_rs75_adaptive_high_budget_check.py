"""Compile and audit the adaptive high-zero numerical budget (not total psi)."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

root = Path(__file__).resolve().parent.parent
output = root / "verification/rs75-adaptive-high-budget-run.json"
record = {
    "kind": "fresh-local-compilation-and-transitive-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in [
            "RSBounds/RS75AdaptiveHighBudget.lean", "RSBounds/RS75DecayingHighZeros.lean",
            "RSBounds/RS75ZeroPowerDecay.lean", "RSBounds/RosserCubicTail.lean",
            "verification/RS75AdaptiveHighBudgetAudit.lean",
            "verification/run_rs75_adaptive_high_budget_check.py",
            "lean-toolchain", "lake-manifest.json",
        ]
    },
    "runs": [],
}

def save():
    output.write_text(json.dumps(record, indent=2) + "\n")

save()
jobs = [
    (["lake", "env", "lean", "-j1", "-o",
      ".lake/build/lib/lean/RSBounds/RS75AdaptiveHighBudget.olean",
      "RSBounds/RS75AdaptiveHighBudget.lean"], "rs75-adaptive-high-budget-build.log"),
    (["lake", "env", "lean", "-j1", "verification/RS75AdaptiveHighBudgetAudit.lean"],
     "rs75-adaptive-high-budget-axioms.log"),
]
for command, name in jobs:
    started = time.monotonic()
    with (root / "verification" / name).open("w") as log:
        result = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name,
        "exit_code": result.returncode, "seconds": time.monotonic() - started})
    save()
    if result.returncode:
        record["exit_code"] = result.returncode
        save()
        raise SystemExit(result.returncode)

groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]",
    (root / "verification/rs75-adaptive-high-budget-axioms.log").read_text(), re.S)
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert len(groups) == 9 and all(
    {a.strip() for a in group.split(",") if a.strip()} <= allowed for group in groups
), "Transitive axiom audit failed"
record["axiom_audit"] = {"declarations": 9, "only_standard_axioms": True}
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = 0
save()
print(json.dumps(record, indent=2))
