"""Compile and audit the actual RS75 Dirichlet-series positivity proof."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

root = Path(__file__).resolve().parent.parent
output = root / "verification/rs75-dirichlet-positivity-run.json"
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in [
            "RSBounds/RS75DirichletPositivity.lean",
            "RSBounds/RS75Polynomial.lean",
            ".lake/packages/TernaryGoldbach/TernaryGoldbach/Explicit/ZeroFreeRegion.lean",
            "verification/RS75DirichletPositivityAudit.lean",
            "verification/run_rs75_dirichlet_positivity_check.py",
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
      ".lake/build/lib/lean/RSBounds/RS75DirichletPositivity.olean",
      "RSBounds/RS75DirichletPositivity.lean"], "rs75-dirichlet-positivity-build.log"),
    (["lake", "env", "lean", "-j1", "verification/RS75DirichletPositivityAudit.lean"],
     "rs75-dirichlet-positivity-axioms.log"),
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
    save()
    if result.returncode:
        record["exit_code"] = result.returncode
        save()
        raise SystemExit(result.returncode)

groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]",
    (root / "verification/rs75-dirichlet-positivity-axioms.log").read_text(), re.S)
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert len(groups) == 5 and all(
    {a.strip() for a in group.split(",") if a.strip()} <= allowed for group in groups
), "Axiom audit failed"
record["axiom_audit"] = {"declarations": 5, "only_standard_axioms": True}
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = 0
save()
print(json.dumps(record, indent=2))
