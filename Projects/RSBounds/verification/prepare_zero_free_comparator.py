"""Compile the independent zero-free challenge/solution; do not run Comparator.

The challenge imports Mathlib only. The two targets include an unconditional
high-height bound and the full finite-RH theorem. No definition holes or
nonstandard solution axioms are permitted by the prepared configuration.
This preparation is not a native Comparator success receipt.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

root = Path(__file__).resolve().parent.parent
output = root / "verification/zero-free-comparator-prep-run.json"
source_names = [
    "comparator/RSZeroFreeChallenge.lean", "comparator/RSZeroFreeSolution.lean",
    "comparator-zero-free.json", "RSBounds/RS75ZeroFree1975.lean",
    "verification/RSZeroFreeSolutionAudit.lean",
    "verification/prepare_zero_free_comparator.py",
    "lean-toolchain", "lakefile.lean", "lake-manifest.json",
]
config = json.loads((root / "comparator-zero-free.json").read_text())
challenge = (root / "comparator/RSZeroFreeChallenge.lean").read_text()
assert re.findall(r"^import\s+(\S+)", challenge, re.M) == ["Mathlib"]
assert "definition_names" not in config
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert set(config["permitted_axioms"]) == allowed
record = {
    "kind": "independent-comparator-source-preparation-and-solution-axiom-audit",
    "native_comparator_status": "not run",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in source_names
    },
    "runs": [],
}

def save():
    output.write_text(json.dumps(record, indent=2) + "\n")

save()
jobs = [
    (["lake", "env", "lean", "-j1", "-R", "comparator", "-o",
      ".lake/build/lib/lean/RSZeroFreeChallenge.olean", "comparator/RSZeroFreeChallenge.lean"],
     "zero-free-comparator-challenge-build.log"),
    (["lake", "env", "lean", "-j1", "-R", "comparator", "-o",
      ".lake/build/lib/lean/RSZeroFreeSolution.olean", "comparator/RSZeroFreeSolution.lean"],
     "zero-free-comparator-solution-build.log"),
    (["lake", "env", "lean", "-j1", "verification/RSZeroFreeSolutionAudit.lean"],
     "zero-free-comparator-solution-axioms.log"),
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
    (root / "verification/zero-free-comparator-solution-axioms.log").read_text(), re.S)
assert len(groups) == 2 and all(
    {a.strip() for a in group.split(",") if a.strip()} <= allowed for group in groups
), "Solution transitive axiom audit failed"
record["solution_axiom_audit"] = {"declarations": 2, "only_standard_axioms": True}
record["object_sha256"] = {
    name: hashlib.sha256((root / name).read_bytes()).hexdigest()
    for name in [".lake/build/lib/lean/RSZeroFreeChallenge.olean",
        ".lake/build/lib/lean/RSZeroFreeSolution.olean"]
}
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = 0
save()
print(json.dumps(record, indent=2))
