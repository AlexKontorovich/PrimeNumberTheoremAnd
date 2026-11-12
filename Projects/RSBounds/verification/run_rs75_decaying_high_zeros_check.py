"""Compile and audit actual decaying high-zero quartic bounds."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

root = Path(__file__).resolve().parent.parent
output = root / "verification/rs75-decaying-high-zeros-run.json"
record = {
    "kind": "fresh-local-compilation-and-transitive-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in [
            "RSBounds/RS75ZeroPowerDecay.lean", "RSBounds/RS75DecayingHighZeros.lean",
            "RSBounds/RS75ZeroFree1975.lean", "RSBounds/PolynomialZeroPairing.lean",
            "RSBounds/RosserCubicTail.lean", "verification/RS75ZeroPowerDecayAudit.lean",
            "verification/RS75DecayingHighZerosAudit.lean",
            "verification/run_rs75_decaying_high_zeros_check.py",
            "lean-toolchain", "lake-manifest.json",
        ]
    },
    "runs": [],
}

def save():
    output.write_text(json.dumps(record, indent=2) + "\n")

save()
jobs = []
for module, prefix in [("RS75ZeroPowerDecay", "rs75-zero-power-decay"),
                       ("RS75DecayingHighZeros", "rs75-decaying-high-zeros")]:
    jobs.append((["lake", "env", "lean", "-j1", "-o",
        ".lake/build/lib/lean/RSBounds/" + module + ".olean",
        "RSBounds/" + module + ".lean"], prefix + "-build.log"))
for module, prefix in [("RS75ZeroPowerDecay", "rs75-zero-power-decay"),
                       ("RS75DecayingHighZeros", "rs75-decaying-high-zeros")]:
    jobs.append((["lake", "env", "lean", "-j1", "verification/" + module + "Audit.lean"],
        prefix + "-axioms.log"))
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

allowed = {"propext", "Classical.choice", "Quot.sound"}
for prefix, count in [("rs75-zero-power-decay", 5), ("rs75-decaying-high-zeros", 6)]:
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]",
        (root / "verification" / (prefix + "-axioms.log")).read_text(), re.S)
    assert len(groups) == count and all(
        {a.strip() for a in group.split(",") if a.strip()} <= allowed for group in groups
    ), "Transitive axiom audit failed: " + prefix
record["axiom_audit"] = {"declarations": 11, "only_standard_axioms": True}
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = 0
save()
print(json.dumps(record, indent=2))
