#!/usr/bin/env python3
"""Freshly check the four finite-height modules and their public axiom audit."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[1]
modules = ["BacklundLowMainTerm", "BacklundLowCountGeneric", "BacklundLowZeros",
           "BacklundLowCount"]
audit = "verification/BacklundLowCountAudit.lean"
receipt_path = root / "verification/backlund-low-count-run.json"
receipt = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "lean_version": "Lean 4.35.0",
    "source_sha256": {}, "builds": [], "status": "running",
}
sources = [f"RSBounds/{m}.lean" for m in modules] + [audit,
    "RSBounds/BacklundLowScalarBase.lean", "RSBounds/BacklundLowScalarData.lean",
    "RSBounds/BacklundRH100Bridge.lean", "RSBounds/RosserCountDefinition.lean"]
for name in sources:
    receipt["source_sha256"][name] = hashlib.sha256((root / name).read_bytes()).hexdigest()

def save():
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")

save()
for module in modules:
    cmd = ["lake", "env", "lean", "-o", f".lake/build/lib/lean/RSBounds/{module}.olean",
           f"RSBounds/{module}.lean"]
    log = f"verification/backlund-low-count-{module}-build.log"
    started = time.monotonic()
    with (root / log).open("w") as output:
        result = subprocess.run(cmd, cwd=root, stdout=output, stderr=subprocess.STDOUT)
    receipt["builds"].append({"module": module, "command": cmd, "log": log,
                             "exit_code": result.returncode,
                             "elapsed_seconds": round(time.monotonic() - started, 3)})
    save()
    if result.returncode:
        receipt["status"] = "build-failed"
        save()
        print((root / log).read_text())
        sys.exit(result.returncode)

log = "verification/backlund-low-count-axioms.log"
cmd = ["lake", "env", "lean", audit]
with (root / log).open("w") as output:
    result = subprocess.run(cmd, cwd=root, stdout=output, stderr=subprocess.STDOUT)
text = (root / log).read_text()
expected = len(re.findall(r"^#print axioms ", (root / audit).read_text(), re.M))
found = re.findall(r"depends on axioms:\s*\[([^]]*)\]", text, re.S)
allowed = {"propext", "Classical.choice", "Quot.sound"}
actual = [{name.strip() for name in match.split(",") if name.strip()} for match in found]
okay = result.returncode == 0 and len(found) == expected and all(a <= allowed for a in actual)
receipt["audit"] = {"command": cmd, "log": log, "exit_code": result.returncode,
                    "expected_theorems": expected, "audited_theorems": len(found),
                    "axioms": sorted(set().union(*actual)) if actual else [], "passed": okay}
receipt["status"] = "passed" if okay else "audit-failed"
receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
receipt["result"] = (
    "Actual inclusive zero-count error is strictly below 1 for 0<=T<=100; "
    "the original Rosser envelope follows for 2<=T<=100. The RH100 input "
    "is a replayed theorem, not a hypothesis. The public theorem and the "
    "29 retained interval witnesses are included in the axiom audit."
) if okay else "The combined axiom audit has not passed; inspect its log."
save()
print(text)
sys.exit(0 if okay else 1)
