"""Rebuild only the local analytic closure affected by namespace isolation.

The already checked RH100 numerical certificate modules are imported, not
recompiled. No mathematical proof body is changed by the namespace fix.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path(__file__).resolve().parent.parent
modules = [
    "RSBounds.BacklundDigammaSeriesAdapter",
    "RSBounds.BacklundDigammaStirling",
    "RSBounds.BacklundGammaModulusDigamma",
    "RSBounds.BacklundGammaModulusHorizontal",
    "RSBounds.BacklundFunctionalStrip",
    "RSBounds.BacklundLeftZetaBoundary",
    "RSBounds.BacklundCircleMajorantGeometry",
    "RSBounds.BacklundStrip",
    "RSBounds.BacklundCircleMajorantBounds",
    "RSBounds.BacklundCircleCount",
    "RSBounds.BacklundHighCount",
    "RSBounds",
]
audits = [
    "verification/BacklundGammaModulusAudit.lean",
    "verification/BacklundHighCountAudit.lean",
    "verification/BacklundNamespaceIntegrationAudit.lean",
]
sources = [m.replace(".", "/") + ".lean" for m in modules] + audits
record = {
    "kind": "fresh-namespace-integration-rebuild-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "adaptation_record": "verification/backlund-namespace-adaptation.json",
    "source_sha256": {
        s: hashlib.sha256((root / s).read_bytes()).hexdigest() for s in sources
    },
    "replayed_rh100_numerical_modules": False,
    "runs": [],
    "status": "running",
}
receipt = root / "verification/backlund-namespace-integration-run.json"


def save():
    receipt.write_text(json.dumps(record, indent=2) + "\n")


save()
jobs = [
    (["lake", "env", "lean", "-j1", "-o",
      ".lake/build/lib/lean/" + m.replace(".", "/") + ".olean",
      m.replace(".", "/") + ".lean"],
     "backlund-namespace-" + m.replace(".", "-") + "-build.log", False)
    for m in modules
] + [
    (["lake", "env", "lean", "-j1", a],
     "backlund-namespace-" + Path(a).stem + ".log", True)
    for a in audits
]
for command, logname, is_audit in jobs:
    print("Checking " + command[-1], flush=True)
    path = root / "verification" / logname
    with path.open("w") as output:
        result = subprocess.run(command, cwd=root, stdout=output,
                                stderr=subprocess.STDOUT)
    row = {"command": command, "log": logname, "exit_code": result.returncode}
    record["runs"].append(row)
    if result.returncode:
        record["status"] = "failed"
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
        print(path.read_text(), flush=True)
        raise SystemExit(result.returncode)
    if is_audit:
        sets = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", path.read_text())
        assert sets, "No printed axiom sets: " + logname
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        assert all({a.strip() for a in s.split(",") if a.strip()} <= allowed
                   for s in sets), "Nonstandard axiom: " + logname
        row["printed_axiom_sets"] = len(sets)
        row["only_standard_axioms"] = True
    save()
record["status"] = "verified"
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
save()
print("Namespace integration and all audits verified", flush=True)
