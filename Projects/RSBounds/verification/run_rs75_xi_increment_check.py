"""Check the actual xi real-axis increment and its transitive axioms."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / "verification"
record = OUT / "rs75-xi-increment-run.json"
files = [
    "RSBounds/RS75XiIncrement.lean",
    "RSBounds/RS75RealAxisNumerics.lean",
    "RSBounds/ZetaZeroTable.lean",
    "verification/RS75XiIncrementAudit.lean",
    "verification/run_rs75_xi_increment_check.py",
    "lean-toolchain", "lake-manifest.json",
]
data = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_sha256": {
        f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files
    },
    "runs": [],
}

def save():
    record.write_text(json.dumps(data, indent=2) + "\n")

save()
for command, label in [
    (["lake", "env", "lean", "-j1", "-o",
      ".lake/build/lib/lean/RSBounds/RS75XiIncrement.olean",
      "RSBounds/RS75XiIncrement.lean"], "rs75-xi-increment-build"),
    (["lake", "env", "lean", "-j1", "verification/RS75XiIncrementAudit.lean"],
     "rs75-xi-increment-axioms"),
]:
    started = time.monotonic()
    with (OUT / (label + ".log")).open("w") as out:
        result = subprocess.run(command, stdout=out, stderr=subprocess.STDOUT)
    data["runs"].append({"command": command, "log": label + ".log",
        "exit_code": result.returncode, "seconds": time.monotonic() - started})
    save()
    print(label, result.returncode, flush=True)
    if result.returncode:
        data["exit_code"] = result.returncode
        save()
        raise SystemExit(result.returncode)

groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]",
                    (OUT / "rs75-xi-increment-axioms.log").read_text(), re.S)
expected = len(re.findall(r"^#print axioms ",
                         (OUT / "RS75XiIncrementAudit.lean").read_text(), re.M))
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert len(groups) == expected and all(
    {s.strip() for s in group.split(",") if s.strip()} <= allowed for group in groups)
data.update(exit_code=0,
    axiom_audit={"declarations": expected, "only_standard_axioms": True},
    finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
save()
print("All", expected, "axiom audits passed.", flush=True)
