"""Fresh exact-source builds, each followed by in-process transitive axiom checks."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
sources = [
    "RSBounds/SchoenfeldReciprocalSquare.lean",
    "RSBounds/SchoenfeldSquareCutoffs.lean",
]
tracked = sources + [
    "RSBounds/RS75XiIncrement.lean",
    "RSBounds/RS75RealAxisLogDerivative.lean",
    "RSBounds/ZetaZeroTable.lean",
    "RSBounds/PolynomialZeroCountBridge.lean",
    "RSBounds/PolynomialZeroPairing.lean",
    "verification/SchoenfeldReciprocalSquareAudit.lean",
    "verification/run_schoenfeld_reciprocal_square_check.py",
]
audit = [line for line in (root / tracked[-2]).read_text().splitlines()
         if line.startswith("#print axioms ")]
assert len(audit) == 10
groups = [audit[:7], audit[7:]]
record = {
    "kind": "fresh-reciprocal-square-builds-with-in-process-transitive-axiom-audits",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                      for name in tracked},
    "runs": [],
}
receipt = root / "verification/schoenfeld-reciprocal-square-run.json"
receipt.write_text(json.dumps(record, indent=2) + "\n")
all_axioms = []
for i, (name, checks) in enumerate(zip(sources, groups)):
    text = (root / name).read_text() + "\n" + "\n".join(checks) + "\n"
    obj = ".lake/build/lib/lean/" + name.removesuffix(".lean") + ".olean"
    cmd = ["lean", "-j1", "-Dprofiler=true", "--stdin", "-o", obj, name]
    log = root / f"verification/schoenfeld-reciprocal-square-build-{i + 1}.log"
    started = time.monotonic()
    with log.open("wb") as out:
        result = subprocess.run(cmd, cwd=root, input=text.encode(), stdout=out,
                                stderr=subprocess.STDOUT)
    run = {"command": cmd, "log": str(log.relative_to(root)),
           "stdin_sha256": hashlib.sha256(text.encode()).hexdigest(),
           "seconds": time.monotonic() - started, "exit_code": result.returncode}
    record["runs"].append(run)
    record["exit_code"] = result.returncode
    receipt.write_text(json.dumps(record, indent=2) + "\n")
    if result.returncode:
        print(log.read_text())
        raise SystemExit(result.returncode)
    output = log.read_text()
    found = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output, re.S)
    assert len(found) == len(checks), (name, len(found), len(checks))
    assert all({entry.strip() for entry in group.split(",") if entry.strip()} <=
               {"propext", "Classical.choice", "Quot.sound"} for group in found)
    run["only_standard_axioms"] = True
    run["object_sha256"] = hashlib.sha256((root / obj).read_bytes()).hexdigest()
    all_axioms += re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]", output, re.S)
    print(f"{name}: fresh build and {len(checks)} standard-axiom checks passed.", flush=True)
assert all(hashlib.sha256((root / name).read_bytes()).hexdigest() == digest
           for name, digest in record["source_sha256"].items()), "Source changed during audit"
record["axiom_audit"] = {"declarations": 10, "only_standard_axioms": True}
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
receipt.write_text(json.dumps(record, indent=2) + "\n")
(root / "verification/schoenfeld-reciprocal-square-axioms.log").write_text(
    "\n".join(all_axioms) + "\n")
