"""Exact-source finite-parts check with in-process transitive axiom audits."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
source = "RSBounds/MertensFiniteParts.lean"
audit = "verification/MertensFinitePartsAudit.lean"
runner = "verification/run_mertens_finite_parts_check.py"
tracked = [source, audit, runner]
checks = [line for line in (root / audit).read_text().splitlines()
          if line.startswith("#print axioms ")]
assert len(checks) == 3
text = (root / source).read_text() + "\n" + "\n".join(checks) + "\n"
obj = ".lake/build/lib/lean/RSBounds/MertensFiniteParts.olean"
log = root / "verification/mertens-finite-parts-build.log"
receipt = root / "verification/mertens-finite-parts-run.json"
cmd = ["lean", "-j1", "-Dprofiler=true", "--stdin", "-o", obj, source]
record = {
    "kind": "fresh-finite-parts-build-with-in-process-transitive-axiom-audits",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                      for name in tracked},
    "command": cmd,
    "stdin_sha256": hashlib.sha256(text.encode()).hexdigest(),
    "log": str(log.relative_to(root)),
}
receipt.write_text(json.dumps(record, indent=2) + "\n")
started = time.monotonic()
with log.open("wb") as out:
    result = subprocess.run(cmd, cwd=root, input=text.encode(), stdout=out,
                            stderr=subprocess.STDOUT)
record["seconds"] = time.monotonic() - started
record["exit_code"] = result.returncode
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
receipt.write_text(json.dumps(record, indent=2) + "\n")
if result.returncode:
    print(log.read_text())
    raise SystemExit(result.returncode)
output = log.read_text()
found = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output, re.S)
assert len(found) == len(checks), (len(found), len(checks))
assert all({entry.strip() for entry in group.split(",") if entry.strip()} <=
           {"propext", "Classical.choice", "Quot.sound"} for group in found)
assert all(hashlib.sha256((root / name).read_bytes()).hexdigest() == digest
           for name, digest in record["source_sha256"].items()), "Source changed during audit"
record["axiom_audit"] = {"declarations": 3, "only_standard_axioms": True}
record["object_sha256"] = hashlib.sha256((root / obj).read_bytes()).hexdigest()
receipt.write_text(json.dumps(record, indent=2) + "\n")
(root / "verification/mertens-finite-parts-axioms.log").write_text(
    "\n".join(re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]", output, re.S)) + "\n")
print("MertensFiniteParts: fresh build and three standard-axiom checks passed.", flush=True)
