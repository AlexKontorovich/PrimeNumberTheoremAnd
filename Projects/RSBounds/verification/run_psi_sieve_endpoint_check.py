"""Check the endpoint proof and its transitive axioms in one Lean invocation.

Lean's documented --stdin option is used with the original source filename.
The input is precisely the source followed by the audit's #print commands;
both the source and this complete input are hashed in the receipt.
"""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE = "RSBounds/PsiSieveEndpointReduction.lean"
AUDIT = "verification/PsiSieveEndpointReductionAudit.lean"
INPUT = "verification/psi-sieve-endpoint-check-input.lean"
LOG = "verification/psi-sieve-endpoint-check.log"
RECORD = ROOT / "verification/psi-sieve-endpoint-run.json"
audit_commands = "\n".join(
    line for line in (ROOT / AUDIT).read_text().splitlines()
    if line.startswith("#print axioms ")
) + "\n"
(ROOT / INPUT).write_text((ROOT / SOURCE).read_text() + "\n" + audit_commands)
files = [SOURCE, AUDIT, INPUT, "verification/run_psi_sieve_endpoint_check.py",
         "lean-toolchain", "lake-manifest.json", "lakefile.lean"]
record = {
    "kind": "single-pass-source-compilation-and-appended-axiom-audits",
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in files
    },
    "command": ["lake", "env", "lean", "-j1", "--stdin", SOURCE, "-o",
                ".lake/build/lib/lean/RSBounds/PsiSieveEndpointReduction.olean"],
    "stdin": INPUT,
    "log": LOG,
}
RECORD.write_text(json.dumps(record, indent=2) + "\n")
started = time.monotonic()
with (ROOT / INPUT).open() as inp, (ROOT / LOG).open("w") as out:
    result = subprocess.run(record["command"], cwd=ROOT, stdin=inp,
                            stdout=out, stderr=subprocess.STDOUT)
record.update(exit_code=result.returncode, elapsed_seconds=time.monotonic()-started,
              finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
if result.returncode == 0:
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]",
                        (ROOT / LOG).read_text(), re.S)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    passed = len(groups) == 10 and all(
        {x.strip() for x in group.split(",") if x.strip()} <= allowed for group in groups
    )
    record["axiom_audit"] = {"declarations": len(groups), "only_standard_axioms": passed}
    if not passed:
        record["exit_code"] = 1
RECORD.write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(record["exit_code"])
