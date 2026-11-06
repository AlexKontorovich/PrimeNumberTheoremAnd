"""Compile one polynomial-formula module and audit its actual theorem axioms."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("module", choices=["PolynomialExplicitFormula", "PolynomialQuarticFormula",
                                       "PolynomialZetaFormula"])
args = parser.parse_args()
project = Path(__file__).resolve().parents[1]
workspace = project.parent
elan = workspace / ".tools" / "elan-home"
env = os.environ.copy()
env.update(ELAN_HOME=str(elan), PATH=str(elan / "bin") + os.pathsep + env["PATH"],
           LEAN_NUM_THREADS="1", TMPDIR=str(workspace / ".tools" / "tmp"))
stems = {"PolynomialExplicitFormula": "polynomial-explicit-formula",
         "PolynomialQuarticFormula": "polynomial-quartic-formula",
         "PolynomialZetaFormula": "polynomial-zeta-formula"}
stem = stems[args.module]
files = [f"RSBounds/{args.module}.lean", f"verification/{args.module}Audit.lean"]
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_sha256": {f: hashlib.sha256((project / f).read_bytes()).hexdigest() for f in files},
    "runs": [],
}
result = 0
for command, filename in [
    (["lake", "build", f"RSBounds.{args.module}"], f"{stem}-build.log"),
    (["lake", "env", "lean", f"verification/{args.module}Audit.lean"], f"{stem}-axioms.log"),
]:
    with (project / "verification" / filename).open("w") as output:
        completed = subprocess.run(command, cwd=project, env=env, stdout=output,
                                   stderr=subprocess.STDOUT, check=False)
    record["runs"].append({"command": command, "log": filename, "exit_code": completed.returncode})
    print(f"{filename}: exit {completed.returncode}", flush=True)
    if completed.returncode:
        result = completed.returncode
        break
record["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record["exit_code"] = result
(project / "verification" / f"{stem}-run.json").write_text(json.dumps(record, indent=2) + "\n")
raise SystemExit(result)
