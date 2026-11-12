"""Check the vendored IEANTN Gauss-series closure and print exact axiom sets."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
sources = sorted(str(p.relative_to(root)) for p in
                 (root / "RSBounds/IEANTNGamma").glob("*.lean"))
sources += ["RSBounds/IEANTNDigamma.lean", "verification/IEANTNDigammaAudit.lean"]
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "upstream_repository": "https://github.com/teorth/IEANTN",
    "upstream_commit": "466b41b28ecc224398cf53a99c5fe9618131398b",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in sources
    },
    "runs": [],
}
jobs = [
    (["lake", "build", "RSBounds.IEANTNDigamma"], "ieantn-gamma-build.log"),
    (["lake", "env", "lean", "verification/IEANTNDigammaAudit.lean"],
     "ieantn-gamma-axioms.log"),
]
for command, name in jobs:
    path = root / "verification" / name
    with path.open("w") as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name, "exit_code": result.returncode})
    if result.returncode:
        break
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = result.returncode
(root / "verification/ieantn-gamma-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
