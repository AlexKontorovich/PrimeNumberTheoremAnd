"""Check one exact source and listed declarations; persist its outcome and hashes.

Usage: python verification/run_fresh_module_check.py MODULE STEM DECLARATION ...
The caller supplies the pinned compiler and LEAN_PATH (or invokes this via lake env).
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[1]
module, stem, *names = sys.argv[1:]
assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', module)
assert re.fullmatch(r'[a-z0-9-]+', stem)
source = f'RSBounds/{module}.lean'
audit = f'verification/{module}Audit.lean'
commands = '\n'.join(f'#print axioms {name}' for name in names)
(root / audit).write_text(f'import RSBounds.{module}\n\n' + commands + '\n')
stdin = (root / source).read_text() + '\n' + commands + '\n'
files = [source, audit, 'lean-toolchain', 'lake-manifest.json',
         'verification/run_fresh_module_check.py']
hashes = {f: hashlib.sha256((root / f).read_bytes()).hexdigest() for f in files}
lean = shutil.which('lean')
assert lean
obj = f'.lake/build/lib/lean/RSBounds/{module}.olean'
cmd = [lean, '-j1', '-Dprofiler=true', '--stdin', '-o', obj, source]
log = f'verification/{stem}-build.log'
receipt = root / f'verification/{stem}-run.json'
data = {
    'kind': 'fresh-source-and-in-process-transitive-axiom-audit',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'lean_version': subprocess.check_output([lean, '--version'], text=True).strip(),
    'source_sha256': hashes, 'stdin_sha256': hashlib.sha256(stdin.encode()).hexdigest(),
    'stdin_recipe': 'Exact source followed by the listed fully qualified axiom commands.',
    'audited_declarations': names, 'command': cmd, 'log': log, 'exit_code': None,
}
receipt.write_text(json.dumps(data, indent=2) + '\n')
start = time.monotonic()
with (root / log).open('wb') as output:
    result = subprocess.run(cmd, cwd=root, input=stdin.encode(), stdout=output,
                            stderr=subprocess.STDOUT)
data.update(exit_code=result.returncode, seconds=time.monotonic() - start,
            finished_utc=datetime.now(timezone.utc).isoformat())
receipt.write_text(json.dumps(data, indent=2) + '\n')
if result.returncode:
    print((root / log).read_text())
    raise SystemExit(result.returncode)
text = (root / log).read_text()
groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]', text, re.S)
assert len(groups) == len(names), groups
assert all({x.strip() for x in g.split(',') if x.strip()} <=
           {'propext', 'Classical.choice', 'Quot.sound'} for g in groups)
assert all(hashlib.sha256((root / f).read_bytes()).hexdigest() == h
           for f, h in hashes.items()), 'Source changed during check'
data['axiom_audit'] = {'declarations': len(names), 'only_standard_axioms': True}
data['object_sha256'] = hashlib.sha256((root / obj).read_bytes()).hexdigest()
receipt.write_text(json.dumps(data, indent=2) + '\n')
entries = re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]", text, re.S)
(root / f'verification/{stem}-axioms.log').write_text('\n'.join(entries) + '\n')
print(f'{module}: passed {len(names)} standard-axiom audits.', flush=True)
