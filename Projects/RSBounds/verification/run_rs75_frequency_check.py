"""Compile and audit the actual nonzero-frequency RS75 log-derivative bound."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / 'verification'
files = ['RSBounds/RS75Frequency.lean',
         'RSBounds/BacklundGammaModulusDigamma.lean',
         '.lake/packages/TernaryGoldbach/TernaryGoldbach/Explicit/ZeroFreeRegion.lean',
         'verification/RS75FrequencyAudit.lean',
         'verification/run_rs75_frequency_check.py']
data = {
    'kind': 'fresh-compilation-with-in-process-transitive-axiom-audit',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'source_sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest()
                      for f in files},
    'runs': [],
}
receipt = OUT / 'rs75-frequency-run.json'

def save():
    receipt.write_text(json.dumps(data, indent=2) + '\n')

source = (ROOT / 'RSBounds/RS75Frequency.lean').read_text()
audit_lines = (ROOT / 'verification/RS75FrequencyAudit.lean').read_text().splitlines()
audit_commands = [line for line in audit_lines if line.strip() and not line.startswith('import ')]
assert len(audit_commands) == 1 and all(line.startswith('#print axioms ') for line in audit_commands)
stdin = source + '\n' + '\n'.join(audit_commands) + '\n'
data['stdin_recipe'] = 'Exact proof source, newline, and the public theorem transitive #print axioms command.'
data['stdin_sha256'] = hashlib.sha256(stdin.encode()).hexdigest()
data['module_name_source'] = 'Explicit filename argument; verified in pinned Lean/Shell.lean lines498-553.'
save()
command = ['lake', 'env', 'lean', '-j1', '-Dprofiler=true', '--stdin', '-o',
           '.lake/build/lib/lean/RSBounds/RS75Frequency.olean', 'RSBounds/RS75Frequency.lean']
print('Compiling RS75Frequency and auditing its public theorem in the same process.', flush=True)
started = time.monotonic()
logname = 'rs75-frequency-build.log'
with (OUT / logname).open('wb') as output:
    result = subprocess.run(command, input=stdin.encode(), stdout=output, stderr=subprocess.STDOUT)
data['runs'].append({'command': command, 'log': logname,
                     'exit_code': result.returncode,
                     'seconds': time.monotonic() - started,
                     'stdin_sha256': data['stdin_sha256']})
save()
if result.returncode:
    data.update(exit_code=result.returncode, finished_utc=datetime.now(timezone.utc).isoformat())
    save()
    print((OUT / logname).read_text(), flush=True)
    raise SystemExit(result.returncode)
log = (OUT / logname).read_text()
audit_output = re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]", log, re.S)
(OUT / 'rs75-frequency-axioms.log').write_text('\n'.join(audit_output) + '\n')
groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]', log, re.S)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert len(groups) == 1 and all(
    {x.strip() for x in g.split(',') if x.strip()} <= allowed for g in groups)
data['axiom_audit'] = {'declarations': len(groups), 'only_standard_axioms': True}
data.update(exit_code=0, finished_utc=datetime.now(timezone.utc).isoformat())
save()
print(json.dumps(data, indent=2), flush=True)
