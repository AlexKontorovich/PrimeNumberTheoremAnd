"""Compile the finite handoff and audit its public implication in one process."""
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
source = ROOT / 'RSBounds/RS75FiniteHandoff.lean'
audit = ROOT / 'verification/RS75FiniteHandoffAudit.lean'
commands = '\n'.join(line for line in audit.read_text().splitlines()
                     if line.startswith('#print axioms'))
input_text = source.read_text() + '\n' + commands + '\n'
args = ['lake', 'env', 'lean', '-j1', '-Dprofiler=true', '--stdin',
        '-o', '.lake/build/lib/lean/RSBounds/RS75FiniteHandoff.olean',
        'RSBounds/RS75FiniteHandoff.lean']
rec = {
    'kind': 'fresh-source-compilation-and-in-process-transitive-axiom-audit',
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'command': args,
    'source_sha256': {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [source, audit, Path(__file__).resolve()]},
    'stdin_sha256': hashlib.sha256(input_text.encode()).hexdigest(),
    'stdin_description': 'Exact source followed by the four #print axioms commands from the audit file.',
    'log': 'verification/rs75-finite-handoff-build-audit.log',
}
record = ROOT / 'verification/rs75-finite-handoff-run.json'
record.write_text(json.dumps(rec, indent=2) + '\n')
started = time.monotonic()
with (ROOT / rec['log']).open('wb') as out:
    result = subprocess.run(args, input=input_text.encode(), stdout=out,
                            stderr=subprocess.STDOUT)
rec.update(exit_code=result.returncode, seconds=time.monotonic() - started,
           finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
if result.returncode == 0:
    groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]',
                        (ROOT / rec['log']).read_text(), re.S)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    valid = len(groups) == 4 and all(
        {x.strip() for x in g.split(',') if x.strip()} <= allowed for g in groups)
    rec['axiom_audit'] = {'declarations': len(groups), 'only_standard_axioms': valid}
    if not valid:
        rec['exit_code'] = 1
record.write_text(json.dumps(rec, indent=2) + '\n')
print(json.dumps(rec, indent=2), flush=True)
raise SystemExit(rec['exit_code'])
