"""Check the new scalar-only eight-band budget and its transitive axioms.

Previously successful unchanged local modules are reused only after checking
their source, predecessor source, and object hashes. No RH certificate is
compiled by this runner. This is not a proof of a psi estimate.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess

root = Path(__file__).resolve().parent.parent
modules = ['QuarticBudgetNumericsBase', 'QuarticFirst29BudgetNumerics']
sources = ['RSBounds/' + m + '.lean' for m in modules] + [
    'verification/QuarticFirst29ScalarAudit.lean']
receipt = root / 'verification/quartic-first29-scalar-run.json'
previous = json.loads(receipt.read_text()) if receipt.exists() else {}
record = {
    'kind': 'scalar-only-kernel-compilation-and-axiom-audit',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'source_sha256': {s: hashlib.sha256((root / s).read_bytes()).hexdigest() for s in sources},
    'full_psi_estimate_proved': False,
    'runs': [], 'status': 'running',
}


def save():
    receipt.write_text(json.dumps(record, indent=2) + '\n')


save()
for i, m in enumerate(modules):
    source = 'RSBounds/' + m + '.lean'
    target = '.lake/build/lib/lean/RSBounds/' + m + '.olean'
    signature = [record['source_sha256'][s] for s in sources[:i+1]]
    old = next((r for r in previous.get('runs', []) if r.get('module') == m), None)
    if old and old.get('exit_code') == 0 and old.get('signature') == signature and (
        (root / target).exists() and old.get('olean_sha256') ==
        hashlib.sha256((root / target).read_bytes()).hexdigest()
    ):
        row = dict(old)
        row['reused'] = True
        record['runs'].append(row)
        save()
        print('Reusing checked unchanged ' + source, flush=True)
        continue
    command = ['lake', 'env', 'lean', '-j1', '-o', target, source]
    log = 'verification/quartic-first29-' + m + '-build.log'
    print('Checking ' + source, flush=True)
    with (root / log).open('w') as output:
        result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
    row = {'module':m, 'command':command, 'log':log, 'signature':signature,
           'exit_code':result.returncode}
    record['runs'].append(row)
    if result.returncode:
        record['status'] = 'build-failed'
        save()
        print((root / log).read_text(), flush=True)
        raise SystemExit(result.returncode)
    row['olean_sha256'] = hashlib.sha256((root / target).read_bytes()).hexdigest()
    save()

command = ['lake', 'env', 'lean', '-j1', sources[-1]]
log = 'verification/quartic-first29-scalar-axioms.log'
print('Auditing scalar certificate declarations', flush=True)
with (root / log).open('w') as output:
    result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
record['runs'].append({'command':command, 'log':log, 'exit_code':result.returncode})
if result.returncode:
    record['status'] = 'audit-failed'
    save()
    print((root / log).read_text(), flush=True)
    raise SystemExit(result.returncode)
sets = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', (root / log).read_text())
assert len(sets) == 9, len(sets)
assert all({a.strip() for a in s.split(',') if a.strip()} <=
           {'propext', 'Classical.choice', 'Quot.sound'} for s in sets)
record['printed_axiom_sets'] = len(sets)
record['only_standard_axioms'] = True
record['status'] = 'verified'
record['finished_utc'] = datetime.now(timezone.utc).isoformat()
save()
print('Scalar budget and all nine axiom audits verified', flush=True)
