"""Fresh wrapper builds, axiom audit, exports, and independent Comparator.

Prerequisite: build/replay the recorded local and vendored dependency closure.
The from-export flags avoid asking Lake to rebuild those numerical proofs again.
Exports are made afresh below, and their hashes are recorded alongside source
and imported-object hashes. Process sandboxing is disabled because bwrap cannot
mount tmpfs in this workspace; theorem comparison and kernel checking remain on.
"""
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
OUT = ROOT / 'verification'
RECORD = OUT / 'zero-count-run.json'
EXPORTS = ROOT / '.lake' / 'zero-count-exports'
EXPORTS.mkdir(parents=True, exist_ok=True)
data = {'kind': 'fresh-build-axiom-audit-and-independent-comparator',
        'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'sandbox_disabled': True, 'runs': []}

# The same roots as Lake.CLI.Check.compareIt in this pinned Lean toolchain.
# Explicit primitives are required even if absent from a theorem's own closure.
cfg = json.loads((ROOT / 'comparator-zero-count.json').read_text())
export_targets = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind',
    *cfg['theorem_names'], *cfg['permitted_axioms'],
    'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod',
    'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft',
    'Nat.shiftRight', 'String.ofList', 'Char.ofNat', 'List', 'eagerReduce',
    'Nat', 'String', 'String.mk', 'Char', 'optParam', 'autoParam',
    'semiOutParam', 'outParam']
data['export_targets'] = export_targets

def sha(path):
    return hashlib.file_digest(path.open('rb'), 'sha256').hexdigest()

def save():
    RECORD.write_text(json.dumps(data, indent=2) + '\n')

def run(args, label, stdout=None):
    log = OUT / (label + '.log')
    started = time.monotonic()
    with log.open('wb') as err:
        if stdout is None:
            proc = subprocess.run(args, stdout=err, stderr=subprocess.STDOUT)
        else:
            with stdout.open('wb') as out:
                proc = subprocess.run(args, stdout=out, stderr=err)
    rec = {'command': args, 'log': str(log.relative_to(ROOT)),
           'exit_code': proc.returncode, 'seconds': time.monotonic() - started}
    if stdout is not None:
        rec.update(export=str(stdout.relative_to(ROOT)), export_sha256=sha(stdout),
                   export_bytes=stdout.stat().st_size)
    data['runs'].append(rec)
    save()
    print(label, proc.returncode, flush=True)
    if proc.returncode:
        data['exit_code'] = proc.returncode
        save()
        raise SystemExit(proc.returncode)

sources = set()
def visit(path):
    if path in sources:
        return
    sources.add(path)
    for mod in re.findall(r'^(?:public\s+)?import\s+(\S+)', path.read_text(), re.M):
        for prefix in [ROOT, ROOT / 'vendor' / 'rh100']:
            target = prefix / (mod.replace('.', '/') + '.lean')
            if target.is_file():
                visit(target)
                break

visit(ROOT / 'RSBounds' / 'Rosser1941.lean')
visit(ROOT / 'RSBounds' / 'ZetaZeroTable.lean')
sources.update(ROOT / f for f in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
    'comparator-zero-count.json', 'comparator/RSZeroCountChallenge.lean',
    'comparator/RSZeroCountSolution.lean', 'verification/Rosser1941Audit.lean'])
data['source_sha256'] = {str(p.relative_to(ROOT)): sha(p) for p in sorted(sources)}
save()

run(['lake', 'env', 'lean', '-j1', '-o', '.lake/build/lib/lean/RSBounds/Rosser1941.olean',
     'RSBounds/Rosser1941.lean'], 'zero-count-global-build')
run(['lake', 'env', 'lean', '-j1', 'verification/Rosser1941Audit.lean'],
    'zero-count-axioms')
axiom_sets = re.findall(r'depends on axioms:\s*\[([^]]*)\]',
                       (OUT / 'zero-count-axioms.log').read_text(), re.S)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert len(axiom_sets) == 5 and all(
    {s.strip() for s in group.split(',') if s.strip()} <= allowed for group in axiom_sets
), 'Public theorem axiom audit failed'
data['public_axiom_audit'] = {'declarations': 5, 'only_standard_axioms': True}
save()
for mod in ['RSZeroCountChallenge', 'RSZeroCountSolution']:
    prep = OUT / 'zero-count-challenge-prep.json'
    if mod == 'RSZeroCountChallenge' and prep.is_file():
        prior = json.loads(prep.read_text())
        candidates = {
            'source_sha256': ROOT / 'comparator/RSZeroCountChallenge.lean',
            'manifest_sha256': ROOT / 'lake-manifest.json',
            'toolchain_sha256': ROOT / 'lean-toolchain',
            'config_sha256': ROOT / 'comparator-zero-count.json',
            'object_sha256': ROOT / '.lake/build/lib/lean/RSZeroCountChallenge.olean',
            'export_sha256': EXPORTS / 'RSZeroCountChallenge.export'}
        if prior.get('exit_code') == 0 and prior.get('export_targets') == export_targets and all(
                p.is_file() and prior.get(k) == sha(p) for k, p in candidates.items()):
            data['runs'].append({'kind': 'reuse-validated-fresh-challenge-export',
                'receipt': str(prep.relative_to(ROOT)), 'receipt_sha256': sha(prep),
                'export_sha256': prior['export_sha256'], 'exit_code': 0})
            save()
            continue
    run(['lake', 'env', 'lean', '-j1', '-R', 'comparator', '-o',
         '.lake/build/lib/lean/' + mod + '.olean', 'comparator/' + mod + '.lean'],
        'zero-count-' + mod + '-build')
    run(['lake', 'env', 'leanexport', mod, '--', *export_targets],
        'zero-count-' + mod + '-export', EXPORTS / (mod + '.export'))

data['object_sha256'] = {}
for p in sorted(sources):
    if p.suffix != '.lean':
        continue
    rel = p.relative_to(ROOT)
    if str(rel).startswith('vendor/rh100/'):
        rel = rel.relative_to('vendor/rh100')
    elif str(rel).startswith('comparator/'):
        rel = rel.relative_to('comparator')
    obj = ROOT / '.lake/build/lib/lean' / rel.with_suffix('.olean')
    if obj.is_file():
        data['object_sha256'][str(obj.relative_to(ROOT))] = sha(obj)
save()

run(['lake', 'comparator', '--config', 'comparator-zero-count.json',
     '--challenge-from-export', str(EXPORTS / 'RSZeroCountChallenge.export'),
     '--solution-from-export', str(EXPORTS / 'RSZeroCountSolution.export'),
     '--inadvisably-no-sandbox'], 'zero-count-comparator')
data.update(exit_code=0, finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
save()
