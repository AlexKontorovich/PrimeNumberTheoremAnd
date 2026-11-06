"""Fresh direct checks of the unchanged pinned Stechkin/zero-free sources.

No Lake dependency build is requested. XiPartial and Digamma are reused from
their existing checked objects. The package's linter option is supplied
explicitly, and the source root keeps the original module names.
"""
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
PKG = Path('.lake/packages/TernaryGoldbach')
revision = subprocess.check_output(['git', '-C', str(PKG), 'rev-parse', 'HEAD'],
                                   text=True).strip()
assert revision == 'ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0'
git_status = subprocess.check_output([
    'git', '-C', str(PKG), 'status', '--short', '--',
    'TernaryGoldbach/Explicit/ZeroFree.lean',
    'TernaryGoldbach/Explicit/ZeroFreeRegion.lean'], text=True)
assert not git_status, 'Pinned source files have local changes'
sources = [str(PKG / 'TernaryGoldbach/Explicit' / (n + '.lean'))
           for n in ['XiPartial', 'Digamma', 'ZeroFree', 'ZeroFreeRegion']]
sources += ['lean-toolchain', 'lake-manifest.json',
            str(PKG / 'lakefile.lean'),
            'verification/RS75StechkinReuseAudit.lean',
            'verification/run_rs75_stechkin_reuse_check.py']

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

record = {
    'kind': 'fresh-unchanged-upstream-compilation-and-transitive-axiom-audit',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'upstream': 'calr3/ternary-goldbach',
    'pinned_revision': revision,
    'checked_source_git_status': git_status,
    'source_sha256': {name: sha(ROOT / name) for name in sources},
    'imported_object_sha256': {
        str(PKG / '.lake/build/lib/lean/TernaryGoldbach/Explicit' / (n + '.olean')):
        sha(ROOT / PKG / '.lake/build/lib/lean/TernaryGoldbach/Explicit' / (n + '.olean'))
        for n in ['XiPartial', 'Digamma']},
    'runs': [],
}
receipt = OUT / 'rs75-stechkin-reuse-run.json'

def save():
    receipt.write_text(json.dumps(record, indent=2) + '\n')

jobs = []
for n in ['ZeroFree', 'ZeroFreeRegion']:
    src = str(PKG / 'TernaryGoldbach/Explicit' / (n + '.lean'))
    obj = str(PKG / '.lake/build/lib/lean/TernaryGoldbach/Explicit' / (n + '.olean'))
    jobs.append((['lake', 'env', 'lean', '-j1', '-Dlinter.unusedSectionVars=false',
                  '-R', str(PKG), '-o', obj, src],
                 'rs75-stechkin-' + n.lower() + '-fresh-build.log'))
jobs.append((['lake', 'env', 'lean', '-j1', 'verification/RS75StechkinReuseAudit.lean'],
             'rs75-stechkin-reuse-axioms.log'))
save()
for command, logname in jobs:
    print('Checking ' + command[-1], flush=True)
    started = time.monotonic()
    with (OUT / logname).open('wb') as out:
        result = subprocess.run(command, stdout=out, stderr=subprocess.STDOUT)
    record['runs'].append({'command': command, 'log': logname,
                          'exit_code': result.returncode,
                          'seconds': time.monotonic() - started})
    save()
    if result.returncode:
        record.update(exit_code=result.returncode,
                      finished_utc=datetime.now(timezone.utc).isoformat())
        save()
        print((OUT / logname).read_text(), flush=True)
        raise SystemExit(result.returncode)

groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]',
                    (OUT / 'rs75-stechkin-reuse-axioms.log').read_text(), re.S)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert len(groups) == 18 and all(
    {x.strip() for x in group.split(',') if x.strip()} <= allowed
    for group in groups), 'Unexpected axiom audit result'
record['axiom_audit'] = {'declarations': len(groups), 'only_standard_axioms': True}
record['object_sha256'] = {
    str(PKG / '.lake/build/lib/lean/TernaryGoldbach/Explicit' / (n + '.olean')):
    sha(ROOT / PKG / '.lake/build/lib/lean/TernaryGoldbach/Explicit' / (n + '.olean'))
    for n in ['ZeroFree', 'ZeroFreeRegion']}
record.update(exit_code=0, finished_utc=datetime.now(timezone.utc).isoformat())
save()
print(json.dumps(record, indent=2), flush=True)
