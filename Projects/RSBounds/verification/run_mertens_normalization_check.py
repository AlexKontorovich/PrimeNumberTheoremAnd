"""Persist exact-source checks, including exit status, independently of a tool session."""
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
specs = {
    'MertensCenteredNormalization': ('mertens-centered-normalization', [
        'TernaryGoldbach.RSBounds.MertensCenteredNormalization.centered_average_tendsto',
        'TernaryGoldbach.RSBounds.MertensCenteredNormalization.centered_limit_eq']),
    'Schoenfeld1976Targets': ('schoenfeld-1976-targets', []),
}
deps = [
    'RSBounds/MertensAbelianNormalization.lean',
    'RSBounds/MellinAbelianLimit.lean',
    'RSBounds/MertensAbelIdentity.lean',
    'RSBounds/MertensPsiAbel.lean',
    'RSBounds/Targets.lean', 'lean-toolchain', 'lake-manifest.json',
    'verification/run_mertens_normalization_check.py',
]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
lean = shutil.which('lean')
assert lean
version = subprocess.check_output([lean, '--version'], text=True).strip()
for module in sys.argv[1:] or specs:
    stem, names = specs[module]
    source = f'RSBounds/{module}.lean'
    audit = '\n'.join(f'#print axioms {name}' for name in names)
    stdin = (root / source).read_text() + '\n' + audit + '\n'
    files = list(dict.fromkeys([source] + deps))
    hashes = {f: hashlib.sha256((root / f).read_bytes()).hexdigest() for f in files}
    obj = f'.lake/build/lib/lean/RSBounds/{module}.olean'
    cmd = [lean, '-j1', '-Dprofiler=true', '--stdin', '-o', obj, source]
    log = f'verification/{stem}-build.log'
    receipt = root / f'verification/{stem}-run.json'
    data = {
        'kind': 'fresh-source-and-transitive-axiom-audit' if names else 'specifications-compilation',
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'lean_version': version, 'source_sha256': hashes,
        'stdin_sha256': hashlib.sha256(stdin.encode()).hexdigest(),
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
        print((root / log).read_text(), flush=True)
        raise SystemExit(result.returncode)
    text = (root / log).read_text()
    groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]', text, re.S)
    assert len(groups) == len(names), groups
    assert all({x.strip() for x in g.split(',') if x.strip()} <= allowed for g in groups)
    assert all(hashlib.sha256((root / f).read_bytes()).hexdigest() == h
               for f, h in hashes.items()), 'A source changed during the check'
    data['object_sha256'] = hashlib.sha256((root / obj).read_bytes()).hexdigest()
    if names:
        data['axiom_audit'] = {'declarations': len(names), 'only_standard_axioms': True}
        entries = re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]", text, re.S)
        (root / f'verification/{stem}-axioms.log').write_text('\n'.join(entries) + '\n')
    receipt.write_text(json.dumps(data, indent=2) + '\n')
    print(f'{module}: passed ({len(names)} transitive axiom audits).', flush=True)
