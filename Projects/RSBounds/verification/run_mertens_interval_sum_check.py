"""Compile the actual reciprocal-cube tail and audit its exports in one process."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, time

root = Path(__file__).resolve().parents[1]
files = [
    'RSBounds/MertensIntervalSum.lean',
    'RSBounds/Mertens.lean',
    'verification/MertensIntervalSumAudit.lean',
    'verification/run_mertens_interval_sum_check.py',
]
audit = [s for s in (root / files[-2]).read_text().splitlines()
         if s.startswith('#print axioms ')]
assert len(audit) == 7
stdin = (root / files[0]).read_text() + '\n' + '\n'.join(audit) + '\n'
data = {
    'kind': 'fresh-mertens-interval-sum-build-with-in-process-transitive-axiom-audit',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'source_sha256': {f: hashlib.sha256((root / f).read_bytes()).hexdigest() for f in files},
    'stdin_recipe': 'Exact source plus seven fully qualified #print axioms commands.',
    'stdin_sha256': hashlib.sha256(stdin.encode()).hexdigest(),
    'runs': [],
}
receipt = root / 'verification/mertens-interval-sum-run.json'
receipt.write_text(json.dumps(data, indent=2) + '\n')
cmd = ['lake', 'env', 'lean', '-j1', '-Dprofiler=true', '--stdin', '-o',
       '.lake/build/lib/lean/RSBounds/MertensIntervalSum.olean', files[0]]
t = time.monotonic()
log = root / 'verification/mertens-interval-sum-build.log'
with log.open('wb') as out:
    result = subprocess.run(cmd, cwd=root, input=stdin.encode(), stdout=out,
                            stderr=subprocess.STDOUT)
data['runs'].append({'command': cmd, 'log': str(log.relative_to(root)),
                     'exit_code': result.returncode, 'seconds': time.monotonic() - t})
data['build_exit_code'] = result.returncode
data['exit_code'] = result.returncode
receipt.write_text(json.dumps(data, indent=2) + '\n')
if result.returncode:
    print(log.read_text())
    raise SystemExit(result.returncode)
text = log.read_text()
groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]', text, re.S)
assert len(groups) == 7, len(groups)
assert all({x.strip() for x in s.split(',') if x.strip()} <=
           {'propext', 'Classical.choice', 'Quot.sound'} for s in groups)
data['axiom_audit'] = {'declarations': 7, 'only_standard_axioms': True}
data['object_sha256'] = hashlib.sha256(
    (root / '.lake/build/lib/lean/RSBounds/MertensIntervalSum.olean').read_bytes()).hexdigest()
assert all(hashlib.sha256((root / f).read_bytes()).hexdigest() == h
           for f, h in data['source_sha256'].items()), 'Source changed during check'
data['finished_utc'] = datetime.now(timezone.utc).isoformat()
receipt.write_text(json.dumps(data, indent=2) + '\n')
entries = re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]", text, re.S)
(root / 'verification/mertens-interval-sum-axioms.log').write_text('\n'.join(entries) + '\n')
print('Finite-interval Mangoldt identity and seven standard-axiom audits passed.')
