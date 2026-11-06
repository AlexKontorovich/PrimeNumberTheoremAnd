"""Freshly compile the pinned unconditional prime-product certificate through 100000."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, time

root = Path(__file__).resolve().parents[1]
files = [
    '../ternary-goldbach/TernaryGoldbach/Prelim/SmallMertensProd.lean',
    '../ternary-goldbach/TernaryGoldbach/Prelim/RamareWalk.lean',
    'verification/SmallMertensProdAudit.lean',
    'verification/run_small_mertens_prod_check.py',
]
audit = [s for s in (root / files[-2]).read_text().splitlines()
         if s.startswith('#print axioms ')]
assert len(audit) == 4
stdin = (root / files[0]).read_text() + '\n' + '\n'.join(audit) + '\n'
data = {
    'kind': 'fresh-small-mertens-prod-build-with-in-process-transitive-axiom-audit',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'source_sha256': {f: hashlib.sha256((root / f).read_bytes()).hexdigest() for f in files},
    'stdin_recipe': 'Exact source plus four fully qualified #print axioms commands.',
    'stdin_sha256': hashlib.sha256(stdin.encode()).hexdigest(),
    'runs': [],
}
receipt = root / 'verification/small-mertens-prod-run.json'
receipt.write_text(json.dumps(data, indent=2) + '\n')
cmd = ['lake', 'env', 'lean', '-j1', '-Dprofiler=true', '--stdin', '-o',
       '.lake/build/lib/lean/TernaryGoldbach/Prelim/SmallMertensProd.olean', 'TernaryGoldbach/Prelim/SmallMertensProd.lean']
t = time.monotonic()
log = root / 'verification/small-mertens-prod-build.log'
with log.open('wb') as out:
    result = subprocess.run(cmd, cwd=root.parent / 'ternary-goldbach', input=stdin.encode(), stdout=out,
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
assert len(groups) == 4, len(groups)
assert all({x.strip() for x in s.split(',') if x.strip()} <=
           {'propext', 'Classical.choice', 'Quot.sound'} for s in groups)
data['axiom_audit'] = {'declarations': 4, 'only_standard_axioms': True}
data['object_sha256'] = hashlib.sha256(
    (root.parent / 'ternary-goldbach/.lake/build/lib/lean/TernaryGoldbach/Prelim/SmallMertensProd.olean').read_bytes()).hexdigest()
assert all(hashlib.sha256((root / f).read_bytes()).hexdigest() == h
           for f, h in data['source_sha256'].items()), 'Source changed during check'
data['finished_utc'] = datetime.now(timezone.utc).isoformat()
receipt.write_text(json.dumps(data, indent=2) + '\n')
entries = re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]", text, re.S)
(root / 'verification/small-mertens-prod-axioms.log').write_text('\n'.join(entries) + '\n')
print('Upstream prime-product certificate through 100000 and four standard-axiom audits passed.')
