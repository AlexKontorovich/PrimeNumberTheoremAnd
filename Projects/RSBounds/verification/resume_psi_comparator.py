"""Replay the exact previously built/exported psi proof after session loss.

The original build/export receipt and unfinished Comparator log are retained.
Every recorded source/config/object hash and both export hashes must match
before this script starts the independent Comparator again.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / 'verification'
prior_path = OUT / 'psi-run.json'
prior = json.loads(prior_path.read_text())

def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

for group in ['source_sha256', 'object_sha256']:
    assert prior[group], f'Missing {group}'
    for name, expected in prior[group].items():
        assert sha(ROOT / name) == expected, f'Changed {group}: {name}'

prep_path = OUT / 'psi-challenge-prep.json'
prep = json.loads(prep_path.read_text())
reuse = next(r for r in prior['runs'] if r.get('kind') ==
            'reuse-validated-fresh-challenge-export')
assert sha(prep_path) == reuse['receipt_sha256']
challenge = ROOT / '.lake/psi-exports/RSPsiChallenge.export'
solution = ROOT / '.lake/psi-exports/RSPsiSolution.export'
assert sha(challenge) == prep['export_sha256'] == reuse['export_sha256']
export_run = next(r for r in prior['runs'] if r.get('export') ==
                  '.lake/psi-exports/RSPsiSolution.export')
assert export_run['exit_code'] == 0
assert sha(solution) == export_run['export_sha256']
assert solution.stat().st_size == export_run['export_bytes']
assert prior['public_axiom_audit'] == {
    'declarations': 1, 'only_standard_axioms': True}

args = ['lake', 'comparator', '--config', 'comparator-psi.json',
        '--challenge-from-export', str(challenge),
        '--solution-from-export', str(solution), '--inadvisably-no-sandbox']
rec = {
    'kind': 'independent-comparator-replay-of-validated-fresh-exports',
    'reason': 'Earlier session became inaccessible and left no completion verdict.',
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'prior_receipt': 'verification/psi-run.json',
    'prior_receipt_sha256': sha(prior_path),
    'prior_unfinished_log': 'verification/psi-comparator.log',
    'source_hashes_validated': len(prior['source_sha256']),
    'object_hashes_validated': len(prior['object_sha256']),
    'challenge_export_sha256': sha(challenge),
    'solution_export_sha256': sha(solution),
    'sandbox_disabled': True,
    'command': args,
    'log': 'verification/psi-comparator-resume.log',
}
record = OUT / 'psi-resume-run.json'
record.write_text(json.dumps(rec, indent=2) + '\n')
print('All recorded sources, objects, and exports match; starting Comparator.', flush=True)
started = time.monotonic()
with (OUT / 'psi-comparator-resume.log').open('wb') as output:
    result = subprocess.run(args, stdout=output, stderr=subprocess.STDOUT)
rec.update(exit_code=result.returncode, seconds=time.monotonic() - started,
           finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
record.write_text(json.dumps(rec, indent=2) + '\n')
print(json.dumps(rec, indent=2), flush=True)
raise SystemExit(result.returncode)
