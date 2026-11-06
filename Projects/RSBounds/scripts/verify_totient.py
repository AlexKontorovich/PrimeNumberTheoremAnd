#!/usr/bin/env python3
"""Run the independent Comparator and record the actual outcome and inputs."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--no-sandbox', action='store_true')
parser.add_argument('--paranoid', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
out = root / 'verification'
out.mkdir(exist_ok=True)
command = ['lake', 'comparator']
if args.paranoid:
    command.append('--paranoid')
if args.no_sandbox:
    command.append('--inadvisably-no-sandbox')
paths = ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
         'RSBounds/Totient.lean', 'RSBounds/SmallTotientProduct.lean',
         'comparator/RSTotientChallenge.lean',
         'comparator/RSTotientSolution.lean', 'comparator.json']
record = {
    'kind': 'local-verification-transcript',
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'command': command,
    'sandbox_disabled': args.no_sandbox,
    'source_sha256': {p: hashlib.sha256((root/p).read_bytes()).hexdigest()
                      for p in paths},
}
record_path = out / 'totient-run.json'
record_path.write_text(json.dumps(record, indent=2) + '\n')
env = os.environ.copy()
env['LEAN_NUM_THREADS'] = '1'
env['RAYON_NUM_THREADS'] = '1'
with (out/'totient-comparator.log').open('w') as log:
    result = subprocess.run(command, cwd=root, env=env, stdout=log,
                            stderr=subprocess.STDOUT, check=False)
record['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record['exit_code'] = result.returncode
record_path.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'exit_code': result.returncode, 'log': str(out/'totient-comparator.log')}))
raise SystemExit(result.returncode)
