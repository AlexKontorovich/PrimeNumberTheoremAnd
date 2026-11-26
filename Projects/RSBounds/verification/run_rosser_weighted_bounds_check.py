"""Fresh compile and transitive axiom audit of explicit actual weighted zeta zero bounds."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parent.parent
sources = ['RSBounds/RosserWeightedBounds.lean', 'verification/RosserWeightedBoundsAudit.lean',
           'verification/run_rosser_weighted_bounds_check.py',
           'RSBounds/WeightedZetaZeros.lean', 'RSBounds/RosserTailIntegrals.lean',
           'RSBounds/Rosser1941.lean']
record = {
    'kind': 'fresh-local-compilation-and-axiom-audit',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'source_sha256': {name: hashlib.sha256((root/name).read_bytes()).hexdigest()
                      for name in sources},
    'runs': [],
}
jobs = [(['lake', 'env', 'lean', '-j1', '-o',
          '.lake/build/lib/lean/RSBounds/RosserWeightedBounds.olean',
          'RSBounds/RosserWeightedBounds.lean'], 'rosser-weighted-bounds-build.log'),
        (['lake', 'env', 'lean', '-j1', 'verification/RosserWeightedBoundsAudit.lean'],
         'rosser-weighted-bounds-axioms.log')]
exit_code = 0
for command, name in jobs:
    print('Checking '+name, flush=True)
    started = time.monotonic()
    with (root/'verification'/name).open('w') as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record['runs'].append({'command': command, 'log': name, 'exit_code': result.returncode,
                           'elapsed_seconds': time.monotonic()-started})
    print('Completed '+name+' exit='+str(result.returncode), flush=True)
    exit_code = result.returncode
    if exit_code:
        break
if not exit_code:
    content = (root/'verification/rosser-weighted-bounds-axioms.log').read_text()
    groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]', content, re.S)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    clean = len(groups) == 13 and all(
        {s.strip() for s in group.split(',') if s.strip()} <= allowed for group in groups)
    record['axiom_audit'] = {'declarations': len(groups), 'only_standard_axioms': clean}
    exit_code = 0 if clean else 1
record['finished_utc'] = datetime.now(timezone.utc).isoformat()
record['exit_code'] = exit_code
(root/'verification/rosser-weighted-bounds-run.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record, indent=2))
raise SystemExit(exit_code)
