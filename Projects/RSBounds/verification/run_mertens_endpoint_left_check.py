"""Fresh source compilation and transitive axiom audits, one compiler at a time."""
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
allowed = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for module, tag in [('MertensEndpointLeft', 'mertens-endpoint-left')]:
    source = ROOT / f'RSBounds/{module}.lean'
    audit = ROOT / f'verification/{module}Audit.lean'
    commands = '\n'.join(line for line in audit.read_text().splitlines()
                         if line.startswith('#print axioms'))
    input_text = source.read_text() + '\n' + commands + '\n'
    obj = ROOT / f'.lake/build/lib/lean/RSBounds/{module}.olean'
    args = ['lean', '-j1', '-Dprofiler=true', '--stdin',
            '-o', str(obj.relative_to(ROOT)), str(source.relative_to(ROOT))]
    dependencies = [ROOT / 'RSBounds/MertensIntervalLeftBound.lean',
                    ROOT / '.lake/build/lib/lean/RSBounds/MertensIntervalLeftBound.olean',
                    ROOT / 'RSBounds/MertensSignedInterval.lean',
                    ROOT / 'RSBounds/MertensIntervalDecay.lean',
                    ROOT / 'RSBounds/PolynomialExplicitFormula.lean',
                    ROOT / 'RSBounds/PolynomialLeftRemainder.lean',
                    ROOT.parent / 'ternary-goldbach/TernaryGoldbach/Explicit/XiPartial.lean',
                    ROOT.parent / 'ternary-goldbach/TernaryGoldbach/Explicit/ZetaExplicit.lean']
    if module == 'QuadraticSubOne':
        dependencies += [ROOT / 'RSBounds/QuadraticContourLimit.lean',
                         ROOT / '.lake/build/lib/lean/RSBounds/QuadraticContourLimit.olean']
    rec = {
        'kind': 'fresh-source-compilation-and-in-process-transitive-axiom-audit',
        'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'command': args,
        'source_sha256': {str(p.relative_to(ROOT)): sha(p)
                          for p in [source, audit, Path(__file__).resolve()]},
        'key_dependency_sha256': {os.path.relpath(p, ROOT): sha(p) for p in dependencies},
        'stdin_sha256': hashlib.sha256(input_text.encode()).hexdigest(),
        'stdin_description': 'Exact source followed by every #print axioms command from the audit file.',
        'log': f'verification/{tag}-build-audit.log',
    }
    record = ROOT / f'verification/{tag}-run.json'
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
        valid = len(groups) == len(commands.splitlines()) and all(
            {x.strip() for x in g.split(',') if x.strip()} <= allowed for g in groups)
        rec['axiom_audit'] = {'declarations': len(groups), 'only_standard_axioms': valid}
        rec['object_sha256'] = sha(obj)
        rec['source_unchanged'] = sha(source) == rec['source_sha256'][str(source.relative_to(ROOT))]
        if not valid or not rec['source_unchanged']:
            rec['exit_code'] = 1
    record.write_text(json.dumps(rec, indent=2) + '\n')
    print(json.dumps(rec, indent=2), flush=True)
    if rec['exit_code']:
        raise SystemExit(rec['exit_code'])
