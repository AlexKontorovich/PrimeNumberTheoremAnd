"""Fresh check of the scalar budget on the entire x >= exp23 range."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path(__file__).resolve().parent.parent
sources = ['RSBounds/QuarticFirst29BudgetApplication.lean',
           'verification/QuarticFirst29BudgetApplicationAudit.lean']
record = {
    'kind': 'uniform-scalar-budget-compilation-and-axiom-audit',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'source_sha256': {s:hashlib.sha256((root/s).read_bytes()).hexdigest() for s in sources},
    'full_psi_estimate_proved': False,
    'runs': [],
}
receipt = root / 'verification/quartic-first29-application-run.json'
jobs = [
    (['lake','env','lean','-j1','-o',
      '.lake/build/lib/lean/RSBounds/QuarticFirst29BudgetApplication.olean',sources[0]],
     'quartic-first29-application-build.log'),
    (['lake','env','lean','-j1',sources[1]],'quartic-first29-application-axioms.log'),
]
for command, logname in jobs:
    print('Checking '+command[-1],flush=True)
    with (root/'verification'/logname).open('w') as output:
        result=subprocess.run(command,cwd=root,stdout=output,stderr=subprocess.STDOUT)
    record['runs'].append({'command':command,'log':logname,'exit_code':result.returncode})
    if result.returncode:
        record['status']='failed'
        receipt.write_text(json.dumps(record,indent=2)+'\n')
        print((root/'verification'/logname).read_text(),flush=True)
        raise SystemExit(result.returncode)
sets=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',
                (root/'verification'/jobs[-1][1]).read_text())
assert len(sets)==8,len(sets)
assert all({a.strip() for a in s.split(',') if a.strip()} <=
           {'propext','Classical.choice','Quot.sound'} for s in sets)
record['printed_axiom_sets']=8
record['only_standard_axioms']=True
record['status']='verified'
record['finished_utc']=datetime.now(timezone.utc).isoformat()
receipt.write_text(json.dumps(record,indent=2)+'\n')
print('Uniform scalar budget and eight axiom audits verified',flush=True)
