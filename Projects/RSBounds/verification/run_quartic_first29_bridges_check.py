"""Check scalar-to-analytic budget identities without rebuilding their inputs."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess

root=Path(__file__).resolve().parent.parent
sources=['RSBounds/QuarticFirst29BudgetBridges.lean',
         'verification/QuarticFirst29BudgetBridgesAudit.lean']
record={'kind':'scalar-analytic-bridge-compilation-and-axiom-audit',
        'started_utc':datetime.now(timezone.utc).isoformat(),
        'source_sha256':{s:hashlib.sha256((root/s).read_bytes()).hexdigest() for s in sources},
        'runs':[]}
jobs=[(['lake','env','lean','-j1','-o',
        '.lake/build/lib/lean/RSBounds/QuarticFirst29BudgetBridges.olean',sources[0]],
       'quartic-first29-bridges-build.log'),
      (['lake','env','lean','-j1',sources[1]],'quartic-first29-bridges-axioms.log')]
receipt=root/'verification/quartic-first29-bridges-run.json'
for cmd,name in jobs:
    print('Checking '+cmd[-1],flush=True)
    with (root/'verification'/name).open('w') as output:
        result=subprocess.run(cmd,cwd=root,stdout=output,stderr=subprocess.STDOUT)
    record['runs'].append({'command':cmd,'log':name,'exit_code':result.returncode})
    if result.returncode:
        record['status']='failed';receipt.write_text(json.dumps(record,indent=2)+'\n')
        print((root/'verification'/name).read_text(),flush=True)
        raise SystemExit(result.returncode)
sets=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',
                (root/'verification'/jobs[-1][1]).read_text())
assert len(sets)==16,len(sets)
assert all({a.strip() for a in s.split(',') if a.strip()} <=
           {'propext','Classical.choice','Quot.sound'} for s in sets)
record['printed_axiom_sets']=16;record['only_standard_axioms']=True
record['status']='verified';record['finished_utc']=datetime.now(timezone.utc).isoformat()
receipt.write_text(json.dumps(record,indent=2)+'\n')
print('Scalar bridge module and sixteen axiom audits verified',flush=True)
