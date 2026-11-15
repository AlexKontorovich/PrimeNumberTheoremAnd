"""Fresh elementary RS75 parameter build and transitive axiom audit."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,subprocess,time
root=Path(__file__).resolve().parents[1]
sources=['RSBounds/RS75Parameters.lean','verification/RS75ParametersAudit.lean',
         'verification/run_rs75_parameters_check.py']
receipt=root/'verification/rs75-parameters-run.json'
record={'kind':'fresh-elementary-parameters-build-and-axiom-audit',
        'started_utc':datetime.now(timezone.utc).isoformat(),
        'source_sha256':{s:hashlib.sha256((root/s).read_bytes()).hexdigest() for s in sources},
        'runs':[]}
receipt.write_text(json.dumps(record,indent=2)+'\n')
jobs=[(['lake','env','lean','-j1','-o','.lake/build/lib/lean/RSBounds/RS75Parameters.olean',sources[0]],'rs75-parameters-build.log'),
      (['lake','env','lean','-j1',sources[1]],'rs75-parameters-axioms.log')]
for cmd,name in jobs:
 t=time.monotonic()
 with (root/'verification'/name).open('w') as out:
  result=subprocess.run(cmd,cwd=root,stdout=out,stderr=subprocess.STDOUT)
 record['runs'].append({'command':cmd,'log':name,'exit_code':result.returncode,'seconds':time.monotonic()-t})
 receipt.write_text(json.dumps(record,indent=2)+'\n')
 print(name,result.returncode,flush=True)
 if result.returncode:
  print((root/'verification'/name).read_text(),flush=True)
  record['exit_code']=result.returncode;receipt.write_text(json.dumps(record,indent=2)+'\n')
  raise SystemExit(result.returncode)
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',(root/'verification'/jobs[1][1]).read_text(),re.S)
assert len(sets)==21,len(sets)
assert all({x.strip() for x in a.split(',') if x.strip()}<= {'propext','Classical.choice','Quot.sound'} for a in sets)
record.update(exit_code=0,finished_utc=datetime.now(timezone.utc).isoformat(),
              axiom_audit={'declarations':21,'only_standard_axioms':True})
receipt.write_text(json.dumps(record,indent=2)+'\n')
print('Twenty-one standard-axiom parameter audits passed.',flush=True)
