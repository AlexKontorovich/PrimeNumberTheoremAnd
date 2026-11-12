"""Fresh scalar assembly builds and public transitive axiom audit."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess,time
root=Path(__file__).resolve().parents[1]
sources=['RSBounds/RS75ScalarNumericsBase.lean','RSBounds/RS75ZeroFreeNumerics.lean',
         'RSBounds/RS75ZeroFreeScalars.lean','RSBounds/RS75Parameters.lean',
         'verification/RS75ZeroFreeScalarsAudit.lean','verification/run_rs75_zero_free_scalars_check.py',
         'scripts/generate_rs75_zero_free_scalars.py']
record={'kind':'fresh-actual-radical-and-logarithm-scalar-assembly',
 'started_utc':datetime.now(timezone.utc).isoformat(),
 'source_sha256':{s:hashlib.sha256((root/s).read_bytes()).hexdigest() for s in sources},'runs':[]}
receipt=root/'verification/rs75-zero-free-scalars-run.json'
jobs=[]
for name in ['RS75ScalarNumericsBase','RS75ZeroFreeNumerics','RS75ZeroFreeScalars']:
 jobs.append((['lake','env','lean','-j1','-o',f'.lake/build/lib/lean/RSBounds/{name}.olean',f'RSBounds/{name}.lean'],f'rs75-zero-free-{name}-build.log'))
jobs.append((['lake','env','lean','-j1',sources[4]],'rs75-zero-free-scalars-axioms.log'))
receipt.write_text(json.dumps(record,indent=2)+'\n')
for cmd,name in jobs:
 t=time.monotonic()
 with (root/'verification'/name).open('w') as out:
  result=subprocess.run(cmd,cwd=root,stdout=out,stderr=subprocess.STDOUT)
 record['runs'].append({'command':cmd,'log':name,'exit_code':result.returncode,'seconds':time.monotonic()-t})
 receipt.write_text(json.dumps(record,indent=2)+'\n');print(name,result.returncode,flush=True)
 if result.returncode:
  print((root/'verification'/name).read_text(),flush=True)
  record['exit_code']=result.returncode;receipt.write_text(json.dumps(record,indent=2)+'\n');raise SystemExit(result.returncode)
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',(root/'verification'/jobs[-1][1]).read_text(),re.S)
assert len(sets)==16,len(sets)
assert all({a.strip() for a in s.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'} for s in sets)
record.update(exit_code=0,finished_utc=datetime.now(timezone.utc).isoformat(),
 axiom_audit={'declarations':16,'only_standard_axioms':True})
receipt.write_text(json.dumps(record,indent=2)+'\n');print('Sixteen standard-axiom scalar audits passed.',flush=True)
