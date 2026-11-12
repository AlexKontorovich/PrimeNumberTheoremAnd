"""Compile exact optimization algebra and audit exports in the same process."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess,time
root=Path(__file__).resolve().parents[1]
files=['RSBounds/RS75ZeroFreeOptimization.lean','RSBounds/RS75ZeroFreeScalars.lean',
       'RSBounds/RS75ZeroFreeNumerics.lean','verification/RS75ZeroFreeOptimizationAudit.lean',
       'verification/run_rs75_zero_free_optimization_check.py']
audit=[x for x in (root/files[3]).read_text().splitlines() if x.startswith('#print axioms ')]
assert len(audit)==8
stdin=(root/files[0]).read_text()+'\n'+'\n'.join(audit)+'\n'
data={'kind':'fresh-optimization-build-with-in-process-transitive-axiom-audit',
      'started_utc':datetime.now(timezone.utc).isoformat(),
      'source_sha256':{f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files},
      'stdin_recipe':'Exact source plus eight fully qualified #print axioms commands.',
      'stdin_sha256':hashlib.sha256(stdin.encode()).hexdigest(),'runs':[]}
receipt=root/'verification/rs75-zero-free-optimization-run.json'
receipt.write_text(json.dumps(data,indent=2)+'\n')
cmd=['lake','env','lean','-j1','-Dprofiler=true','--stdin','-o',
     '.lake/build/lib/lean/RSBounds/RS75ZeroFreeOptimization.olean',files[0]]
t=time.monotonic();log=root/'verification/rs75-zero-free-optimization-build.log'
with log.open('wb') as out:r=subprocess.run(cmd,cwd=root,input=stdin.encode(),stdout=out,stderr=subprocess.STDOUT)
data['runs'].append({'command':cmd,'log':str(log.relative_to(root)),
                     'exit_code':r.returncode,'seconds':time.monotonic()-t})
data['build_exit_code']=r.returncode
if r.returncode:data['exit_code']=r.returncode
receipt.write_text(json.dumps(data,indent=2)+'\n')
if r.returncode:
 print(log.read_text());raise SystemExit(r.returncode)
text=log.read_text();groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)
assert len(groups)==8,len(groups)
assert all({x.strip() for x in s.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for s in groups)
data['axiom_audit']={'declarations':8,'only_standard_axioms':True}
data.update(exit_code=0,finished_utc=datetime.now(timezone.utc).isoformat())
receipt.write_text(json.dumps(data,indent=2)+'\n')
a=re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]",text,re.S)
(root/'verification/rs75-zero-free-optimization-axioms.log').write_text('\n'.join(a)+'\n')
print('Exact optimization algebra and eight standard-axiom audits passed.')
