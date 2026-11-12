"""Finish the scalar wrapper, auditing all exports in the same Lean process.
The previously successful base/numeric builds are reused after exact source
hash validation; their recorded failed wrapper pass remains intact.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess,time
root=Path(__file__).resolve().parents[1]
prior_path=root/'verification/rs75-zero-free-scalars-run.json'
prior=json.loads(prior_path.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f in ['RSBounds/RS75ScalarNumericsBase.lean','RSBounds/RS75ZeroFreeNumerics.lean']:
 assert sha(root/f)==prior['source_sha256'][f]
 assert any(r['exit_code']==0 and f in r['command'] for r in prior['runs'])
files=['RSBounds/RS75ZeroFreeScalars.lean','RSBounds/RS75ScalarNumericsBase.lean',
       'RSBounds/RS75ZeroFreeNumerics.lean','RSBounds/RS75Parameters.lean',
       'verification/RS75ZeroFreeScalarsAudit.lean','verification/run_rs75_zero_free_scalars_final_check.py']
lines=(root/files[4]).read_text().splitlines()
audit=[s for s in lines if s and not s.startswith('import ')]
assert len([s for s in audit if s.startswith('#print axioms ')])==16
stdin=(root/files[0]).read_text()+'\n'+'\n'.join(audit)+'\n'
record={'kind':'fresh-scalar-wrapper-with-in-process-transitive-axiom-audit',
        'started_utc':datetime.now(timezone.utc).isoformat(),
        'source_sha256':{f:sha(root/f) for f in files},
        'reused_base_numeric_receipt':str(prior_path.relative_to(root)),
        'reused_receipt_sha256':sha(prior_path),
        'reused_object_sha256':{f:sha(root/f) for f in [
           '.lake/build/lib/lean/RSBounds/RS75ScalarNumericsBase.olean',
           '.lake/build/lib/lean/RSBounds/RS75ZeroFreeNumerics.olean']},
        'stdin_recipe':'Exact wrapper source plus audit open/#print commands.',
        'stdin_sha256':hashlib.sha256(stdin.encode()).hexdigest(),'runs':[]}
receipt=root/'verification/rs75-zero-free-scalars-final-run.json'
receipt.write_text(json.dumps(record,indent=2)+'\n')
cmd=['lake','env','lean','-j1','-Dprofiler=true','--stdin','-o',
     '.lake/build/lib/lean/RSBounds/RS75ZeroFreeScalars.olean',files[0]]
log=root/'verification/rs75-zero-free-scalars-final-build.log'
t=time.monotonic()
with log.open('wb') as out:r=subprocess.run(cmd,cwd=root,input=stdin.encode(),stdout=out,stderr=subprocess.STDOUT)
record['runs'].append({'command':cmd,'log':str(log.relative_to(root)),
                      'exit_code':r.returncode,'seconds':time.monotonic()-t})
record.update(exit_code=r.returncode,finished_utc=datetime.now(timezone.utc).isoformat())
receipt.write_text(json.dumps(record,indent=2)+'\n')
if r.returncode:
 print(log.read_text());raise SystemExit(r.returncode)
text=log.read_text();groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)
assert len(groups)==16,len(groups)
assert all({x.strip() for x in g.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for g in groups)
record['axiom_audit']={'declarations':16,'only_standard_axioms':True}
receipt.write_text(json.dumps(record,indent=2)+'\n')
a=re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]",text,re.S)
(root/'verification/rs75-zero-free-scalars-final-axioms.log').write_text('\n'.join(a)+'\n')
print('Actual scalar residual and all sixteen standard-axiom audits passed.')
