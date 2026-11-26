"""Fresh direct scalar checks only; no infinite-moment or zeta claim."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
ROOT=Path(__file__).resolve().parents[1];os.chdir(ROOT);OUT=ROOT/'verification'
files=['RSBounds/RS75GoldenScalarBase.lean','RSBounds/RS75GoldenNumerics.lean',
 'RSBounds/QuarticBudgetNumericsBase.lean','RSBounds/BacklundCenterNumericsBase.lean',
 'RSBounds/BacklundLowScalarBase.lean','scripts/generate_rs75_golden_scalar.py',
 'verification/rs75-golden-moments-diagnostic.py','verification/RS75GoldenNumericsAudit.lean',
 'verification/run_rs75_golden_numerics_check.py']
data={'kind':'fresh-finite-scalar-build-and-axiom-audit','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_sha256':{f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files},'runs':[],
 'scope':'Bounds on actual finite moment centers and their explicit error expressions; no analytic infinite-tail or zeta-derivative binding asserted.'}
record=OUT/'rs75-golden-numerics-run.json'
def save():record.write_text(json.dumps(data,indent=2)+'\n')
save()
for name,src,out in [('base','RSBounds/RS75GoldenScalarBase.lean','.lake/build/lib/lean/RSBounds/RS75GoldenScalarBase.olean'),
 ('numerics','RSBounds/RS75GoldenNumerics.lean','.lake/build/lib/lean/RSBounds/RS75GoldenNumerics.olean'),
 ('axioms','verification/RS75GoldenNumericsAudit.lean',None)]:
 args=['lake','env','lean','-j1']+(['-o',out] if out else [])+[src]
 log=OUT/f'rs75-golden-{name}.log';t=time.monotonic()
 with log.open('wb') as stream:r=subprocess.run(args,stdout=stream,stderr=subprocess.STDOUT)
 data['runs'].append({'command':args,'log':str(log.relative_to(ROOT)),'exit_code':r.returncode,'seconds':time.monotonic()-t});save()
 print(name,r.returncode,flush=True)
 if r.returncode:
  data['exit_code']=r.returncode;save();raise SystemExit(r.returncode)
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',(OUT/'rs75-golden-axioms.log').read_text(),re.S)
assert len(sets)==7
assert all({x.strip() for x in s.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for s in sets)
data.update(exit_code=0,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),axiom_audit={'declarations':7,'only_standard_axioms':True});save()
print('7 standard-three-axiom audits passed.',flush=True)
