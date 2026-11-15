"""Compile and audit the actual golden-ratio estimates in one Lean process."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time,resource
ROOT=Path(__file__).resolve().parents[1];os.chdir(ROOT);OUT=ROOT/'verification'
files=['RSBounds/RS75GoldenRatio.lean','RSBounds/RS75GoldenSeries.lean',
 'RSBounds/RS75GoldenScalarBase.lean','RSBounds/RS75GoldenNumerics.lean',
 'RSBounds/RS75GoldenTails.lean','RSBounds/RS75MomentCalculus.lean',
 'RSBounds/RS75Parameters.lean','RSBounds/InfiniteTrapezoid.lean',
 'RSBounds/BacklundTrapezoid.lean','verification/RS75GoldenRatioAudit.lean',
 'verification/run_rs75_golden_ratio_check.py']
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
source=(ROOT/'RSBounds/RS75GoldenRatio.lean').read_text()
audit=[s for s in (OUT/'RS75GoldenRatioAudit.lean').read_text().splitlines() if s.strip() and not s.startswith('import ')]
assert len(audit)==9 and all(s.startswith('#print axioms ') for s in audit)
stdin=source+'\n'+'\n'.join(audit)+'\n'
dependencies=['RS75GoldenSeries','RS75GoldenScalarBase','RS75GoldenNumerics',
 'RS75GoldenTails','RS75MomentCalculus','RS75Parameters','InfiniteTrapezoid','BacklundTrapezoid']
data={'kind':'fresh-actual-golden-ratio-estimates-with-in-process-axiom-audit',
 'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_sha256':{f:sha(ROOT/f) for f in files},'runs':[],
 'dependency_object_sha256':{dep:sha(ROOT/'.lake/build/lib/lean/RSBounds'/f'{dep}.olean') for dep in dependencies},
 'stdin_recipe':'Exact proof source followed only by the nine public transitive #print axioms commands.',
 'stdin_sha256':hashlib.sha256(stdin.encode()).hexdigest()}
assert data['source_sha256']['RSBounds/RS75GoldenRatio.lean']==hashlib.sha256(source.encode()).hexdigest()
record=OUT/'rs75-golden-ratio-run.json'
def save():record.write_text(json.dumps(data,indent=2)+'\n')
save()
args=['lake','env','lean','-j1','-Dprofiler=true','--stdin','-o','.lake/build/lib/lean/RSBounds/RS75GoldenRatio.olean','RSBounds/RS75GoldenRatio.lean']
log=OUT/'rs75-golden-ratio-build.log';t=time.monotonic();r0=resource.getrusage(resource.RUSAGE_CHILDREN)
with log.open('wb') as stream:r=subprocess.run(args,input=stdin.encode(),stdout=stream,stderr=subprocess.STDOUT)
r1=resource.getrusage(resource.RUSAGE_CHILDREN)
data['runs'].append({'command':args,'log':str(log.relative_to(ROOT)),'exit_code':r.returncode,'seconds':time.monotonic()-t,'user_cpu_seconds':r1.ru_utime-r0.ru_utime,'system_cpu_seconds':r1.ru_stime-r0.ru_stime,'stdin_sha256':data['stdin_sha256']});save()
print('build-and-audit',r.returncode,flush=True)
if r.returncode:data['exit_code']=r.returncode;save();raise SystemExit(r.returncode)
text=log.read_text();out=re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]",text,re.S)
(OUT/'rs75-golden-ratio-axioms.log').write_text('\n'.join(out)+'\n')
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)
assert len(sets)==9
assert all({x.strip() for x in s.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for s in sets)
data['source_hashes_unchanged_at_finish']=all(sha(ROOT/f)==h for f,h in data['source_sha256'].items())
assert data['source_hashes_unchanged_at_finish'],'A source changed during checking'
assert all(sha(ROOT/'.lake/build/lib/lean/RSBounds'/f'{dep}.olean')==h for dep,h in data['dependency_object_sha256'].items()),'A dependency object changed during checking'
data.update(exit_code=0,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),axiom_audit={'declarations':9,'only_standard_axioms':True});save()
print('9 standard-three-axiom audits passed.',flush=True)
