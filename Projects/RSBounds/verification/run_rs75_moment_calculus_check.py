"""Reuse the freshly checked finite telescope; compile and audit its moment application."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, time, os, resource
ROOT=Path(__file__).resolve().parents[1]; os.chdir(ROOT)
OUT=ROOT/'verification'; record=OUT/'rs75-moment-calculus-run.json'
prior=OUT/'rs75-moment-calculus-attempt1-run.json'
old=json.loads(prior.read_text())
assert old['runs'][0]['exit_code']==0
for name in ['RSBounds/InfiniteTrapezoid.lean','RSBounds/BacklundTrapezoid.lean']:
 assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==old['source_sha256'][name]
obj=ROOT/'.lake/build/lib/lean/RSBounds/InfiniteTrapezoid.olean'
assert obj.is_file()
files=['RSBounds/InfiniteTrapezoid.lean','RSBounds/RS75MomentCalculus.lean',
       'RSBounds/BacklundTrapezoid.lean','verification/RS75MomentCalculusAudit.lean',
       'verification/run_rs75_moment_calculus_check.py']
source=(ROOT/'RSBounds/RS75MomentCalculus.lean').read_text()
commands=[l for l in (OUT/'RS75MomentCalculusAudit.lean').read_text().splitlines() if l.strip() and not l.startswith('import ')]
assert len(commands)==13 and all(l.startswith('#print axioms ') for l in commands)
stdin=source+'\n'+'\n'.join(commands)+'\n'
data={'kind':'fresh-compilation-with-in-process-transitive-axiom-audit',
 'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_sha256':{f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files},
 'stdin_recipe':'Exact MomentCalculus source followed by 13 public audit commands, including the imported finite/infinite telescope.',
 'stdin_sha256':hashlib.sha256(stdin.encode()).hexdigest(),
 'checked_dependency':{'source':'RSBounds/InfiniteTrapezoid.lean','source_sha256':old['source_sha256']['RSBounds/InfiniteTrapezoid.lean'],
   'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest(),'recorded_fresh_build':old['runs'][0],
   'prior_receipt':'verification/rs75-moment-calculus-attempt1-run.json'},'runs':[]}
def save():record.write_text(json.dumps(data,indent=2)+'\n')
save();args=['lake','env','lean','-j1','-Dprofiler=true','--stdin','-o','.lake/build/lib/lean/RSBounds/RS75MomentCalculus.olean','RSBounds/RS75MomentCalculus.lean']
t=time.monotonic();r0=resource.getrusage(resource.RUSAGE_CHILDREN)
with (OUT/'rs75-moment-calculus-build.log').open('wb') as output:
 p=subprocess.run(args,input=stdin.encode(),stdout=output,stderr=subprocess.STDOUT)
r1=resource.getrusage(resource.RUSAGE_CHILDREN)
data['runs'].append({'command':args,'log':'rs75-moment-calculus-build.log','exit_code':p.returncode,'seconds':time.monotonic()-t,
 'user_cpu_seconds':r1.ru_utime-r0.ru_utime,'system_cpu_seconds':r1.ru_stime-r0.ru_stime})
data['source_hashes_unchanged_at_finish'] = all(hashlib.sha256((ROOT/f).read_bytes()).hexdigest() == h for f,h in data['source_sha256'].items())
assert data['source_hashes_unchanged_at_finish']
log=(OUT/'rs75-moment-calculus-build.log').read_text()
if not p.returncode:
 groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S)
 allowed={'propext','Classical.choice','Quot.sound'}
 assert len(groups)==13 and all({x.strip() for x in g.split(',') if x.strip()}<=allowed for g in groups)
 (OUT/'rs75-moment-calculus-axioms.log').write_text('\n'.join(re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]",log,re.S))+'\n')
 data['axiom_audit']={'declarations':13,'only_standard_axioms':True}
data.update(exit_code=p.returncode,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());save();print(json.dumps(data,indent=2),flush=True)
if p.returncode: print(log,flush=True)
raise SystemExit(p.returncode)
