from pathlib import Path
import datetime, hashlib, json, re, subprocess, time, os
ROOT=Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT=ROOT/'verification'
record=OUT/'rs75-moment-calculus-run.json'
files=['RSBounds/InfiniteTrapezoid.lean','RSBounds/RS75MomentCalculus.lean',
       'RSBounds/BacklundTrapezoid.lean','verification/RS75MomentCalculusAudit.lean',
       'verification/run_rs75_moment_calculus_check.py']
data={'kind':'fresh-local-compilation-and-axiom-audit',
      'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'source_sha256':{f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files},
      'runs':[]}
def save():record.write_text(json.dumps(data,indent=2)+'\n')
def run(args,log):
 start=time.monotonic()
 with (OUT/log).open('w') as output:
  p=subprocess.run(args,stdout=output,stderr=subprocess.STDOUT)
 data['runs'].append({'command':args,'log':log,'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-start})
 save();print(log,p.returncode,flush=True)
 if p.returncode:
  data.update(exit_code=p.returncode,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());save();raise SystemExit(p.returncode)
save()
for name,label in [('InfiniteTrapezoid','infinite-trapezoid'),('RS75MomentCalculus','rs75-moment-calculus')]:
 run(['lake','env','lean','-j1','-o',f'.lake/build/lib/lean/RSBounds/{name}.olean',f'RSBounds/{name}.lean'],label+'-build.log')
run(['lake','env','lean','-j1','verification/RS75MomentCalculusAudit.lean'],'rs75-moment-calculus-axioms.log')
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',(OUT/'rs75-moment-calculus-axioms.log').read_text(),re.S)
allowed={'propext','Classical.choice','Quot.sound'}
assert len(sets)==13 and all({x.strip() for x in group.split(',') if x.strip()} <=allowed for group in sets)
data.update(exit_code=0,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),axiom_audit={'declarations':13,'only_standard_axioms':True});save()
