"""Compile the exact GoldenTails source and audit its exports in one process."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, time, os, resource
ROOT=Path(__file__).resolve().parents[1]; os.chdir(ROOT)
OUT=ROOT/'verification'; record=OUT/'rs75-golden-tails-run.json'
files=['RSBounds/RS75GoldenTails.lean','verification/RS75GoldenTailsAudit.lean','verification/run_rs75_golden_tails_check.py']
dependencies=['RS75MomentCalculus','RS75GoldenSeries','RS75GoldenNumerics']
files += ['RSBounds/'+dep+'.lean' for dep in dependencies]
source=(ROOT/files[0]).read_text()
commands=[l for l in (ROOT/files[1]).read_text().splitlines() if l.strip() and not l.startswith('import ')]
assert len(commands)==5 and all(l.startswith('#print axioms ') for l in commands)
stdin=source+'\n'+'\n'.join(commands)+'\n'
data={'kind':'fresh-compilation-with-in-process-transitive-axiom-audit','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
'source_sha256':{f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files},
'stdin_recipe':'Exact proof source, newline, then the five public audit commands.',
'stdin_sha256':hashlib.sha256(stdin.encode()).hexdigest(),
'dependency_object_sha256':{dep:hashlib.sha256((ROOT/'.lake/build/lib/lean/RSBounds'/f'{dep}.olean').read_bytes()).hexdigest() for dep in dependencies},'runs':[]}
def save():record.write_text(json.dumps(data,indent=2)+'\n')
save(); args=['lake','env','lean','-j1','-Dprofiler=true','--stdin','-o','.lake/build/lib/lean/RSBounds/RS75GoldenTails.olean','RSBounds/RS75GoldenTails.lean']
t=time.monotonic();r0=resource.getrusage(resource.RUSAGE_CHILDREN)
with (OUT/'rs75-golden-tails-build.log').open('wb') as output:
 p=subprocess.run(args,input=stdin.encode(),stdout=output,stderr=subprocess.STDOUT)
r1=resource.getrusage(resource.RUSAGE_CHILDREN)
data['runs'].append({'command':args,'log':'rs75-golden-tails-build.log','exit_code':p.returncode,'seconds':time.monotonic()-t,'user_cpu_seconds':r1.ru_utime-r0.ru_utime,'system_cpu_seconds':r1.ru_stime-r0.ru_stime})
data['source_hashes_unchanged_at_finish'] = all(hashlib.sha256((ROOT/f).read_bytes()).hexdigest() == h for f,h in data['source_sha256'].items())
assert data['source_hashes_unchanged_at_finish']
log=(OUT/'rs75-golden-tails-build.log').read_text()
if not p.returncode:
 groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S)
 allowed={'propext','Classical.choice','Quot.sound'}
 assert len(groups)==5 and all({x.strip() for x in g.split(',') if x.strip()}<=allowed for g in groups)
 (OUT/'rs75-golden-tails-axioms.log').write_text('\n'.join(re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^]]*\]",log,re.S))+'\n')
 data['axiom_audit']={'declarations':5,'only_standard_axioms':True}
data.update(exit_code=p.returncode,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());save();print(json.dumps(data,indent=2),flush=True)
if p.returncode: print(log,flush=True)
raise SystemExit(p.returncode)
