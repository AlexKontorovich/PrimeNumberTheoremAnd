"""Replay the pinned 99-module RH100 closure, sequentially, on the local Lean.

Uses the existing Mathlib oleans and no upstream memory gate. The pristine
source snapshot is read only. Adaptations live separately in vendor/rh100.
Each successful module is cached by source, transitive imports, toolchain,
and options. A final pinned-type and transitive-axiom audit runs after the
whole closure succeeds. --limit N is an explicitly partial resource probe.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import fcntl
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
SNAPSHOT = ROOT.parent / 'sources/zeta-lab-rh100'
SOURCE = ROOT / 'vendor/rh100'
OUT = ROOT / '.lake/build/lib/lean'
LOGS = ROOT / 'verification/rh100-replay'
RECORD = ROOT / 'verification/rh100-replay-run.json'
EXTERNAL_SNAPSHOT = (SNAPSHOT / 'source-manifest.json').exists()
MANIFEST_PATH = SOURCE / 'upstream-source-manifest.json'
MANIFEST = json.loads(MANIFEST_PATH.read_text())
FILES = {f['module']: f for f in MANIFEST['files']}


def stamp():
    return datetime.now(timezone.utc).isoformat()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def strip_comments(text):
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        c = text[i]
        if depth:
            if pair == '/-': depth += 1; i += 2; continue
            if pair == '-/': depth -= 1; i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if string:
            if c == '\\': out.extend('  '); i += 2; continue
            if c == '"': string = False
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if pair == '/-': depth = 1; out.extend('  '); i += 2; continue
        if pair == '--':
            j = text.find('\n', i)
            if j == -1: j = len(text)
            out.extend(' ' * (j-i)); i = j; continue
        if c == '"': string = True; out.append(' '); i += 1; continue
        out.append(c); i += 1
    return ''.join(out)


def module_options(mod):
    if mod.startswith('Zeta23.'):
        return ['-DrelaxedAutoImplicit=false', '-Dpp.unicode.fun=true']
    if mod.startswith(('RHHeight.', 'RHHeight100.')):
        return ['-DautoImplicit=false', '-DrelaxedAutoImplicit=false']
    return []


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int, default=None)
    parser.add_argument('--fresh', action='store_true')
    parser.add_argument('--only', help='Comma-separated independent module names (no final audit)')
    parser.add_argument('--record', help='Separate worker checkpoint path, relative to project root')
    args = parser.parse_args()
    record_path = ROOT / args.record if args.record else RECORD
    selected = set(args.only.split(',')) if args.only else None
    if selected is not None:
        assert args.record, '--only requires a separate --record checkpoint'
        assert selected <= set(FILES), 'Unknown selected module'
    receipts = LOGS / 'receipts'
    receipts.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    dependencies, hashes = {}, {}
    for mod, item in FILES.items():
        if EXTERNAL_SNAPSHOT:
            pristine = (SNAPSHOT / item['local_path']).read_bytes()
            assert sha(pristine) == item['sha256'], 'Snapshot changed: ' + mod
        path = SOURCE / item['local_path']
        hashes[mod] = sha(path.read_bytes())
        clean = strip_comments(path.read_text())
        imports = re.findall(r'^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)', clean, re.M)
        unknown = [m for m in imports if m not in FILES and not m.startswith(
            ('Mathlib', 'Lean', 'Batteries', 'Aesop', 'Qq', 'Std'))]
        assert not unknown, (mod, unknown)
        dependencies[mod] = [m for m in imports if m in FILES]
    order, visiting, done = [], set(), set()
    def visit(mod):
        assert mod not in visiting, 'Import cycle: ' + mod
        if mod in done: return
        visiting.add(mod)
        for dependency in dependencies[mod]: visit(dependency)
        visiting.remove(mod); done.add(mod); order.append(mod)
    visit(MANIFEST['root_module'])
    assert len(order) == 99 and set(order) == set(FILES)
    lean = subprocess.check_output(['which', 'lean'], text=True).strip()
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    manifest_bytes = (ROOT / 'lake-manifest.json').read_bytes()
    mathlib_manifest = [p for p in json.loads(manifest_bytes)['packages'] if p['name'] == 'mathlib']
    mathlib_signature = sha(json.dumps(mathlib_manifest, sort_keys=True).encode())
    env = os.environ.copy()
    env['LEAN_PATH'] = subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
    env['LEAN_NUM_THREADS'] = '1'
    previous = json.loads(record_path.read_text()) if record_path.exists() else {}
    cached = {r['module']:r for r in previous.get('modules', []) if r.get('exit_code') == 0}
    record = {'kind':'sequential-local-RH100-replay', 'started_utc':stamp(),
              'upstream_repository':MANIFEST['repository'], 'upstream_commit':MANIFEST['commit'],
              'toolchain':version, 'mathlib_manifest':mathlib_manifest, 'root_module':MANIFEST['root_module'],
              'closure_size':len(order), 'topological_order':order,
              'pristine_snapshot_verified':EXTERNAL_SNAPSHOT,
              'source_manifest_sha256':sha(MANIFEST_PATH.read_bytes()),
              'source_manifest_location':str(MANIFEST_PATH),
              'selected_modules':sorted(selected) if selected else None,
              'modules':[], 'status':'running'}
    signatures = {}
    def save():
        temp = record_path.with_suffix('.tmp')
        temp.write_text(json.dumps(record, indent=2)+'\n'); temp.replace(record_path)
    save()
    started_count = 0
    for mod in order:
        item = FILES[mod]
        options = module_options(mod)
        signature = sha(json.dumps([hashes[mod], version, mathlib_signature, options,
            [signatures[x] for x in dependencies[mod]]], sort_keys=True).encode())
        signatures[mod] = signature
        if selected is not None and mod not in selected:
            continue
        target = OUT / (mod.replace('.', '/')+'.olean')
        lock = receipts / (mod + '.lock')
        with lock.open('a') as lock_file:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
            old = cached.get(mod)
            receipt = receipts / (mod + '.json')
            if receipt.exists():
                independent = json.loads(receipt.read_text())
                if independent.get('signature') == signature and independent.get('exit_code') == 0:
                    old = independent
            if not args.fresh and old and old.get('signature') == signature and target.exists() and old.get('olean_sha256') == sha(target.read_bytes()):
                row = dict(old); row['reused_from_previous_replay'] = True
                record['modules'].append(row); save(); continue
            if args.limit is not None and started_count >= args.limit:
                record['status']='partial-resource-probe'; record['finished_utc']=stamp(); save()
                print(f"Partial probe finished: {started_count} new modules; {len(record['modules'])}/{len(order)} checked", flush=True)
                return 0
            target.parent.mkdir(parents=True, exist_ok=True)
            log = LOGS/(mod+'.log'); metrics = LOGS/(mod+'.resources.json')
            cmd = [lean, '-j1', '--root='+str(SOURCE), *options,
                   item['local_path'], '-o', str(target)]
            begin = time.monotonic(); start_utc=stamp()
            print(f"Checking {len(record['modules'])+1}/{len(order)} {mod}", flush=True)
            with log.open('w') as output:
                process = subprocess.Popen(cmd, cwd=SOURCE, env=env, stdout=output, stderr=subprocess.STDOUT)
                _, status, usage = os.wait4(process.pid, 0)
                process.returncode = os.waitstatus_to_exitcode(status)
            elapsed = time.monotonic()-begin
            metrics.write_text(json.dumps({'user_seconds':usage.ru_utime, 'system_seconds':usage.ru_stime,
                'peak_rss_kib':usage.ru_maxrss, 'elapsed_seconds':elapsed}, indent=2)+'\n')
            row={'module':mod, 'source_sha256':hashes[mod], 'upstream_sha256':item['sha256'],
                 'adapted': hashes[mod] != item['sha256'], 'signature':signature,
                 'command':cmd, 'started_utc':start_utc, 'finished_utc':stamp(),
                 'elapsed_seconds':round(elapsed,3), 'peak_rss_kib':usage.ru_maxrss,
                 'log':str(log.relative_to(ROOT)), 'resources':str(metrics.relative_to(ROOT)),
                 'exit_code':process.returncode,
                 'olean_sha256':sha(target.read_bytes()) if process.returncode == 0 else None}
            record['modules'].append(row); started_count += 1; save()
            if process.returncode == 0:
                temp_receipt = receipt.with_suffix('.tmp')
                temp_receipt.write_text(json.dumps(row, indent=2)+'\n')
                temp_receipt.replace(receipt)
            print(f"  exit={process.returncode}, {elapsed:.1f}s, peakRSS={row['peak_rss_kib']} KiB", flush=True)
            if process.returncode:
                record['status']='compilation-failed'; record['finished_utc']=stamp(); save()
                return process.returncode
    if selected is not None:
        record['status']='verified-independent-subset'
        record['finished_utc']=stamp(); save()
        print(f'Independent subset finished: {len(record["modules"])} checked', flush=True)
        return 0
    check=SOURCE/'CheckMain100.lean'; log=LOGS/'CheckMain100.log'
    cmd=[lean, '-j1', '--root='+str(SOURCE), '-DautoImplicit=false',
         '-DrelaxedAutoImplicit=false', str(check)]
    with log.open('w') as output:
        result=subprocess.run(cmd,cwd=SOURCE,env=env,stdout=output,stderr=subprocess.STDOUT)
    text=log.read_text()
    sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)
    allowed={'propext','Classical.choice','Quot.sound'}
    audits_ok=bool(sets) and all({x.strip() for x in group.split(',')} <= allowed for group in sets)
    record['final_audit']={'command':cmd,'log':str(log.relative_to(ROOT)),
        'source_sha256':sha(check.read_bytes()),'exit_code':result.returncode,
        'printed_axiom_sets':len(sets),'only_standard_axioms':audits_ok}
    record['finished_utc']=stamp()
    record['status']='verified' if result.returncode == 0 and audits_ok else 'final-audit-failed'
    save()
    print(record['status']+f", {len(sets)} audited theorem closures",flush=True)
    return 0 if record['status']=='verified' else 1

if __name__ == '__main__':
    raise SystemExit(main())
