#!/usr/bin/env python3
"""Compile every test source afresh, with bounded per-file process groups.

Run `lake build Blaster:shared` first. This checks source files rather than replaying
cached Lake messages. Aggregate modules can be blocked by missing test oleans;
those are recorded separately from reconstruction failures.
"""
import argparse, concurrent.futures, hashlib, json, os, pathlib, re, signal, subprocess, time
p=argparse.ArgumentParser()
p.add_argument('--mode', choices=['strict','normal','checked'], default='strict')
p.add_argument('--out', required=True)
p.add_argument('--limit', type=int, default=120)
p.add_argument('--workers', type=int, default=4)
p.add_argument('files', nargs='*')
a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[1]
native=next(p for p in (root/'.lake/build/lib').glob('libBlaster.*') if p.suffix in ('.dylib','.so'))
out=pathlib.Path(a.out);out.mkdir(parents=True,exist_ok=True)
files=[pathlib.Path(f) for f in a.files] if a.files else sorted(root.glob('Tests/**/*.lean'))+[root/'Tests.lean']
env=os.environ.copy()
for key in ['BLASTER_GEN_PROOF','BLASTER_RECONSTRUCT','BLASTER_SMTPROOF_LOG','BLASTER_SMTPROOF_DUMP','BLASTER_SMTPROOF_PROOFDUMP','BLASTER_SMTPROOF_PROOFFILE']:
    env.pop(key,None)
env['LEAN_NUM_THREADS']='2'
if a.mode=='strict':env['BLASTER_GEN_PROOF']='1'
if a.mode=='checked':env['BLASTER_RECONSTRUCT']='2'
meta=dict(commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),diff_sha256=hashlib.sha256(subprocess.check_output(['git','diff','--binary','--','Blaster','Tests'],cwd=root)).hexdigest(),proof_backends=env.get('BLASTER_SMTPROOF_BACKENDS','automatic arithmetic profile; z3,z3rec,z3+ fallback'),proof_timeout=env.get('BLASTER_SMTPROOF_TIMEOUT','per option, default 20s'),seeds=env.get('BLASTER_SMTPROOF_SEEDS','backend default'))
meta.update(execution='fresh Lean with the compiled Blaster library',native_sha256=hashlib.sha256(native.read_bytes()).hexdigest())
meta['certificate_replay']=env.get('BLASTER_SMTPROOF_CERTIFICATES','0')
(out/'metadata.json').write_text(json.dumps(meta,indent=2))
# Use the branch's default proof-producing portfolio and timeout.
def run(path):
    rel=str(path.relative_to(root) if path.is_absolute() else path)
    log=out/(rel.replace('/','__')+'.log')
    start=time.monotonic();timed_out=False
    with log.open('w') as h:
        proc=subprocess.Popen(['lake','env','lean',f'--load-dynlib={native}',rel],cwd=root,stdout=h,stderr=subprocess.STDOUT,env=env,start_new_session=True)
        try:code=proc.wait(timeout=a.limit)
        except subprocess.TimeoutExpired:
            timed_out=True
            os.killpg(proc.pid,signal.SIGTERM)
            try:proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL);proc.wait()
            code=proc.returncode
    s=log.read_text(errors='replace')
    errors=re.findall(r'^.*?:\d+:\d+: error(?:\([^)]*\))?: (.*)$',s,re.M)
    status='timeout' if timed_out else 'passed' if code==0 else 'crashed' if code<0 or 'Stack overflow detected' in s or 'libc++abi: terminating' in s else 'dependency-blocked' if "object file '" in s and 'does not exist' in s else 'failed'
    return dict(file=rel,mode=a.mode,status=status,exit_code=code,seconds=round(time.monotonic()-start,2),errors=errors,unexpected_undetermined=s.count('⚠️ Undetermined'),checked_proofs=s.count('📜 Proof generated'),reconstructed=s.count('🔒 Kernel-checked proof reconstructed'),log=str(log))
results=[];started=time.time()
with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
    for f in concurrent.futures.as_completed([pool.submit(run,path) for path in files]):
        r=f.result();results.append(r)
        (out/'results.json').write_text(json.dumps(dict(mode=a.mode,limit=a.limit,workers=a.workers,started=started,results=sorted(results,key=lambda r:r['file'])),indent=2))
        print(f"{len(results)}/{len(files)} {r['status']} {r['file']} ({r['seconds']}s) proofs={r['checked_proofs']} errors={len(r['errors'])}",flush=True)
counts={status:sum(r['status']==status for r in results) for status in ['passed','failed','crashed','timeout','dependency-blocked']}
print(json.dumps(dict(counts=counts,checked_proofs=sum(r['checked_proofs'] for r in results),seconds=round(time.time()-started,2))),flush=True)
