#!/usr/bin/env python3
"""Run native Lake Cardano prep benchmarks, serially, with resource bounds.

Dependencies must already be built. Every run regenerates just the target
module, preserving its Lean names and deleting only its own compiled output.
"""
import argparse
import hashlib
import json
import os
import platform
from pathlib import Path
import re
import signal
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', type=Path, required=True, help='Directory containing cardano/, wsc/, blaster/ and the two PlutusCore copies')
parser.add_argument('--label', required=True)
parser.add_argument('--cases', nargs='+', default=['sellnft:1800','minting:1200','paramfeed:10000','governance:9000','global:1600'])
parser.add_argument('--repeat', type=int, default=1)
parser.add_argument('--timeout', type=float, default=300)
parser.add_argument('--max-rss-gib', type=float, default=16)
parser.add_argument('--sample', action='store_true', help='Take one macOS CPU sample; use separate runs from timing comparisons')
parser.add_argument('--reduce-before-arguments', action='store_true', help='Reduce functions and projections before normalizing their arguments')
parser.add_argument('--retain-constructor-choices', action='store_true', help='Keep conditionals and matches inside constructor fields during preparation')
parser.add_argument('--retain-choice-types', nargs='*', default=[], help='Label selected inductive types or constructors to retain field choices')
parser.add_argument('--proofs-only', action='store_true', help='Check properties against the existing, exactly matching prepared benchmark module')
a=parser.parse_args()
if a.repeat < 1 or a.timeout <= 0 or a.max_rss_gib <= 0:
    parser.error('repeat, timeout and memory limit must be positive')
if not re.fullmatch(r'[A-Za-z0-9_-]+', a.label):
    parser.error('label must contain only letters, digits, underscore or hyphen')
if any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', n) for n in a.retain_choice_types):
    parser.error('retain-choice-types must be fully qualified Lean declaration names')
root=a.root.resolve()
logs=root/'results'/a.label
logs.mkdir(parents=True,exist_ok=True)
fixture_names={'sellnft':'SellNFT','minting':'MintingPolicy','paramfeed':'ParamFeed','governance':'Governance','hello':'HelloWorld','unlock':'UnlockPIN'}

def output(cmd,cwd=None):
    return subprocess.check_output(cmd,cwd=cwd,text=True).strip()

def snapshot(parent):
    lines=output(['ps','-axo','pid=,ppid=,rss=,comm=']).splitlines()
    entries=[]
    for line in lines:
        cols=line.split(None,3)
        if len(cols)==4:
            entries.append((int(cols[0]),int(cols[1]),int(cols[2])*1024,cols[3]))
    ids={parent}
    while True:
        more={pid for pid,ppid,_,_ in entries if ppid in ids}
        if more<=ids: break
        ids|=more
    return [e for e in entries if e[0] in ids]

def pin(pkg):
    path=root/pkg
    diff=subprocess.check_output(['git','-c','core.fsmonitor=false','diff','HEAD'],cwd=path)
    return {'commit':output(['git','rev-parse','HEAD'],path),'tracked_patch_sha256':hashlib.sha256(diff).hexdigest()}

result={'label':a.label,'repeat':a.repeat,'timeout_seconds':a.timeout,'rss_limit_bytes':int(a.max_rss_gib*2**30),
        'lean':output(['lake','env','lean','--version'],root/'cardano'),
        'pins':{p:pin(p) for p in ['cardano','wsc','blaster','plutuscore','plutuscore-wsc']},
        'machine':{'system':platform.system(),'release':platform.release(),'architecture':platform.machine(),'logical_cpus':os.cpu_count()},
        'runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'retain_choice_types':a.retain_choice_types,'retain_constructor_choices':a.retain_constructor_choices,'reduce_before_arguments':a.reduce_before_arguments,
        'cpu_sample':a.sample,'phase':'proof' if a.proofs_only else 'prep',
        'allocator_env':{k:v for k,v in os.environ.items() if k.startswith('MIMALLOC_')},'runs':[]}

def save():
    (logs/'results.json').write_text(json.dumps(result,indent=2)+'\n')

for case in a.cases:
    name,raw_budget=case.split(':');budget=int(raw_budget)
    if name=='global':
        cwd=root/'wsc'
        text=f'''import WSC.Prep.GlobalImport
import Blaster
set_option maxHeartbeats 0
namespace WSC.Benchmark
#prep_uplc appliedGlobalPerf programmableLogicGlobal1600 WSC.globalInputs1600 {budget}
end WSC.Benchmark
'''
    else:
        cwd=root/'cardano';fixture=fixture_names[name]
        text=(cwd/f'Tests/Scripts/{fixture}/{fixture}.lean').read_text()
        text=re.sub(r'\(stats-file: [^)]*\)|\(stats-interval: [^)]*\)','',text)
        text=re.sub(r'(#prep_uplc[^\n]*?)\d+\s*\n',lambda m:m[1]+str(budget)+'\n',text)
        text=text.replace('\nnamespace ', '\nset_option maxHeartbeats 0\nnamespace ',1)
    if a.reduce_before_arguments:
        text=text.replace('set_option maxHeartbeats 0', 'set_option blaster.reduceBeforeArguments true\nset_option maxHeartbeats 0')
    if a.retain_constructor_choices:
        text=text.replace('set_option maxHeartbeats 0', 'set_option blaster.hoistConstructorChoices false\nset_option maxHeartbeats 0')
    if a.retain_choice_types:
        text=text.replace('set_option maxHeartbeats 0', 'attribute [local blaster_keep_choices] ' + ' '.join(a.retain_choice_types) + '\nset_option maxHeartbeats 0')
    source=cwd/'Tests/Benchmarks/CardanoPerfCase.lean'
    source.parent.mkdir(parents=True,exist_ok=True)
    module='CardanoPerfCase'
    if a.proofs_only:
        if not source.exists() or source.read_text()!=text:
            raise SystemExit('Prepare the requested case and budget first; the existing module does not match.')
        if name=='global':
            text='''import Tests.Benchmarks.CardanoPerfCase
import Blaster
set_option maxHeartbeats 0
set_option warn.sorry false
namespace WSC.Benchmark
open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext ScriptInfo TxInfo)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)
-- The production global validator rejects the SeizeAct redeemer arm.
-- Other fields, transaction info, purpose and parameter remain symbolic.
theorem seize_arm_rejected :
    ∀ (ppCS : CurrencySymbol) (tin : TxInfo) (sinfo : ScriptInfo) (flds : List Data),
      isUnsuccessful (appliedGlobalPerf.prop ppCS ⟨tin, Data.Constr 1 flds, sinfo⟩) := by
  blaster (timeout: 30)
end WSC.Benchmark
'''
        else:
            text=(cwd/f'Tests/Scripts/{fixture}/Properties.lean').read_text()
            text=text.replace(f'import Tests.Scripts.{fixture}.{fixture}', 'import Tests.Benchmarks.CardanoPerfCase')
            if name=='governance':
                text=text[:text.index('/-- Governance script successful for a minFeeB')]+'end Tests.Scripts.Governance\n'
            text=text.replace('\nnamespace ', '\nset_option maxHeartbeats 0\nnamespace ',1)
            text=re.sub(r'\bblaster\b', 'blaster (timeout: 30)', text)
        module='CardanoPerfProofs'
        source=cwd/f'Tests/Benchmarks/{module}.lean'
    for rep in range(a.repeat):
        source.write_text(text)
        # This file belongs exclusively to this runner in the isolated checkout.
        for suffix in ['olean','olean.hash','ilean','ilean.hash','trace']:
            (cwd/f'.lake/build/lib/lean/Tests/Benchmarks/{module}.{suffix}').unlink(missing_ok=True)
        tag=f'{name}-{budget}-{rep+1}'
        log=logs/(tag+'.log')
        row={'case':name,'budget':budget,'repeat':rep+1,'status':'running','log':str(log),
             'sampled_peak_rss_bytes':0,'prep':{},'source_sha256':hashlib.sha256(text.encode()).hexdigest()}
        result['runs'].append(row);save()
        env=os.environ.copy();env['BLASTER_PREP_METRICS']='1'
        started=time.monotonic();sampler=None;sampled=False;next_checkpoint=started+5
        with log.open('w') as f:
            proc=subprocess.Popen(['lake','build',f'Tests.Benchmarks.{module}'],cwd=cwd,env=env,
                stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                while proc.poll() is None:
                    entries=snapshot(proc.pid)
                    rss=sum(e[2] for e in entries)
                    row['sampled_peak_rss_bytes']=max(row['sampled_peak_rss_bytes'],rss)
                    elapsed=time.monotonic()-started
                    if time.monotonic() >= next_checkpoint:
                        row['elapsed_seconds']=elapsed
                        save()
                        next_checkpoint=time.monotonic()+5
                    if a.sample and not sampled and elapsed>10:
                        lean=[e for e in entries if Path(e[3]).name=='lean']
                        if lean:
                            target=max(lean,key=lambda e:e[2])[0]
                            sampler=subprocess.Popen(['/usr/bin/sample',str(target),'5','10','-file',str(logs/(tag+'.sample.txt'))],stdout=f,stderr=subprocess.STDOUT)
                            sampled=True
                    if elapsed>a.timeout or rss>result['rss_limit_bytes']:
                        row['status']='timeout' if elapsed>a.timeout else 'memory_limit'
                        os.killpg(proc.pid,signal.SIGKILL)
                        proc.wait()
                        break
                    time.sleep(0.5)
            except BaseException as exc:
                row['status']='interrupted'
                row['reason']=type(exc).__name__
                row['elapsed_seconds']=time.monotonic()-started
                save()
                raise
            finally:
                if proc.poll() is None:
                    os.killpg(proc.pid,signal.SIGKILL)
                    proc.wait()
            row['elapsed_seconds']=time.monotonic()-started
            row['exit_code']=proc.returncode
            if row['status']=='running': row['status']='completed' if proc.returncode==0 else 'error'
            if sampler is not None: sampler.wait(timeout=15)
        content=log.read_text()
        if not a.proofs_only:
            for m in re.finditer(r'PREP_METRICS (.+)',content):
                row['prep']={k:int(v) for k,v in re.findall(r'(\w+)=(\d+)',m[1])}
        else:
            row['verdicts']=[line for line in content.splitlines() if 'CardanoPerfProofs.lean:' in line and ('✅' in line or line.startswith('error:'))]
        artifact=cwd/f'.lake/build/lib/lean/Tests/Benchmarks/{module}.olean'
        if row['status']=='completed' and artifact.exists(): row['olean_bytes']=artifact.stat().st_size
        save();print(json.dumps(row),flush=True)
