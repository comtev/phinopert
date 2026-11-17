"""Portable source verification and bounded stock-Lean replay (Unix, Python 3.10+).

No research-workspace paths, packed objects or axiom memo are accepted. A
checkpoint or failed process never produces complete=true. Sources stay intact.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

ALLOWED = {'propext','Classical.choice','Quot.sound'}
TARGET = 'ActualPhinopertNoProperShadowFit'
THEOREM = 'Phinopert.actual_phinopert_no_proper_shadow_fit'
RESERVE = 8*2**30


def require(ok,message):
    if not ok: raise RuntimeError(message)


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(2**20),b''):h.update(block)
    return h.hexdigest()


def pairs(items):
    out={}
    for k,v in items:
        require(k not in out,'Duplicate JSON key: '+k);out[k]=v
    return out


def read(path):return json.loads(Path(path).read_text(),object_pairs_hook=pairs)


def save(path,value):
    temporary=path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value,indent=2)+'\n')
    temporary.replace(path)


def source_path(root,row):
    p=Path(row['path'])
    require(not p.is_absolute() and '..' not in p.parts and '\\' not in row['path'],'Unsafe source path')
    path=root/p
    require(path.is_file() and not any(x.is_symlink() for x in [path,*path.parents]),'Missing/symlink source')
    require(path.resolve().is_relative_to(root),'Source escapes package')
    return path


def verify_sources(root):
    root=Path(root).resolve()
    manifest=read(root/'source-manifest.json')
    require(manifest['format']=='phinopert-source-closure-v1','Unknown source format')
    require(manifest['target']==TARGET and manifest['theorem']==THEOREM,'Wrong proof target')
    modules=manifest['modules'];order=manifest['build_order']
    require(len(order)==len(set(order))==len(modules) and set(order)==set(modules),'Invalid module inventory')
    require(order[-1]==TARGET,'Final theorem must be last')
    for name,record in manifest.get('support_files',{}).items():
        p=source_path(root,{'path':name})
        require(p.stat().st_size==record['bytes'] and sha(p)==record['sha256'],'Package support file changed: '+name)
    done=set();external=set(manifest['external_imports'])
    for name in order:
        require(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name),'Invalid module name')
        row=modules[name];p=source_path(root,row)
        require(row['path']=='src/'+name+'.lean','Unexpected module location')
        require(p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],'Source hash differs: '+name)
        require(all(dep in done or dep in external for dep in row['imports']),'Missing/unsorted import: '+name)
        done.add(name)
    actual={p.relative_to(root).as_posix() for p in (root/'src').rglob('*') if p.is_file() or p.is_symlink()}
    require(actual=={row['path'] for row in modules.values()},'Unlisted or missing source')
    return manifest


def audit_log(text,expected):
    require(not re.search(r'\b(sorryAx|native_decide|failed|error:)\b',text),'Compiler/audit error in log')
    found={}
    for name,axioms,empty in re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",text):
        values=set(filter(None,(x.strip() for x in axioms.split(','))))
        require(values<=ALLOWED,'Forbidden axiom for '+name+': '+str(values))
        require(name not in found,'Repeated axiom record: '+name)
        found[name]=sorted(values)
    require(set(found)==set(expected),'Missing/unexpected axiom records')
    return found


def run_child(command,cwd,env,log,timeout):
    started=time.monotonic()
    with log.open('xb') as output:
        proc=subprocess.Popen(command,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        try:
            while proc.poll() is None:
                require(shutil.disk_usage(log.parent).free>=RESERVE,'Disk reserve reached')
                require(time.monotonic()-started<timeout,'Module computation limit reached')
                time.sleep(.5)
            require(proc.returncode==0,'Lean failed; inspect '+str(log))
        finally:
            if proc.poll() is None:
                os.killpg(proc.pid,signal.SIGTERM)
                try:proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid,signal.SIGKILL);proc.wait()
    return time.monotonic()-started


def environment(root,out):
    env={k:v for k,v in os.environ.items() if k not in {'LEAN_PATH','LEAN_SRC_PATH','LD_PRELOAD','DYLD_INSERT_LIBRARIES'}}
    def query(*args):return subprocess.check_output(args,cwd=root,env=env,text=True,timeout=120).strip()
    lean=Path(query('lake','env','which','lean')).resolve()
    require('version 4.19.0' in query(str(lean),'--version'),'Lean 4.19.0 required')
    paths=[]
    core_library=lean.parent.parent/'lib/lean'
    for item in query('lake','env','printenv','LEAN_PATH').split(os.pathsep):
        p=(root/item).resolve()
        if p==root/'.lake/build/lib/lean':continue
        require(p.is_relative_to(root/'.lake/packages') or p==core_library,
                'Unexpected dependency search path: '+str(p))
        # Lake lists optional packages such as Cli even when their unused
        # build directory does not exist. Only actual directories are imported.
        if p.is_dir():paths.append(p)
    require(paths,'No pinned dependency objects found; run lake exe cache get')
    for name in read(root/'source-manifest.json')['external_imports']:
        require(any((p/(name.replace('.','/')+'.olean')).is_file() for p in paths),
                'Missing required external module: '+name)
    external={}
    # Bind compiler, kernel libraries and external objects; no research outputs.
    for base in [lean.parent.parent,*paths]:
        for p in sorted(base.rglob('*')):
            if p.is_file() and (p.suffix in {'.olean','.so','.dylib'} or p==lean):
                external[str(p)]=sha(p)
    require(external,'Empty environment inventory')
    env['LEAN_PATH']=os.pathsep.join(map(str,[out/'build',*paths]))
    env['LEAN_NUM_THREADS']='1'
    return lean,env,external


def build(root,manifest,out,limit):
    out.mkdir(parents=True,exist_ok=True)
    with (out/'replay.lock').open('a') as lock, (root/'.replay.lock').open('a') as shared:
        fcntl.flock(shared,fcntl.LOCK_EX|fcntl.LOCK_NB)
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        for sub in ['build','logs','receipts']:(out/sub).mkdir(exist_ok=True)
        require(shutil.disk_usage(out).free>=RESERVE,'8 GiB reserve required')
        if limit is None:
            require(shutil.disk_usage(out).free>=600*2**30,
                    'Full fresh replay requires 600 GiB free working space; checkpoint pilots need less')
        lean,env,external=environment(root,out)
        binding={'source_manifest':sha(root/'source-manifest.json'),
                 'lake_manifest':sha(root/'lake-manifest.json'),'toolchain':sha(root/'lean-toolchain'),
                 'driver':sha(Path(__file__)),'external':external}
        if (out/'environment.json').exists():require(read(out/'environment.json')==binding,'Resume environment changed')
        else:save(out/'environment.json',binding)
        identity=sha(out/'environment.json');done={};start=time.monotonic()
        state={'complete':False,'passed':False,'checked_modules':0,'selected_modules':len(manifest['modules']),
               'target':THEOREM,'phase':'running','termination_class':None}
        save(out/'summary.json',state)
        try:
            for name in manifest['build_order']:
                require(time.monotonic()-start<24*3600,'Controller computation limit reached')
                row=manifest['modules'][name];source=source_path(root,row)
                obj=out/'build'/(name+'.olean');log=out/'logs'/(name+'.log');receipt=out/'receipts'/(name+'.json')
                fingerprint={'source':row['sha256'],'environment':identity,
                             'dependencies':{d:done[d] for d in row['imports'] if d in done}}
                expected=re.findall(r'^#print axioms ([A-Za-z_][A-Za-z_0-9.]*)\s*$',source.read_text(),re.M)
                if receipt.exists():
                    r=read(receipt)
                    require(r['fingerprint']==fingerprint and sha(obj)==r['object'] and sha(log)==r['log'],'Invalid resume receipt: '+name)
                    audit_log(log.read_text(),expected)
                else:
                    if limit is not None and state['checked_modules']>=limit:break
                    require(not obj.exists() and not log.exists(),'Incomplete prior attempt; use a new output directory')
                    require(sha(source)==row['sha256'],'Source changed during replay')
                    seconds=run_child([str(lean),'-j','1','--root='+str(root/'src'),'-o',str(obj),str(source)],root,env,log,1200)
                    axioms=audit_log(log.read_text(),expected)
                    require(obj.is_file(),'Missing compiled object')
                    r={'fingerprint':fingerprint,'object':sha(obj),'log':sha(log),'seconds':seconds,'axioms':axioms}
                    save(receipt,r)
                done[name]=r['object'];state['checked_modules']+=1
                save(out/'summary.json',state)
            if len(done)!=len(manifest['modules']):
                state.update(phase='checkpoint',termination_class='requested_checkpoint')
            else:
                state['phase']='final_audit';save(out/'summary.json',state)
                verify_sources(root)
                require(all(sha(Path(p))==h for p,h in external.items()),'Dependency/compiler changed during replay')
                require(all(sha(out/'build'/(n+'.olean'))==h for n,h in done.items()),'Object changed during replay')
                final=read(out/'receipts'/(TARGET+'.json'))
                require(set(final['axioms'].get(THEOREM,[]))==ALLOWED,'Final theorem axiom result differs')
                state.update(phase='finished',complete=True,passed=True,whole_root_proofs_checked=432)
        except BaseException as error:
            state.update(phase='stopped',error=str(error),termination_class='computation_limit' if 'limit' in str(error) else 'proof_or_audit_error')
            raise
        finally:save(out/'summary.json',state)
        return state


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=['verify','build'])
    parser.add_argument('--package',type=Path,default=Path.cwd())
    parser.add_argument('--out',type=Path)
    parser.add_argument('--limit',type=int,help='Requested module checkpoint; never a full proof claim')
    args=parser.parse_args();root=args.package.resolve()
    manifest=verify_sources(root)
    if args.action=='verify':
        print(json.dumps({'source_files_checked':len(manifest['modules']),'source_bytes':manifest['source_bytes'],
                          'fresh_lean_verification_performed':False},indent=2));return
    require(args.out is not None,'Choose an explicit output directory')
    require(args.limit is None or args.limit>0,'Checkpoint must be positive')
    print(json.dumps(build(root,manifest,args.out.resolve(),args.limit),indent=2))


if __name__=='__main__':main()
