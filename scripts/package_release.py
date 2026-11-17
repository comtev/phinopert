"""Create a deterministic repository ZIP from the checked manifest only."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import zipfile
from check_release import verify, require

ROOT=Path(__file__).resolve().parents[1]


def file_sha(path):
    digest=hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda:source.read(2**20),b''):digest.update(block)
    return digest.hexdigest()


def stage_proof_source(root,source,destination):
    """Stage the separately distributed source asset; never put it in the ZIP."""
    assets=json.loads((root/'release-assets.json').read_text())['assets']
    rows=[row for row in assets if row['role']=='complete-project-lean-source-closure']
    require(len(rows)==1,'Expected exactly one proof-source asset')
    row=rows[0]
    require(Path(row['file']).name==row['file'] and row['file'] not in {'.','..'},'Unsafe asset filename')
    require(source.is_file() and not source.is_symlink(),'Expected a regular proof-source archive')
    require(source.stat().st_size==row['bytes'] and file_sha(source)==row['sha256'],
            'Proof-source archive does not match release-assets.json')
    destination.mkdir(parents=True,exist_ok=True)
    target=destination/row['file']
    if target.exists():
        require(not target.is_symlink() and target.is_file() and
                target.stat().st_size==row['bytes'] and file_sha(target)==row['sha256'],
                'Refusing to replace an existing different asset')
    else:
        with source.open('rb') as src, target.open('xb') as dst:shutil.copyfileobj(src,dst,2**20)
        require(file_sha(target)==row['sha256'],'Staged proof-source hash differs')
    sidecar=target.with_name(target.name+'.sha256')
    expected=row['sha256']+'  '+row['file']+'\n'
    if sidecar.exists():require(sidecar.read_text()==expected,'Existing checksum sidecar differs')
    else:
        with sidecar.open('x') as output:output.write(expected)
    return {'archive':str(target),'bytes':row['bytes'],'sha256':row['sha256'],
            'checksum':str(sidecar),'uploaded_to_github':False}


def package(root,out):
    verify(root)
    manifest=json.loads((root/'release-manifest.json').read_text())
    names=sorted([*manifest['files'],'release-manifest.json'])
    out.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(out,'x',compression=zipfile.ZIP_DEFLATED) as archive:
        for name in names:
            info=zipfile.ZipInfo('phinopert/'+name,date_time=(2026,11,17,0,0,0))
            info.create_system=3;info.external_attr=0o100644<<16
            info.compress_type=zipfile.ZIP_DEFLATED
            archive.writestr(info,(root/name).read_bytes())
    with zipfile.ZipFile(out) as archive:
        require(archive.testzip() is None,'ZIP CRC failure')
        require(archive.namelist()==['phinopert/'+n for n in names],'Unexpected archive inventory')
        for name in names:
            require(archive.read('phinopert/'+name)==(root/name).read_bytes(),'Archive bytes differ: '+name)
    digest=hashlib.sha256(out.read_bytes()).hexdigest()
    out.with_suffix(out.suffix+'.sha256').write_text(digest+'  '+out.name+'\n')
    return {'archive':str(out),'bytes':out.stat().st_size,'sha256':digest,'files':len(names),
            'fresh_lean_verification_performed':False}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--proof-source',type=Path,
                        help='Verify and stage the separate proof-source asset alongside the repository ZIP')
    args=parser.parse_args()
    verify(ROOT)
    proof=stage_proof_source(ROOT,args.proof_source.resolve(),args.out.resolve().parent) if args.proof_source else None
    result=package(ROOT,args.out.resolve())
    if proof is not None:result['proof_source_asset']=proof
    print(json.dumps(result,indent=2))
