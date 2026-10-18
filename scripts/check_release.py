"""Check a curated release inventory. Integrity is not a mathematical proof."""
import hashlib
import json
from pathlib import Path
import sys


def require(ok, message):
    if not ok:
        raise ValueError(message)


def no_duplicates(pairs):
    result={}
    for key,value in pairs:
        require(key not in result, 'Duplicate JSON key: '+key)
        result[key]=value
    return result


def verify(root):
    root=Path(root).resolve()
    manifest=json.loads((root/'release-manifest.json').read_text(),object_pairs_hook=no_duplicates)
    require(manifest['format']=='curated-research-release-v1','Unknown inventory format')
    require(manifest['files'],'Empty inventory')
    for name,record in manifest['files'].items():
        rel=Path(name)
        require(not rel.is_absolute() and '..' not in rel.parts and '\\' not in name,'Unsafe member: '+name)
        path=root/rel
        require(not any(p.is_symlink() for p in [path,*path.parents] if p!=root.parent), 'Symlink member: '+name)
        require(path.resolve().is_relative_to(root) and path.is_file(),'Missing or escaping member: '+name)
        data=path.read_bytes()
        require(len(data)==record['bytes'] and hashlib.sha256(data).hexdigest()==record['sha256'],'Changed member: '+name)
    return dict(files_checked=len(manifest['files']),integrity_checked=True,mathematical_proof_checked=False)


if __name__=='__main__':
    root=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]
    print(json.dumps(verify(root),indent=2))
