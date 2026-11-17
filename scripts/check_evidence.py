"""Check included completion evidence. This does not run Lean or prove a theorem."""
import hashlib
import json
from pathlib import Path
import re
from check_release import no_duplicates, require

ROOT = Path(__file__).resolve().parents[1]
THEOREM = 'Phinopert.actual_phinopert_no_proper_shadow_fit'
FINAL_SHA = '3bded0dcd6bb6eb7099f96aee5b5faf7bd3516be210b1e90337f20bd8166cf20'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(), object_pairs_hook=no_duplicates)


def verify(root=ROOT):
    root=Path(root)
    folder=root/'verification/v129'
    summary=read(folder/'summary.json')
    audit=read(folder/'final-audit.json')
    require(sha(folder/'final-audit.json') == FINAL_SHA == summary['final_audit_sha256'],
            'Final audit digest differs from retained completion record')
    for field in ['complete','passed','full_non_rupert_theorem_formalised']:
        require(summary[field] is True, 'Incomplete recorded result: '+field)
    require(summary['phase']=='finished' and summary['selected_modules']==1146, 'Wrong final stage')
    for record in [summary,audit]:
        require(record['passed'] is True and record['actual_global_theorem']==THEOREM, 'Wrong result or theorem')
        for key,value in [('checked_modules',1146),('whole_root_proofs_checked',432),
                          ('authenticated_prefix_modules',1144),('native_kernel_modules',2)]:
            require(record[key]==value, 'Wrong final count: '+key)
    require(audit['server_before_sha256']==audit['server_after_sha256'], 'Before/after evidence differs')
    for module,theorem in [('ActualPhinopertNoProperShadowFit',THEOREM),
                           ('OriginalRootRange000To432','Phinopert.originalrootrange000to432_excludes')]:
        receipt=read(folder/(module+'.receipt.json'))
        require(sha(root/'lean'/(module+'.lean'))==receipt['source_sha256'], 'Final source changed')
        log=folder/(module+'.log')
        require(sha(log)==receipt['log_sha256'], 'Axiom log changed')
        match=re.fullmatch(r"'"+re.escape(theorem)+r"' depends on axioms: \[([^\]]+)\]\s*",log.read_text())
        require(match is not None, 'Missing or unexpected axiom output')
        require(set(match[1].split(', '))==ALLOWED, 'Unexpected axiom set')
        require(0 < receipt['seconds'] < 1200, 'Recorded module time exceeds guard')
    paper=read(root/'verification/paper-build.json')
    require(sha(root/'paper/phinopert.tex')==paper['paper_source_sha256'] and
            sha(root/'paper/phinopert.pdf')==paper['pdf_sha256'], 'Paper build record is stale')
    return {'retained_evidence_consistent':True,'recorded_roots':432,
            'recorded_final_stage_modules':1146,'fresh_lean_verification_performed':False}


if __name__=='__main__':
    print(json.dumps(verify(),indent=2))
