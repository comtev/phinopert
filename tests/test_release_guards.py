"""Negative controls for release tooling; these are not mathematical proof tests."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import check_evidence
import check_release
import replay_lean
import package_release


class GuardTests(unittest.TestCase):
    def test_changed_release_asset_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);source=root/'proof.tar.gz';source.write_bytes(b'original')
            row={'file':source.name,'role':'complete-project-lean-source-closure',
                 'bytes':source.stat().st_size,'sha256':package_release.file_sha(source)}
            (root/'release-assets.json').write_text(json.dumps({'assets':[row]}))
            source.write_bytes(b'modified')
            with self.assertRaisesRegex(ValueError,'does not match'):
                package_release.stage_proof_source(root,source,root/'dist')

    def test_asset_staging_preserves_existing_files(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);source=root/'proof.tar.gz';source.write_bytes(b'original')
            row={'file':source.name,'role':'complete-project-lean-source-closure',
                 'bytes':source.stat().st_size,'sha256':package_release.file_sha(source)}
            (root/'release-assets.json').write_text(json.dumps({'assets':[row]}))
            package_release.stage_proof_source(root,source,root/'dist')
            package_release.stage_proof_source(root,source,root/'dist')
            target=root/'dist'/source.name;target.write_bytes(b'preserve me')
            with self.assertRaisesRegex(ValueError,'Refusing to replace'):
                package_release.stage_proof_source(root,source,root/'dist')
            self.assertEqual(target.read_bytes(),b'preserve me')

    def test_duplicate_json(self):
        with self.assertRaises(ValueError):
            json.loads('{"x":1,"x":2}',object_pairs_hook=check_release.no_duplicates)

    def test_forbidden_axiom(self):
        with self.assertRaises(RuntimeError):
            replay_lean.audit_log("'X' depends on axioms: [sorryAx]\n",['X'])

    def test_missing_axiom_record(self):
        with self.assertRaises(RuntimeError):replay_lean.audit_log('', ['X'])

    def test_duplicate_axiom_record(self):
        with self.assertRaises(RuntimeError):
            replay_lean.audit_log("'X' depends on axioms: [propext]\n"*2,['X'])

    def test_allowed_and_empty(self):
        self.assertEqual(replay_lean.audit_log("'X' does not depend on any axioms\n",['X']),{'X':[]})
        self.assertEqual(replay_lean.audit_log("'X' depends on axioms: [Quot.sound]\n",['X']),{'X':['Quot.sound']})

    def test_path_escape(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(RuntimeError):replay_lean.source_path(Path(d),{'path':'../escape'})

    def test_source_tamper_and_order(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'src').mkdir();p=root/'src/ActualPhinopertNoProperShadowFit.lean';p.write_text('import Missing\n')
            row={'path':'src/'+p.name,'sha256':replay_lean.sha(p),'bytes':p.stat().st_size,'imports':['Missing']}
            m={'format':'phinopert-source-closure-v1','target':replay_lean.TARGET,'theorem':replay_lean.THEOREM,
               'modules':{replay_lean.TARGET:row},'build_order':[replay_lean.TARGET],'external_imports':[]}
            (root/'source-manifest.json').write_text(json.dumps(m))
            with self.assertRaisesRegex(RuntimeError,'Missing/unsorted'):replay_lean.verify_sources(root)
            row['imports']=[];(root/'source-manifest.json').write_text(json.dumps(m));p.write_text('changed')
            with self.assertRaisesRegex(RuntimeError,'Source hash'):replay_lean.verify_sources(root)

    def test_retained_completion(self):
        self.assertFalse(check_evidence.verify()['fresh_lean_verification_performed'])


if __name__=='__main__':unittest.main()
