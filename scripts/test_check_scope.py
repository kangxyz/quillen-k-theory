"""Offline Git-object fixtures for assessed Aglib scope; no Lean or network."""
import json
from pathlib import Path
import subprocess
import sys
import shutil
import os
import tempfile
import unittest
from check_scope import select
from dependency_scope import verify_runtime
from library_sources import lean_imports, is_import_surface

class AssessedAglibTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='quillen-assessed-aglib-')
        self.directory=Path(self.tmp.name).resolve()
        self.root,self.source=self.directory/'consumer',self.directory/'aglib'
        for root in (self.root,self.source): root.mkdir();self.git(root,'init','-q')
        for path in ['lean-toolchain','lakefile.toml','lake-manifest.json','scripts/build_serial.py','scripts/resource_guard.py']:
            self.write(self.source,path,'stable runtime\n')
        self.write(self.source,'Aglib/A.lean','def a := 1\n')
        self.write(self.source,'Aglib/U.lean','def u := 1\n')
        self.write(self.source,'Aglib.lean','import Aglib.A Aglib.U\n')
        self.old=self.commit(self.source)
        self.write(self.source,'Aglib/A.lean','def a := 2\n')
        self.write(self.source,'Aglib/B.lean','def b := 1\n')
        self.write(self.source,'Aglib.lean','import Aglib.A Aglib.U Aglib.B\n')
        self.new=self.commit(self.source)
        sources={'Quillen/P.lean':'import Aglib.A\ndef p := a\n',
                 'Quillen/C.lean':'import Quillen.P\ndef c := p\n',
                 'Quillen/U.lean':'import Aglib.U\ndef u := 1\n',
                 'Quillen.lean':'import Quillen.P Quillen.C Quillen.U\n',
                 'QuillenTest/T.lean':'import Quillen.C\nexample : True := trivial\n',
                 'QuillenTest/Axioms.lean':'import Quillen\n',
                 'examples/downstream/Audit.lean':'import Consumer\n',
                 'examples/downstream/Consumer/Use.lean':'import Quillen.C\ndef use := c\n',
                 'examples/downstream/Consumer/PublicLibraries.lean':'import Aglib\n',
                 'examples/downstream/Consumer/FacadeUse.lean':'import Consumer.PublicLibraries\ndef facadeUse := 1\n',
                 'examples/downstream/Consumer.lean':'import Consumer.Use Consumer.FacadeUse\n',
                 'lean-toolchain':'leanprover/lean4:v4.34.1\n'}
        for path,text in sources.items(): self.write(self.root,path,text)
        for name in ['check_scope.py', 'check_run.py', 'dependency_scope.py', 'library_sources.py']:
            (self.root/'scripts').mkdir(exist_ok=True)
            shutil.copyfile(Path(__file__).with_name(name), self.root/'scripts'/name)
        self.write(self.root,'.gitignore','__pycache__/\n')
        self.write_pins(self.old);self.base=self.commit(self.root);self.write_pins(self.new)
    def tearDown(self): self.tmp.cleanup()
    def write(self,root,path,text):
        p=root/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
    def git(self,root,*args):
        return subprocess.check_output(['git',*args],cwd=root,text=True,stderr=subprocess.DEVNULL).strip()
    def commit(self,root):
        self.git(root,'add','.')
        self.git(root,'-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-qm','fixture')
        return self.git(root,'rev-parse','HEAD')
    def write_pins(self,rev):
        self.write(self.root,'lakefile.toml','name = "Fixture"\n[[require]]\nname = "Aglib"\ngit = "https://example.invalid/aglib"\nrev = "'+rev+'"\n')
        d={'packages':[{'name':'Aglib','rev':rev,'inputRev':rev,'url':'https://example.invalid/aglib'},
                       {'name':'mathlib','rev':'stable','inputRev':'stable'}]}
        for p in ['lake-manifest.json','examples/downstream/lake-manifest.json']:
            self.write(self.root,p,json.dumps(d)+'\n')
    def plan(self): return select(self.root,aglib_source=self.source)
    def test_objects_facade_closure_topology_and_determinism(self):
        p=self.plan();self.assertEqual(p,self.plan())
        self.assertEqual(p['providers'],['Quillen.C','Quillen.P'])
        self.assertEqual(p['provider_batches'],[['Quillen.P'],['Quillen.C']])
        self.assertEqual(p['tests'],['QuillenTest.T'])
        self.assertEqual(p['clients'],['Consumer.FacadeUse','Consumer.Use'])
        self.assertFalse(p['full']);self.assertTrue(p['trust']);self.assertTrue(p['client_trust'])
        d=p['dependency_assessment'];self.assertEqual(d['old'],self.old);self.assertEqual(d['new'],self.new)
        self.assertIn('Aglib.B',d['changed_production_modules']);self.assertNotIn(str(self.directory),json.dumps(d))
    def test_ordinary_pin_guard_stays_closed(self):
        with self.assertRaisesRegex(ValueError,'global validation inputs'): select(self.root)
    def test_other_global_and_dependency_changes_reject(self):
        for path in ['lean-toolchain','lakefile.toml','lake-manifest.json','examples/downstream/lake-manifest.json']:
            original=(self.root/path).read_text()
            self.write(self.root,path,original.replace('stable','other') if 'stable' in original else original+'\n# changed\n')
            with self.assertRaises(ValueError): self.plan()
            self.write(self.root,path,original)
    def test_inconsistent_pins_and_changed_upstream_runtime_reject(self):
        p='examples/downstream/lake-manifest.json';self.write(self.root,p,(self.root/p).read_text().replace(self.new,self.old))
        with self.assertRaises(ValueError): self.plan()
        self.write(self.source,'scripts/resource_guard.py','changed budget\n')
        changed=self.commit(self.source);self.write_pins(changed)
        with self.assertRaisesRegex(ValueError,'runtime/config changed'): self.plan()
    def test_missing_objects_and_redirected_source_reject(self):
        self.write_pins('f'*40)
        with self.assertRaises(ValueError): self.plan()
        self.write_pins(self.new);link=self.directory/'redirect';link.symlink_to(self.source,target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'symlink'): select(self.root,aglib_source=link)
        with self.assertRaises(ValueError): select(self.root,aglib_source=self.source/'Aglib')
    def test_git_source_symlink_rejects(self):
        p=self.source/'Aglib/B.lean';p.unlink();p.symlink_to('A.lean');self.write_pins(self.commit(self.source))
        with self.assertRaisesRegex(ValueError,'regular Git blob'): self.plan()
    def test_changed_local_facade_kept_and_local_change_union(self):
        self.write(self.root,'Quillen/U.lean','import Aglib.U\ndef u := 2\n')
        self.write(self.root,'Quillen.lean','import Quillen.P Quillen.C Quillen.U\n-- changed facade\n')
        p=self.plan();self.assertIn('Quillen.U',p['providers']);self.assertIn('Quillen',p['providers'])
    def test_runtime_math_drift_rejects_helpers_separate(self):
        verify_runtime(self.source,self.new)
        self.write(self.source,'scripts/resource_guard.py','separately guarded overlay\n');verify_runtime(self.source,self.new)
        self.write(self.source,'Aglib/A.lean','def a := 99\n')
        with self.assertRaisesRegex(ValueError,'mathematical/config drift'): verify_runtime(self.source,self.new)
    def test_owned_dependency_container_link_with_exact_math(self):
        packages=self.directory/'privatepackages';packages.mkdir()
        self.source.rename(packages/'Aglib');self.source=packages/'Aglib'
        workspace=self.directory/'workspace';workspace.mkdir()
        (workspace/'packages').symlink_to(packages,target_is_directory=True)
        linked=workspace/'packages/Aglib'
        result=verify_runtime(linked,self.new)
        self.assertEqual(result['resolved_dependency_root'],str(self.source))
        with self.assertRaisesRegex(ValueError,'symlink'): select(self.root,aglib_source=linked)
        target=self.source/'Aglib/A.lean';target.unlink();target.symlink_to('U.lean')
        with self.assertRaisesRegex(ValueError,'mathematical/config drift'): verify_runtime(linked,self.new)
    def test_runtime_extra_and_redirected_math_reject(self):
        self.write(self.source,'Aglib/Extra.lean','def extra := 1\n')
        with self.assertRaisesRegex(ValueError,'source set drift'): verify_runtime(self.source,self.new)
        (self.source/'Aglib/Extra.lean').unlink();p=self.source/'Aglib/A.lean';p.unlink();p.symlink_to('U.lean')
        with self.assertRaisesRegex(ValueError,'mathematical/config drift'): verify_runtime(self.source,self.new)
    def test_run_cmd_stop_and_quoted_identifier(self):
        text='import Aglib.A\nrun_cmd do\n  let quoted := "Aglib.Fake"\n'
        self.assertEqual(lean_imports(text),['Aglib.A']);self.assertFalse(is_import_surface(text))
        self.assertEqual(lean_imports('import Aglib.«run_cmd»\n'),['Aglib.run_cmd'])
    def test_runner_recomputes_plan_and_rejects_edited_targets_and_source_drift(self):
        from ci_adapter import QuillenAdapter
        plan=self.plan();path=self.directory/'plan.json';path.write_text(json.dumps(plan))
        adapter=QuillenAdapter(scope_file=path,aglib_source=self.source)
        self.assertEqual(adapter.select_scope(self.root)['scope'],plan)
        plan['providers']=[];path.write_text(json.dumps(plan))
        with self.assertRaisesRegex(ValueError,'stale'):
            adapter.select_scope(self.root)
        path.write_text(json.dumps(self.plan()))
        self.write(self.root,'Quillen/P.lean','import Aglib.A\ndef p := a + 1\n')
        with self.assertRaisesRegex(ValueError,'stale'):
            adapter.select_scope(self.root)
    def test_assessed_committed_head_rejects_actual_control_and_source_set_drift(self):
        from check_run import verify_assessed_inputs
        self.commit(self.root)
        plan=select(self.root,base=self.base,head='HEAD',aglib_source=self.source)
        runner=self.root/'scripts/check_run.py';original=runner.read_text()
        runner.write_text(original+'\n# Unexpected actual working-tree control.\n')
        with self.assertRaisesRegex(ValueError,'validation control differs'):
            verify_assessed_inputs(self.root,plan)
        runner.write_text(original)
        self.write(self.root,'Unexpected.lean','def unexpected := 1\n')
        with self.assertRaisesRegex(ValueError,'Unclassified Lean source'):
            verify_assessed_inputs(self.root,plan)
    def test_ci_source_only_acquisition_follows_accepted_ancestor(self):
        from ci_adapter import QuillenAdapter
        from unittest.mock import patch
        head=self.commit(self.root)
        baseline={'base':self.base,'verified_base':self.base,'head':head}
        with patch('ci_adapter.accepted_baseline',return_value=baseline) as accepted, \
             patch('ci_adapter.acquire_assessment_source',return_value=self.source) as acquire:
            payload=QuillenAdapter().plan(self.root,'owner/repo','main',head)
        self.assertEqual(payload['scope']['base'],self.base)
        self.assertEqual(payload['scope']['dependency_assessment']['old'],self.old)
        self.assertEqual(payload['scope']['dependency_assessment']['new'],self.new)
        self.assertEqual(acquire.call_args.args[:3],(self.root,self.base,head))
        self.assertIn('protocol',accepted.call_args.kwargs)
    def test_deleted_external_module_retains_old_consumer_edge(self):
        (self.source/'Aglib/A.lean').unlink()
        revision=self.commit(self.source);self.write_pins(revision)
        self.assertIn('Quillen.P',self.plan()['providers'])
    def test_working_tree_proof_drift_changes_descriptor(self):
        self.write(self.root,'Quillen/P.lean','import Aglib.A\ndef p := a + 1\n');p=self.plan()
        self.write(self.root,'Quillen/P.lean','import Aglib.A\ndef p := a + 2\n')
        self.assertNotEqual(p['dependency_assessment'],self.plan()['dependency_assessment'])
if __name__=='__main__': unittest.main()
