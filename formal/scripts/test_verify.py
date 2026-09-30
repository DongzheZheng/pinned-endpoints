"""Bounded, standard-library tests of verifier failure gates (no Lean build)."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("portable_verify", Path(__file__).with_name("verify.py"))
verify = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verify)


class ServerGuardTests(unittest.TestCase):
    def test_local_or_unopted_execution_is_rejected(self):
        for system, flag in (("Darwin", "1"), ("Linux", ""), ("Windows", "1")):
            with patch.object(verify.platform, "system", return_value=system), patch.dict(verify.os.environ, {"PINNED_LEAN_SERVER": flag}):
                with self.assertRaisesRegex(verify.VerificationError, "local Lean execution is disabled"):
                    verify.require_server_execution()

    def test_authorized_linux_server_is_allowed(self):
        with patch.object(verify.platform, "system", return_value="Linux"), patch.dict(verify.os.environ, {"PINNED_LEAN_SERVER": "1"}):
            verify.require_server_execution()


class ScannerTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        code = verify.uncomment('namespace Resonance.A\n/- outer /- nested -/ -/\n'
                                'theorem x : True := by trivial -- tail\n'
                                'end Resonance.A\n')
        self.assertEqual(verify.declarations(code, "Resonance.A"), ["Resonance.A.x"])
        self.assertIn('"/- literal -/"', verify.uncomment('def x := "/- literal -/"'))
        with self.assertRaises(verify.VerificationError):
            verify.uncomment('/- unclosed')

    def test_private_attribute_and_missed_declaration(self):
        code = 'namespace Resonance.A\n@[simp] private lemma x : True := by trivial\nend Resonance.A'
        self.assertEqual(verify.declarations(code, "Resonance.A"), ["PRIVATE:Resonance.A.x"])
        with self.assertRaises(verify.VerificationError):
            verify.declarations(code.replace('private lemma', 'protected lemma'), "Resonance.A")

    def test_actual_private_name_resolution(self):
        kernel = '_private.Resonance.A.17.Resonance.A.x'
        text = f'PRIVATE_NAME Resonance.A.x {kernel}\n'
        self.assertEqual(verify.resolve_private(['PRIVATE:Resonance.A.x'], text), [kernel])
        self.assertEqual(verify.normalized_source_name(kernel), 'PRIVATE:Resonance.A.x')
        with self.assertRaises(verify.VerificationError):
            verify.resolve_private(['PRIVATE:Resonance.A.x'], text + text)
        with self.assertRaises(verify.VerificationError):
            verify.resolve_private(['_private.Resonance.A.18.Resonance.A.x'], text)
        private_check = verify.type_checker([kernel], [])
        self.assertNotIn('#check ' + kernel, private_check)
        self.assertIn('Expected a theorem', private_check)


class ConeTests(unittest.TestCase):
    TEXT = ('CONE_ROOT Resonance.A.x\nCONE_ROOT Resonance.A.generated\n'
            'CONE_CONSTANT Resonance.A.x\nCONE_CONSTANT Resonance.A.generated\n'
            'CONE_CONSTANT propext\nCONE_AXIOM propext\n'
            'CONE_COUNTS roots=2 constants=3 unsafe=0 partial=0\n')

    def test_generated_roots_are_covered(self):
        self.assertEqual(verify.parse_cone(self.TEXT, ['Resonance.A.x'], verify.STANDARD_AXIOMS)['root_count'], 2)

    def test_missing_or_duplicate_roots_rejected(self):
        for text in (self.TEXT.replace('CONE_CONSTANT Resonance.A.generated\n', ''),
                     self.TEXT + 'CONE_ROOT Resonance.A.x\n'):
            with self.assertRaises(verify.VerificationError):
                verify.parse_cone(text, ['Resonance.A.x'], verify.STANDARD_AXIOMS)
        with self.assertRaises(verify.VerificationError):
            verify.parse_cone(self.TEXT, ['Resonance.A.missing'], verify.STANDARD_AXIOMS)

    def test_no_unsafe_partial_or_axiom_exceptions(self):
        for suffix in ('CONE_UNSAFE Lean.anything\n', 'CONE_PARTIAL Mathlib.anything\n',
                       'CONE_AXIOM sorryAx\n'):
            with self.assertRaises(verify.VerificationError):
                verify.parse_cone(self.TEXT + suffix, ['Resonance.A.x'], verify.STANDARD_AXIOMS)


class FrozenSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest, cls.payloads, cls.modules = verify.source_snapshot(verify.REPOSITORY)

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name, data in self.payloads.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        (self.root / 'verification').mkdir()
        self.manifest_copy = copy.deepcopy(self.manifest)
        self.save_manifest()

    def save_manifest(self):
        (self.root / 'verification/manifest.json').write_text(json.dumps(self.manifest_copy))

    def test_exact_frozen_package(self):
        manifest, _, modules = verify.source_snapshot(self.root)
        self.assertEqual(len(modules), 21)
        self.assertEqual(len(manifest['theorems']), len(self.manifest['theorems']))

    def test_one_changed_byte_is_rejected(self):
        path = self.root / (self.modules[0].replace('.', '/') + '.lean')
        path.write_bytes(path.read_bytes() + b'\n')
        with self.assertRaisesRegex(verify.VerificationError, 'hash mismatch'):
            verify.source_snapshot(self.root)

    def test_unlisted_source_is_rejected(self):
        (self.root / 'Resonance/Unlisted.lean').write_text('theorem unrelated : True := by trivial\n')
        with self.assertRaisesRegex(verify.VerificationError, 'Unlisted or missing'):
            verify.source_snapshot(self.root)

    def test_omitted_theorem_is_rejected(self):
        self.manifest_copy['theorems'].pop()
        self.save_manifest()
        with self.assertRaisesRegex(verify.VerificationError, 'theorem inventory'):
            verify.source_snapshot(self.root)

    def test_rehashed_axiom_cannot_bypass_source_gate(self):
        name = self.modules[0].replace('.', '/') + '.lean'
        path = self.root / name
        payload = path.read_bytes() + b'\naxiom fabricated : False\n'
        path.write_bytes(payload)
        self.manifest_copy['source_sha256'][name] = verify.digest(payload)
        self.save_manifest()
        with self.assertRaisesRegex(verify.VerificationError, 'Forbidden source token'):
            verify.source_snapshot(self.root)

    def test_historical_counts_are_not_runtime_authority(self):
        self.manifest_copy['historical_counts'] = {'roots': -999, 'status': 'PASS'}
        self.save_manifest()
        _, _, modules = verify.source_snapshot(self.root)
        self.assertEqual(len(modules), 21)

    def test_allowed_axioms_cannot_be_widened(self):
        self.manifest_copy['allowed_axioms'].append('sorryAx')
        self.save_manifest()
        with self.assertRaisesRegex(verify.VerificationError, 'standard axioms'):
            verify.source_snapshot(self.root)


if __name__ == '__main__':
    unittest.main()
