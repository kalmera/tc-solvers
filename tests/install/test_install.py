import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
ADAPTER = ROOT / 'ocaml/adapters/goblint'
spec = importlib.util.spec_from_file_location('installer', ADAPTER / 'install.py')
installer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(installer)


class InstallTests(unittest.TestCase):
    def test_preserves_unrelated_files_and_backs_up_replacements(self):
        with tempfile.TemporaryDirectory(prefix='tc solvers ') as tmp:
            checkout = Path(tmp) / 'analyzer'
            solver = checkout / 'src/solver'
            solver.mkdir(parents=True)
            subprocess.run(['git', 'init', '-q', str(checkout)], check=True)
            for name in ('selector.ml', 'qS_register.ml', 'other_register.ml', 'slrtc_register.ml'):
                (solver / name).write_text('original ' + name)
            backup = installer.install(checkout, ADAPTER / 'generated')
            for name in ('selector.ml', 'qS_register.ml', 'other_register.ml'):
                self.assertEqual((solver / name).read_text(), 'original ' + name)
            self.assertEqual((backup / 'slrtc_register.ml').read_text(), 'original slrtc_register.ml')
            for name in installer.FILES:
                self.assertEqual((solver / name).read_bytes(), (ADAPTER / 'generated' / name).read_bytes())
            second = installer.install(checkout, ADAPTER / 'generated')
            self.assertNotEqual(second, backup)
            self.assertEqual((second / 'slrtc_register.ml').read_bytes(), (solver / 'slrtc_register.ml').read_bytes())

    def test_rejects_incomplete_sources_before_installing(self):
        with tempfile.TemporaryDirectory() as tmp:
            checkout = Path(tmp)
            target = checkout / 'src/solver'
            target.mkdir(parents=True)
            (target / 'selector.ml').write_text('keep')
            with self.assertRaisesRegex(ValueError, 'Missing'):
                installer.install(checkout, checkout / 'missing')
            self.assertEqual(list(target.iterdir()), [target / 'selector.ml'])
