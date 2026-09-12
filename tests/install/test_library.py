import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('library_generator', ROOT / 'ocaml/library/generate.py')
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)


class LibraryTests(unittest.TestCase):
    def test_generation_matches_and_rejects_changed_boundaries(self):
        bitmap = (ROOT / 'ocaml/runtime/rank_worklist_bitmap.ml').read_text()
        for variant in ('simple', 'restarting', 'narrowing_fixed_point'):
            with self.subTest(variant=variant):
                source = (ROOT / f'ocaml/adapters/goblint/generated/slrtc_{variant}.ml').read_text()
                actual = generator.transform(source, variant, bitmap)
                self.assertEqual(actual, (ROOT / f'ocaml/library/generated/core_{variant}.ml').read_text())
                for old, new in [('    let solve xs roots _old_data =', '    let renamed ='),
                                 ('    type set =', '    type renamed ='),
                                 ('            incr SolverStats.evals', '            unknown_stats ()')]:
                    with self.assertRaises(ValueError):
                        generator.transform(source.replace(old, new), variant, bitmap)

    def test_isolated_build_install_and_consumer(self):
        # Copy only the library: no Rocq, extracted reference libraries, adapters,
        # or test helpers. The only available project dependency is Stdlib.
        with tempfile.TemporaryDirectory(prefix='tc-solvers-library-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'ocaml/library', root / 'library')
            (root / 'dune-project').write_text('(lang dune 3.19)\n(name tc-solvers)\n')
            (root / 'tc-solvers.opam').write_text('opam-version: "2.0"\n')
            def run(*args, cwd=root):
                result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT)
                self.assertEqual(result.returncode, 0, result.stdout)
                return result.stdout
            run('dune', 'build', '-p', 'tc-solvers', '@install')
            prefix = root / 'installed'
            run('dune', 'install', '--prefix', str(prefix), 'tc-solvers')
            lib = prefix / 'lib/tc-solvers'
            metadata = run('ocamlobjinfo', str(lib / 'tc_solvers.cma'))
            for dependency in ('Batteries', 'Yojson', 'Goblint'):
                self.assertNotIn(dependency, metadata)
            consumer = root / 'consumer'
            consumer.mkdir()
            shutil.copyfile(ROOT / 'tests/library_api/api.ml', consumer / 'main.ml')
            run('ocamlc', '-I', str(lib), str(lib / 'tc_solvers.cma'), 'main.ml',
                '-o', 'main.exe', cwd=consumer)
            run(str(consumer / 'main.exe'), cwd=consumer)
            # Internal generated cores are not part of the public namespace.
            (consumer / 'private.ml').write_text('module Hidden = Tc_solvers.Core_simple\n')
            result = subprocess.run(['ocamlc', '-I', str(lib), '-c', 'private.ml'], cwd=consumer,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Unbound module', result.stdout)
