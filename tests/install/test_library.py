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
        source = (ROOT / 'ocaml/extracted/PlusRestartingRuntime.ml').read_text()
        actual = generator.transform_plus(source, bitmap)
        self.assertEqual(actual, (ROOT / 'ocaml/library/generated/core_plus_restarting.ml').read_text())
        for marker in ('  type work_queue =', 'module ListDiscoveryOrder =',
                       'let next_contribution = snd updated in',
                       '  type contribution_row = D.t M.t',
                       '| ConstraintSystem.Get (target, kget) ->\n          if is_dormant st target'):
            with self.assertRaises(ValueError):
                generator.transform_plus(source.replace(marker, 'changed boundary'), bitmap)

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
            for dependency in ('Batteries', 'Yojson', 'Goblint', 'Tc_solvers_extracted'):
                self.assertNotIn(dependency, metadata)
            consumer = root / 'consumer'
            consumer.mkdir()
            shutil.copyfile(ROOT / 'tests/library_api/api.ml', consumer / 'main.ml')
            run('ocamlc', '-I', str(lib), str(lib / 'tc_solvers.cma'), 'main.ml',
                '-o', 'main.exe', cwd=consumer)
            run(str(consumer / 'main.exe'), cwd=consumer)
            # Internal generated cores are not part of the public namespace.
            for internal in ('Core_simple', 'Core_plus_restarting'):
                (consumer / 'private.ml').write_text(f'module Hidden = Tc_solvers.{internal}\n')
                result = subprocess.run(['ocamlc', '-I', str(lib), '-c', 'private.ml'], cwd=consumer,
                                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('Unbound module', result.stdout)

            # Compile the private generated source in this temporary consumer
            # to inspect old contribution states without exposing runtime types.
            (consumer / 'interfaces.ml').write_text('include Tc_solvers\n')
            shutil.copyfile(ROOT / 'ocaml/library/generated/core_plus_restarting.ml',
                            consumer / 'cache_core.ml')
            (consumer / 'cache_state.ml').write_text(r'''module V = struct type t = int let eq_dec = Int.equal let hash = Hashtbl.hash end
module D = struct
  type t = int
  let bottom = 0
  let joins = ref 0
  let join a b = incr joins; a lor b
  let leq a b = a land b = a
end
module U = struct
  type phase = int
  let initial_phase _ _ = 0
  let update _ _ phase old input = phase+1,D.join old input
end
module SU = struct
  type phase = int
  let aggregates = ref []
  let initial_phase _ _ = 0
  let update _ _ phase _ input aggregate =
    aggregates := aggregate :: !aggregates;
    phase+1,input
end
module K = Set.Make(Int)
module S = struct
  type t = K.t
  let empty=K.empty let mem=K.mem let add=K.add let elements=K.elements
end
module T = Map.Make(Int)
module M = struct
  type 'a t = 'a T.t
  let empty=T.empty
  let lookup m k=T.find_opt k m
  let update m k v=T.add k v m
  let values m=List.map snd(T.bindings m)
end
module F = struct
  let recompute_controlled=true let defer_spawns=true
  let restart_side_phases=true let eliminate_dead_sides=true
end
module Observe = struct let enabled=false let emit _=assert false end
module C = Cache_core.Make(V)(D)(U)(SU)(S)(M)(F)(Observe)(struct let cache=true end)
let () =
  let before = List.fold_left C.observe C.empty_state [0;1;10] in
  let write state source input =
    let frame=C.fresh_frame state source 0 in
    fst(C.write_side_contribution state frame 10 input)
  in
  let a=write before 0 3 in
  let b=write a 0 2 in
  let c=write b 1 4 in
  let d=write c 0 1 in
  let e=write d 0 0 in
  let f=write e 1 4 in
  let g=write f 1 0 in
  assert(List.rev !(SU.aggregates)=[0;3;2;6;5;4;4]);
  assert((C.stored_side_cell f 1 10).C.side_phase=2);
  let joins= !(D.joins) in
  for _=0 to 100 do
    List.iter (fun (state,expected)->assert(C.aggregate state 10=expected))
      [before,0;a,3;b,2;c,6;d,5;e,4;f,4;g,0]
  done;
  assert(!(D.joins)=joins);
  assert(not(C.is_materialized g 10));
  let reset=C.reset_registered_cells a 0 in
  assert(C.aggregate reset 10=3 && !(D.joins)=joins);
  assert(C.contribution_row a 10 == C.contribution_row reset 10);
  assert((C.stored_side_cell reset 0 10).C.side_phase=0);
  let weak=Weak.create 1 in
  let fresh () =
    let old=C.replace_contribution C.empty_state 7 99 1 in
    Weak.set weak 0 (Some(C.contribution_row old 99).C.contributors);
    C.replace_contribution old 7 99 2
  in
  let latest=fresh() in
  Gc.full_major();
  assert(Weak.get weak 0=None);
  assert(C.aggregate (Sys.opaque_identity latest) 99=2);
  print_endline "aggregate states: old/new isolation, cached reads, reset retention, phases and historical-map release passed"
''')
            run('ocamlc', '-I', str(lib), str(lib / 'tc_solvers.cma'),
                'interfaces.ml', 'cache_core.ml', 'cache_state.ml',
                '-o', 'cache_state.exe', cwd=consumer)
            run(str(consumer / 'cache_state.exe'), cwd=consumer)
