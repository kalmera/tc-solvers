#!/usr/bin/env python3
"""Generate compile-time FIFO-deferred Dirty-Read Simple adapters."""
from pathlib import Path
import os

here = Path(__file__).resolve().parent
output = Path(os.environ.get("CATCHING_UP_OUTPUT", str(here.parent / "generated")))


def replace_once(source, old, new):
    assert source.count(old) == 1, old
    return source.replace(old, new, 1)


for control in ('', 'inlined_'):
    source = (output / f'slrtc_{control}dirty_read_simple.ml').read_text()
    source = replace_once(source, 'module Make\n', '''module type FEATURES = sig val defer_spawns : bool end
module DeferredFeatures = struct let defer_spawns = true end

module Make
''')
    source = replace_once(source, '    (Control : CONTROL)\n',
                          '    (Control : CONTROL)\n    (Features : FEATURES)\n')
    source = replace_once(source, '      let state = create_state () in', '''      let state = create_state () in
      let pending_fifo = Stdlib.Queue.create () in
      let demanded = VH.create 16 in
      let defer_spawn target =
        if not (VH.mem demanded target) then begin
          VH.replace demanded target ();
          Stdlib.Queue.add target pending_fifo
        end
      in''')
    source = replace_once(source, '      and spawn frame target =\n', '''      and spawn frame target =
        if Features.defer_spawns then defer_spawn target
        else spawn_immediate frame target

      and spawn_immediate frame target =
''')
    source = replace_once(source, '      if dormant_stats_enabled then\n        Stdlib.Printf.eprintf', '''      let rec drain_spawns () =
        match Stdlib.Queue.take_opt pending_fifo with
        | None -> ()
        | Some target ->
          begin match Control.solve_seeds_with_fuel Stdlib.max_int
            is_started (fun () -> queue_pop state.queue) solve_requested [target] with
          | Control.SeedsSolved _ -> ()
          | Control.SeedsOutOfFuel -> failwith "Deferred Simple: exhausted spawn fuel"
          end;
          drain_spawns ()
      in
      drain_spawns ();
      if dormant_stats_enabled then
        Stdlib.Printf.eprintf''')
    source = source.replace('Make (Control) (', 'Make (Control) (DeferredFeatures) (')
    source = source.replace('DirtyReadSimple', 'DeferredSimple')
    source = source.replace('Dormant Simple', 'Deferred Simple')
    source = source.replace('dormant_simple/DormantSimple.v', 'deferred_simple/DeferredSimple.v')
    source = source.replace('make test-dormant-adapters', 'make test-deferred-simple-adapters')
    (output / f'slrtc_{control}deferred_simple.ml').write_text(source)
