#!/usr/bin/env python3
"""Generate Plus Restarting (SLR-TC+) adapters from Dirty-Read Restarting."""
from pathlib import Path
import os
here = Path(__file__).resolve().parent
output = Path(os.environ.get("CATCHING_UP_OUTPUT", str(here.parent / "generated")))
for control in ('', 'inlined_'):
    s = (output / f'slrtc_{control}dirty_read_restarting.ml').read_text()
    s = s.replace('  val side_effect_phase_reset : bool', '  val recompute_controlled : bool\n  val defer_spawns : bool\n  val side_effect_phase_reset : bool', 1)
    s = s.replace('  let side_effect_phase_reset = true', '  let recompute_controlled = false\n  let defer_spawns = true\n  let side_effect_phase_reset = true', 1)
    old = """            if not (lattice_equal next old) then
              write_changed_value state frame.owner_rank owner_info owner next"""
    new = """            if not (lattice_equal next old) then begin
              write_changed_value state frame.owner_rank owner_info owner next;
              if Features.recompute_controlled then
                enqueue state owner
            end"""
    assert s.count(old) == 1
    s = s.replace(old, new)
    old = '      let state = create_state () in'
    new = '''      let state = create_state () in
          let pending_fifo = Stdlib.Queue.create () in
          let demanded = VH.create 16 in
          let defer_spawn target =
            if not (VH.mem demanded target) then begin
              VH.replace demanded target ();
              Stdlib.Queue.add target pending_fifo
            end
          in
          let pop_spawn () =
            Stdlib.Queue.take_opt pending_fifo
          in'''
    assert s.count(old) == 1
    s = s.replace(old, new)
    old = '      and spawn frame target =\n        let owner_rank = frame.owner_rank in'
    new = '''      and spawn frame target =
            if Features.defer_spawns then defer_spawn target
            else spawn_immediate frame target

          and spawn_immediate frame target =
            let owner_rank = frame.owner_rank in'''
    assert s.count(old) == 1
    s = s.replace(old, new)
    old = '      solve_initial state.queue is_started solve_requested roots xs;'
    new = '''      solve_initial state.queue is_started solve_requested roots xs;
          (* Drain ordinary work completely before selecting the next deferred demand.
             A real read still solves its target immediately through the normal get. *)
          let rec drain_spawns () =
            match pop_spawn () with
            | None -> ()
            | Some target ->
              solve_initial state.queue is_started solve_requested [target] [];
              drain_spawns ()
          in
          drain_spawns ();'''
    assert s.count(old) == 1
    s = s.replace(old, new)
    s = s.replace('DirtyReadRestarting', 'PlusRestarting').replace('dirty_read_restarting/PlusRestarting.v', 'plus_restarting/PlusRestarting.v')
    (output / f'slrtc_{control}plus_restarting.ml').write_text(s)
