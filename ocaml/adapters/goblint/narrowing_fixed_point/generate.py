#!/usr/bin/env python3
"""Generate isolated adapters for the proved narrowing fixed-point machine.

Only callback control is extracted; mutable state operations are an adapter,
not a mechanized refinement. Inputs are the Restarting templates.
"""
from pathlib import Path
import os

here = Path(__file__).resolve().parent
extraction = here.parent
runtime = extraction.parent.parent / "runtime"
output = extraction / "generated"
output.mkdir(exist_ok=True)

def generate(inlined):
    # Expand the shared Restarting template.
    source = (extraction / 'goblint_slrtc_restarting.ml.in').read_text()
    control = (extraction / ('goblint_control_inlined.ml' if inlined else
                            '../../extracted/GoblintControl.ml')).read_text()
    import re
    control = re.sub(r'^(let (?:eval_rhs|solve_one|solve_loop_fuel|solve_seeds_with_fuel))0 ', r'\1 ', control, flags=re.M)
    source = source.replace('(* @@CONTROL@@ *)', 'module Control = struct\n' + control + '\nend')
    backend = os.environ.get('RANK_WORKLIST', 'bitmap')
    backends = {'bitmap':'rank_worklist_bitmap.ml', 'binary':'rank_worklist_binary_heap.ml',
                'pqueue':'rank_worklist_pqueue.ml'}
    if backend not in backends:
        raise ValueError(f'unsupported rank worklist {backend}')
    discovery = (extraction / 'goblint_discovery_order.ml.inc').read_text().replace(
        '    (* @@RANK_WORKLIST@@ *)', '    module RankQueue = struct\n' +
        (runtime / backends[backend]).read_text() + '\n    end')
    source = source.replace('    (* @@DISCOVERY_ORDER@@ *)', discovery)
    trace = '    let trace_supported = true\n    let trace_algorithm = "NarrowingFixedPoint"\n' + \
            f'    let trace_control = "{"inlined" if inlined else "extracted"}"\n' + \
            (extraction / 'goblint_trace.ml.inc').read_text()
    source = source.replace('    (* @@TRACE@@ *)', trace)
    source = source.replace('open Slrtc_update', 'open Slrtc_nfp_update')
    source = source.replace('Goblint callback adapter for SLR-TC Restarting.', 'Goblint callback adapter for Narrowing Fixed Point.')
    source = source.replace('[rocq/solvers/slr/restarting/Restarting.v]', '[rocq/solvers/slr/narrowing_fixed_point/NarrowingFixedPoint.v]')
    def once(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise ValueError(f'template changed, expected one {old!r}, found {source.count(old)}')
        source = source.replace(old, new)
    once('      S.Dom.equal left right',
         '      left == right || (S.Dom.leq left right && S.Dom.leq right left)')
    # Return the decision already made at commit, rather than comparing again
    # for owner recomputation and tracing. Equivalent updates retain the old value.
    a = source.index('    let[@inline always] set_value state frame direct =')
    b = source.index('    let solve xs roots _old_data =', a)
    source = source[:a] + '''    let[@inline always] set_value state frame direct =
      let owner = frame.owner in
      let owner_info = frame.owner_info in
      let candidate =
        S.Dom.join direct
          (S.Dom.join (start_value state owner) owner_info.side_aggregate)
      in
      let old = VH.find state.sigma owner in
      let changed =
        if lattice_equal candidate old then false
        else if owner_info.controlled then begin
          let next_phase, next =
            U.update false owner frame.owner_phase old candidate
          in
          frame.owner_phase <- next_phase;
          if lattice_equal next old then false
          else begin
            write_changed_value state frame.owner_rank owner_info owner next;
            true
          end
        end else begin
          write_changed_value state frame.owner_rank owner_info owner candidate;
          true
        end
      in
      if not changed then
        trace_value state.queue.trace frame.owner_rank false;
      changed

''' + source[b:]
    # Match the frozen generated feature interface without changing its source.
    a = source.index('module type FEATURES = sig')
    b = source.index('\nend', a) + len('\nend')
    source = source[:a] + '''module Features = struct
  let side_effect_phase_reset = true
  let dead_side_elimination = true
end
module type FEATURES = sig
  val side_effect_phase_reset : bool
  val dead_side_elimination : bool
end''' + source[b:]
    # Arbitrary clear_owner uses lazy deletion, with one physical entry per rank.
    once('      mutable queued : bool;', '      mutable queued : bool;\n      mutable resident : bool;')
    once('        queued = false;', '        queued = false;\n        resident = false;')
    once('    let[@inline always] queue_max_rank queue =\n      if RankQueue.is_empty queue.heap\n      then -1\n      else RankQueue.get_max_elt queue.heap', '''    let rec queue_max_rank queue =
      if RankQueue.is_empty queue.heap then -1 else
      let r = RankQueue.get_max_elt queue.heap in
      let info = Dynarray.get queue.infos r in
      if info.queued then r else begin
        RankQueue.remove_max queue.heap;
        info.resident <- false;
        queue_max_rank queue
      end''')
    once('        RankQueue.add queue.heap variable_rank;', '''        if not info.resident then begin
          RankQueue.add queue.heap variable_rank;
          info.resident <- true
        end;''')
    once('      info.queued <- false;', '      info.queued <- false;\n      info.resident <- false;')
    a = source.index('    let[@inline always] queue_pop queue =')
    b = source.index('    let[@inline always] trace_get', a)
    source = source[:a] + '''    let[@inline always] queue_pop queue =
      ignore (queue_max_rank queue);
      match RankQueue.pop_max queue.heap with
      | None -> None | Some r -> Some (finish_queue_pop queue r)

''' + source[b:]
    once('      mutable previous_targets : set option;\n', '')
    once('            previous_targets = None;\n', '')
    once('      mutable current_targets : set option;', '''      mutable current_targets : set option;
      mutable publication_targets : S.v list;
      mutable previous_order : S.v list;''')
    once('            current_targets = None;', '''            current_targets = None;
            publication_targets = [];
            previous_order = [];''')
    once('      let state = create_state () in', '''      let state = create_state () in
      let last_order = VH.create 32 in''')
    once('''            frame.previous_targets <-
              begin match state.last_targets with
              | Some last_targets -> VH.find_option last_targets owner
              | None -> None
              end;
''', '')
    once('        let start_evaluation _ =\n          frame.min_scope', '''        let start_evaluation _ =
          owner_info.queued <- false;
          frame.previous_order <- VH.find_default last_order owner [];
          frame.publication_targets <- [];
          frame.min_scope''')
    once('''              finish_evaluation frame;
              set_value state frame direct)
            (fun _ -> drain_episode ())''', '''              finish_evaluation frame;
              let next_rank = queue_max_rank state.queue in
              if owner_info.controlled && next_rank > owner_rank then begin
                let next = queue_remove_max state.queue next_rank in
                solve_episode next;
                evaluate_owner ()
              end else if owner_info.queued then
                evaluate_owner ()
              else begin
                let changed = set_value state frame direct in
                if owner_info.controlled && changed then
                  enqueue state owner;
                drain_episode ()
              end)
            (fun _ -> ())''')
    # Initial contributions are RHS constants, as in the extracted reference.
    # Let the first controlled update observe them; solve_initial seeds their roots.
    once('''          VH.replace state.starts variable start;
          VH.replace state.sigma variable start)''',
         '''          VH.replace state.starts variable start)''')
    once('      and side frame target raw =\n', '''      and side frame target raw =
        ignore (rank state.queue target);
''')
    once('        VH.replace local_side target input;', '''        if not (VH.mem local_side target) then
          frame.publication_targets <- target :: frame.publication_targets;
        VH.replace local_side target input;''')
    once('''        end;
        write_side_contribution frame target input

      and write_side_contribution frame target input =''', '''        end

      and write_side_contribution ?(live=false) frame target input =''')
    once('        VH.replace contributions source next_contribution;', '''        VH.replace contributions source next_contribution;
        let old_leq_next =
          old_contribution == next_contribution ||
          S.Dom.leq old_contribution next_contribution
        in
        let cell_changed =
          not (old_leq_next &&
            (old_contribution == next_contribution ||
             S.Dom.leq next_contribution old_contribution))
        in
        if cell_changed then
          enqueue state source;''')
    once('          if S.Dom.leq old_contribution next_contribution then',
         '          if old_leq_next then')
    once('''          if source_rank < target_rank
             && not (VH.mem state.sigma target)''', '''          if not live && source_rank < target_rank
             && not (VH.mem state.sigma target)''')
    a = source.index('      and finish_evaluation frame =')
    b = source.index('      and spawn frame target =', a)
    source = source[:a] + '''      and finish_evaluation frame =
        if Features.dead_side_elimination then
          List.iter (fun target ->
            let current = match frame.current_targets with
              | Some targets -> VH.mem targets target | None -> false in
            if not current then write_side_contribution frame target bottom)
            frame.previous_order;
        (* Publish the complete batch in list-set order. Live writes enqueue;
           they never enter a target episode in the middle of the batch. *)
        List.iter (fun target ->
          let input = match frame.local_side with
            | Some values -> VH.find values target | None -> bottom in
          write_side_contribution ~live:true frame target input)
          frame.publication_targets;
        VH.replace last_order frame.owner frame.publication_targets;
        if Features.dead_side_elimination then begin
          match state.last_targets, frame.current_targets with
          | Some targets, Some current -> VH.replace targets frame.owner current
          | None, Some current ->
            let targets = VH.create 32 in
            state.last_targets <- Some targets;
            VH.replace targets frame.owner current
          | Some targets, None -> VH.remove targets frame.owner
          | None, None -> ()
        end

''' + source[b:]
    once('''                let next = queue_remove_max state.queue next_rank in
                solve_episode next;
                evaluate_owner ()''', '''                let rec drain_higher () =
                  let next_rank = queue_max_rank state.queue in
                  if next_rank > owner_rank then begin
                    let next = queue_remove_max state.queue next_rank in
                    solve_episode next;
                    drain_higher ()
                  end
                in
                drain_higher ();
                evaluate_owner ()''')
    if '@@' in source.replace('[@@CONTROL@@]', ''):
        raise ValueError('unexpanded marker')
    variant = 'narrowing_fixed_point'
    name = f'slrtc_{"inlined_" if inlined else ""}{variant}.ml'
    description = 'narrowing fixed-point'
    target = 'goblint-solvers'
    (output / name).write_text(
        f'(* GENERATED: {description}, {backend} worklist. make {target} *)\n' + source)

for inline in (False, True):
    generate(inline)
update = (extraction / 'goblint_slrtc_update.ml').read_text()
update += '''\n(** Finite-height join iteration; the caller supplies the domain. *)
module JoinUpdate (S : DemandEqConstrSys) = struct
  type phase = unit
  let initial_phase _ _ = ()
  let update _ _ _ old input = (), S.Dom.join old input
end
'''
(output / 'slrtc_nfp_update.ml').write_text(update)
print('generated extracted-control and inlined narrowing fixed-point adapters')
