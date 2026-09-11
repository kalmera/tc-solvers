    (** Default online order for callback-based solvers. Variables receive
        dense, increasing ranks when first encountered. Existing ranks never
        change, and the work queue always selects the greatest queued rank. *)
    (* @@RANK_WORKLIST@@ *)

    type queue = {
      heap : RankQueue.t;
      trace : trace;
      infos : rank_info Dynarray.t;
      ranks : int VH.t;
      mutable next_rank : int;
    }

    let[@inline always] create_queue () =
      {
        heap = RankQueue.create ();
        trace = create_trace ();
        infos = Dynarray.create ();
        ranks = VH.create 32;
        next_rank = 0;
      }

    let[@inline always] rank queue variable =
      try VH.find queue.ranks variable with Not_found ->
        let result = queue.next_rank in
        queue.next_rank <- result + 1;
        VH.replace queue.ranks variable result;
        Dynarray.add_last queue.infos (make_rank_info variable);
        trace_node queue.trace result variable;
        result

    (** Queue ranks are nonnegative, so [-1] denotes an empty heap without
        allocating an [option] in the episode-draining hot path. *)
    let[@inline always] queue_max_rank queue =
      if RankQueue.is_empty queue.heap
      then -1
      else RankQueue.get_max_elt queue.heap

    let[@inline always] queue_insert queue variable =
      let variable_rank = rank queue variable in
      let info = Dynarray.get queue.infos variable_rank in
      if not info.queued then begin
        info.variable <- variable;
        RankQueue.add queue.heap variable_rank;
        info.queued <- true;
        trace_queue queue.trace "push" variable_rank
      end

    let[@inline always] finish_queue_pop queue result_rank =
      let info = Dynarray.get queue.infos result_rank in
      info.queued <- false;
      trace_queue queue.trace "pop" result_rank;
      info.variable

    let[@inline always] queue_remove_max queue result_rank =
      RankQueue.remove_max queue.heap;
      finish_queue_pop queue result_rank

    let[@inline always] queue_pop queue =
      match RankQueue.pop_max queue.heap with
      | None -> None
      | Some result_rank ->
        Some (finish_queue_pop queue result_rank)

    let[@inline always] trace_get queue source_rank target_rank =
      match queue.trace with
      | TraceDisabled -> ()
      | TraceEnabled _ ->
        let selected = target_rank <= source_rank in
        let new_w =
          selected
          && not (Dynarray.get queue.infos target_rank).controlled
        in
        trace_dependency queue.trace "get" source_rank target_rank
          (if selected then Some target_rank else None) new_w

    let[@inline always] trace_side queue source_rank target_rank =
      match queue.trace with
      | TraceDisabled -> ()
      | TraceEnabled _ ->
        let selected = source_rank <= target_rank in
        let new_w =
          selected
          && not (Dynarray.get queue.infos source_rank).controlled
        in
        trace_dependency queue.trace "side" source_rank target_rank
          (if selected then Some source_rank else None) new_w

    let[@inline always] seed_started queue variable =
      match VH.find_option queue.ranks variable with
      | None -> false
      | Some variable_rank ->
        (Dynarray.get queue.infos variable_rank).started

    (** Roots are discovered one at a time. Work reached from one seed is
        drained before the next seed can receive a rank. Starting-state
        variables which were not reached from a root are seeded afterward. *)
    let solve_initial queue solve_episode roots starts =
      let seeds = roots @ List.map fst starts in
      match
        Control.solve_seeds_with_fuel Stdlib.max_int
          (seed_started queue)
          (fun () -> queue_pop queue)
          solve_episode seeds
      with
      | Control.SeedsSolved _ -> ()
      | Control.SeedsOutOfFuel ->
        failwith "SLRTC: exhausted max_int seed fuel"

    let finish_trace queue =
      match queue.trace with
      | TraceDisabled -> ()
      | TraceEnabled _ ->
        let w = ref 0 in
        Dynarray.iter
          (fun info -> if info.controlled then incr w)
          queue.infos;
        trace_finish queue.trace (Dynarray.length queue.infos) !w
