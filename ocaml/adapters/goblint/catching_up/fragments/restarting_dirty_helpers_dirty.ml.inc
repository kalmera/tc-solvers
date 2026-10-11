let[@inline always] defer_readers state readers =
  let deferred =
    match state.deferred_wakes with
    | Some deferred -> deferred
    | None ->
      let deferred = VH.create 4 in
      state.deferred_wakes <- Some deferred;
      deferred
  in
  VH.iter (fun reader () -> VH.replace deferred reader ()) readers

let[@inline always] flush_deferred state =
  match state.deferred_wakes with
  | None -> ()
  | Some deferred ->
    queue_insert_readers state.queue (-1) deferred;
    VH.clear deferred

let[@inline always] write_dirty_value
    state target_rank target_info target value =
  VH.replace state.sigma target value;
  trace_value state.queue.trace target_rank true;
  begin match target_info.readers with
  | None -> ()
  | Some readers ->
    defer_readers state readers;
    VH.clear readers
  end

let[@inline always] try_dirty_read
    state owner_rank target_rank target_info target =
  if owner_rank <> target_rank
     && queue_side_dirty state.queue target_rank
     && VH.mem state.sigma target
  then
    match S.system target with
    | Some _ -> ()
    | None ->
      let old = VH.find state.sigma target in
      let candidate =
        S.Dom.join (start_value state target) target_info.side_aggregate
      in
      let was_controlled = target_info.controlled in
      if lattice_equal candidate old then begin
        target_info.started <- true;
        target_info.controlled <- true;
        queue_cancel state.queue target_rank
      end else if was_controlled then begin
        let _, next =
          U.update false target (U.initial_phase false target) old candidate
        in
        if S.Dom.leq old next then begin
          target_info.started <- true;
          target_info.controlled <- true;
          queue_cancel state.queue target_rank;
          if not (lattice_equal next old) then
            write_dirty_value state target_rank target_info target next
        end
      end else if S.Dom.leq old candidate then begin
        target_info.started <- true;
        target_info.controlled <- true;
        queue_cancel state.queue target_rank;
        write_dirty_value state target_rank target_info target candidate
      end
