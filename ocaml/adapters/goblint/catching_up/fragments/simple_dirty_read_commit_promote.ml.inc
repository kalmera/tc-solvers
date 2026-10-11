let was_controlled = target_info.controlled in
if lattice_equal candidate old then begin
  target_info.started <- true;
  target_info.controlled <- true;
  queue_cancel state.queue target_rank;
  Some old
end else
  let phase =
    match target_info.normal_phase with
    | Some phase -> phase
    | None -> U.initial_phase false target
  in
  let next_phase, next =
    if was_controlled then
      U.update false target phase old candidate
    else
      phase, candidate
  in
  if S.Dom.leq old next then begin
    target_info.started <- true;
    target_info.controlled <- true;
    if was_controlled then
      target_info.normal_phase <- Some next_phase;
    if not (lattice_equal next old) then
      write_changed_value
        state target_rank target_info target next;
    queue_cancel state.queue target_rank;
    Some next
  end else
    None
