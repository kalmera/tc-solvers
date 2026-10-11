type queue = {
  heap : RankQueue.t;
  trace : trace;
  physically_queued : bool Dynarray.t;
  side_dirty : bool Dynarray.t;
  infos : rank_info Dynarray.t;
  ranks : int VH.t;
  mutable next_rank : int;
}

let[@inline always] create_queue () =
  {
    heap = RankQueue.create ();
    trace = create_trace ();
    physically_queued = Dynarray.create ();
    side_dirty = Dynarray.create ();
    infos = Dynarray.create ();
    ranks = VH.create 32;
    next_rank = 0;
  }

let[@inline always] fresh_rank queue variable =
  let result = queue.next_rank in
  queue.next_rank <- result + 1;
  VH.replace queue.ranks variable result;
  Dynarray.add_last queue.infos (make_rank_info variable);
  Dynarray.add_last queue.physically_queued false;
  Dynarray.add_last queue.side_dirty false;
  trace_node queue.trace result variable;
  result

let[@inline always] rank queue variable =
  match VH.find_option queue.ranks variable with
  | Some result -> result
  | None -> fresh_rank queue variable

let[@inline always] queue_insert queue variable =
  let variable_rank = rank queue variable in
  let info = Dynarray.get queue.infos variable_rank in
  if not info.queued then begin
    info.variable <- variable;
    info.queued <- true;
    if not (Dynarray.get queue.physically_queued variable_rank) then begin
      Dynarray.set queue.physically_queued variable_rank true;
      RankQueue.add queue.heap variable_rank
    end;
    trace_queue queue.trace "push" variable_rank
  end

let queue_defer_side_stabilization = false

let[@inline always] queue_insert_side queue variable =
  queue_insert queue variable

let queue_insert_readers queue _changed_rank readers =
  VH.iter (fun reader () -> queue_insert queue reader) readers

let[@inline always] queue_force_side _queue _target_rank = false

let[@inline always] queue_mark_side_dirty queue target_rank =
  Dynarray.set queue.side_dirty target_rank true

let[@inline always] queue_clear_side_dirty queue target_rank =
  Dynarray.set queue.side_dirty target_rank false

let[@inline always] queue_side_dirty queue target_rank =
  Dynarray.get queue.side_dirty target_rank

let[@inline always] queue_cancel queue target_rank =
  (Dynarray.get queue.infos target_rank).queued <- false;
  queue_clear_side_dirty queue target_rank

let[@inline always] finish_physical_pop queue result_rank =
  Dynarray.set queue.physically_queued result_rank false;
  let info = Dynarray.get queue.infos result_rank in
  if info.queued then begin
    info.queued <- false;
    trace_queue queue.trace "pop" result_rank;
    Some info.variable
  end else
    None

let rec discard_cancelled_maxima queue =
  if not (RankQueue.is_empty queue.heap) then begin
    let maximum = RankQueue.get_max_elt queue.heap in
    if not (Dynarray.get queue.infos maximum).queued then begin
      RankQueue.remove_max queue.heap;
      Dynarray.set queue.physically_queued maximum false;
      discard_cancelled_maxima queue
    end
  end

let[@inline always] queue_max_rank queue =
  discard_cancelled_maxima queue;
  if RankQueue.is_empty queue.heap then -1 else RankQueue.get_max_elt queue.heap

let[@inline always] queue_remove_max queue result_rank =
  RankQueue.remove_max queue.heap;
  match finish_physical_pop queue result_rank with
  | Some variable -> variable
  | None -> assert false

let rec queue_pop queue =
  match RankQueue.pop_max queue.heap with
  | None -> None
  | Some result_rank ->
    begin match finish_physical_pop queue result_rank with
    | Some variable -> Some variable
    | None -> queue_pop queue
    end

let[@inline always] queue_note_evaluation _queue _owner_rank = ()
let[@inline always] queue_enter_episode _queue = ()
let[@inline always] queue_leave_episode _queue = ()
