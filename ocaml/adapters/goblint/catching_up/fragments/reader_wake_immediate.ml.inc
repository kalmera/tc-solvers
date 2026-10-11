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

let[@inline always] fresh_rank queue variable =
  let result = queue.next_rank in
  queue.next_rank <- result + 1;
  VH.replace queue.ranks variable result;
  Dynarray.add_last queue.infos (make_rank_info variable);
  trace_node queue.trace result variable;
  result

let[@inline always] rank queue variable =
  match VH.find_option queue.ranks variable with
  | Some result -> result
  | None -> fresh_rank queue variable

(* Queue ranks are nonnegative, so [-1] denotes an empty heap without
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

let queue_defer_side_stabilization = false

let[@inline always] queue_insert_side queue variable =
  queue_insert queue variable

let queue_insert_readers queue _changed_rank readers =
  VH.iter (fun reader () -> queue_insert queue reader) readers

let[@inline always] queue_force_side _queue _target_rank = false

let[@inline always] queue_note_evaluation _queue _owner_rank = ()

let[@inline always] queue_enter_episode _queue = ()

let[@inline always] queue_leave_episode _queue = ()

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
