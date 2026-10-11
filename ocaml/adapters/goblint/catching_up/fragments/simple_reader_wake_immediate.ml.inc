type queue = {
  heap : RankQueue.t;
  infos : rank_info Dynarray.t;
  ranks : int VH.t;
  mutable next_rank : int;
}

let[@inline always] create_queue () =
  {
    heap = RankQueue.create ();
    infos = Dynarray.create ();
    ranks = VH.create 32;
    next_rank = 0;
  }

let[@inline always] fresh_rank queue variable =
  let result = queue.next_rank in
  queue.next_rank <- result + 1;
  VH.replace queue.ranks variable result;
  Dynarray.add_last queue.infos (make_rank_info variable);
  result

let[@inline always] rank queue variable =
  match VH.find_option queue.ranks variable with
  | Some result -> result
  | None -> fresh_rank queue variable

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
    info.queued <- true
  end

let[@inline always] queue_insert_readers queue _changed_rank readers =
  VH.iter (fun reader () -> queue_insert queue reader) readers

let[@inline always] queue_note_side_change
    _queue _source_rank _target_rank = ()

let[@inline always] queue_clear_side_dirty _queue _target_rank = ()

let[@inline always] queue_can_flush_dirty_read
    _queue _owner_rank _target_rank = false

let[@inline always] queue_cancel _queue _target_rank = ()

let[@inline always] queue_note_evaluation _queue _owner_rank = ()

let[@inline always] queue_enter_episode _queue = ()

let[@inline always] queue_leave_episode _queue = ()

let[@inline always] finish_queue_pop queue result_rank =
  let info = Dynarray.get queue.infos result_rank in
  info.queued <- false;
  info.variable

let[@inline always] queue_remove_max queue result_rank =
  RankQueue.remove_max queue.heap;
  finish_queue_pop queue result_rank

let[@inline always] queue_pop queue =
  match RankQueue.pop_max queue.heap with
  | None -> None
  | Some result_rank -> Some (finish_queue_pop queue result_rank)
