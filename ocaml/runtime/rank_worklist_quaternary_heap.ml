(** A four-child max-heap for the same distinct integer-rank workload as the
    binary backend. *)

type t = {
  mutable data : int array;
  mutable size : int;
}

let create () = { data = [||]; size = 0 }
let[@inline always] is_empty queue = queue.size = 0

let ensure_capacity queue value =
  if queue.size = Array.length queue.data then begin
    let capacity = max 16 (2 * queue.size) in
    let data = Array.make capacity value in
    Array.blit queue.data 0 data 0 queue.size;
    queue.data <- data
  end

let rec sift_up data position value =
  if position = 0 then
    Array.unsafe_set data 0 value
  else
    let parent = (position - 1) / 4 in
    let parent_value = Array.unsafe_get data parent in
    if value > parent_value then begin
      Array.unsafe_set data position parent_value;
      sift_up data parent value
    end else
      Array.unsafe_set data position value

let[@inline always] add queue value =
  ensure_capacity queue value;
  let position = queue.size in
  queue.size <- position + 1;
  sift_up queue.data position value

let[@inline always] get_max_elt queue =
  if queue.size = 0 then invalid_arg "empty rank worklist";
  Array.unsafe_get queue.data 0

let[@inline always] greater_child data size first =
  let selected = ref first in
  let limit = min size (first + 4) in
  for candidate = first + 1 to limit - 1 do
    if Array.unsafe_get data candidate > Array.unsafe_get data !selected then
      selected := candidate
  done;
  !selected

let rec sift_down data size position value =
  let first = (4 * position) + 1 in
  if first >= size then
    Array.unsafe_set data position value
  else
    let child = greater_child data size first in
    let child_value = Array.unsafe_get data child in
    if child_value > value then begin
      Array.unsafe_set data position child_value;
      sift_down data size child value
    end else
      Array.unsafe_set data position value

let[@inline always] remove_max queue =
  let size = queue.size in
  if size > 0 then begin
    let next_size = size - 1 in
    queue.size <- next_size;
    if next_size > 0 then
      sift_down queue.data next_size 0
        (Array.unsafe_get queue.data next_size)
  end

let[@inline always] pop_max queue =
  if queue.size = 0 then None
  else begin
    let result = Array.unsafe_get queue.data 0 in
    remove_max queue;
    Some result
  end
