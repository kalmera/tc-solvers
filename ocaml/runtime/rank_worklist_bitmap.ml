(* A hierarchical bitmap for distinct dense nonnegative ranks. Each level
    summarizes the nonempty words of the level below it. Native OCaml integer
    words avoid the allocation incurred by boxed [int64] operations. *)

let word_shift = 5
let word_bits = 1 lsl word_shift
let word_mask = word_bits - 1
let level_count = 7

type t = {
  levels : int array array;
  mutable maximum : int;
}

let create () =
  { levels = Array.init level_count (fun _ -> [||]); maximum = -1 }

let[@inline always] is_empty queue = queue.maximum < 0

let ensure_word queue level index =
  let words = Array.unsafe_get queue.levels level in
  if index >= Array.length words then begin
    let capacity = max (index + 1) (max 4 (2 * Array.length words)) in
    let grown = Array.make capacity 0 in
    Array.blit words 0 grown 0 (Array.length words);
    Array.unsafe_set queue.levels level grown
  end

let rec set_index queue level index =
  let word_index = index lsr word_shift in
  ensure_word queue level word_index;
  let words = Array.unsafe_get queue.levels level in
  let previous = Array.unsafe_get words word_index in
  let bit = 1 lsl (index land word_mask) in
  if previous land bit = 0 then begin
    Array.unsafe_set words word_index (previous lor bit);
    if previous = 0 && level + 1 < level_count then
      set_index queue (level + 1) word_index
  end

let[@inline always] add queue rank =
  set_index queue 0 rank;
  if rank > queue.maximum then queue.maximum <- rank

let[@inline always] get_max_elt queue =
  if queue.maximum < 0 then invalid_arg "empty rank worklist";
  queue.maximum

let highest_bit word =
  let upper16 = word lsr 16 in
  let base16, part16 =
    if upper16 <> 0 then 16, upper16 else 0, word
  in
  let upper8 = part16 lsr 8 in
  let base8, byte =
    if upper8 <> 0 then base16 + 8, upper8 else base16, part16
  in
  base8 +
    if byte >= 128 then 7
    else if byte >= 64 then 6
    else if byte >= 32 then 5
    else if byte >= 16 then 4
    else if byte >= 8 then 3
    else if byte >= 4 then 2
    else if byte >= 2 then 1
    else 0

let mask_through offset =
  if offset = word_mask then -1
  else (1 lsl (offset + 1)) - 1

(* Find the greatest set index strictly below [limit] at [level], or [-1].
    The sentinel keeps maximum removal allocation-free. *)
let rec find_before queue level limit =
  if limit <= 0 then -1
  else
    let last = limit - 1 in
    let word_index = last lsr word_shift in
    let words = Array.unsafe_get queue.levels level in
    if word_index >= Array.length words then
      find_before queue level (Array.length words * word_bits)
    else
      let masked =
        Array.unsafe_get words word_index land
          mask_through (last land word_mask)
      in
      if masked <> 0 then
        (word_index * word_bits) + highest_bit masked
      else if level + 1 >= level_count then
        -1
      else
        let previous_word = find_before queue (level + 1) word_index in
        if previous_word < 0 then -1
        else
          let word = Array.unsafe_get words previous_word in
          (previous_word * word_bits) + highest_bit word

let rec clear_index queue level index =
  let word_index = index lsr word_shift in
  let words = Array.unsafe_get queue.levels level in
  let previous = Array.unsafe_get words word_index in
  let bit = 1 lsl (index land word_mask) in
  let next = previous land lnot bit in
  Array.unsafe_set words word_index next;
  if next = 0 && level + 1 < level_count then
    clear_index queue (level + 1) word_index

let[@inline always] remove_max queue =
  let maximum = queue.maximum in
  if maximum >= 0 then begin
    clear_index queue 0 maximum;
    queue.maximum <- find_before queue 0 maximum
  end

let[@inline always] pop_max queue =
  let result = queue.maximum in
  if result < 0 then None
  else begin
    remove_max queue;
    Some result
  end
