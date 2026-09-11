module type Variable = sig
  type t

  val equal : t -> t -> bool
  val hash : t -> int
end

module type Order = sig
  type t

  val lt : t -> t -> bool
end

module Make
    (V : Variable)
    (O : Order with type t = V.t) =
struct
  module Ordering = O

  module Heap = Pqueue.MakeMax (struct
    type t = V.t

    let compare left right =
      if Ordering.lt left right then -1
      else if Ordering.lt right left then 1
      else 0
  end)

  module Present = Hashtbl.Make (struct
    type t = V.t

    let equal = V.equal
    let hash = V.hash
  end)

  type t = {
    heap : Heap.t;
    present : unit Present.t;
  }

  let empty () =
    {
      heap = Heap.create ();
      present = Present.create 16;
    }

  let insert value queue =
    if not (Present.mem queue.present value) then begin
      Heap.add queue.heap value;
      Present.add queue.present value ()
    end;
    queue

  let insert_all values queue =
    List.iter (fun value -> ignore (insert value queue)) values;
    queue

  let peek_max queue =
    Heap.max_elt queue.heap

  let pop_max queue =
    match Heap.pop_max queue.heap with
    | None ->
        None
    | Some value ->
        Present.remove queue.present value;
        Some (value, queue)
end
