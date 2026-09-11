(** OCaml 5.4 reference backend. *)

include Pqueue.MakeMax (struct
  type t = int

  let compare = Int.compare
end)
