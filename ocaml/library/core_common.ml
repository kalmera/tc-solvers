module type SYSTEM = sig
  type v
  type d
  module Var : sig type t = v val equal : t -> t -> bool end
  module Dom : sig
    type t = d
    val bot : unit -> t
    val equal : t -> t -> bool
    val leq : t -> t -> bool
    val join : t -> t -> t
  end
  val system : v -> ((v -> d) -> (v -> d -> unit) -> (v -> unit) -> d) option
end
module type TABLE = sig
  include Hashtbl.S
  val find_option : 'a t -> key -> 'a option
  val find_default : 'a t -> key -> 'a -> 'a
end
module Table (V : Interfaces.VAR) = struct
  include Hashtbl.Make (V)
  let find_option = find_opt
  let find_default table key default =
    match find_opt table key with Some value -> value | None -> default
end
