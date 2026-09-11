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
    (O : Order with type t = V.t) : sig
  module Ordering : Order with type t = O.t

  type t

  val empty : unit -> t
  val insert : V.t -> t -> t
  val insert_all : V.t list -> t -> t
  val peek_max : t -> V.t option
  val pop_max : t -> (V.t * t) option
end
