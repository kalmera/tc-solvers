open Interfaces

module type S =
 functor (V:VAR) ->
 functor (D:DOMAIN) ->
 sig
  type rhs

  val coq_Ret : D.t -> rhs

  val coq_Get : V.t -> (D.t -> rhs) -> rhs

  val coq_Side : V.t -> D.t -> rhs -> rhs

  val coq_Spawn : V.t -> rhs -> rhs

  type system = V.t -> rhs
 end

module Make :
 functor (V:VAR) ->
 functor (D:DOMAIN) ->
 sig
  type rhs =
  | Ret of D.t
  | Get of V.t * (D.t -> rhs)
  | Side of V.t * D.t * rhs
  | Spawn of V.t * rhs

  val rhs_rect :
    (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
    D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

  val rhs_rec :
    (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
    D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

  type system = V.t -> rhs
 end
