open Interfaces
open List

module ListSet :
 functor (V:VAR) ->
 sig
  type t = V.t list

  val empty : t

  val mem : V.t -> t -> bool

  val add : V.t -> t -> t

  val elements : t -> V.t list
 end

module AssocMap :
 functor (V:VAR) ->
 sig
  type 'a t = (V.t * 'a) list

  val empty : 'a1 t

  val lookup : 'a1 t -> V.t -> 'a1 option

  val update : 'a1 t -> V.t -> 'a1 -> 'a1 t

  val values : 'a1 t -> 'a1 list
 end

module OrderedListQueue :
 functor (V:VAR) ->
 functor (O:sig
  val lt : V.t -> V.t -> bool
 end) ->
 sig
  type t = V.t list

  val empty : unit -> t

  val insert_fresh : V.t -> t -> t

  val insert : V.t -> t -> t

  val insert_all : V.t list -> t -> t

  val peek_max : t -> V.t option

  val pop_max : t -> (V.t * t) option
 end
