open Datatypes
open Interfaces

module type DISCOVERY_ORDER =
 functor (V:VAR) ->
 sig
  type t

  val empty : t

  val lookup : t -> V.t -> int option

  val size : t -> int

  val observe : t -> V.t -> t * int
 end

module type STATELESS_RANK =
 functor (V:VAR) ->
 sig
  val rank : V.t -> int
 end

module FixedRankDiscoveryOrder :
 functor (V:VAR) ->
 functor (Fixed:sig
  val rank : V.t -> int
 end) ->
 sig
  type t = V.t list

  val empty : t

  val lookup : t -> V.t -> int option

  val size : t -> int

  val observe : t -> V.t -> t * int
 end

module ListDiscoveryOrder :
 functor (V:VAR) ->
 sig
  type t = V.t list

  val empty : t

  val lookup : t -> V.t -> int option

  val size : t -> int

  val observe : t -> V.t -> t * int
 end
