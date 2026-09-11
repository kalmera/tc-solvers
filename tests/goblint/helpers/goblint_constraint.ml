(** Minimal frontend signatures for running the unchanged generated adapters.
    The real Goblint build separately checks its complete interfaces. *)
open Batteries

module ConstrSys = struct
  module type DemandEqConstrSys = sig
    type v
    type d
    module Var : sig
      type t = v
      val equal : t -> t -> bool
      val var_id : t -> string
      val pretty_trace : unit -> t -> string
    end
    module Dom : sig
      type t = d
      val bot : unit -> t
      val equal : t -> t -> bool
      val leq : t -> t -> bool
      val join : t -> t -> t
      val widen : t -> t -> t
      val narrow : t -> t -> t
      val show : t -> string
    end
    val system : v -> ((v -> d) -> (v -> d -> unit) -> (v -> unit) -> d) option
  end
end

module SolverTypes = struct
  module type IncrSolverArg = sig
    val should_prune : bool
    val should_verify : bool
    val should_warn : bool
    val should_save_run : bool
  end
  module type DemandEqIncrSolver =
    functor (Arg : IncrSolverArg)
      (S : ConstrSys.DemandEqConstrSys)
      (H : Hashtbl.S with type key = S.v) -> sig
      type marshal
      val copy_marshal : marshal -> marshal
      val relift_marshal : marshal -> marshal
      val solve : (S.v * S.d) list -> S.v list -> marshal option -> S.d H.t * marshal
    end
end
