(* SLR-TC Goblint registrations. Generated adapters use the shared update module. *)
open Batteries
open PostSolver
open Goblint_constraint.ConstrSys
open Goblint_constraint.SolverTypes
open Goblint_constraint.Translators

module AddPost (Sol : DemandEqIncrSolver) = functor (Arg : IncrSolverArg)
  (S : DemandEqConstrSys)
  (VH : Hashtbl.S with type key = S.v) ->
struct
  module Sol = Sol (Arg) (S) (VH)
  type marshal = Sol.marshal
  let copy_marshal = Sol.copy_marshal
  let relift_marshal = Sol.relift_marshal


  let solve xs vs qs =
    let (rho, m) = Sol.solve xs vs qs in
    let module EqS = EqConstrSysFromDemandConstrSys (S) in
    let module MakeIncrListArg =
    struct
      module Arg = Arg
      include ListArgFromStdArg (EqS) (VH) (Arg)
      let init_reachable ~vh = VH.create (VH.length vh)
    end
    in

    let module Post = MakeIncrList (MakeIncrListArg) in
    Post.post xs vs rho;
    (rho, m)
end

module Features = struct
  let recompute_controlled = false
  let side_effect_phase_reset = false
  let dead_side_elimination = false
end
module Fifo = struct include Features let defer_spawns = true end
module FifoRecompute = struct include Fifo let recompute_controlled = true end
module Immediate = struct include Features let defer_spawns = false end
module U = Slrtc_catching_up_update.DefaultUpdate
(* The historical slrtc_dfr identifiers remain aliases for benchmark compatibility. *)
let () = Selector.add_solver ("slrtc_s_default", (module AddPost (Slrtc_simple.Make (Slrtc_simple.Control) (U))))
let () = Selector.add_solver ("slrtc_r_no_side_reset_keep_dead_default", (module AddPost (Slrtc_restarting.Make (Slrtc_restarting.Control) (Features) (U))))
let () = Selector.add_solver ("slrtc_rr_no_side_reset_keep_dead_default", (module AddPost (Slrtc_reluctant_restarting.Make (Slrtc_reluctant_restarting.Control) (Features) (U))))
let () = Selector.add_solver ("slrtc_dr_no_side_reset_keep_dead_default", (module AddPost (Slrtc_dormant_restarting.Make (Slrtc_dormant_restarting.Control) (Features) (Slrtc_dormant_restarting.ReluctantSidePolicy) (U))))
let () = Selector.add_solver ("slrtc_drr_no_side_reset_keep_dead_default", (module AddPost (Slrtc_dirty_read_restarting.Make (Slrtc_dirty_read_restarting.Control) (Features) (Slrtc_dirty_read_restarting.ReluctantSidePolicy) (U))))
let () = Selector.add_solver ("slrtc_plus_restarting_no_side_reset_keep_dead_default", (module AddPost (Slrtc_plus_restarting.Make (Slrtc_plus_restarting.Control) (Fifo) (Slrtc_plus_restarting.ReluctantSidePolicy) (U))))
let () = Selector.add_solver ("slrtc_dfr_no_side_reset_keep_dead_default", (module AddPost (Slrtc_plus_restarting.Make (Slrtc_plus_restarting.Control) (Fifo) (Slrtc_plus_restarting.ReluctantSidePolicy) (U))))
let () = Selector.add_solver ("slrtc_plus_restarting_no_side_reset_keep_dead_default_immediate", (module AddPost (Slrtc_plus_restarting.Make (Slrtc_plus_restarting.Control) (Immediate) (Slrtc_plus_restarting.ReluctantSidePolicy) (U))))
let () = Selector.add_solver ("slrtc_dfr_no_side_reset_keep_dead_default_immediate", (module AddPost (Slrtc_plus_restarting.Make (Slrtc_plus_restarting.Control) (Immediate) (Slrtc_plus_restarting.ReluctantSidePolicy) (U))))

let () = Selector.add_solver ("slrtc_dfs_default", (module AddPost
  (Slrtc_deferred_simple.Make (Slrtc_deferred_simple.Control) (Fifo)
    (Slrtc_deferred_simple.ReluctantSidePolicy) (U))))
let () = Selector.add_solver ("slrtc_dfs_default_immediate", (module AddPost
  (Slrtc_deferred_simple.Make (Slrtc_deferred_simple.Control) (Immediate)
    (Slrtc_deferred_simple.ReluctantSidePolicy) (U))))

let () = Selector.add_solver ("slrtc_plus_restarting_no_side_reset_keep_dead_default_recompute_controlled", (module AddPost (Slrtc_plus_restarting.Make (Slrtc_plus_restarting.Control) (FifoRecompute) (Slrtc_plus_restarting.ReluctantSidePolicy) (U))))
let () = Selector.add_solver ("slrtc_dfr_no_side_reset_keep_dead_default_recompute_controlled", (module AddPost (Slrtc_plus_restarting.Make (Slrtc_plus_restarting.Control) (FifoRecompute) (Slrtc_plus_restarting.ReluctantSidePolicy) (U))))
