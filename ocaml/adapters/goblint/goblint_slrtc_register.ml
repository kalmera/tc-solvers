(* The six paper variants: extracted callback control, two-copy-one-box updates. *)
open Batteries
open Goblint_constraint.ConstrSys
open Goblint_constraint.SolverTypes
open PostSolver

(* Run Goblint's standard postsolving for our demand-driven adapters. *)
module AddPost (Solver : DemandEqIncrSolver) (Arg : IncrSolverArg)
    (S : DemandEqConstrSys) (VH : Hashtbl.S with type key = S.v) =
struct
  module Base = Solver (Arg) (S) (VH)
  include Base
  module EqS = Goblint_constraint.Translators.EqConstrSysFromDemandConstrSys (S)
  module Post = MakeList (ListArgFromStdArg (EqS) (VH) (Arg))

  let solve xs vs old_data =
    let values, data = Base.solve xs vs old_data in
    Post.post xs vs values;
    (values, data)
end

module Base = struct
  let side_effect_phase_reset = false
  let dead_side_elimination = false
end
module SideReset = struct
  let side_effect_phase_reset = true
  let dead_side_elimination = false
end
module DeadSide = struct
  let side_effect_phase_reset = false
  let dead_side_elimination = true
end
module Both = struct
  let side_effect_phase_reset = true
  let dead_side_elimination = true
end

module Restarting (Features : Slrtc_restarting.FEATURES) =
  Slrtc_restarting.Make (Slrtc_restarting.Control) (Features) (Slrtc_update.CopyUpdate)

let () =
  Selector.add_solver ("slrtc_s", (module AddPost
    (Slrtc_simple.SLRTC (Slrtc_update.CopyUpdate))));
  Selector.add_solver ("slrtc_r", (module AddPost (Restarting (Base))));
  Selector.add_solver ("slrtc_rs", (module AddPost (Restarting (SideReset))));
  Selector.add_solver ("slrtc_rd", (module AddPost (Restarting (DeadSide))));
  Selector.add_solver ("slrtc_rds", (module AddPost (Restarting (Both))));
  Selector.add_solver ("slrtc_n", (module AddPost
    (Slrtc_narrowing_fixed_point.SLRTC (Slrtc_update.CopyUpdate))))
