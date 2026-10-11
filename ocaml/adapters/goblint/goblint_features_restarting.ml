(* The three compile-time policies exposed by the proved Restarting solver.
    The Goblint adapter default enables side reset and dead-side elimination,
    and disables controlled-owner recomputation. *)

let side_effect_phase_reset = true
let dead_side_elimination = true
let recompute_controlled = false
