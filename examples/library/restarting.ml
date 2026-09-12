open Domain

module U = Tc_solvers.Update.TwoCopy (V) (D)
module Features = struct
  let side_effect_phase_reset = true
  let dead_side_elimination = true
end
module Solver = Tc_solvers.Slr.Restarting.Make (V) (D) (U) (Features)

let system = function
  | 0 -> Some (fun get side spawn ->
      spawn 2;
      side 1 1;
      side 1 2;
      max 1 (get 2))
  | 2 -> Some (fun _ _ _ -> 1)
  | _ -> None

let () =
  let solution = Solver.solve system [0] in
  assert (Solver.value solution 0 = 1);
  assert (Solver.value solution 1 = 2);
  assert (Solver.mem solution 2);
  assert (not (Solver.mem solution 99));
  Solver.iter (fun variable value -> Printf.printf "%d = %d\n" variable value) solution
