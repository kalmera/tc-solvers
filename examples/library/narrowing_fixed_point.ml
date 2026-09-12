open Domain

module U = Tc_solvers.Update.TwoCopy (V) (D)
module Solver = Tc_solvers.Slr.Narrowing_fixed_point.Make (V) (D) (U)

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
