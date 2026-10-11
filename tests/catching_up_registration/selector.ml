let names = ref []
let add_solver (name, (_ : (module Goblint_constraint.SolverTypes.DemandEqIncrSolver))) =
  if List.mem name !names then failwith ("duplicate solver: " ^ name);
  names := name :: !names
