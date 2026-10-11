module AddPost (S : Goblint_constraint.SolverTypes.DemandEqIncrSolver) = S

module ListArgFromStdArg
    (S : Goblint_constraint.ConstrSys.DemandEqConstrSys)
    (VH : Batteries.Hashtbl.S with type key = S.v)
    (_ : Goblint_constraint.SolverTypes.IncrSolverArg) = struct end
module MakeIncrList (_ : sig end) = struct
  let post _ _ _ = ()
end
