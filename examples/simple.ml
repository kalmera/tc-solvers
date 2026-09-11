module V = struct
  type t = int

  let eq_dec = Int.equal
end

module D = struct
  type t = bool * bool

  let bottom = (false, false)
  let join (a, b) (c, d) = (a || c, b || d)
  let leq (a, b) (c, d) = ((not a) || c) && ((not b) || d)
end

module U = struct
  type phase = unit

  let initial_phase _is_side _variable = ()
  let update _is_side _variable phase _old input = (phase, input)
end

module S = struct
  type t = V.t list

  let empty = []
  let mem = List.mem
  let add value values = if List.mem value values then values else value :: values
  let elements values = values
end

module M = struct
  type 'a t = (V.t * 'a) list

  let empty = []
  let lookup values key = List.assoc_opt key values
  let update values key value = (key, value) :: List.remove_assoc key values
  let values entries = List.map snd entries
end

module Solver =
  Tc_solvers_extracted_simple.Simple.FirstDiscovery
    (V) (D) (U) (S) (M)

let system = function
  | 0 ->
    Solver.ConstraintSystem.Side
      (1, (true, false),
        Solver.ConstraintSystem.Side
          (1, (false, true), Solver.ConstraintSystem.Ret D.bottom))
  | _ -> Solver.ConstraintSystem.Ret D.bottom

let () =
  let state =
    match Solver.solve_fuel 200 system [0; 2] with
    | Some final -> final
    | None -> failwith "Simple exhausted smoke-test fuel"
  in
  if Solver.Ranking.lookup (Solver.ranking state) 0 <> Some 0 then
    failwith "first root did not receive rank zero";
  if Solver.Ranking.lookup (Solver.ranking state) 1 <> Some 1 then
    failwith "discovered side target did not receive rank one";
  if Solver.Ranking.lookup (Solver.ranking state) 2 <> Some 2 then
    failwith "later root was ranked before work reached from the first root";
  if Solver.stored_contribution state 0 1 <> (true, true) then
    failwith "Simple lost an accumulated side effect"
