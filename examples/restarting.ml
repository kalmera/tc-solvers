module V = struct
  type t = int

  let eq_dec = Int.equal
end

module D = struct
  type t = bool * bool

  let bottom = (false, false)

  let join (left_a, left_b) (right_a, right_b) =
    (left_a || right_a, left_b || right_b)

  let leq (left_a, left_b) (right_a, right_b) =
    ((not left_a) || right_a) && ((not left_b) || right_b)
end

module U = struct
  type phase = int

  let initial_phase _is_side _variable = 0
  let update _is_side _variable phase _old input = (phase + 1, input)
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

module Restarting =
  Tc_solvers_extracted_restarting.Restarting

module Smoke (Features : Restarting.FEATURES) = struct
  module Solver =
    Restarting.FirstDiscovery (V) (D) (U) (S) (M) (Features)

  let accumulated_system = function
    | 0 ->
      Solver.ConstraintSystem.Side
        (1, (true, false),
          Solver.ConstraintSystem.Side
            (1, (false, true),
              Solver.ConstraintSystem.Ret D.bottom))
    | _ -> Solver.ConstraintSystem.Ret D.bottom

  let check_accumulation () =
    let state =
      match Solver.solve_fuel 200 accumulated_system [0; 2] with
      | Some final -> final
      | None -> failwith "Restarting solver exhausted accumulation fuel"
    in
    if Solver.Ranking.lookup (Solver.ranking state) 0 <> Some 0
       || Solver.Ranking.lookup (Solver.ranking state) 1 <> Some 1
       || Solver.Ranking.lookup (Solver.ranking state) 2 <> Some 2
    then failwith "Restarting solver did not delay later root ranking";
    if Solver.stored_contribution state 0 1 <> (true, true) then
      failwith "Restarting solver overwrote repeated side effects";
    if Solver.sigma_value state 1 <> (true, true) then
      failwith "Restarting solver did not publish accumulated side effects"

  let disappearing_system = function
    | 0 -> Solver.ConstraintSystem.Ret D.bottom
    | 2 ->
      Solver.ConstraintSystem.Get
        (0, fun (enabled, _) ->
          if enabled
          then Solver.ConstraintSystem.Ret D.bottom
          else
            Solver.ConstraintSystem.Side
              (1, (false, true), Solver.ConstraintSystem.Ret D.bottom))
    | 3 ->
      Solver.ConstraintSystem.Side
        (0, (true, false), Solver.ConstraintSystem.Ret D.bottom)
    | _ -> Solver.ConstraintSystem.Ret D.bottom

  let check_dead_side_switch () =
    let state =
      match Solver.solve_fuel 600 disappearing_system [0; 2; 3] with
      | Some final -> final
      | None -> failwith "Restarting solver exhausted dead-side fuel"
    in
    let expected =
      if Features.eliminate_dead_sides then D.bottom else (false, true)
    in
    let actual = Solver.sigma_value state 1 in
    if actual <> expected then
      let show (a, b) = Printf.sprintf "(%b, %b)" a b in
      failwith
        (Printf.sprintf
           "compile-time dead-side switch was ignored: expected %s, got %s"
           (show expected) (show actual))

  let run () =
    check_accumulation ();
    check_dead_side_switch ()
end

module F00 = struct
  let restart_side_phases = false
  let eliminate_dead_sides = false
end

module F01 = struct
  let restart_side_phases = false
  let eliminate_dead_sides = true
end

module F10 = struct
  let restart_side_phases = true
  let eliminate_dead_sides = false
end

module F11 = struct
  let restart_side_phases = true
  let eliminate_dead_sides = true
end

module S00 = Smoke (F00)
module S01 = Smoke (F01)
module S10 = Smoke (F10)
module S11 = Smoke (F11)

let () =
  S00.run ();
  S01.run ();
  S10.run ();
  S11.run ()
