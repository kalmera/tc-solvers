(* Differential execution of the generated Goblint adapter and full extracted
    machine. The callback adapter is not asserted to be a proved refinement. *)
type rhs = Ret of int | Get of int * (int -> rhs)
         | Spawn of int * rhs | Side of int * int * rhs

module V = struct type t = int let eq_dec = Int.equal end
module D = struct
  type t = int
  let bottom = 0
  let leq = ( <= )
  let join = max
end
module WN = struct
  let widen _ _ = 5
  let narrow old input = max input (old - 1)
end
module Set = struct
  type t = int list
  let empty = []
  let mem = List.mem
  let add x xs = if mem x xs then xs else x :: xs
  let elements xs = xs
end
module Map = struct
  type 'a t = (int * 'a) list
  let empty = []
  let lookup xs x = List.assoc_opt x xs
  let update xs x v = (x, v) :: List.remove_assoc x xs
  let values entries = List.map snd entries
end
let current = ref (fun _ -> Ret 0)
let rhsless = ref []
module System = struct
  type v = int
  type d = int
  module Var = struct
    type t = int
    let equal = Int.equal
    let var_id = string_of_int
    let pretty_trace () = string_of_int
  end
  module Dom = struct
    type t = int
    let bot () = 0
    let equal = Int.equal
    let leq = D.leq
    let join = D.join
    let widen = WN.widen
    let narrow = WN.narrow
    let show = string_of_int
  end
  let rec eval get side spawn = function
    | Ret d -> d
    | Get (x,k) -> eval get side spawn (k (get x))
    | Side (x,d,k) -> side x d; eval get side spawn k
    | Spawn (x,k) -> spawn x; eval get side spawn k
  let system x = if List.mem x !rhsless then None
    else Some (fun get side spawn -> eval get side spawn (!current x))
end
module Arg = struct
  let should_prune = false
  let should_verify = false
  let should_warn = false
  let should_save_run = false
end
module H = Batteries.Hashtbl.Make (struct
  type t = int let equal = Int.equal let hash = Hashtbl.hash
end)
module U = Slrtc_update.CopyUpdate (System)
module type Policy = sig val reluctant : bool end
module Side (P : Policy) = struct
  type phase = U.phase
  let initial_phase _source target = U.initial_phase true target
  let update _source target phase old input aggregate =
    let phase, value = U.update true target phase old input in
    phase, if P.reluctant && not (D.leq input old) && D.leq input aggregate
      then D.join old input else value
end
module type Config = sig
  val recompute_controlled : bool
  val defer_spawns : bool
  val reluctant : bool
  val restart_side_phases : bool
  val eliminate_dead_sides : bool
end
let compare name actual expected =
  let actual = List.sort Stdlib.compare (H.fold (fun x v acc -> (x,v)::acc) actual []) in
  let expected = List.sort Stdlib.compare expected in
  if actual <> expected then
    let show xs = String.concat ", " (List.map (fun (x,v) -> Printf.sprintf "%d=%d" x v) xs) in
    failwith (Printf.sprintf "%s: got [%s], expected [%s]" name (show actual) (show expected))

module Restarting (C : Config) = struct
  module SU = Side (C)
  module R = PlusRestartingRuntime.Engine (V) (D) (U) (SU) (Set) (Map) (C)
  module Policy = struct let reluctant = C.reluctant let stats_name = "test" end
  module Features = struct
    let recompute_controlled = C.recompute_controlled
    let defer_spawns = C.defer_spawns
    let side_effect_phase_reset = C.restart_side_phases
    let dead_side_elimination = C.eliminate_dead_sides
  end
  module A = Slrtc_plus_restarting.Make (Slrtc_plus_restarting.Control)
    (Features) (Policy) (Slrtc_update.CopyUpdate) (Arg) (System) (H)
  module I = Slrtc_inlined_plus_restarting.Make (Slrtc_inlined_plus_restarting.Control)
    (Features) (Policy) (Slrtc_update.CopyUpdate) (Arg) (System) (H)
  let rec convert = function
    | Ret d -> R.ConstraintSystem.Ret d
    | Get (x,k) -> R.ConstraintSystem.Get (x, fun d -> convert (k d))
    | Side (x,d,k) -> R.ConstraintSystem.Side (x,d,convert k)
    | Spawn (x,k) -> R.ConstraintSystem.Spawn (x,convert k)
  module Old = DirtyReadRestartingRuntime.Engine (V) (D) (U) (SU) (Set) (Map) (C)
  let rec convert_old = function
    | Ret d -> Old.ConstraintSystem.Ret d
    | Get (x,k) -> Old.ConstraintSystem.Get (x, fun d -> convert_old (k d))
    | Side (x,d,k) -> Old.ConstraintSystem.Side (x,d,convert_old k)
    | Spawn (x,k) -> Old.ConstraintSystem.Spawn (x,convert_old k)
  let test name tf roots =
    let st = match R.solve_fuel 100000 (fun x -> convert (tf x)) roots with
      | Some st -> st | None -> failwith (name ^ ": restarting fuel") in
    let expected = R.sigma st in
    if not C.defer_spawns && not C.recompute_controlled then begin
      let old = match Old.solve_fuel 100000 (fun x -> convert_old (tf x)) roots with
        | Some st -> st | None -> failwith (name ^ ": old fuel") in
      if List.sort Stdlib.compare expected <> List.sort Stdlib.compare (Old.sigma old)
      then failwith (name ^ ": disabled feature changed the store")
    end;
    compare (name ^ " restarting") (fst (A.solve [] roots None)) expected;
    compare (name ^ " restarting inlined") (fst (I.solve [] roots None)) expected
end
module R0000 = Restarting (struct let recompute_controlled = false let defer_spawns = false let reluctant = false let restart_side_phases = false let eliminate_dead_sides = false end)
module R0001 = Restarting (struct let recompute_controlled = false let defer_spawns = false let reluctant = false let restart_side_phases = false let eliminate_dead_sides = true end)
module R0010 = Restarting (struct let recompute_controlled = false let defer_spawns = false let reluctant = false let restart_side_phases = true let eliminate_dead_sides = false end)
module R0011 = Restarting (struct let recompute_controlled = false let defer_spawns = false let reluctant = false let restart_side_phases = true let eliminate_dead_sides = true end)
module R0100 = Restarting (struct let recompute_controlled = false let defer_spawns = false let reluctant = true let restart_side_phases = false let eliminate_dead_sides = false end)
module R0101 = Restarting (struct let recompute_controlled = false let defer_spawns = false let reluctant = true let restart_side_phases = false let eliminate_dead_sides = true end)
module R0110 = Restarting (struct let recompute_controlled = false let defer_spawns = false let reluctant = true let restart_side_phases = true let eliminate_dead_sides = false end)
module R0111 = Restarting (struct let recompute_controlled = false let defer_spawns = false let reluctant = true let restart_side_phases = true let eliminate_dead_sides = true end)
module R1000 = Restarting (struct let recompute_controlled = false let defer_spawns = true let reluctant = false let restart_side_phases = false let eliminate_dead_sides = false end)
module R1001 = Restarting (struct let recompute_controlled = false let defer_spawns = true let reluctant = false let restart_side_phases = false let eliminate_dead_sides = true end)
module R1010 = Restarting (struct let recompute_controlled = false let defer_spawns = true let reluctant = false let restart_side_phases = true let eliminate_dead_sides = false end)
module R1011 = Restarting (struct let recompute_controlled = false let defer_spawns = true let reluctant = false let restart_side_phases = true let eliminate_dead_sides = true end)
module R1100 = Restarting (struct let recompute_controlled = false let defer_spawns = true let reluctant = true let restart_side_phases = false let eliminate_dead_sides = false end)
module R1101 = Restarting (struct let recompute_controlled = false let defer_spawns = true let reluctant = true let restart_side_phases = false let eliminate_dead_sides = true end)
module R1110 = Restarting (struct let recompute_controlled = false let defer_spawns = true let reluctant = true let restart_side_phases = true let eliminate_dead_sides = false end)
module R1111 = Restarting (struct let recompute_controlled = false let defer_spawns = true let reluctant = true let restart_side_phases = true let eliminate_dead_sides = true end)
module R0000On = Restarting (struct let recompute_controlled = true let defer_spawns = false let reluctant = false let restart_side_phases = false let eliminate_dead_sides = false end)
module R0001On = Restarting (struct let recompute_controlled = true let defer_spawns = false let reluctant = false let restart_side_phases = false let eliminate_dead_sides = true end)
module R0010On = Restarting (struct let recompute_controlled = true let defer_spawns = false let reluctant = false let restart_side_phases = true let eliminate_dead_sides = false end)
module R0011On = Restarting (struct let recompute_controlled = true let defer_spawns = false let reluctant = false let restart_side_phases = true let eliminate_dead_sides = true end)
module R0100On = Restarting (struct let recompute_controlled = true let defer_spawns = false let reluctant = true let restart_side_phases = false let eliminate_dead_sides = false end)
module R0101On = Restarting (struct let recompute_controlled = true let defer_spawns = false let reluctant = true let restart_side_phases = false let eliminate_dead_sides = true end)
module R0110On = Restarting (struct let recompute_controlled = true let defer_spawns = false let reluctant = true let restart_side_phases = true let eliminate_dead_sides = false end)
module R0111On = Restarting (struct let recompute_controlled = true let defer_spawns = false let reluctant = true let restart_side_phases = true let eliminate_dead_sides = true end)
module R1000On = Restarting (struct let recompute_controlled = true let defer_spawns = true let reluctant = false let restart_side_phases = false let eliminate_dead_sides = false end)
module R1001On = Restarting (struct let recompute_controlled = true let defer_spawns = true let reluctant = false let restart_side_phases = false let eliminate_dead_sides = true end)
module R1010On = Restarting (struct let recompute_controlled = true let defer_spawns = true let reluctant = false let restart_side_phases = true let eliminate_dead_sides = false end)
module R1011On = Restarting (struct let recompute_controlled = true let defer_spawns = true let reluctant = false let restart_side_phases = true let eliminate_dead_sides = true end)
module R1100On = Restarting (struct let recompute_controlled = true let defer_spawns = true let reluctant = true let restart_side_phases = false let eliminate_dead_sides = false end)
module R1101On = Restarting (struct let recompute_controlled = true let defer_spawns = true let reluctant = true let restart_side_phases = false let eliminate_dead_sides = true end)
module R1110On = Restarting (struct let recompute_controlled = true let defer_spawns = true let reluctant = true let restart_side_phases = true let eliminate_dead_sides = false end)
module R1111On = Restarting (struct let recompute_controlled = true let defer_spawns = true let reluctant = true let restart_side_phases = true let eliminate_dead_sides = true end)
let tests = [R0000.test; R0001.test; R0010.test; R0011.test; R0100.test; R0101.test; R0110.test; R0111.test; R1000.test; R1001.test; R1010.test; R1011.test; R1100.test; R1101.test; R1110.test; R1111.test; R0000On.test; R0001On.test; R0010On.test; R0011On.test; R0100On.test; R0101On.test; R0110On.test; R0111On.test; R1000On.test; R1001On.test; R1010On.test; R1011On.test; R1100On.test; R1101On.test; R1110On.test; R1111On.test]
let count = ref 0
let test ?(missing=[]) name tf roots =
  current := tf; rhsless := missing;
  List.iter (fun run -> run name tf roots) tests;
  incr count

let () =
  test "duplicate dormant roots" (fun _ -> Ret 0) [0;0;1];
  test "dormant read" (function 0 -> Get (1, fun d -> Ret d) | _ -> Ret 0) [0];
  test "wake dormant reader" (function
    | 0 -> Get (1, fun d -> Ret d)
    | 2 -> Side (1,3,Ret 0) | _ -> Ret 0) [0;2];
  test "bottom side promotes" (function
    | 0 -> Side (1,0,Ret 0) | _ -> Ret 0) [1;0];
  test "accumulated sides" (function
    | 0 -> Side (1,3,Side (1,1,Ret 0)) | _ -> Ret 0) [0];
  test "covered second writer" (function
    | 0 -> Spawn (1,Spawn (2,Ret 0))
    | 1 -> Side (3,3,Ret 0) | 2 -> Side (3,2,Ret 0) | _ -> Ret 0) [0];
  test "controlled constant without self-read" (function
    | 0 -> Get (1, fun _ -> Ret 1)
    | _ -> Get (0, fun _ -> Ret 0)) [0];
  test "controlled constant with deferred spawn" (function
    | 0 -> Get (1, fun _ -> Spawn (2, Ret 1))
    | 1 -> Get (0, fun _ -> Ret 0) | _ -> Ret 0) [0];
  test "self loop" (fun _ -> Get (0, fun d -> Ret (min 3 (d+1)))) [0];
  test "read cycle" (function
    | 0 -> Get (1, fun d -> Ret (min 3 (d+1)))
    | _ -> Get (0,fun d -> Ret d)) [0];
  test "dormant spawn" (function 0 -> Spawn (1,Ret 2) | _ -> Ret 0) [0];
  test ~missing:[1] "rhsless incoming" (function
    | 0 -> Side (1,2,Get (1,fun d -> Ret d)) | _ -> Ret 0) [0];
  test "side target disappears on reevaluation" (function
    | 0 -> Get (1, fun d -> if d = 0 then Side (3,1,Ret 0) else Ret 0)
    | 2 -> Side (1,2,Ret 0) | _ -> Ret 0) [0;2];
  test "same writer grows across episodes" (function
    | 0 -> Get (1, fun d -> Side (3,d,Ret 0))
    | 2 -> Side (1,3,Ret 0) | _ -> Ret 0) [0;2];
  test ~missing:[1] "dirty lower target read twice" (function
    | 0 -> Side (1,1,Ret 0)
    | 2 -> Side (1,3,Get (1,fun a -> Get (1,fun b -> Ret (max a b))))
    | _ -> Ret 0) [0;2];
  test ~missing:[1] "dirty read defers an existing reader" (function
    | 0 -> Side (1,1,Ret 0)
    | 2 -> Get (1,fun d -> Ret d)
    | 3 -> Side (1,3,Get (1,fun d -> Ret d))
    | _ -> Ret 0) [0;2;3];
  test "nested duplicate spawns" (function
    | 0 -> Spawn (1,Spawn (2,Spawn (1,Ret 1)))
    | 1 -> Spawn (3,Ret 1) | 2 -> Ret 2 | _ -> Ret 3) [0];
  test "spawn then synchronous read" (function
    | 0 -> Spawn (1,Get (2,fun d -> Ret d)) | 1 -> Ret 1 | _ -> Ret 2) [0];
  test "spawn cycle" (function
    | 0 -> Spawn (1,Ret 1) | _ -> Spawn (0,Ret 1)) [0];
  (* Enumerate first-callback and promotion orderings on a small finite domain. *)
  for value = 0 to 3 do
    List.iter (fun roots ->
      test "promotion order" (function
        | 0 -> Get (2,fun d -> Ret d)
        | 1 -> Side (2,value,Ret 0) | _ -> Ret 0) roots)
      [[0;1];[1;0];[2;0;1];[0;2;1]]
  done;
  Printf.printf "Plus Restarting adapters: %d cases x 32 policies x 2 adapters passed.\n" !count
