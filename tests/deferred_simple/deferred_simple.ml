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
  val defer_spawns : bool
  val reluctant : bool
end
let compare name actual expected =
  let actual = List.sort Stdlib.compare (H.fold (fun x v acc -> (x,v)::acc) actual []) in
  let expected = List.sort Stdlib.compare expected in
  if actual <> expected then
    let show xs = String.concat ", " (List.map (fun (x,v) -> Printf.sprintf "%d=%d" x v) xs) in
    failwith (Printf.sprintf "%s: got [%s], expected [%s]" name (show actual) (show expected))

module Simple (C : Config) = struct
  module SU = Side (C)
  module R = DeferredSimpleRuntime.Engine (V) (D) (U) (SU) (Set) (Map) (C)
  module Policy = struct let reluctant = C.reluctant let stats_name = "test" end
  module Features = struct
    let defer_spawns = C.defer_spawns
  end
  module A = Slrtc_deferred_simple.Make (Slrtc_deferred_simple.Control)
    (Features) (Policy) (Slrtc_update.CopyUpdate) (Arg) (System) (H)
  module I = Slrtc_inlined_deferred_simple.Make (Slrtc_inlined_deferred_simple.Control)
    (Features) (Policy) (Slrtc_update.CopyUpdate) (Arg) (System) (H)
  let rec convert = function
    | Ret d -> R.ConstraintSystem.Ret d
    | Get (x,k) -> R.ConstraintSystem.Get (x, fun d -> convert (k d))
    | Side (x,d,k) -> R.ConstraintSystem.Side (x,d,convert k)
    | Spawn (x,k) -> R.ConstraintSystem.Spawn (x,convert k)
  let test name tf roots =
    let st = match R.solve_fuel 100000 (fun x -> convert (tf x)) roots with
      | Some st -> st | None -> failwith (name ^ ": simple fuel") in
    let expected = R.sigma st in
    compare (name ^ " simple") (fst (A.solve [] roots None)) expected;
    compare (name ^ " simple inlined") (fst (I.solve [] roots None)) expected
end
module ImmediateStandard = Simple (struct let defer_spawns = false let reluctant = false end)
module ImmediateReluctant = Simple (struct let defer_spawns = false let reluctant = true end)
module DeferredStandard = Simple (struct let defer_spawns = true let reluctant = false end)
module DeferredReluctant = Simple (struct let defer_spawns = true let reluctant = true end)
let tests = [ImmediateStandard.test; ImmediateReluctant.test;
             DeferredStandard.test; DeferredReluctant.test]
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
  Printf.printf "Deferred simple adapters: %d cases x 4 policies x 2 adapters passed.\n" !count
