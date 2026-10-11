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
  let widen old input = if input <= old then old else 5
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
module U = struct
  type phase = W | N | F
  let initial_phase _ _ = W
  let update _ _ phase old input = match phase with
    | W | N -> if input <= old then N, WN.narrow old input
      else (if phase=N then F else W), WN.widen old input
    | F -> F, WN.widen old input
end
module Flags = struct
  let restart_side_phases = true
  let eliminate_dead_sides = true
  let recompute_controlled = true
end
module Credit = struct let remaining_changes _ _ = 0 end
module Empty = struct end
module Reference = Tc_solvers_extracted_narrowing_fixed_point.NarrowingFixedPointRuntime.Solver
  (V) (D) (U) (Set) (Map) (Flags) (Empty) (Credit) (Empty) (Empty)
module R = Reference.R
let rec convert = function
  | Ret d -> R.ConstraintSystem.Ret d
  | Get (x,k) -> R.ConstraintSystem.Get (x, fun d -> convert (k d))
  | Spawn (x,k) -> R.ConstraintSystem.Spawn (x, convert k)
  | Side (x,d,k) -> R.ConstraintSystem.Side (x,d,convert k)

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
module Adapter = Slrtc_narrowing_fixed_point.SLRTC (Slrtc_nfp_update.WNUpdate) (Arg) (System) (H)
module Inlined = Slrtc_inlined_narrowing_fixed_point.SLRTC (Slrtc_nfp_update.WNUpdate) (Arg) (System) (H)

let rec add_constant d = function
  | Ret v -> Ret (max v d)
  | Get (x,k) -> Get (x, fun v -> add_constant d (k v))
  | Spawn (x,k) -> Spawn (x, add_constant d k)
  | Side (x,v,k) -> Side (x,v, add_constant d k)

module JoinAdapter = Slrtc_narrowing_fixed_point.SLRTC (Slrtc_nfp_update.JoinUpdate) (Arg) (System) (H)
module JoinInlined = Slrtc_inlined_narrowing_fixed_point.SLRTC (Slrtc_nfp_update.JoinUpdate) (Arg) (System) (H)
module JU = struct
  type phase = unit
  let initial_phase _ _ = ()
  let update _ _ _ old input = (), max old input
end
module JoinReference = Tc_solvers_extracted_narrowing_fixed_point.NarrowingFixedPointRuntime.Solver
  (V) (D) (JU) (Set) (Map) (Flags) (Empty) (Credit) (Empty) (Empty)
let rec join_convert = function
  | Ret d -> JoinReference.R.ConstraintSystem.Ret d
  | Get (x,k) -> JoinReference.R.ConstraintSystem.Get (x, fun d -> join_convert (k d))
  | Side (x,d,k) -> JoinReference.R.ConstraintSystem.Side (x,d,join_convert k)
  | Spawn (x,k) -> JoinReference.R.ConstraintSystem.Spawn (x,join_convert k)

let compare name actual expected =
  List.iter (fun (x,v) ->
    if H.find_option actual x <> Some v then
      failwith (Printf.sprintf "%s: owner %d: got %s, expected %d" name x
        (match H.find_option actual x with None -> "missing" | Some v -> string_of_int v) v)) expected;
  if H.length actual <> List.length expected then failwith (name ^ ": owner sets differ")

let check_final name body st =
  let value x = R.sigma_value st x in
  let rec replay = function
    | Ret d -> d
    | Get (x,k) ->
      if not (List.mem_assoc x (R.sigma st)) then failwith (name ^ ": unsolved read");
      replay (k (value x))
    | Spawn (x,k) ->
      if not (List.mem_assoc x (R.sigma st)) then failwith (name ^ ": unsolved spawn");
      replay k
    | Side (x,d,k) ->
      if d > value x then failwith (name ^ ": unsound side effect");
      replay k
  in
  List.iter (fun (x,old) ->
    let direct = replay (body x) in
    let input = max direct (R.aggregate st x) in
    if direct > old then failwith (name ^ ": unsound direct result");
    if WN.narrow old input <> old then
      failwith (Printf.sprintf "%s: owner %d is not narrowing-fixed (%d vs %d)"
        name x old input)) (R.sigma st)

let test ?(starts=[]) ?(missing=[]) name tf roots =
  current := tf; rhsless := missing;
  let start x = List.fold_left (fun v (y,d) -> if x=y then max v d else v) 0 starts in
  let body x = add_constant (start x) (if List.mem x missing then Ret 0 else tf x) in
  let expected = match Reference.solve_fuel 100000 (fun x -> convert (body x))
      (roots @ List.map fst starts) with
    | Some st -> check_final name body st; R.sigma st
    | None -> failwith (name ^ ": reference exhausted fuel") in
  compare name (fst (Adapter.solve starts roots None)) expected;
  compare (name ^ " inlined") (fst (Inlined.solve starts roots None)) expected;
  let joined = match JoinReference.solve_fuel 100000 (fun x -> join_convert (body x))
      (roots @ List.map fst starts) with
    | Some st -> JoinReference.R.sigma st | None -> failwith (name ^ ": join reference exhausted fuel") in
  compare (name ^ " join") (fst (JoinAdapter.solve starts roots None)) joined;
  compare (name ^ " join inlined") (fst (JoinInlined.solve starts roots None)) joined

let () =
  test "empty" (fun _ -> Ret 0) [];
  test "ordinary cycle and duplicate roots" (function
    | 0 -> Get (1, fun v -> Ret v) | 1 -> Get (0, fun _ -> Ret 1) | _ -> Ret 0) [0;0];
  test "effectful local-repair witness" (function
    | 0 -> Side (3,1,Ret 1)
    | 1 -> Get (2, fun v -> Side (2,min v 1,Ret (max v 1)))
    | 2 -> Get (0, fun v -> Side (1,1,Ret (min v 1)))
    | 3 -> Get (1, fun _ -> Ret 2) | _ -> Ret 0) [0];
  test "repeated source-target publication" (function
    | 0 -> Get (1, fun v -> Ret v)
    | 1 -> Get (0, fun _ -> Get (1, fun own ->
        Side (3,max 1 (min own 2),Side (3,2,Get (3,fun v -> Ret (if v<=2 then 1 else 2))))))
    | 2 -> Side (0,3,Ret 0) | _ -> Ret 0) [0;2];
  test "masked contribution and dynamic reads" (function
    | 0 -> Get (0,fun own -> if own=0 then Side (3,1,Ret 1) else
        Get (4,fun _ -> Side (3,2,Get (3,fun v -> Ret (if v<=3 then 1 else 3)))))
    | 4 -> Get (0,fun _ -> Side (3,3,Ret 0)) | _ -> Ret 0) [0];
  test "stale read after higher solve" (function
    | 0 -> Get (0,fun own -> if own=0 then Ret 1 else Side (1,0,
        Get (2,fun a -> Get (1,fun _ -> Ret (max 1 a)))))
    | 1 -> Side (2,2,Ret 0) | _ -> Ret 1) [0];
  test "spawns and side-only non-root" (function
    | 0 -> Spawn (1,Side (2,2,Ret 1)) | 1 -> Side (2,1,Ret 0) | _ -> Ret 0) [0];
  test "initial values, duplicate contributions, RHS-less owner"
    ~starts:[0,1;0,2;3,3] ~missing:[3] (function
      | 0 -> Side (1,1,Ret 0) | _ -> Ret 0) [0];
  test "independent higher publications" (function
    | 0 -> Side (1,1,Side (2,2,Side (3,3,Ret 1)))
    | _ -> Ret 0) [0];
  test "higher work invalidates an earlier source read" (function
    | 0 -> Get (4,fun v -> Side (1,1,Side (2,2,Side (3,3,Ret (max 1 v)))))
    | 2 -> Side (4,2,Ret 0)
    | 3 -> Side (4,3,Ret 0)
    | _ -> Ret 0) [0];
  print_endline "narrowing fixed point: extracted-control, inlined, and join adapters agree with extracted machine"
