type rhs = Ret of int | Get of int * (int -> rhs)
         | Spawn of int * rhs | Side of int * int * rhs

module V = struct type t = int let eq_dec = Int.equal let equal = Int.equal let hash _ = 0 end
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
module Domain = struct include D include WN end
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
let rec add_constant d = function
  | Ret v -> Ret (max v d)
  | Get (x,k) -> Get (x, fun v -> add_constant d (k v))
  | Spawn (x,k) -> Spawn (x, add_constant d k)
  | Side (x,v,k) -> Side (x,v, add_constant d k)

module F00 = struct let side_effect_phase_reset = false let dead_side_elimination = false let recompute_controlled = true end
module F01 = struct let side_effect_phase_reset = false let dead_side_elimination = true let recompute_controlled = true end
module F10 = struct let side_effect_phase_reset = true let dead_side_elimination = false let recompute_controlled = true end
module F11 = struct let side_effect_phase_reset = true let dead_side_elimination = true let recompute_controlled = true end
module F00Off = struct include F00 let recompute_controlled = false end
module F01Off = struct include F01 let recompute_controlled = false end
module F10Off = struct include F10 let recompute_controlled = false end
module F11Off = struct include F11 let recompute_controlled = false end
module type SOLVER = Tc_solvers.SOLVER with type variable = int and type value = int
module Empty = struct end
(* Computational credit argument of the fuelled reference; this is not a proof witness. *)
module Credit = struct let remaining_changes _ _ = 0 end

(* Existing mutable-adapter behavior, independently checked against the untouched
   Goblint modules below. These are concrete reference gaps, not equivalence claims.
   Initial-store gaps also reflect our constant-RHS encoding of starts in the
   extracted reference, which has no initial-store argument. *)
let policy = ref ""
let comparisons = ref 0
let observed_gaps = ref 0
let reference_gaps = [
  ("TwoCopy", "effectful local-repair witness Simple"),
    ([0,1;1,5;2,5;3,2], [0,1;1,1;2,1;3,2]);
  ("WidenNarrow", "repeated source-target publication Simple"),
    ([0,5;1,2;2,0;3,5], [0,5;1,5;2,0;3,5]);
  ("WidenNarrow", "masked contribution and dynamic reads Simple"),
    ([0,3;3,5;4,0], [0,1;3,3;4,0]);
  ("WidenNarrow", "higher work invalidates an earlier source read Simple"),
    ([0,5;1,5;2,5;3,5;4,5], [0,3;1,2;2,2;3,3;4,3]);
] @ List.map (fun variant ->
  ("WidenNarrow", "initial values, duplicate contributions, RHS-less owner " ^ variant),
    ([0,5;1,5;3,3], [0,2;1,5;3,3])) ["Simple"; "R00Off"; "R01Off"; "R10Off"; "R11Off"]
@ List.map (fun variant ->
  ("WidenNarrow", "initial values, duplicate contributions, RHS-less owner " ^ variant),
    ([0,2;1,1;3,3], [0,2;1,5;3,3])) ["R00"; "R01"; "R10"; "R11"]

module CheckPolicy
  (U : Tc_solvers.UPDATE with type variable = int and type value = int)
  (GU : Slrtc_update.UPDATE) = struct
  module LSimple = Tc_solvers.Slr.Simple.Make (V) (D) (U)
  module GSimple = Slrtc_simple.SLRTC (GU) (Arg) (System) (H)
  module ESimple = Tc_solvers_extracted_simple.Simple.FirstDiscovery (V) (D) (U) (Set) (Map)
  let reference_Simple body roots =
    let module C = ESimple.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ESimple.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ESimple.sigma final
    | None -> failwith "Simple: extracted reference exhausted fuel"
  module LR00 = Tc_solvers.Slr.Restarting.Make (V) (D) (U) (F00)
  module GR00 = Slrtc_restarting.Make (Slrtc_restarting.Control) (F00) (GU) (Arg) (System) (H)
  module FlagsR00 = struct
    let restart_side_phases = F00.side_effect_phase_reset
    let eliminate_dead_sides = F00.dead_side_elimination
    let recompute_controlled = F00.recompute_controlled
  end
  module ER00 = Tc_solvers_extracted_restarting.Restarting.FirstDiscovery (V) (D) (U) (Set) (Map) (FlagsR00)
  let reference_R00 body roots =
    let module C = ER00.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ER00.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ER00.sigma final
    | None -> failwith "R00: extracted reference exhausted fuel"
  module LR01 = Tc_solvers.Slr.Restarting.Make (V) (D) (U) (F01)
  module GR01 = Slrtc_restarting.Make (Slrtc_restarting.Control) (F01) (GU) (Arg) (System) (H)
  module FlagsR01 = struct
    let restart_side_phases = F01.side_effect_phase_reset
    let eliminate_dead_sides = F01.dead_side_elimination
    let recompute_controlled = F01.recompute_controlled
  end
  module ER01 = Tc_solvers_extracted_restarting.Restarting.FirstDiscovery (V) (D) (U) (Set) (Map) (FlagsR01)
  let reference_R01 body roots =
    let module C = ER01.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ER01.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ER01.sigma final
    | None -> failwith "R01: extracted reference exhausted fuel"
  module LR10 = Tc_solvers.Slr.Restarting.Make (V) (D) (U) (F10)
  module GR10 = Slrtc_restarting.Make (Slrtc_restarting.Control) (F10) (GU) (Arg) (System) (H)
  module FlagsR10 = struct
    let restart_side_phases = F10.side_effect_phase_reset
    let eliminate_dead_sides = F10.dead_side_elimination
    let recompute_controlled = F10.recompute_controlled
  end
  module ER10 = Tc_solvers_extracted_restarting.Restarting.FirstDiscovery (V) (D) (U) (Set) (Map) (FlagsR10)
  let reference_R10 body roots =
    let module C = ER10.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ER10.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ER10.sigma final
    | None -> failwith "R10: extracted reference exhausted fuel"
  module LR11 = Tc_solvers.Slr.Restarting.Make (V) (D) (U) (F11)
  module GR11 = Slrtc_restarting.Make (Slrtc_restarting.Control) (F11) (GU) (Arg) (System) (H)
  module FlagsR11 = struct
    let restart_side_phases = F11.side_effect_phase_reset
    let eliminate_dead_sides = F11.dead_side_elimination
    let recompute_controlled = F11.recompute_controlled
  end
  module ER11 = Tc_solvers_extracted_restarting.Restarting.FirstDiscovery (V) (D) (U) (Set) (Map) (FlagsR11)
  let reference_R11 body roots =
    let module C = ER11.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ER11.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ER11.sigma final
    | None -> failwith "R11: extracted reference exhausted fuel"
  module LR00Off = Tc_solvers.Slr.Restarting.Make (V) (D) (U) (F00Off)
  module GR00Off = Slrtc_restarting.Make (Slrtc_restarting.Control) (F00Off) (GU) (Arg) (System) (H)
  module FlagsR00Off = struct
    let restart_side_phases = F00Off.side_effect_phase_reset
    let eliminate_dead_sides = F00Off.dead_side_elimination
    let recompute_controlled = F00Off.recompute_controlled
  end
  module ER00Off = Tc_solvers_extracted_restarting.Restarting.FirstDiscovery (V) (D) (U) (Set) (Map) (FlagsR00Off)
  let reference_R00Off body roots =
    let module C = ER00Off.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ER00Off.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ER00Off.sigma final
    | None -> failwith "R00Off: extracted reference exhausted fuel"
  module LR01Off = Tc_solvers.Slr.Restarting.Make (V) (D) (U) (F01Off)
  module GR01Off = Slrtc_restarting.Make (Slrtc_restarting.Control) (F01Off) (GU) (Arg) (System) (H)
  module FlagsR01Off = struct
    let restart_side_phases = F01Off.side_effect_phase_reset
    let eliminate_dead_sides = F01Off.dead_side_elimination
    let recompute_controlled = F01Off.recompute_controlled
  end
  module ER01Off = Tc_solvers_extracted_restarting.Restarting.FirstDiscovery (V) (D) (U) (Set) (Map) (FlagsR01Off)
  let reference_R01Off body roots =
    let module C = ER01Off.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ER01Off.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ER01Off.sigma final
    | None -> failwith "R01Off: extracted reference exhausted fuel"
  module LR10Off = Tc_solvers.Slr.Restarting.Make (V) (D) (U) (F10Off)
  module GR10Off = Slrtc_restarting.Make (Slrtc_restarting.Control) (F10Off) (GU) (Arg) (System) (H)
  module FlagsR10Off = struct
    let restart_side_phases = F10Off.side_effect_phase_reset
    let eliminate_dead_sides = F10Off.dead_side_elimination
    let recompute_controlled = F10Off.recompute_controlled
  end
  module ER10Off = Tc_solvers_extracted_restarting.Restarting.FirstDiscovery (V) (D) (U) (Set) (Map) (FlagsR10Off)
  let reference_R10Off body roots =
    let module C = ER10Off.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ER10Off.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ER10Off.sigma final
    | None -> failwith "R10Off: extracted reference exhausted fuel"
  module LR11Off = Tc_solvers.Slr.Restarting.Make (V) (D) (U) (F11Off)
  module GR11Off = Slrtc_restarting.Make (Slrtc_restarting.Control) (F11Off) (GU) (Arg) (System) (H)
  module FlagsR11Off = struct
    let restart_side_phases = F11Off.side_effect_phase_reset
    let eliminate_dead_sides = F11Off.dead_side_elimination
    let recompute_controlled = F11Off.recompute_controlled
  end
  module ER11Off = Tc_solvers_extracted_restarting.Restarting.FirstDiscovery (V) (D) (U) (Set) (Map) (FlagsR11Off)
  let reference_R11Off body roots =
    let module C = ER11Off.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ER11Off.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ER11Off.sigma final
    | None -> failwith "R11Off: extracted reference exhausted fuel"
  module LNfp = Tc_solvers.Slr.Narrowing_fixed_point.Make (V) (D) (U)
  module GNfp = Slrtc_narrowing_fixed_point.Make (Slrtc_narrowing_fixed_point.Control) (F11) (GU) (Arg) (System) (H)
  module FlagsNfp = struct
    let restart_side_phases = F11.side_effect_phase_reset
    let eliminate_dead_sides = F11.dead_side_elimination
    let recompute_controlled = F11.recompute_controlled
  end
  module ENfp = Tc_solvers_extracted_narrowing_fixed_point.NarrowingFixedPointRuntime.Solver (V) (D) (U) (Set) (Map) (FlagsNfp) (Empty) (Credit) (Empty) (Empty)
  let reference_Nfp body roots =
    let module C = ENfp.R.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ENfp.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ENfp.R.sigma final
    | None -> failwith "Nfp: extracted reference exhausted fuel"
  let check (module L : SOLVER) goblint reference label starts missing tf roots =
    current := tf; rhsless := missing;
    let actual = L.solve ~initial:starts System.system roots in
    let expected_g = fst (goblint starts roots None) in
    let bindings = ref [] in
    L.iter (fun x d -> bindings := (x,d) :: !bindings) actual;
    List.iter (fun (x,d) ->
      if H.find_option expected_g x <> Some d then
        failwith (label ^ ": Goblint mismatch at " ^ string_of_int x)) !bindings;
    assert (H.length expected_g = List.length !bindings);
    let start x = List.fold_left (fun d (y,v) -> if x=y then max d v else d) 0 starts in
    let body x = add_constant (start x) (if List.mem x missing then Ret 0 else tf x) in
    let expected = reference body (roots @ List.map fst starts) in
    let sorted = List.sort Stdlib.compare in
    incr comparisons;
    (match List.assoc_opt (!policy, label) reference_gaps with
    | Some (known_reference, known_adapter) ->
        incr observed_gaps;
        if sorted expected <> known_reference || sorted !bindings <> known_adapter then
          let show bindings = String.concat ";"
            (List.map (fun (x,d) -> Printf.sprintf "%d=%d" x d) (sorted bindings)) in
          failwith (Printf.sprintf "%s: documented reference gap changed (reference [%s], adapter [%s])"
            label (show expected) (show !bindings))
    | None ->
        if sorted expected <> sorted !bindings then
          failwith (label ^ ": unexpected extracted machine mismatch"));
    List.iter (fun (x,d) -> assert (L.mem actual x && L.value actual x = d)) !bindings;
    assert (not (L.mem actual 999) && L.value actual 999 = D.bottom);
    let fresh = L.solve (fun _ -> None) [] in
    assert (not (L.mem fresh 0));
    List.iter (fun (x,d) -> assert (L.value actual x = d)) !bindings;
    let exception Callback_failure in
    (try ignore (L.solve (fun _ -> raise Callback_failure) [0]); assert false
     with Callback_failure -> ());
    (try ignore (L.solve (fun _ -> Some (fun _ _ _ -> raise Callback_failure)) [0]); assert false
     with Callback_failure -> ());
    let recovered = L.solve (fun _ -> Some (fun _ _ _ -> 1)) [0] in
    assert (L.value recovered 0 = 1)

  let test ?(starts=[]) ?(missing=[]) name tf roots =
    check (module LSimple) GSimple.solve reference_Simple (name ^ " Simple") starts missing tf roots;
    check (module LR00) GR00.solve reference_R00 (name ^ " R00") starts missing tf roots;
    check (module LR01) GR01.solve reference_R01 (name ^ " R01") starts missing tf roots;
    check (module LR10) GR10.solve reference_R10 (name ^ " R10") starts missing tf roots;
    check (module LR11) GR11.solve reference_R11 (name ^ " R11") starts missing tf roots;
    check (module LR00Off) GR00Off.solve reference_R00Off (name ^ " R00Off") starts missing tf roots;
    check (module LR01Off) GR01Off.solve reference_R01Off (name ^ " R01Off") starts missing tf roots;
    check (module LR10Off) GR10Off.solve reference_R10Off (name ^ " R10Off") starts missing tf roots;
    check (module LR11Off) GR11Off.solve reference_R11Off (name ^ " R11Off") starts missing tf roots;
    check (module LNfp) GNfp.solve reference_Nfp (name ^ " Nfp") starts missing tf roots

  let run () =
  test "empty" (fun _ -> Ret 0) [];
  test "ordinary cycle and duplicate roots" (function
    | 0 -> Get (1, fun v -> Ret v) | 1 -> Get (0, fun _ -> Ret 1) | _ -> Ret 0) [0;0];
  test "controlled owner without a self-read" (function
    | 0 -> Get (1, fun _ -> Ret 1) | 1 -> Get (0, fun _ -> Ret 0) | _ -> Ret 0) [0];
  if !policy = "WidenNarrow" then begin
    let enabled = LR11.solve System.system [0] in
    let disabled = LR11Off.solve System.system [0] in
    assert (LR11.value enabled 0 = 1);
    assert (LR11Off.value disabled 0 = 5)
  end;
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
  test "disappearing side contributions" (function
    | 0 -> Ret 0
    | 2 -> Get (0, fun v -> if v > 0 then Ret 0 else Side (1,2,Ret 0))
    | 3 -> Side (0,1,Ret 0) | _ -> Ret 0) [0;2;3];
  test "bottom owner remains distinguishable from absent" (fun _ -> Ret 0) [0];
  test "later root waits for discovered work" (function
    | 0 -> Side (1,1,Ret 0) | 2 -> Get (1,fun v -> Ret v) | _ -> Ret 0) [0;2]
end

module TwoCopy = Tc_solvers.Update.TwoCopy (V) (Domain)
module WidenNarrow = Tc_solvers.Update.WidenNarrow (V) (Domain)
module Join = Tc_solvers.Update.Join (V) (D)
module CopyChecks = CheckPolicy (TwoCopy) (Slrtc_update.CopyUpdate)
module WNChecks = CheckPolicy (WidenNarrow) (Slrtc_update.WNUpdate)
module JoinChecks = CheckPolicy (Join) (Slrtc_nfp_update.JoinUpdate)
let () =
  policy := "TwoCopy"; CopyChecks.run ();
  policy := "WidenNarrow"; WNChecks.run ();
  policy := "Join"; JoinChecks.run ();
  assert (!observed_gaps = List.length reference_gaps);
  Printf.printf "library: %d differential cases match Goblint; %d documented extracted-reference gaps verified\n"
    !comparisons !observed_gaps
