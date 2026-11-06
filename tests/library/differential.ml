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
  module LNfpOff = Tc_solvers.Slr.Narrowing_fixed_point.Make_with_features (V) (D) (U) (F11Off)
  module GNfpOff = Slrtc_narrowing_fixed_point.Make (Slrtc_narrowing_fixed_point.Control) (F11Off) (GU) (Arg) (System) (H)
  module FlagsNfpOff = struct
    let restart_side_phases = F11Off.side_effect_phase_reset
    let eliminate_dead_sides = F11Off.dead_side_elimination
    let recompute_controlled = F11Off.recompute_controlled
  end
  module ENfpOff = Tc_solvers_extracted_narrowing_fixed_point.NarrowingFixedPointRuntime.Solver (V) (D) (U) (Set) (Map) (FlagsNfpOff) (Empty) (Credit) (Empty) (Empty)
  let reference_NfpOff body roots =
    let module C = ENfpOff.R.ConstraintSystem in
    let rec convert = function
      | Ret d -> C.Ret d
      | Get (x,k) -> C.Get (x, fun d -> convert (k d))
      | Side (x,d,k) -> C.Side (x,d,convert k)
      | Spawn (x,k) -> C.Spawn (x,convert k)
    in
    match ENfpOff.solve_fuel 100000 (fun x -> convert (body x)) roots with
    | Some final -> ENfpOff.R.sigma final
    | None -> failwith "NfpOff: extracted reference exhausted fuel"
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
    check (module LNfp) GNfp.solve reference_Nfp (name ^ " Nfp") starts missing tf roots;
    check (module LNfpOff) GNfpOff.solve reference_NfpOff (name ^ " NfpOff") starts missing tf roots

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
    assert (LR11Off.value disabled 0 = 5);
    let nfp_enabled = LNfp.solve System.system [0] in
    let nfp_disabled = LNfpOff.solve System.system [0] in
    assert (LNfp.value nfp_enabled 0 = 1);
    assert (LNfpOff.value nfp_disabled 0 = 5)
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

(* Plus compares stores, every transition, discoveries, evaluation order and
   complete policy calls against the untouched reference, in all 16 settings. *)
module PlusV = struct include V let compare = Int.compare let hash = Hashtbl.hash end
module OrderedMap = Stdlib.Map.Make (Int)
module OrderedSet = Stdlib.Set.Make (Int)
module PlusMaps = struct
  type 'a t = 'a OrderedMap.t
  let empty = OrderedMap.empty
  let lookup map key = OrderedMap.find_opt key map
  let update map key value = OrderedMap.add key value map
  let values map = List.map snd (OrderedMap.bindings map)
end
module PlusSets = struct
  type t = OrderedSet.t
  let empty = OrderedSet.empty
  let mem = OrderedSet.mem
  let add = OrderedSet.add
  let elements = OrderedSet.elements
end
module PlusChecks (Policy : Tc_solvers.UPDATE with type variable = int and type value = int) = struct
  let run ?(shrinking = false) flags body roots =
    let module F = struct
      let recompute_controlled = flags land 1 <> 0
      let defer_spawns = flags land 2 <> 0
      let side_effect_phase_reset = flags land 4 <> 0
      let dead_side_elimination = flags land 8 <> 0
      let restart_side_phases = side_effect_phase_reset
      let eliminate_dead_sides = dead_side_elimination
    end in
    let policy_calls = ref [] in
    let initial_calls = ref [] in
    let module P = struct
      include Policy
      let initial_phase side owner =
        let phase = Policy.initial_phase side owner in
        initial_calls := (side,owner,phase) :: !initial_calls;
        phase
      let update side owner phase old input =
        let next_phase, value = Policy.update side owner phase old input in
        policy_calls := (side,owner,phase,old,input,next_phase,value) :: !policy_calls;
        next_phase, value
    end in
    let side_calls = ref [] in
    let side_initials = ref [] in
    let module SU = struct
      type variable = int
      type value = int
      type phase = int
      let initial_phase source target =
        side_initials := (source,target) :: !side_initials; 0
      let update source target phase old input aggregate =
        side_calls := (source,target,phase,old,input,aggregate) :: !side_calls;
        phase + 1, if shrinking then input else max old input
    end in
    let module L = Tc_solvers.Slr.Plus_restarting.Make_with_features (PlusV) (D) (P) (SU) (F) in
    let module R = Tc_solvers_extracted_plus_restarting.PlusRestartingRuntime.Engine
      (PlusV) (D) (P) (SU) (PlusSets) (PlusMaps) (F) in
    let rec convert_l = function
      | Ret d -> L.Ret d
      | Get (x,k) -> L.Get (x,fun d -> convert_l (k d))
      | Side (x,d,next) -> L.Side (x,d,convert_l next)
      | Spawn (x,next) -> L.Spawn (x,convert_l next)
    in
    let reference_transition = ref 0 in
    let reference_reads = ref [] and reference_requests = ref [] in
    let reference_evals = ref [] and reference_ranks = ref [] in
    let rec convert_r owner = function
      | Ret d -> R.ConstraintSystem.Ret d
      | Get (x,k) -> R.ConstraintSystem.Get (x,fun d ->
          reference_reads := (!reference_transition,owner,x,d) :: !reference_reads;
          convert_r owner (k d))
      | Side (x,d,next) -> R.ConstraintSystem.Side (x,d,convert_r owner next)
      | Spawn (x,next) -> R.ConstraintSystem.Spawn (x,convert_r owner next)
    in
    let actual_events = ref [] in
    let actual_evals = ref [] and actual_ranks = ref [] in
    let actual_requests = ref [] and actual_reads = ref [] in
    let last_transition = ref (-1) in
    let actual = L.solve ~max_steps:100000 ~on_event:(fun { Tc_solvers.transition; event } ->
      actual_events := { Tc_solvers.transition; event } :: !actual_events;
      assert (transition >= !last_transition);
      last_transition := transition;
      match event with
      | Tc_solvers.Evaluation_start owner -> actual_evals := (transition,owner) :: !actual_evals
      | Tc_solvers.Discover d -> actual_ranks := (transition,d.variable,d.rank) :: !actual_ranks
      | Tc_solvers.Read_request r -> actual_requests := (transition,r.owner,r.target) :: !actual_requests
      | Tc_solvers.Read r -> actual_reads := (transition,r.owner,r.target,r.value) :: !actual_reads
      | _ -> ()) (fun x -> convert_l (body x)) roots in
    let actual_calls = !policy_calls and actual_sides = !side_calls in
    let actual_initials = !initial_calls and actual_side_initials = !side_initials in
    policy_calls := []; side_calls := []; initial_calls := []; side_initials := [];
    let rec run limit steps config =
      match R.terminal_state config with
      | Some _ -> steps, config
      | None when steps = limit -> steps, config
      | None ->
        reference_transition := steps;
        begin match config.R.cfg_control with
        | R.RunRhs (fr,R.ConstraintSystem.Get (target,_),_) ->
          reference_requests := (steps,fr.R.frame_owner,target) :: !reference_requests
        | _ -> ()
        end;
        match R.next_config (fun x -> convert_r x (body x)) config with
        | None -> failwith "Plus reference stuck"
        | Some next ->
          if R.Ranking.size next.R.cfg_state.ranking > R.Ranking.size config.R.cfg_state.ranking then
            begin match next.R.cfg_state.ranking with
            | x :: _ -> reference_ranks := (steps,x,R.Ranking.size next.R.cfg_state.ranking - 1) :: !reference_ranks
            | [] -> assert false
            end;
          begin match next.R.cfg_control,config.R.cfg_control with
          | R.RunRhs (fr,_,_), (R.StartEpisode _ | R.RunDrain _) ->
            reference_evals := (steps,fr.R.frame_owner) :: !reference_evals
          | _ -> ()
          end;
          run limit (steps+1) next
    in
    let steps, expected = run 100000 0 (R.initial_config roots) in
    assert (Option.is_some (R.terminal_state expected));
    assert (L.completion actual = Tc_solvers.Complete);
    assert ((L.statistics actual).steps = steps && !last_transition < steps);
    assert ((L.statistics actual).observer_errors = 0);
    assert (L.bindings actual = OrderedMap.bindings expected.R.cfg_state.sigma);
    assert (!actual_evals = !reference_evals && !actual_ranks = !reference_ranks);
    assert (!actual_requests = !reference_requests && !actual_reads = !reference_reads);
    assert (actual_calls = !policy_calls && actual_sides = !side_calls);
    assert (actual_initials = !initial_calls && actual_side_initials = !side_initials);
    policy_calls := []; side_calls := []; initial_calls := []; side_initials := [];
    let cached_events = ref [] in
    let cached = L.solve ~aggregate_cache:true ~max_steps:100000
      ~on_event:(fun event -> cached_events := event :: !cached_events)
      (fun x -> convert_l (body x)) roots in
    assert (L.bindings cached = L.bindings actual);
    assert (L.completion cached = L.completion actual && L.statistics cached = L.statistics actual);
    assert (!cached_events = !actual_events);
    assert (actual_calls = !policy_calls && actual_sides = !side_calls);
    assert (actual_initials = !initial_calls && actual_side_initials = !side_initials);
    (* Bounded solves retain requested dependencies before callees return. *)
    List.iter (fun budget ->
      let requests = ref [] and reads = ref [] in
      let events = ref [] in
      let partial = L.solve ~max_steps:budget ~on_event:(fun { Tc_solvers.transition; event } ->
        events := { Tc_solvers.transition; event } :: !events;
        assert (transition >= 0 && transition < budget);
        match event with
        | Tc_solvers.Read_request r -> requests := (transition,r.owner,r.target) :: !requests
        | Tc_solvers.Read r -> reads := (transition,r.owner,r.target,r.value) :: !reads
        | _ -> ()) (fun x -> convert_l (body x)) roots in
      reference_requests := []; reference_reads := [];
      reference_evals := []; reference_ranks := [];
      let steps, expected = run budget 0 (R.initial_config roots) in
      assert ((L.statistics partial).steps = steps && (L.statistics partial).observer_errors = 0);
      assert (!requests = !reference_requests && !reads = !reference_reads);
      assert (L.bindings partial = OrderedMap.bindings expected.R.cfg_state.sigma);
      assert (L.completion partial =
        if Option.is_some (R.terminal_state expected) then Tc_solvers.Complete else Tc_solvers.Step_limit);
      let cached_events = ref [] in
      let cached = L.solve ~aggregate_cache:true ~max_steps:budget
        ~on_event:(fun event -> cached_events := event :: !cached_events)
        (fun x -> convert_l (body x)) roots in
      assert (L.bindings cached = L.bindings partial);
      assert (L.completion cached = L.completion partial && L.statistics cached = L.statistics partial);
      assert (!cached_events = !events)
    ) [0;1;5;17;20]

  let all () =
    let fixtures = [
      ([], (fun _ -> Ret 0));
      ([0;0;3], (function 0 -> Spawn (2,Spawn (1,Spawn (2,Ret 1))) | x -> Ret (min x 3)));
      ([0], (function 0 -> Get (1,fun _ -> Ret 1) | 1 -> Get (0,fun _ -> Ret 0) | _ -> Ret 0));
      ([0], (function 0 -> Side (1,1,Side (1,2,Get (1,fun v -> Ret v))) | _ -> Ret 0));
      ([0;2;3], (function 2 -> Get (0,fun v -> if v=0 then Side (1,2,Ret 0) else Ret 0)
        | 3 -> Side (0,1,Ret 0) | _ -> Ret 0));
      ([0], (function 0 -> Get (1,fun _ -> Spawn (1,Ret 1)) | _ -> Ret 0));
      ([0], (function 0 -> Get (1,fun _ -> Side (1,0,Ret 1)) | _ -> Ret 0));
      ([0;3], (function 0 -> Side (2,1,Ret 1) | 3 -> Side (2,2,Get (2,fun v -> Ret v)) | _ -> Ret 0));
      ([0], (function 0 -> Get (0,fun own -> Side (0,min 2 (own+1),Ret 0)) | _ -> Ret 0));
      ([0], (function 0 -> Side (1,1,Side (2,1,Side (1,2,Side (2,2,
          Get (1,fun _ -> Ret 0))))) | _ -> Ret 0));
    ] in
    for flags = 0 to 15 do
      List.iter (fun (roots,body) -> run flags body roots) fixtures;
      run ~shrinking:true flags (function
        | 0 -> Get (0,fun own -> Side (1,(if own=0 then 2 else 1),Ret 1))
        | _ -> Ret 0) [0]
    done;
    run 3 (function
      | 0 -> Get (0,fun _ -> Get (0,fun _ -> Spawn (90,Spawn (91,Get (1,fun v -> Ret v)))))
      | x when x < 12 -> Get (x+1,fun v -> Ret v)
      | _ -> Ret 1) [0]
end
module PlusJoinChecks = PlusChecks (Join)
module PlusCopyChecks = PlusChecks (TwoCopy)
module PlusWNChecks = PlusChecks (WidenNarrow)
let () =
  PlusJoinChecks.all (); PlusCopyChecks.all (); PlusWNChecks.all ();
  print_endline "Plus library: 531 reference/full-fold/cache comparisons, complete typed events and bounded prefixes (16 configurations, 3 policies) passed"
