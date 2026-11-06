module V = struct type t = int let equal = Int.equal let hash _ = 0 end
module D = struct
  type t = int
  let bottom = 0
  let join = max
  let leq = ( <= )
  let calls = ref []
  let widen old input = calls := (old,input) :: !calls; 5
  let narrow old input = max input (old - 1)
end
module Copy = Tc_solvers.Update.TwoCopy (V) (D)
module WN = Tc_solvers.Update.WidenNarrow (V) (D)
module Join = Tc_solvers.Update.Join (V) (D)
module Custom = struct
  type variable = int
  type value = int
  type phase = int
  let calls = ref []
  let initial_phase _ _ = 0
  let update side variable phase old input =
    calls := (side, variable, phase) :: !calls;
    phase + 1, max old input
end
module Solver = Tc_solvers.Slr.Simple.Make (V) (D) (Custom)

let () =
  let p = Copy.initial_phase false 0 in
  let p, a = Copy.update false 0 p 0 1 in
  let p, b = Copy.update false 0 p a 2 in
  assert (a = 1 && b = 2 && !(D.calls) = []);
  let p, c = Copy.update false 0 p b 4 in
  assert (c = 5 && !(D.calls) = [2,4]);
  let p, d = Copy.update false 0 p c 3 in
  assert (d = 4);
  let p, e = Copy.update false 0 p d 5 in
  let _, f = Copy.update false 0 p e 1 in
  assert (f = 5 && List.hd !(D.calls) = (5,1));
  let _, x = WN.update false 0 (WN.initial_phase false 0) 0 1 in
  assert (x = 5);
  let _, x = Join.update true 1 (Join.initial_phase true 1) 2 1 in
  assert (x = 2);
  let lookups = ref [] in
  let system x =
    lookups := x :: !lookups;
    match x with
    | 0 -> Some (fun get side _ ->
        ignore (get 0); side 1 1; side 1 2; 1)
    | _ -> None
  in
  let s = Solver.solve system [0;2] in
  let first_seen = List.fold_left (fun xs x ->
    if List.mem x xs then xs else xs @ [x]) [] (List.rev !lookups) in
  assert (first_seen = [0;1;2]);
  assert (Solver.value s 1 = 2 && Solver.mem s 2);
  assert (List.exists (fun (side,_,_) -> side) !(Custom.calls));
  assert (List.exists (fun (side,_,_) -> not side) !(Custom.calls));
  let initialized = Solver.solve ~initial:[3,1;3,2] (fun _ -> None) [] in
  assert (Solver.value initialized 3 = 2);
  let reentrant = Solver.solve (fun _ -> Some (fun _ _ _ ->
    let inner = Solver.solve (fun _ -> None) [9] in
    assert (Solver.mem inner 9); 1)) [0] in
  assert (Solver.value reentrant 0 = 1 && not (Solver.mem reentrant 9));
  print_endline "library API: updates, custom policy, ordering, and reentrant fresh solves passed"


(* Equal domain values need not have equal OCaml representations. *)
module Equivalent = struct
  type t = { level : int; stamp : int }
  let sequence = ref 0
  let fresh level = incr sequence; { level; stamp = !sequence }
  let bottom = { level = 0; stamp = 0 }
  let leq left right = left.level <= right.level
  let join left right = fresh (max left.level right.level)
end
module EJ = Tc_solvers.Update.Join (V) (Equivalent)
module ES = Tc_solvers.Slr.Simple.Make (V) (Equivalent) (EJ)
module Flags = struct
  let side_effect_phase_reset = true
  let dead_side_elimination = true
  let recompute_controlled = true
end
module ER = Tc_solvers.Slr.Restarting.Make (V) (Equivalent) (EJ) (Flags)
module EN = Tc_solvers.Slr.Narrowing_fixed_point.Make (V) (Equivalent) (EJ)
module type EQUIVALENT_SOLVER = Tc_solvers.SOLVER
  with type variable = int and type value = Equivalent.t
let check_equivalence (module S : EQUIVALENT_SOLVER) =
  let a = Equivalent.fresh 1 and b = Equivalent.fresh 1 in
  assert (a.stamp <> b.stamp && Equivalent.leq a b && Equivalent.leq b a);
  let evaluations = ref 0 in
  let solution = S.solve (fun _ -> Some (fun get _ _ ->
    incr evaluations;
    if !evaluations > 10 then failwith "structural equality used for domain values";
    ignore (get 0);
    Equivalent.fresh 1)) [0] in
  assert ((S.value solution 0).level = 1)
let () =
  check_equivalence (module ES);
  check_equivalence (module ER);
  check_equivalence (module EN)

(* The practical Plus API exposes typed variables/events, not machine records. *)
module PV = struct
  type t = { identity : int; display : string }
  let compare a b = Int.compare a.identity b.identity
  let equal a b = compare a b = 0
  let hash v = Hashtbl.hash v.identity
end
module PD = struct
  include D
  let comparisons = ref 0
  let leq a b = incr comparisons; a <= b
end
module PU = Tc_solvers.Update.Join (PV) (PD)
module PSU = Tc_solvers.Update.SideJoin (PV) (PD)
module Plus = Tc_solvers.Slr.Plus_restarting.Make (PV) (PD) (PU) (PSU)
let pv identity = PV.{ identity; display = "same presentation" }
let plus_system variable =
  match variable.PV.identity with
  | 0 -> Plus.Spawn (pv 3, Plus.Get (pv 1, fun v ->
      Plus.Side (pv 2, v, Plus.Side (pv 2, 2, Plus.Ret v))))
  | 1 -> Plus.Ret 1
  | 3 -> Plus.Ret 3
  | _ -> Plus.Ret 0
let () =
  assert ((pv 0).PV.display = (pv 1).PV.display && not (PV.equal (pv 0) (pv 1)));
  let events = ref [] and live = ref 0 in
  PD.comparisons := 0;
  let plain = Plus.solve plus_system [pv 0] in
  let comparisons = !(PD.comparisons) in
  PD.comparisons := 0;
  let observed = Plus.solve ~on_event:(fun e ->
    incr live;
    if List.length !events < 2 then events := e :: !events)
    plus_system [pv 0] in
  assert (!(PD.comparisons) = comparisons);
  assert (!live > 2 && List.length !events = 2);
  assert (Plus.bindings plain = Plus.bindings observed);
  assert (Plus.statistics plain = Plus.statistics observed);
  assert (Plus.value observed (pv 0) = 1 && Plus.value observed (pv 2) = 2);
  assert (Plus.value observed (pv 3) = 3);
  let saved = Plus.bindings observed in
  let changes = ref [] and discoveries = ref [] in
  ignore (Plus.solve ~on_event:(fun { Tc_solvers.event; _ } -> match event with
    | Tc_solvers.Value_change change ->
      changes := (change.variable.PV.identity, change.old_value, change.value) :: !changes
    | Tc_solvers.Discover discovery ->
      discoveries := (discovery.variable.PV.identity, discovery.rank) :: !discoveries
    | _ -> ()) plus_system [pv 0]);
  assert (List.rev !discoveries = [0,0;1,1;2,2;3,3]);
  assert (List.mem (2,0,1) !changes && List.mem (2,1,2) !changes);
  let bad_observer = Plus.solve ~on_event:(fun _ -> failwith "observer") plus_system [pv 0] in
  assert (Plus.bindings bad_observer = saved);
  assert ((Plus.statistics bad_observer).observer_errors = !live);
  let partial = Plus.solve ~max_steps:0 plus_system [pv 0] in
  assert (Plus.completion partial = Tc_solvers.Step_limit);
  assert (Plus.bindings partial = [] && (Plus.statistics partial).steps = 0);
  let empty = Plus.solve (fun _ -> Plus.Ret 0) [] in
  assert (Plus.completion empty = Tc_solvers.Complete);
  assert (Plus.bindings observed = saved && Plus.bindings empty = []);
  let nested = ref false in
  ignore (Plus.solve ~on_event:(fun _ ->
    if not !nested then begin
      nested := true;
      let inner = Plus.solve (fun _ -> Plus.Ret 4) [pv 9] in
      assert (Plus.value inner (pv 9) = 4)
    end) plus_system [pv 0]);
  assert !nested;
  let exception Client_failure in
  (try ignore (Plus.solve (fun _ -> raise Client_failure) [pv 0]); assert false
   with Client_failure -> ());
  print_endline "Plus library API: typed identity, observations, deltas, isolation and stable results passed"

(* Policies must advance even when they return an equivalent value. *)
module PhasePolicy = struct
  type variable = int
  type value = int
  type phase = int
  let calls = ref []
  let initial_phase _ _ = 0
  let update _ owner phase old _input =
    calls := (owner,phase) :: !calls;
    phase + 1, if phase = 0 then old else 2
end
module PhaseSide = struct
  type variable = int
  type value = int
  type phase = int
  let calls = ref []
  let initial_phase _ _ = 0
  let update source target phase old input _aggregate =
    calls := (source,target,phase) :: !calls;
    phase + 1, max old input
end
module IV = struct include V let compare = Int.compare end
module PhasePlus = Tc_solvers.Slr.Plus_restarting.Make (IV) (D) (PhasePolicy) (PhaseSide)
let () =
  let solution = PhasePlus.solve (function
    | 0 -> PhasePlus.Side (1,1,PhasePlus.Side (1,1,
        PhasePlus.Get (1,fun _ -> PhasePlus.Ret 1)))
    | 1 -> PhasePlus.Side (0,1,PhasePlus.Ret 1)
    | _ -> PhasePlus.Ret 0) [0] in
  assert (PhasePlus.completion solution = Tc_solvers.Complete);
  assert (List.mem (0,1,1) !(PhaseSide.calls));
  assert (List.exists (fun (_,phase) -> phase > 0) !(PhasePolicy.calls));
  print_endline "Plus library API: equivalent ordinary/side results retain policy phases"

module EquivalentSide = struct
  type variable = int
  type value = Equivalent.t
  type phase = int
  let initial_phase _ _ = 0
  let phases = ref []
  let update _ _ phase old input _aggregate =
    phases := phase :: !phases;
    phase+1, Equivalent.join old input
end
module EquivalentPlus = Tc_solvers.Slr.Plus_restarting.Make (IV) (Equivalent) (EJ) (EquivalentSide)
let () =
  let equal_side_updates = ref 0 and stored = ref None in
  let result = EquivalentPlus.solve ~on_event:(fun { Tc_solvers.event; _ } -> match event with
    | Tc_solvers.Side_update { old_value; value; _ }
      when old_value.Equivalent.level = value.Equivalent.level && old_value.stamp <> value.stamp ->
        incr equal_side_updates
    | Tc_solvers.Value_change { variable = 1; value; _ } -> stored := Some value
    | _ -> ())
    (function
      | 0 -> EquivalentPlus.Side (1,Equivalent.fresh 1,
          EquivalentPlus.Side (1,Equivalent.fresh 1,
            EquivalentPlus.Get (0,fun _ -> EquivalentPlus.Ret (Equivalent.fresh 1))))
      | _ -> EquivalentPlus.Ret Equivalent.bottom) [0] in
  assert (EquivalentPlus.completion result = Tc_solvers.Complete);
  assert (!equal_side_updates > 0 && List.mem 1 !(EquivalentSide.phases));
  assert (Some (EquivalentPlus.value result 1) = !stored);
  print_endline "Plus library API: equivalent representatives retain contributions, phases and stored values"

(* Requests survive a budget boundary while recursive callees are pending. *)
let nested_reads variable =
  match variable.PV.identity with
  | 0 -> Plus.Get (pv 0,fun _ -> Plus.Get (pv 0,fun _ ->
      Plus.Spawn (pv 90,Plus.Spawn (pv 91,Plus.Get (pv 1,fun v -> Plus.Ret v)))))
  | x when x < 12 -> Plus.Get (pv (x+1),fun v -> Plus.Ret v)
  | _ -> Plus.Ret 1
let () =
  let retained = ref [] in
  let partial = Plus.solve ~max_steps:20 ~on_event:(fun event -> retained := event :: !retained)
    nested_reads [pv 0] in
  let events = List.rev !retained in
  let requests = List.filter (fun { Tc_solvers.event; _ } ->
    match event with Tc_solvers.Read_request _ -> true | _ -> false) events in
  let reads = List.filter (fun { Tc_solvers.event; _ } ->
    match event with Tc_solvers.Read _ -> true | _ -> false) events in
  assert (Plus.completion partial = Tc_solvers.Step_limit);
  assert ((Plus.statistics partial).steps = 20);
  assert (List.length requests = 9 && List.length reads = 2);
  List.iter (fun { Tc_solvers.transition; _ } -> assert (transition >= 0 && transition < 20)) events;
  (* Immediate self-reads request and complete in one transition. *)
  assert (List.map (fun { Tc_solvers.transition; _ } -> transition) reads = [2;3]);
  let rec requests_precede_completions pending = function
    | [] -> ()
    | { Tc_solvers.transition; event } :: rest ->
      match event with
      | Tc_solvers.Read_request { owner; target } ->
        requests_precede_completions ((owner,target,transition) :: pending) rest
      | Tc_solvers.Read { owner; target; _ } ->
        let _,_,requested = List.find (fun (o,t,_) -> PV.equal owner o && PV.equal target t) pending in
        assert (requested <= transition);
        requests_precede_completions pending rest
      | _ -> requests_precede_completions pending rest
  in
  requests_precede_completions [] events;
  let complete_events = ref [] in
  let complete = Plus.solve ~on_event:(fun event -> complete_events := event :: !complete_events)
    nested_reads [pv 0] in
  assert (Plus.completion complete = Tc_solvers.Complete);
  let prefix = List.filter (fun { Tc_solvers.transition; _ } -> transition < 20)
    (List.rev !complete_events) in
  assert (prefix = events);
  (* Nested solves have independent counters; the outer envelope is immutable. *)
  let first = ref true and outer_events = ref [] in
  let nested = Plus.solve ~max_steps:20 ~on_event:(fun envelope ->
    if !first then begin
      first := false;
      let inner = Plus.solve ~on_event:(fun { Tc_solvers.transition; _ } ->
        assert (transition >= 0)) (fun _ -> Plus.Ret 1) [pv 99] in
      assert ((Plus.statistics inner).observer_errors = 0)
    end;
    outer_events := envelope :: !outer_events) nested_reads [pv 0] in
  assert ((Plus.statistics nested).observer_errors = 0);
  assert (List.rev !outer_events = events && List.rev !retained = events);
  let called = ref false in
  ignore (Plus.solve ~max_steps:0 ~on_event:(fun _ -> called := true) nested_reads [pv 0]);
  assert (not !called);
  print_endline "Plus observations: indexed requests preserve 9 dependencies / 2 completions at 20 transitions"

(* Incomparable and masked decreases, withdrawal and post-policy contributions. *)
module Bits = struct
  type t = int
  let bottom = 0
  let join = ( lor )
  let leq a b = a land b = a
end
module BitsOrdinary = Tc_solvers.Update.Join (IV) (Bits)
module BitsSide = struct
  type variable = int
  type value = int
  type phase = int
  let calls = ref []
  let initial_phase _ _ = 0
  let update source target phase old input aggregate =
    calls := (source,target,phase,old,input,aggregate) :: !calls;
    (* Source 5 demonstrates that the policy result, not raw payload, is stored. *)
    phase+1, if source=5 then input land 1 else input
end
module BitsPlus = Tc_solvers.Slr.Plus_restarting.Make (IV) (Bits) (BitsOrdinary) (BitsSide)
let bits_system = function
  | 0 -> BitsPlus.Side (10,1,BitsPlus.Side (10,2,BitsPlus.Ret 1))
  | 1 -> BitsPlus.Side (10,4,BitsPlus.Ret 1)
  | 2 -> BitsPlus.Get (2,fun own -> BitsPlus.Side (10,(if own=0 then 2 else 4),BitsPlus.Ret 1))
  | 3 -> BitsPlus.Get (3,fun own -> BitsPlus.Side (10,(if own=0 then 3 else 1),BitsPlus.Ret 1))
  | 4 -> BitsPlus.Get (4,fun own -> if own=0 then BitsPlus.Side (10,8,BitsPlus.Ret 1) else BitsPlus.Ret 1)
  | 5 -> BitsPlus.Side (10,2,BitsPlus.Ret 0)
  | _ -> BitsPlus.Ret 0
let () =
  let solve cache =
    BitsSide.calls := [];
    let events = ref [] in
    let result = BitsPlus.solve ~aggregate_cache:cache
      ~on_event:(fun event -> events := event :: !events) bits_system [0;1;2;3;4;5] in
    result, !events, !(BitsSide.calls)
  in
  let full,events,calls = solve false in
  let cached,cached_events,cached_calls = solve true in
  assert (BitsPlus.completion cached = Tc_solvers.Complete);
  assert (BitsPlus.value cached 10 = 7 && BitsPlus.bindings cached = BitsPlus.bindings full);
  assert (events = cached_events && calls = cached_calls);
  assert (List.exists (fun { Tc_solvers.event; _ } ->
    match event with Tc_solvers.Side_update { source=2; old_value=2; value=4; _ } -> true | _ -> false) events);
  assert (List.exists (fun { Tc_solvers.event; _ } ->
    match event with Tc_solvers.Side_update { source=4; old_value=8; value=0; _ } -> true | _ -> false) events);
  assert (List.exists (fun { Tc_solvers.event; _ } ->
    match event with Tc_solvers.Side_update { source=5; input=2; value=0; _ } -> true | _ -> false) events);
  print_endline "Plus aggregate cache: incomparable/masked decreases, withdrawals and policy results match full folds"

(* Cached and folded aggregates may have different equivalent representatives. *)
let equivalent_event { Tc_solvers.transition; event } =
  let level v = v.Equivalent.level in
  let event = match event with
    | Tc_solvers.Evaluation_start v -> Tc_solvers.Evaluation_start v
    | Tc_solvers.Evaluation_result (v,d) -> Tc_solvers.Evaluation_result (v,level d)
    | Tc_solvers.Read_request { owner; target } -> Tc_solvers.Read_request { owner; target }
    | Tc_solvers.Read { owner; target; value } -> Tc_solvers.Read { owner; target; value=level value }
    | Tc_solvers.Side { owner; target; value } -> Tc_solvers.Side { owner; target; value=level value }
    | Tc_solvers.Spawn { owner; target } -> Tc_solvers.Spawn { owner; target }
    | Tc_solvers.Discover { variable; rank } -> Tc_solvers.Discover { variable; rank }
    | Tc_solvers.Materialize { variable; value } -> Tc_solvers.Materialize { variable; value=level value }
    | Tc_solvers.Value_change { variable; old_value; value } ->
      Tc_solvers.Value_change { variable; old_value=level old_value; value=level value }
    | Tc_solvers.Side_update { source; target; input; old_value; value } ->
      Tc_solvers.Side_update { source; target; input=level input; old_value=level old_value; value=level value }
  in { Tc_solvers.transition; event }
let () =
  let solve cache =
    EquivalentSide.phases := [];
    let events = ref [] in
    let result = EquivalentPlus.solve ~aggregate_cache:cache
      ~on_event:(fun event -> events := equivalent_event event :: !events)
      (function
        | 0 -> EquivalentPlus.Side (2,Equivalent.fresh 1,EquivalentPlus.Ret (Equivalent.fresh 1))
        | 1 -> EquivalentPlus.Side (2,Equivalent.fresh 1,EquivalentPlus.Side (2,Equivalent.fresh 1,
            EquivalentPlus.Get (2,fun v -> EquivalentPlus.Ret v)))
        | _ -> EquivalentPlus.Ret Equivalent.bottom) [0;1] in
    result, !events, !(EquivalentSide.phases)
  in
  let full,events,phases = solve false in
  let cached,cached_events,cached_phases = solve true in
  assert (List.map (fun (v,d) -> v,d.Equivalent.level) (EquivalentPlus.bindings full) =
          List.map (fun (v,d) -> v,d.Equivalent.level) (EquivalentPlus.bindings cached));
  assert (EquivalentPlus.statistics cached = EquivalentPlus.statistics full);
  assert (events = cached_events && phases = cached_phases);
  print_endline "Plus aggregate cache: equivalent representatives preserve phase, scheduling and typed event semantics"
