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
