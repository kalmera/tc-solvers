
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('v, 'd, 'monad) transfer =
  ('v -> 'monad) -> ('v -> 'd -> 'monad) -> ('v -> 'monad) -> 'monad

type ('v, 'd, 'monad) system = 'v -> ('v, 'd, 'monad) transfer option

(** val eval_transfer :
    ('a1 -> 'a3) -> ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1, 'a2, 'a3)
    transfer -> 'a3 **)

let eval_transfer read emit spawn body =
  body read emit spawn

type ('v, 'd, 'monad) owner_operations = { begin_evaluation : ('v -> 'monad);
                                           read_value : ('v -> 'v -> 'monad);
                                           emit_side_effect : ('v -> 'v -> 'd
                                                              -> 'monad);
                                           spawn_variable : ('v -> 'v ->
                                                            'monad);
                                           commit_value : ('v -> 'd -> 'monad);
                                           drain_owner : ('v -> 'monad) }

(** val begin_evaluation : ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a3 **)

let begin_evaluation o =
  o.begin_evaluation

(** val read_value : ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a1 -> 'a3 **)

let read_value o =
  o.read_value

(** val emit_side_effect :
    ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a1 -> 'a2 -> 'a3 **)

let emit_side_effect o =
  o.emit_side_effect

(** val spawn_variable :
    ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a1 -> 'a3 **)

let spawn_variable o =
  o.spawn_variable

(** val commit_value :
    ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a2 -> 'a3 **)

let commit_value o =
  o.commit_value

(** val drain_owner : ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a3 **)

let drain_owner o =
  o.drain_owner

type solve_result =
| Solved
| OutOfFuel

(** val solve_result_rect : 'a1 -> 'a1 -> solve_result -> 'a1 **)

let solve_result_rect f f0 = function
| Solved -> f
| OutOfFuel -> f0

(** val solve_result_rec : 'a1 -> 'a1 -> solve_result -> 'a1 **)

let solve_result_rec f f0 = function
| Solved -> f
| OutOfFuel -> f0

type seeded_result =
| SeedsSolved of int
| SeedsOutOfFuel

(** val seeded_result_rect : (int -> 'a1) -> 'a1 -> seeded_result -> 'a1 **)

let seeded_result_rect f f0 = function
| SeedsSolved n -> f n
| SeedsOutOfFuel -> f0

(** val seeded_result_rec : (int -> 'a1) -> 'a1 -> seeded_result -> 'a1 **)

let seeded_result_rec f f0 = function
| SeedsSolved n -> f n
| SeedsOutOfFuel -> f0

(** val solve_owner :
    (__ -> __ -> 'a3) -> (__ -> __ -> 'a3 -> (__ -> 'a3) -> 'a3) -> 'a2 ->
    ('a1, 'a2, 'a3) owner_operations -> ('a1, 'a2, 'a3) system -> 'a1 -> 'a3 **)

let solve_owner ret bind bottom operations constraint_system owner =
  bind __ __ (operations.begin_evaluation owner) (fun _ ->
    Obj.magic bind __ __
      (match constraint_system owner with
       | Some body ->
         eval_transfer (operations.read_value owner)
           (operations.emit_side_effect owner)
           (operations.spawn_variable owner) body
       | None -> Obj.magic ret __ bottom)
      (fun direct ->
      bind __ __ (operations.commit_value owner direct) (fun _ ->
        operations.drain_owner owner)))

(** val solve_worklist :
    (__ -> __ -> 'a2) -> (__ -> __ -> 'a2 -> (__ -> 'a2) -> 'a2) -> int ->
    (unit -> 'a2) -> ('a1 -> 'a2) -> 'a2 **)

let rec solve_worklist ret bind fuel pop_owner solve_queued_owner =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ret __ OutOfFuel)
    (fun remaining ->
    Obj.magic bind __ __ (pop_owner ()) (fun picked ->
      match picked with
      | Some owner ->
        bind __ __ (solve_queued_owner owner) (fun _ ->
          solve_worklist ret bind remaining pop_owner solve_queued_owner)
      | None -> Obj.magic ret __ Solved))
    fuel

(** val solve_with_fuel :
    (__ -> __ -> 'a2) -> (__ -> __ -> 'a2 -> (__ -> 'a2) -> 'a2) -> int ->
    ('a1 list -> 'a2) -> (unit -> 'a2) -> ('a1 -> 'a2) -> 'a1 list -> 'a2 **)

let solve_with_fuel ret bind fuel initialize_roots pop_owner solve_queued_owner roots =
  bind __ __ (initialize_roots roots) (fun _ ->
    solve_worklist ret bind fuel pop_owner solve_queued_owner)

(** val drain_with_fuel :
    (__ -> __ -> 'a2) -> (__ -> __ -> 'a2 -> (__ -> 'a2) -> 'a2) -> int ->
    (unit -> 'a2) -> ('a1 -> 'a2) -> 'a2 **)

let rec drain_with_fuel ret bind fuel pop_owner solve_queued_owner =
  Obj.magic bind __ __ (pop_owner ()) (fun picked ->
    match picked with
    | Some owner ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> Obj.magic ret __ SeedsOutOfFuel)
         (fun remaining ->
         bind __ __ (solve_queued_owner owner) (fun _ ->
           drain_with_fuel ret bind remaining pop_owner solve_queued_owner))
         fuel)
    | None -> Obj.magic ret __ (SeedsSolved fuel))

(** val solve_seeds_with_fuel :
    (__ -> __ -> 'a2) -> (__ -> __ -> 'a2 -> (__ -> 'a2) -> 'a2) -> int ->
    ('a1 -> 'a2) -> (unit -> 'a2) -> ('a1 -> 'a2) -> 'a1 list -> 'a2 **)

let rec solve_seeds_with_fuel ret bind fuel is_started pop_owner solve_owner0 = function
| [] -> Obj.magic ret __ (SeedsSolved fuel)
| root :: remaining_roots ->
  Obj.magic bind __ __ (is_started root) (fun started ->
    if started
    then solve_seeds_with_fuel ret bind fuel is_started pop_owner
           solve_owner0 remaining_roots
    else ((fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Obj.magic ret __ SeedsOutOfFuel)
            (fun remaining_fuel ->
            bind __ __ (solve_owner0 root) (fun _ ->
              Obj.magic bind __ __
                (drain_with_fuel ret bind remaining_fuel pop_owner
                  solve_owner0)
                (fun drained ->
                match drained with
                | SeedsSolved after_drain ->
                  solve_seeds_with_fuel ret bind after_drain is_started
                    pop_owner solve_owner0 remaining_roots
                | SeedsOutOfFuel -> Obj.magic ret __ SeedsOutOfFuel)))
            fuel))
