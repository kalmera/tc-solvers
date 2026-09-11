let[@inline always] solve_one
    bottom start_evaluation get side spawn set_value drain_owner system owner =
  start_evaluation owner;
  let direct =
    match system owner with
    | Some body -> body (get owner) (side owner) (spawn owner)
    | None -> bottom
  in
  set_value owner direct;
  drain_owner owner

let[@inline always] solve_all
    _fuel initialize pop_owner solve_owner roots =
  initialize roots;
  let rec loop () =
    match pop_owner () with
    | None -> true
    | Some owner ->
      solve_owner owner;
      loop ()
  in
  loop ()

type seeded_result =
  | SeedsSolved of int
  | SeedsOutOfFuel

let rec drain_with_fuel fuel pop_owner solve_owner =
  match pop_owner () with
  | None -> SeedsSolved fuel
  | Some owner ->
    if fuel = 0 then SeedsOutOfFuel
    else begin
      solve_owner owner;
      drain_with_fuel (fuel - 1) pop_owner solve_owner
    end

let rec solve_seeds_with_fuel
    fuel is_started pop_owner solve_owner roots =
  match roots with
  | [] -> SeedsSolved fuel
  | root :: remaining_roots ->
    if is_started root then
      solve_seeds_with_fuel
        fuel is_started pop_owner solve_owner remaining_roots
    else if fuel = 0 then
      SeedsOutOfFuel
    else begin
      solve_owner root;
      match drain_with_fuel (fuel - 1) pop_owner solve_owner with
      | SeedsOutOfFuel -> SeedsOutOfFuel
      | SeedsSolved after_drain ->
        solve_seeds_with_fuel
          after_drain is_started pop_owner solve_owner remaining_roots
    end
