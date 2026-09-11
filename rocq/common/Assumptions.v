From Stdlib Require Import List Sorting.Permutation.
From TcSolvers Require Export common.Interfaces.

Set Implicit Arguments.

(** Public assumptions for correctness and termination.

    These contracts are separate from the computational interfaces so
    extraction does not carry proof-oriented module fields. *)

Module Type DOMAIN_LAWS (D : DOMAIN).
  Parameter leq_refl :
    forall x, D.leq x x = true.
  Parameter leq_trans :
    forall x y z,
      D.leq x y = true ->
      D.leq y z = true ->
      D.leq x z = true.
  Parameter bottom_least :
    forall x, D.leq D.bottom x = true.
  Parameter join_upper_left :
    forall x y, D.leq x (D.join x y) = true.
  Parameter join_upper_right :
    forall x y, D.leq y (D.join x y) = true.
  Parameter join_least :
    forall x y z,
      D.leq x z = true ->
      D.leq y z = true ->
      D.leq (D.join x y) z = true.
  Parameter join_commutative :
    forall x y,
      D.leq (D.join x y) (D.join y x) = true /\
      D.leq (D.join y x) (D.join x y) = true.
  Parameter join_associative :
    forall x y z,
      D.leq (D.join (D.join x y) z) (D.join x (D.join y z)) = true /\
      D.leq (D.join x (D.join y z)) (D.join (D.join x y) z) = true.
End DOMAIN_LAWS.

Module Type ORDER_LAWS (V : VAR) (O : ORDER V).
  Parameter lt_irrefl :
    forall x, O.lt x x = false.
  Parameter lt_trans :
    forall x y z,
      O.lt x y = true ->
      O.lt y z = true ->
      O.lt x z = true.
  Parameter lt_total :
    forall x y,
      x <> y ->
      O.lt x y = true \/ O.lt y x = true.
  Parameter lt_asymmetric :
    forall x y,
      O.lt x y = true ->
      O.lt y x = false.
End ORDER_LAWS.

Module Type UPDATE_LAWS
  (V : VAR) (D : DOMAIN) (U : UPDATE V D).

  Definition equivalent (x y : D.t) : Prop :=
    D.leq x y = true /\ D.leq y x = true.

  Parameter update_sound :
    forall is_side variable phase old input,
      D.leq input
        (snd (U.update is_side variable phase old input)) = true.

  Parameter update_extensional :
    forall is_side variable phase old old' input input',
      equivalent old old' ->
      equivalent input input' ->
      equivalent
        (snd (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old' input')).

  Parameter update_stutter_closed :
    forall is_side variable phase old input,
      equivalent
        (snd (U.update is_side variable phase old input)) old ->
      forall old' input',
        equivalent old' old ->
        equivalent input' input ->
        equivalent
          (snd (U.update is_side variable
            (fst (U.update is_side variable phase old input))
            old' input'))
          old'.

  Parameter remaining_changes : U.phase -> D.t -> nat.

  Parameter remaining_changes_extensional :
    forall phase old old',
      equivalent old old' ->
      remaining_changes phase old = remaining_changes phase old'.

  Parameter remaining_changes_nonincreasing :
    forall is_side variable phase old input,
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <=
      remaining_changes phase old.

  Parameter update_change_consumes :
    forall is_side variable phase old input,
      ~ equivalent
          (snd (U.update is_side variable phase old input)) old ->
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <
      remaining_changes phase old.
End UPDATE_LAWS.

Module Type SET_LAWS (V : VAR) (S : SET V).
  Parameter mem_spec :
    forall x xs,
      S.mem x xs = true <-> List.In x (S.elements xs).
  Parameter empty_spec :
    forall x,
      S.mem x S.empty = false.
  Parameter add_spec :
    forall x y xs,
      S.mem x (S.add y xs) = true <->
      x = y \/ S.mem x xs = true.
End SET_LAWS.

Module Type MAP_LAWS (V : VAR) (M : MAP V).
  Parameter values_empty :
    forall A,
      M.values (M.empty A) = nil.
  Parameter lookup_empty :
    forall A x,
      M.lookup (M.empty A) x = None.
  Parameter lookup_update_same :
    forall A (m : M.t A) x value,
      M.lookup (M.update m x value) x = Some value.
  Parameter lookup_update_other :
    forall A (m : M.t A) x y value,
      x <> y ->
      M.lookup (M.update m y value) x = M.lookup m x.
  Parameter lookup_values :
    forall A (m : M.t A) x value,
      M.lookup m x = Some value ->
      List.In value (M.values m).

  (** Updating one key replaces exactly its previous value in the multiset
      exposed by [values], or adds one value when the key was absent.  This
      prevents proof-irrelevant map representation changes from changing an
      aggregate. *)
  Parameter values_update :
    forall A (m : M.t A) x value,
      exists rest,
        Permutation
          (M.values (M.update m x value))
          (value :: rest) /\
        match M.lookup m x with
        | Some previous =>
            Permutation (M.values m) (previous :: rest)
        | None =>
            Permutation (M.values m) rest
        end.
End MAP_LAWS.

Module Type QUEUE_LAWS
  (V : VAR) (O : ORDER V) (Q : QUEUE V O).

  Parameter In : V.t -> Q.t -> Prop.
  Parameter ordered : Q.t -> Prop.
  Parameter distinct : Q.t -> Prop.

  Parameter in_dec :
    forall x q, {In x q} + {~ In x q}.

  Parameter pop_empty :
    Q.pop_max (Q.empty tt) = None.

  Parameter peek_empty :
    Q.peek_max (Q.empty tt) = None.

  Parameter empty_ordered : ordered (Q.empty tt).
  Parameter empty_distinct : distinct (Q.empty tt).

  Parameter insert_members :
    forall x y q,
      In x (Q.insert y q) <-> x = y \/ In x q.

  Parameter insert_all_members :
    forall x xs q,
      In x (Q.insert_all xs q) <->
      List.In x xs \/ In x q.

  Parameter insert_ordered :
    forall x q,
      ordered q ->
      ordered (Q.insert x q).

  Parameter insert_distinct :
    forall x q,
      distinct q ->
      distinct (Q.insert x q).

  Parameter insert_all_ordered :
    forall xs q,
      ordered q ->
      ordered (Q.insert_all xs q).

  Parameter insert_all_distinct :
    forall xs q,
      distinct q ->
      distinct (Q.insert_all xs q).

  Parameter pop_members :
    forall q head tail x,
      Q.pop_max q = Some (head, tail) ->
      (In x q <-> x = head \/ In x tail).

  Parameter pop_removes_head :
    forall q head tail,
      Q.pop_max q = Some (head, tail) ->
      ~ In head tail.

  Parameter peek_pop_agree :
    forall q,
      Q.peek_max q =
      match Q.pop_max q with
      | Some (head, _) => Some head
      | None => None
      end.

  Parameter peek_none_no_members :
    forall q,
      Q.peek_max q = None ->
      forall x, ~ In x q.

  Parameter pop_maximal :
    forall q head tail (x : V.t),
      Q.pop_max q = Some (head, tail) ->
      In x q ->
      O.lt head x = false.

  Parameter pop_ordered :
    forall q head tail,
      ordered q ->
      Q.pop_max q = Some (head, tail) ->
      ordered tail.

  Parameter pop_distinct :
    forall q head tail,
      distinct q ->
      Q.pop_max q = Some (head, tail) ->
      distinct tail.
End QUEUE_LAWS.
