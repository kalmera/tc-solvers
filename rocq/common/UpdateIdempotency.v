From TcSolvers Require Import common.Interfaces.

(** Proof-only law. Phases may change on replay; only the value is stable.
    Side updates are deliberately unrestricted. *)
Module Type VALUE_IDEMPOTENT (V : VAR) (D : DOMAIN) (U : UPDATE V D).
  Parameter ordinary_value_idempotent : forall owner phase old input,
    let result := U.update false owner phase old input in
    D.leq (snd (U.update false owner (fst result) (snd result) input))
      (snd result) = true /\
    D.leq (snd result)
      (snd (U.update false owner (fst result) (snd result) input)) = true.
End VALUE_IDEMPOTENT.
