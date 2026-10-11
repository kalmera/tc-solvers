From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain common.ReluctantUpdate common.Assumptions common.SideUpdate
  solvers.slr.plus_restarting.Proofs.
Import ListNotations.

(** Post-solutions must cover spawned constraints even when all values are bottom. *)
Module E := Chain.
Module SU := ReluctantSideUpdate E.V E.D E.U.
Module Sound := OrdinaryUpdateSoundAdapter E.V E.D E.U E.UL.
Module SideSound := ReluctantSideUpdateSoundLaws E.V E.D E.U E.DL E.UL.
Module Core := Proofs.Make E.V E.D E.U SU E.S E.M PlusRestarting.AllEnabledFeatures
  E.DL Sound SideSound E.SL E.ML.
Module Sem := Core.Sem.
Module R := Sem.R.
Import R.ConstraintSystem.
Definition spawning owner := match owner with
| 0 => Spawn 1 (Ret E.D.Bot) | _ => Ret E.D.Bot end.
Definition bottom (_ : E.V.t) := E.D.Bot.
Definition spawned : Sem.observation :=
 {| Sem.Observation.observed_direct := E.D.Bot;
    Sem.Observation.observed_reads := [];
    Sem.Observation.observed_sides := [];
    Sem.Observation.observed_spawns := [1] |}.
Example missing_spawn_rejected : ~ Sem.post_solution_on spawning [0] bottom.
Proof.
 intro H. assert (Hobs : Sem.observes_at bottom (spawning 0) spawned).
 { split; [exact (Sem.ObserveSpawn 1 (Sem.ObserveRet E.D.Bot))|intros target value Hin; contradiction]. }
 destruct (H 0 (or_introl eq_refl) spawned Hobs) as [_ [_ Hspawn]].
 specialize (Hspawn 1 (or_introl eq_refl)). cbn in Hspawn. intuition discriminate.
Qed.

Example covered_spawn_accepted : Sem.post_solution_on spawning [0;1] bottom.
Proof.
 intros owner Hin result [Hobs Hreads].
 destruct Hin as [<-|[<-|[]]]; cbn [spawning] in Hobs.
 - inversion Hobs; subst. inversion H2; subst. cbn.
   split; [reflexivity|]. split; [intros t v Hin; contradiction|].
   intros target [<-|[]]. now right; left.
 - inversion Hobs; subst. cbn.
   split; [reflexivity|]. split; [intros target value Hin; contradiction|intros target Hin; contradiction].
Qed.
Example missing_spawn_not_least : ~ Sem.least_solution_on spawning [0] bottom.
Proof. intros [Hpost _]. exact (missing_spawn_rejected Hpost). Qed.

Definition branching owner := match owner with
 | 0 => Get 2 (fun value => Spawn
     (if E.D.leq value E.D.Bot then 1 else 3) (Ret E.D.Bot))
 | _ => Ret E.D.Bot end.
Definition raised owner := if Nat.eqb owner 2 then E.D.Top else E.D.Bot.
Definition raised_observation : Sem.observation :=
 {| Sem.Observation.observed_direct := E.D.Bot;
    Sem.Observation.observed_reads := [(2,E.D.Top)];
    Sem.Observation.observed_sides := [];
    Sem.Observation.observed_spawns := [3] |}.
Example final_valuation_spawn_must_be_covered :
 ~ Sem.post_solution_on branching [0;1;2] raised.
Proof.
 intro H. assert (Hobs : Sem.observes_at raised (branching 0) raised_observation).
 { split.
   - exact (Sem.ObserveGet 2 E.D.Top
       (fun value => Spawn (if E.D.leq value E.D.Bot then 1 else 3) (Ret E.D.Bot))
       (Sem.ObserveSpawn 3 (Sem.ObserveRet E.D.Bot))).
   - intros target value [Heq|[]]. inversion Heq; reflexivity. }
 destruct (H 0 (or_introl eq_refl) raised_observation Hobs) as [_ [_ Hspawn]].
 specialize (Hspawn 3 (or_introl eq_refl)). cbn in Hspawn. intuition discriminate.
Qed.

Definition incomplete := R.materialize R.empty_state 0.
Example owner_post_solution_rejects_missing_spawn :
 ~ Core.owner_post_solution spawning incomplete 0.
Proof.
 intros [_ [_ Hspawns]].
 assert (Hobs : Sem.observes_at (R.sigma_value incomplete) (spawning 0) spawned).
 { split; [exact (Sem.ObserveSpawn 1 (Sem.ObserveRet E.D.Bot))|].
   intros target value Hin; contradiction. }
 destruct (Hspawns spawned Hobs 1 (or_introl eq_refl)) as [value Hlookup].
 vm_compute in Hlookup. discriminate.
Qed.
Example dormant_spawn_is_covered :
 match R.solve_fuel 100 spawning [0] with
 | Some final => R.semantic_lookup final 1 = Some E.D.Bot /\
     E.M.lookup (R.sigma final) 1 = None
 | None => False end.
Proof. vm_compute. split; reflexivity. Qed.
Example absent_read_prevents_vacuous_post_solution :
 ~ Core.owner_post_solution (fun _ => Get 1 (fun value => Ret value)) R.empty_state 0.
Proof.
 intros [[direct [reads [effects Heval]]] _].
 inversion Heval; subst.
 match goal with H : R.semantic_lookup R.empty_state _ = Some _ |- _ =>
   vm_compute in H; discriminate end.
Qed.
