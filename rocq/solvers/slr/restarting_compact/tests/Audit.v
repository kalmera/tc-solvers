From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain common.FiniteHeight
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.restarting_compact.Proofs.

(** Instantiate the proof functor once. Concrete audits do not live in the
    generic proof unit, so clients do not pay for these instantiations. *)
Import ListNotations.
Module E := Chain.
Module Ranks := ListDiscoveryOrder E.V.
Module RL := ListDiscoveryOrderLaws E.V.
Module RF := ListFiniteDiscoveryOrderLaws E.V.
Module U := JoinUpdate E.V E.D.
Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
Module P := Proofs.Make E.V E.D U E.S E.M Ranks Restarting.AllEnabledFeatures
  RL RF E.DL UL E.SL E.ML.

Definition successful_run_below := P.successful_run_below UBL.update_preserves_upper_bound.

Print Assumptions P.ordinary_aggregate.
Print Assumptions P.termination_iff_fuel.
Print Assumptions P.quiet_commit_narrowing_fixed.

Definition successful_run_least fuel tf roots (finite : P.Sem.finite_system tf roots) final :=
  @P.successful_run_least fuel tf roots finite final UBL.update_preserves_upper_bound.
Print Assumptions P.reachable_rank_bound.
Print Assumptions P.successful_run_correct.
Print Assumptions successful_run_least.

(** A back read controls owner 0. Its two effects on owner 2 accumulate,
    and the spawned owner 3 must be included in the final post-solution. *)
Definition effects_and_spawn owner : P.Syntax.rhs :=
  match owner with
  | 0 => P.Syntax.Get 1 (fun value =>
      P.Syntax.Side 2 E.D.One (P.Syntax.Side 2 E.D.Two
        (P.Syntax.Spawn 3 (P.Syntax.Ret value))))
  | 1 => P.Syntax.Get 0 (fun _ => P.Syntax.Ret E.D.Three)
  | 2 => P.Syntax.Ret E.D.Bot
  | _ => P.Syntax.Get 2 (fun value => P.Syntax.Ret value)
  end.
Definition example_final := P.R.cfg_state
  (P.R.run_fuel 128 effects_and_spawn (P.R.initial_config [0])).
Example effects_and_spawn_terminates : P.R.solve_fuel 128 effects_and_spawn [0] = Some example_final.
Proof. vm_compute; reflexivity. Qed.
Example effects_and_spawn_values :
  P.R.sigma_value example_final 0 = E.D.Three /\
  P.R.sigma_value example_final 2 = E.D.Two /\
  P.R.sigma_value example_final 3 = E.D.Two /\
  P.R.stored_contribution example_final 0 2 = E.D.Two.
Proof. vm_compute; repeat split; reflexivity. Qed.
Example effects_and_spawn_correct : P.correct_final_state effects_and_spawn [0] example_final.
Proof. exact (@P.successful_run_correct 128 effects_and_spawn [0] example_final effects_and_spawn_terminates). Qed.
