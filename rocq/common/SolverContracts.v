From Stdlib Require Import List.
From TcSolvers Require Export common.SolverInterfaces common.SolverParameters.

Set Implicit Arguments.

(** Hybrid theorem contracts: modules supply the semantic and execution
    interfaces; records in [Prop] supply independent theorem capabilities.
    Common parameter signatures are exported alongside these contracts;
    no specific solver or collection implementation is imported here.
    Generic consequences use only the supplied proof certificates. *)

(** Preserve the original qualified signature names for existing clients. *)
Module Type SEMANTICS := SolverInterfaces.SEMANTICS.
Module Type SOLVER_VIEW := SolverInterfaces.SOLVER_VIEW.
Module Type EXECUTION := SolverInterfaces.EXECUTION.

(** Define the record types once, outside the specifications functor. Their
    parameters are the named propositions below. Reinstantiating the functor
    therefore preserves certificate types for separately compiled clients. *)
Record Correctness (soundness_statement : Prop) : Prop := {
  successful_run_correct : soundness_statement
}.
Record Termination (termination_statement fuel_statement : Prop) : Prop := {
  semantic_termination : termination_statement;
  sufficient_fuel : fuel_statement
}.
Record Leastness (leastness_statement : Prop) : Prop := {
  successful_run_least : leastness_statement
}.
Record Fixedness (fixedness_statement : Prop) : Prop := {
  successful_run_fixed : fixedness_statement
}.
Record FallbackAvoidance (fallback_statement : Prop) : Prop := {
  avoids_fallback : fallback_statement
}.

Module Make (V : VAR) (D : DOMAIN) (Sem : SEMANTICS V D)
  (R : SOLVER_VIEW V D Sem) (E : EXECUTION V D Sem R).
  Include SolverSpecifications.Make V D Sem R.
  Definition terminates_to (tf : system) roots final :=
    E.steps tf (E.initial_config roots) (E.terminal_config final) /\ E.quiescent final.

  Definition Soundness : Prop := forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final -> correct_final_state tf roots final.
  Definition SemanticTermination : Prop := forall tf roots,
    Sem.finite_system tf roots -> exists final, terminates_to tf roots final.
  Definition SufficientFuel : Prop := forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final.
  Definition TotalCorrectness : Prop := forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      correct_final_state tf roots final.

  Definition Correctness := Correctness Soundness.
  Definition Termination := Termination SemanticTermination SufficientFuel.
  Definition successful_run_correct := @successful_run_correct Soundness.
  Definition semantic_termination := @semantic_termination SemanticTermination SufficientFuel.
  Definition sufficient_fuel := @sufficient_fuel SemanticTermination SufficientFuel.

  Definition source_strict_on (tf : system) support roots :=
    forall owner, In owner support -> ~ In owner roots ->
    forall values result, Sem.observes_at values (tf owner) result ->
      D.leq (values owner) D.bottom = true ->
      D.leq (Sem.observed_direct result) D.bottom = true /\
      (forall target value, In (target, value) (Sem.observed_sides result) ->
        D.leq value D.bottom = true).
  Definition SuccessfulRunLeastness : Prop :=
    forall fuel tf roots (finite : Sem.finite_system tf roots) final,
      source_strict_on tf (Sem.support finite) roots ->
      Sem.system_monotone_on tf (Sem.support finite) ->
      R.solve_fuel fuel tf roots = Some final ->
      Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
  Definition TotalLeastness : Prop := forall tf roots (finite : Sem.finite_system tf roots),
    source_strict_on tf (Sem.support finite) roots ->
    Sem.system_monotone_on tf (Sem.support finite) ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
  Definition Leastness := Leastness SuccessfulRunLeastness.
  Definition successful_run_least := @successful_run_least SuccessfulRunLeastness.

  (** Precision contracts take an explicit precondition and fixedness input.
      This retains finite/unbounded and direct/side-aggregate variants without
      importing solver-specific feature flags into the common interface. *)
  Definition SuccessfulRunFixedness (pre : system -> list V.t -> Prop)
    narrow input : Prop := forall fuel tf roots final,
    pre tf roots -> R.solve_fuel fuel tf roots = Some final ->
    narrowing_fixed_with narrow input tf final.
  Definition Fixedness pre narrow input := Fixedness (SuccessfulRunFixedness pre narrow input).
  Definition successful_run_fixed pre narrow input :=
    @successful_run_fixed (SuccessfulRunFixedness pre narrow input).
  Definition FallbackFree (pre : system -> list V.t -> Prop)
    (safe : E.config -> Prop) : Prop := forall tf roots,
    pre tf roots -> forall c, E.steps tf (E.initial_config roots) c -> safe c.
  Definition FallbackAvoidance pre safe := FallbackAvoidance (FallbackFree pre safe).
  Definition avoids_fallback pre safe := @avoids_fallback (FallbackFree pre safe).

  Module Type SOUND.
    Parameter correctness : Correctness.
  End SOUND.

  Module Type VERIFIED.
    Include SOUND.
    Parameter termination : Termination.
  End VERIFIED.

  Module Type VERIFIED_LEAST.
    Include VERIFIED.
    Parameter leastness : Leastness.
  End VERIFIED_LEAST.

  (** Consequences shared by every solver with the required certificates. *)
  Theorem total_correct_from : Correctness -> Termination -> TotalCorrectness.
  Proof.
    intros Hcorrect Htermination tf roots finite.
    destruct (@sufficient_fuel Htermination tf roots finite) as [fuel [final Hrun]].
    exists fuel, final. split; [exact Hrun |].
    exact (@successful_run_correct Hcorrect fuel tf roots final Hrun).
  Qed.
  Theorem total_least_from : Termination -> Leastness -> TotalLeastness.
  Proof.
    intros Htermination Hleast tf roots finite Hstrict Hmono.
    destruct (@sufficient_fuel Htermination tf roots finite) as [fuel [final Hrun]].
    exists fuel, final. split; [exact Hrun |].
    exact (@successful_run_least Hleast fuel tf roots finite final Hstrict Hmono Hrun).
  Qed.
  Theorem owner_post_solution_from : Correctness ->
    forall fuel tf roots final owner,
      R.solve_fuel fuel tf roots = Some final -> solved final owner ->
      owner_post_solution tf final owner.
  Proof.
    intros Hcorrect fuel tf roots final owner Hrun Howner.
    exact (proj2 (@successful_run_correct Hcorrect fuel tf roots final Hrun) owner Howner).
  Qed.

  (* Keep export functors flat: nesting an Include here triggers a Rocq 9.1
     module-substitution assertion when certificates come from another module. *)
  Module SoundConsequences (Certificates : SOUND).
    Definition successful_run_correct := successful_run_correct Certificates.correctness.
    Definition successful_run_owner_post_solution :=
      owner_post_solution_from Certificates.correctness.
  End SoundConsequences.

  Module Consequences (Certificates : VERIFIED).
    Definition successful_run_correct := successful_run_correct Certificates.correctness.
    Definition successful_run_owner_post_solution :=
      owner_post_solution_from Certificates.correctness.
    Definition semantic_termination := semantic_termination Certificates.termination.
    Definition sufficient_fuel := sufficient_fuel Certificates.termination.
    Definition total_correct :=
      total_correct_from Certificates.correctness Certificates.termination.
  End Consequences.

  Module LeastConsequences (Certificates : VERIFIED_LEAST).
    Definition successful_run_least := successful_run_least Certificates.leastness.
    Definition total_least_solution :=
      total_least_from Certificates.termination Certificates.leastness.
  End LeastConsequences.
End Make.

(** Specifications consume a solver's exported views directly. *)
Module ForSolver (V : VAR) (D : DOMAIN) (Solver : SOLVER V D).
  Include Make V D Solver.Sem Solver.View Solver.Execution.
End ForSolver.
