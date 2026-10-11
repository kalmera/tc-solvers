From TcSolvers Require Import common.SolverContracts.
From TcSolvers Require solvers.slr.simple.SimpleInterface solvers.slr.restarting.RestartingInterface
  solvers.slr.narrowing_fixed_point.NarrowingFixedPointInterface
  solvers.slr.reluctant_restarting.ReluctantRestartingInterface
  solvers.slr.dormant_restarting.DormantRestartingInterface
  solvers.slr.dirty_read_restarting.DirtyReadRestartingInterface
  solvers.slr.deferred_simple.DeferredSimpleInterface
  solvers.slr.plus_restarting.PlusRestarting.

(* No solver proof file or update/collection laws are imported or supplied. *)
Module Client (V : VAR) (D : DOMAIN) (Solver : SOLVER V D).
  Module Spec := SolverContracts.ForSolver V D Solver.
  Module Predicates := SolverSpecifications.Make V D Solver.Sem Solver.View.
  Definition same_correctness :
    Spec.correct_final_state = Predicates.correct_final_state := eq_refl.
  Definition same_fixedness :
    Spec.narrowing_fixed_with = Predicates.narrowing_fixed_with := eq_refl.
  Module WithCertificates (Certificates : Spec.VERIFIED_LEAST).
    Module Total := Spec.Consequences Certificates.
    Include Spec.LeastConsequences Certificates.
    Definition soundness : Spec.Soundness := Total.successful_run_correct.
    Definition total : Spec.TotalCorrectness := Total.total_correct.
    Definition least : Spec.TotalLeastness := total_least_solution.
  End WithCertificates.
End Client.

Module Check (V : VAR) (D : DOMAIN) (U : UPDATE V D) (SU : SIDE_UPDATE V D)
  (S : SET V) (M : MAP V) (Ranks : DISCOVERY_ORDER V) (Features : RESTARTING_FEATURES).
  Module SimpleSolver := SimpleInterface.Make V D U S M Ranks.
  Module SimpleClient := Client V D SimpleSolver.
  Module RestartingSolver := RestartingInterface.Make V D U S M Ranks Features.
  Module RestartingClient := Client V D RestartingSolver.
  Module NarrowingSolver := NarrowingFixedPointInterface.Make V D U S M Features.
  Module NarrowingClient := Client V D NarrowingSolver.
  Module ReluctantSolver := ReluctantRestartingInterface.Make V D U SU S M Ranks Features.
  Module ReluctantClient := Client V D ReluctantSolver.
  Module DormantSolver := DormantRestartingInterface.Make V D U SU S M Ranks Features.
  Module DormantClient := Client V D DormantSolver.
  Module DirtyReadSolver := DirtyReadRestartingInterface.Make V D U SU S M Ranks Features.
  Module DirtyReadClient := Client V D DirtyReadSolver.
  Module DeferredSimpleSolver := DeferredSimpleInterface.Make V D U SU S M Ranks Features.
  Module DeferredSimpleClient := Client V D DeferredSimpleSolver.
  Module PlusRestartingSolver := PlusRestarting.Interface V D U SU S M Ranks Features.
  Module PlusRestartingClient := Client V D PlusRestartingSolver.
End Check.
