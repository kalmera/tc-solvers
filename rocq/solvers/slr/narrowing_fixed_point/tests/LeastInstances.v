From Stdlib Require Import List.
From TcSolvers Require Import common.FiniteHeight common.instances.Chain
  solvers.slr.narrowing_fixed_point.Theorems.
Import ListNotations.

(** Concrete finite-height client; the three queued side targets exercise the
    batched drain while all unrequested owners remain source-strict. *)
Module BatchedJoinLeast.
 Module E := Chain.
 Module U := JoinUpdate E.V E.D.
 Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
 Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
 Module Solver := Theorems.LeastSolutionMake E.V E.D U E.S E.M
  Base.AllEnabledFeatures E.DL UL UBL E.SL E.ML.
 Import Solver.
 Definition tf owner := if E.V.eq_dec owner 0 then
  R.ConstraintSystem.Side 1 E.D.One
   (R.ConstraintSystem.Side 2 E.D.Two
    (R.ConstraintSystem.Side 3 E.D.Three (R.ConstraintSystem.Ret E.D.One)))
  else R.ConstraintSystem.Ret E.D.Bot.
 Definition finite : Sem.finite_system tf [0].
 Proof.
  refine (@Sem.Build_finite_system tf [0] [0;1;2;3] _ _ _).
  - repeat constructor;cbn;intuition discriminate.
  - intros owner [->|H];[now left |contradiction].
  - intros owner Hin. unfold tf. destruct (E.V.eq_dec owner 0).
    + constructor;[right;now left |].
      constructor;[right;right;now left |].
      constructor;[right;right;right;now left |constructor].
    + constructor.
 Defined.
 Lemma observations owner lower upper :
  Sem.rhs_observes (tf owner) lower -> Sem.rhs_observes (tf owner) upper ->
  lower=upper.
 Proof.
  unfold tf. destruct (E.V.eq_dec owner 0);intros Hl Hu;
  repeat match goal with H : Sem.rhs_observes _ _ |- _ => inversion H;subst;clear H end;
  reflexivity.
 Qed.
 Lemma monotone : Sem.system_monotone_on tf [0;1;2;3].
 Proof.
  constructor;intros owner Hin lower upper Hl Hu Hreads;
  pose proof (@observations owner lower upper Hl Hu) as Heq;subst upper.
  - intros x Hx;exact Hx.
  - constructor;cbn.
    + apply E.DL.leq_refl.
    + intros target value Hin'. exists value. split;[exact Hin' |apply E.DL.leq_refl].
    + intros x Hx;exact Hx.
 Qed.
 Lemma strict : Solver.source_strict_on tf [0;1;2;3] [0].
 Proof.
  intros owner Hin Hnonroot values result Hobs Hbottom.
  unfold tf in Hobs. destruct (E.V.eq_dec owner 0) as [->|Hne];
  [exfalso;apply Hnonroot;now left |].
  destruct Hobs as [Hobs Hreads]. inversion Hobs;subst. cbn.
  split;[reflexivity |intros target value H;contradiction].
 Qed.
 Definition total_least_solution := @Solver.total_least_solution.
 Definition least_result := @Solver.total_least_solution tf [0] finite strict monotone.
End BatchedJoinLeast.

(* Print Assumptions BatchedJoinLeast.least_result. *)
