Require CoreStats.

Instance Default_Step {a} : HsToRocq.Err.Default (Step a) :=
  HsToRocq.Err.Build_Default _ Done.
Instance Default_Value : HsToRocq.Err.Default Value :=
  HsToRocq.Err.Build_Default _ (LitVal HsToRocq.Err.default).
Instance Default_StackElem : HsToRocq.Err.Default StackElem :=
  HsToRocq.Err.Build_Default _ (Update HsToRocq.Err.default).

(* ----------- termination metric for step function --------------- *)

Require Import Lia.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;lia.

Ltac solve_step_obligations :=
  repeat split; intros; try discriminate; termination_by_omega.

Definition step_measure (conf : Conf) : nat := 
  match conf with 
  | (heap , expr, stack ) => CoreStats.exprSize expr 
  end.

(* ----------- ----------------------------------- --------------- *)

(*
solve_step_obligations solves most. But for the remainder we need the following 
proof script. I'm not sure how to turn this into a tactic.

Next Obligation.
  match goal with [wc : Core.Tickish _ |- _ ] => destruct wc; auto end.
Defined.
Next Obligation.
  match goal with [a : Core.Expr _ , h : Core.isTypeArg a = true |- _ ] => 
                 destruct a; simpl in h; try discriminate end;
  simpl; replace (BinPos.Pos.to_nat 1) with 1; try lia; reflexivity.
Defined.
Next Obligation.
  repeat split; intros; intro h0; inversion h0.
Defined.
Next Obligation.
  repeat split; intros; intro h0; inversion h0.
Defined.  
Next Obligation.
  repeat split; intros; intro h0; inversion h0.
Defined.  
Next Obligation.
  repeat split; intros; intro h0; inversion h0.
Defined.  
Next Obligation.
  repeat split; intros; intro h0; inversion h0.
Defined.  
Next Obligation.
  repeat split; intros; intro h0; inversion h0.
Defined.  
Next Obligation.
  repeat split; intros; intro h0; inversion h0.
Defined.  
*)
