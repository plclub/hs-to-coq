Require CoreStats.

Instance Default_Step {a} : HsToCoq.Err.Default (Step a) :=
  HsToCoq.Err.Build_Default _ Done.
Instance Default_Value : HsToCoq.Err.Default Value :=
  HsToCoq.Err.Build_Default _ (LitVal HsToCoq.Err.default).
Instance Default_StackElem : HsToCoq.Err.Default StackElem :=
  HsToCoq.Err.Build_Default _ (Update HsToCoq.Err.default).

(* ----------- termination metric for step function --------------- *)

Require Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

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
  simpl; replace (BinPos.Pos.to_nat 1) with 1; try Omega.omega; reflexivity.
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
