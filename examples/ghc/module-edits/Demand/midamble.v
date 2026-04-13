(* DEMAND midamble file. Termination defs and tactics . *)

Require Import HsToRocq.Nat.
Require Import HsToRocq.Unpeel.
Require Import Lia.

Ltac solve_not_zero_N := match goal with
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] =>
    unfold GHC.Base.op_zeze__ in H;
    unfold GHC.Base.Eq_Char___ in H;
    simpl in H;
    apply N.eqb_neq in H end;
    zify;
    lia.
Ltac simpl_not_zero := match goal with
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] =>
  unfold GHC.Base.op_zeze__ in H;
    unfold Eq_nat in H;
    simpl in H;
  apply Nat.eqb_neq in H end.
Ltac solve_error_sub :=
  unfold error_sub;
  let Hltb := fresh in
  let HeqHltb := fresh in
  match goal with
    [ |- context[ Nat.ltb ?x (Pos.to_nat 1) ] ] =>
    remember (Nat.ltb x (Pos.to_nat 1)) as Hltb eqn:HeqHltb;
      destruct Hltb;
      symmetry in HeqHltb;
      try (rewrite Nat.ltb_lt in HeqHltb);
      try (rewrite Nat.ltb_ge in HeqHltb);
      try solve [zify; lia]
  end.

Ltac distinguish := split; intros; unfold not; intros [? ?]; discriminate.
Ltac solve_mkWorkerDemand := Tactics.program_simpl; simpl_not_zero; solve_error_sub.

Ltac solve_dmdTransform := Tactics.program_simpl; try solve_mkWorkerDemand; try distinguish.

(* GHC 9.10: StrictSig renamed to DmdSig *)
(* Unpeel_StrictSig removed — StrictSig no longer exists *)
(* Str_size/StrDmd_size/ArgStrDmd_size removed — Str/StrDmd types removed in GHC 9.10 *)
