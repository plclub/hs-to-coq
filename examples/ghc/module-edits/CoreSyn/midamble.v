(* ------------- CoreSyn midamble.v ------------ *)
Require Import Coq.ZArith.ZArith.
Require Import Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Ltac intro_split := 
  try intros [? [? [? ?]]];
  try intros [? [? ?]];
  try intros [? ?].
  
Ltac distinguish3 := 
  split; intros; unfold not;  intro_split; discriminate.

Ltac solve_collectAnnArgsTicks :=   
  Tactics.program_simpl;
  try solve [distinguish3];
  try solve [repeat match goal with [ f : AnnExpr _ _ |- _ ] => destruct f end;
             Tactics.program_simpl;
             omega].

(* This function is needed to show the termination of collectAnnArgs, 
   collectAnnArgsTicks. *)
Fixpoint size_AnnExpr' {a}{b} (e: AnnExpr' a b) :=
  match e with 
  | AnnVar _ => 0
  | AnnLit _ => 0
  | AnnLam _ (_ , bdy) => S (size_AnnExpr' bdy)
  | AnnApp (_,e1) (_, e2) => S (size_AnnExpr' e1 + size_AnnExpr' e2)
  | AnnCase (_,scrut) bndr _ alts => 
    S (size_AnnExpr' scrut + 
       List.fold_right plus 0 
                          (List.map (fun p =>
                                       match p with 
                                         | (_,_,(_,e)) => size_AnnExpr' e
                                    end) 
                                    alts))
  | AnnLet (AnnNonRec v (_,rhs)) (_,body) => 
        S (size_AnnExpr' rhs + size_AnnExpr' body)
  | AnnLet (AnnRec pairs) (_,body) => 
        S (Lists.List.fold_right plus 0 
          (Lists.List.map (fun p => size_AnnExpr' (snd (snd p))) pairs) +
           size_AnnExpr' body)

  | AnnCast (_,e) _ => S (size_AnnExpr' e)
(*  | AnnTick _ (_,e) => S (size_AnnExpr' e) *)
  | AnnType _ => 0
  | AnnCoercion _ => 0 
  end.

(* ---------------------------------- *)

Instance Default__Expr {b} : HsToCoq.Err.Default (Expr b) :=
  HsToCoq.Err.Build_Default _ (Mk_Var HsToCoq.Err.default).

Instance Default__Tickish {a} : HsToCoq.Err.Default (Tickish a) :=
  HsToCoq.Err.Build_Default _ (Breakpoint HsToCoq.Err.default HsToCoq.Err.default).

Instance Default_TaggedBndr {t}`{HsToCoq.Err.Default t} : HsToCoq.Err.Default (TaggedBndr t) :=
  HsToCoq.Err.Build_Default _ (TB HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__AnnExpr' {a}{b} : HsToCoq.Err.Default (AnnExpr' a b) :=
  HsToCoq.Err.Build_Default _ (AnnVar HsToCoq.Err.default). 

Instance Default__AnnBind {a}{b} : HsToCoq.Err.Default (AnnBind a b) :=
  HsToCoq.Err.Build_Default _ (AnnRec HsToCoq.Err.default). 

Instance Default__Bind {b} : HsToCoq.Err.Default (Bind b) :=
  HsToCoq.Err.Build_Default _ (Rec HsToCoq.Err.default). 

Instance Default__CoreVect : HsToCoq.Err.Default CoreVect :=
  HsToCoq.Err.Build_Default _ (Vect HsToCoq.Err.default HsToCoq.Err.default). 

Instance Default__CoreRule : HsToCoq.Err.Default CoreRule :=
  HsToCoq.Err.Build_Default _ (BuiltinRule HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__RuleEnv : HsToCoq.Err.Default RuleEnv :=
  HsToCoq.Err.Build_Default _ (Mk_RuleEnv HsToCoq.Err.default HsToCoq.Err.default).


(* ---------------------------------- *)

(* See comments in CoreSyn/edits file. We can't use termination edits for collect. *)

Definition collectNAnnBndrs {bndr} {annot}`{HsToCoq.Err.Default annot}
    : nat -> AnnExpr bndr annot -> (list bndr * AnnExpr bndr annot)%type :=
          fun orig_n e =>
            let fix collect (arg_0__:nat) (arg_1__ : list bndr) (arg_2__:AnnExpr bndr annot) :=
                               match arg_0__, arg_1__, arg_2__ with
                               | O, bs, body =>
                                 pair (GHC.List.reverse bs) body 
                               | S m, bs, body =>
                                   match arg_0__, arg_1__, arg_2__ with
                                   | n, bs, pair _ (AnnLam b body) => collect m (cons b bs) body
                                   | _, _, _ =>
                                       Panic.panicStr (GHC.Base.hs_string__ "collectNBinders") Panic.someSDoc
                                   end
                               end in
            collect orig_n nil e.
