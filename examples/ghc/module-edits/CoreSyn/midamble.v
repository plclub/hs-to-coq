(* ------------- CoreSyn midamble.v ------------ *)
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;lia.

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
             lia].

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
                                         | Mk_AnnAlt _ _ (_,e) => size_AnnExpr' e
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

#[global] Instance Default__Expr {b} : HsToCoq.Err.Default (Expr b) :=
  HsToCoq.Err.Build_Default _ (Mk_Var HsToCoq.Err.default).

(* Default__Tickish removed: Tickish is now GHC.Types.Tickish.CoreTickish (axiomatized) *)

#[global] Instance Default_TaggedBndr {t}`{HsToCoq.Err.Default t} : HsToCoq.Err.Default (TaggedBndr t) :=
  HsToCoq.Err.Build_Default _ (TB HsToCoq.Err.default HsToCoq.Err.default).

#[global] Instance Default__AnnExpr' {a}{b} : HsToCoq.Err.Default (AnnExpr' a b) :=
  HsToCoq.Err.Build_Default _ (AnnVar HsToCoq.Err.default). 

#[global] Instance Default__AnnBind {a}{b} : HsToCoq.Err.Default (AnnBind a b) :=
  HsToCoq.Err.Build_Default _ (AnnRec HsToCoq.Err.default). 

#[global] Instance Default__Bind {b} : HsToCoq.Err.Default (Bind b) :=
  HsToCoq.Err.Build_Default _ (Rec HsToCoq.Err.default). 

(* Default__CoreVect removed: CoreVect doesn't exist in GHC 9.10 *)

(* Default__CoreRule and Default__RuleEnv injected by sed before record accessors *)


(* ---------------------------------- *)

(* collectBinders and collectNBinders — no longer auto-generated in GHC 9.10 *)

Definition collectBinders {b : Type} : Expr b -> (list b * Expr b)%type :=
  let fix go (bs : list b) (e : Expr b) : (list b * Expr b) :=
    match e with
    | Lam b body => go (cons b bs) body
    | _ => pair (GHC.List.reverse bs) e
    end in
  fun e => go nil e.

Definition collectNBinders {b : Type}
  : nat -> Expr b -> (list b * Expr b)%type :=
  fun orig_n orig_expr =>
    let fix go (n : nat) (bs : list b) (expr : Expr b) : (list b * Expr b) :=
      match n, bs, expr with
      | O, _, _ => pair (GHC.List.reverse bs) expr
      | S m, _, Lam b body => go m (cons b bs) body
      | _, _, _ => Panic.panicStr (GHC.Base.hs_string__ "collectNBinders") Panic.someSDoc
      end in
    go orig_n nil orig_expr.

Definition collectArgs {b : Type} : Expr b -> (Expr b * list (Expr b))%type :=
  let fix go (e : Expr b) (args : list (Expr b)) : (Expr b * list (Expr b)) :=
    match e with
    | App f a => go f (cons a args)
    | _ => pair e args
    end in
  fun e => go e nil.

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
