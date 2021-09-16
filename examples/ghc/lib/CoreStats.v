(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Import Core.
Require Import Data.Foldable.
Require Import GHC.Base.
Require Import GHC.Num.
Require HsToCoq.Err.
Require Id.

(* Converted type declarations: *)

Inductive CoreStats : Type :=
  | CS (cs_tm : nat) (cs_ty : nat) (cs_co : nat) (cs_vb : nat) (cs_jb : nat)
   : CoreStats.

Instance Default__CoreStats : HsToCoq.Err.Default CoreStats :=
  HsToCoq.Err.Build_Default _ (CS HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Definition cs_co (arg_0__ : CoreStats) :=
  let 'CS _ _ cs_co _ _ := arg_0__ in
  cs_co.

Definition cs_jb (arg_0__ : CoreStats) :=
  let 'CS _ _ _ _ cs_jb := arg_0__ in
  cs_jb.

Definition cs_tm (arg_0__ : CoreStats) :=
  let 'CS cs_tm _ _ _ _ := arg_0__ in
  cs_tm.

Definition cs_ty (arg_0__ : CoreStats) :=
  let 'CS _ cs_ty _ _ _ := arg_0__ in
  cs_ty.

Definition cs_vb (arg_0__ : CoreStats) :=
  let 'CS _ _ _ cs_vb _ := arg_0__ in
  cs_vb.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreStats.Outputable__CoreStats' *)

Definition plusCS : CoreStats -> CoreStats -> CoreStats :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CS p1 q1 r1 v1 j1, CS p2 q2 r2 v2 j2 =>
        CS (p1 + p2) (q1 + q2) (r1 + r2) (v1 + v2) (j1 + j2)
    end.

Definition zeroCS : CoreStats :=
  CS 0 0 0 0 0.

Definition oneTM : CoreStats :=
  let 'CS cs_tm_0__ cs_ty_1__ cs_co_2__ cs_vb_3__ cs_jb_4__ := zeroCS in
  CS 1 cs_ty_1__ cs_co_2__ cs_vb_3__ cs_jb_4__.

Definition sumCS {a} : (a -> CoreStats) -> list a -> CoreStats :=
  fun f => foldl' (fun s a => plusCS s (f a)) zeroCS.

Axiom tyStats : AxiomatizedTypes.Type_ -> CoreStats.

Definition altBndrStats : list Var -> CoreStats :=
  fun vs => plusCS oneTM (sumCS (tyStats ∘ varType) vs).

Definition bndrStats : Var -> CoreStats :=
  fun v => plusCS oneTM (tyStats (varType v)).

Axiom coStats : AxiomatizedTypes.Coercion -> CoreStats.

Definition letBndrStats : BasicTypes.TopLevelFlag -> Var -> CoreStats :=
  fun top_lvl v =>
    let ty_stats := tyStats (varType v) in
    if orb (isTyVar v) (BasicTypes.isTopLevel top_lvl) : bool then bndrStats v else
    if Id.isJoinId v : bool
    then plusCS (let 'CS cs_tm_1__ cs_ty_2__ cs_co_3__ cs_vb_4__ cs_jb_5__ :=
                   oneTM in
                 CS cs_tm_1__ cs_ty_2__ cs_co_3__ cs_vb_4__ 1) ty_stats else
    plusCS (let 'CS cs_tm_8__ cs_ty_9__ cs_co_10__ cs_vb_11__ cs_jb_12__ := oneTM in
            CS cs_tm_8__ cs_ty_9__ cs_co_10__ 1 cs_jb_12__) ty_stats.

Definition bindStats : BasicTypes.TopLevelFlag -> CoreBind -> CoreStats :=
  fix exprStats (arg_0__ : CoreExpr) : CoreStats
    := let altStats (arg_0__ : CoreAlt) : CoreStats :=
         let 'pair (pair _ bs) r := arg_0__ in
         plusCS (altBndrStats bs) (exprStats r) in
       match arg_0__ with
       | Mk_Var _ => oneTM
       | Lit _ => oneTM
       | Mk_Type t => tyStats t
       | Mk_Coercion c => coStats c
       | App f a => plusCS (exprStats f) (exprStats a)
       | Lam b e => plusCS (bndrStats b) (exprStats e)
       | Let b e => plusCS (bindStats BasicTypes.NotTopLevel b) (exprStats e)
       | Case e b _ as_ =>
           plusCS (plusCS (exprStats e) (bndrStats b)) (sumCS altStats as_)
       | Cast e co => plusCS (coStats co) (exprStats e)
       end
  with bindStats (arg_0__ : BasicTypes.TopLevelFlag) (arg_1__ : CoreBind)
    : CoreStats
    := let bindingStats (top_lvl : BasicTypes.TopLevelFlag) (v : Var) (r : CoreExpr)
        : CoreStats :=
         plusCS (letBndrStats top_lvl v) (exprStats r) in
       match arg_0__, arg_1__ with
       | top_lvl, NonRec v r => bindingStats top_lvl v r
       | top_lvl, Rec prs => sumCS (fun '(pair v r) => bindingStats top_lvl v r) prs
       end for bindStats.

Definition coreBindsStats : list CoreBind -> CoreStats :=
  sumCS (bindStats BasicTypes.TopLevel).

Definition exprStats : CoreExpr -> CoreStats :=
  fix exprStats (arg_0__ : CoreExpr) : CoreStats
    := let altStats (arg_0__ : CoreAlt) : CoreStats :=
         let 'pair (pair _ bs) r := arg_0__ in
         plusCS (altBndrStats bs) (exprStats r) in
       match arg_0__ with
       | Mk_Var _ => oneTM
       | Lit _ => oneTM
       | Mk_Type t => tyStats t
       | Mk_Coercion c => coStats c
       | App f a => plusCS (exprStats f) (exprStats a)
       | Lam b e => plusCS (bndrStats b) (exprStats e)
       | Let b e => plusCS (bindStats BasicTypes.NotTopLevel b) (exprStats e)
       | Case e b _ as_ =>
           plusCS (plusCS (exprStats e) (bndrStats b)) (sumCS altStats as_)
       | Cast e co => plusCS (coStats co) (exprStats e)
       end
  with bindStats (arg_0__ : BasicTypes.TopLevelFlag) (arg_1__ : CoreBind)
    : CoreStats
    := let bindingStats (top_lvl : BasicTypes.TopLevelFlag) (v : Var) (r : CoreExpr)
        : CoreStats :=
         plusCS (letBndrStats top_lvl v) (exprStats r) in
       match arg_0__, arg_1__ with
       | top_lvl, NonRec v r => bindingStats top_lvl v r
       | top_lvl, Rec prs => sumCS (fun '(pair v r) => bindingStats top_lvl v r) prs
       end for exprStats.

Definition bindingStats
   : BasicTypes.TopLevelFlag -> Var -> CoreExpr -> CoreStats :=
  fun top_lvl v r => plusCS (letBndrStats top_lvl v) (exprStats r).

Definition altStats : CoreAlt -> CoreStats :=
  fun '(pair (pair _ bs) r) => plusCS (altBndrStats bs) (exprStats r).

Definition bndrSize : Var -> nat :=
  fun arg_0__ => 1.

Definition bndrsSize : list Var -> nat :=
  sum ∘ map bndrSize.

Definition bindSize : CoreBind -> nat :=
  fix exprSize (arg_0__ : CoreExpr) : nat
    := let altSize (arg_0__ : CoreAlt) : nat :=
         let 'pair (pair _ bs) e := arg_0__ in
         bndrsSize bs + exprSize e in
       match arg_0__ with
       | Mk_Var _ => 1
       | Lit _ => 1
       | App f a => exprSize f + exprSize a
       | Lam b e => bndrSize b + exprSize e
       | Let b e => bindSize b + exprSize e
       | Case e b _ as_ => exprSize e + bndrSize b + 1 + sum (map altSize as_)
       | Cast e _ => 1 + exprSize e
       | Mk_Type _ => 1
       | Mk_Coercion _ => 1
       end
  with bindSize (arg_0__ : CoreBind) : nat
    := let pairSize (arg_0__ : (Var * CoreExpr)%type) : nat :=
         let 'pair b e := arg_0__ in
         bndrSize b + exprSize e in
       match arg_0__ with
       | NonRec b e => bndrSize b + exprSize e
       | Rec prs => sum (map pairSize prs)
       end for bindSize.

Definition coreBindsSize : list CoreBind -> nat :=
  fun bs => sum (map bindSize bs).

Definition exprSize : CoreExpr -> nat :=
  fix exprSize (arg_0__ : CoreExpr) : nat
    := let altSize (arg_0__ : CoreAlt) : nat :=
         let 'pair (pair _ bs) e := arg_0__ in
         bndrsSize bs + exprSize e in
       match arg_0__ with
       | Mk_Var _ => 1
       | Lit _ => 1
       | App f a => exprSize f + exprSize a
       | Lam b e => bndrSize b + exprSize e
       | Let b e => bindSize b + exprSize e
       | Case e b _ as_ => exprSize e + bndrSize b + 1 + sum (map altSize as_)
       | Cast e _ => 1 + exprSize e
       | Mk_Type _ => 1
       | Mk_Coercion _ => 1
       end
  with bindSize (arg_0__ : CoreBind) : nat
    := let pairSize (arg_0__ : (Var * CoreExpr)%type) : nat :=
         let 'pair b e := arg_0__ in
         bndrSize b + exprSize e in
       match arg_0__ with
       | NonRec b e => bndrSize b + exprSize e
       | Rec prs => sum (map pairSize prs)
       end for exprSize.

Definition tickSize : Tickish Id -> nat :=
  fun arg_0__ => match arg_0__ with | ProfNote _ _ _ => 1 | _ => 1 end.

Definition pairSize : (Var * CoreExpr)%type -> nat :=
  fun '(pair b e) => bndrSize b + exprSize e.

Definition altSize : CoreAlt -> nat :=
  fun '(pair (pair _ bs) e) => bndrsSize bs + exprSize e.

(* External variables:
     App Case Cast CoreAlt CoreBind CoreExpr Id Lam Let Lit Mk_Coercion Mk_Type
     Mk_Var NonRec ProfNote Rec Tickish Var bool foldl' isTyVar list map nat
     op_z2218U__ op_zp__ op_zt__ orb pair sum varType AxiomatizedTypes.Coercion
     AxiomatizedTypes.Type_ BasicTypes.NotTopLevel BasicTypes.TopLevel
     BasicTypes.TopLevelFlag BasicTypes.isTopLevel HsToCoq.Err.Build_Default
     HsToCoq.Err.Default HsToCoq.Err.default Id.isJoinId
*)
