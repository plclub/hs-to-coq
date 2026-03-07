(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require Coq.Lists.List.
Require Core.
Require CoreArity.
Require CoreFVs.
Require CoreUtils.
Require Data.Foldable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require MkCore.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

#[global] Definition FreeVarSet :=
  Core.DVarSet%type.

#[global] Definition BoundVarSet :=
  Core.DIdSet%type.

Inductive FloatInBind : Type :=
  | FB : BoundVarSet -> FreeVarSet -> MkCore.FloatBind -> FloatInBind.

#[global] Definition FloatInBinds :=
  (list FloatInBind)%type.

#[global] Definition DropBox :=
  (FreeVarSet * FloatInBinds)%type%type.

#[global] Definition RevFloatInBinds :=
  (list FloatInBind)%type.

(* Midamble *)

Instance Default_FloatBind : HsToCoq.Err.Default MkCore.FloatBind.
Admitted.

Instance Default_FloatInBind : HsToCoq.Err.Default FloatInBind :=
  HsToCoq.Err.Build_Default _ (FB HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `FloatIn.Outputable__FloatInBind' *)

(* Skipping definition `FloatIn.floatInwards' *)

Axiom fiExpr : Platform.Platform ->
               RevFloatInBinds -> CoreFVs.CoreExprWithFVs -> Core.CoreExpr.

#[global] Definition fiRhs
   : Platform.Platform ->
     RevFloatInBinds -> Core.CoreBndr -> CoreFVs.CoreExprWithFVs -> Core.CoreExpr :=
  fun platform to_drop bndr rhs =>
    match Id.idJoinPointHood bndr with
    | Outputable.JoinPoint join_arity =>
        let 'pair bndrs body := Core.collectNAnnBndrs join_arity rhs in
        Core.mkLams bndrs (fiExpr platform to_drop body)
    | _ => fiExpr platform to_drop rhs
    end.

#[global] Definition fbFVs : FloatInBind -> Core.DVarSet :=
  fun '(FB _ fvs _) => fvs.

#[global] Definition floatedBindsFVs : RevFloatInBinds -> FreeVarSet :=
  fun binds => Core.mapUnionDVarSet fbFVs binds.

#[global] Definition noFloatIntoLam : list Core.Var -> bool :=
  fun bndrs =>
    let bad := fun b => andb (Core.isId b) (negb (CoreArity.isOneShotBndr b)) in
    Data.Foldable.any bad bndrs.

#[global] Definition noFloatIntoArg : CoreFVs.CoreExprWithFVs' -> bool :=
  fun expr =>
    let deann_expr := Core.deAnnotate' expr in
    match expr with
    | Core.AnnLam bndr e =>
        let 'pair bndrs _ := Core.collectAnnBndrs e in
        orb (noFloatIntoLam (cons bndr bndrs)) (Data.Foldable.all Core.isTyVar (cons
                                                                                bndr bndrs))
    | _ => orb (CoreUtils.exprIsTrivial deann_expr) (CoreUtils.exprIsHNF deann_expr)
    end.

#[global] Definition noFloatIntoRhs
   : BasicTypes.RecFlag -> Core.Id -> CoreFVs.CoreExprWithFVs' -> bool :=
  fun is_rec bndr rhs =>
    if Id.isJoinId bndr : bool then BasicTypes.isRec is_rec else
    if Core.definitelyUnliftedType (Id.idType bndr) : bool then true else
    noFloatIntoArg rhs.

#[global] Definition dropBoxFloats : DropBox -> RevFloatInBinds :=
  fun '(pair _ floats) => GHC.List.reverse floats.

Definition floatIsCase : MkCore.FloatBind -> bool :=
  fun fb => match fb with
  | MkCore.FloatCase _ _ _ _ => true
  | MkCore.FloatLet _ => false
  end.

#[global] Definition floatIsDupable
   : Platform.Platform -> MkCore.FloatBind -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | platform, MkCore.FloatCase scrut _ _ _ =>
        CoreUtils.exprIsDupable platform scrut
    | platform, MkCore.FloatLet (Core.Rec prs) =>
        Data.Foldable.all (CoreUtils.exprIsDupable platform GHC.Base.∘ Data.Tuple.snd)
        prs
    | platform, MkCore.FloatLet (Core.NonRec _ r) =>
        CoreUtils.exprIsDupable platform r
    end.

#[global] Definition initDropBox : Core.DVarSet -> DropBox :=
  fun fvs => pair fvs nil.

#[global] Definition usedInDropBox : Core.DIdSet -> DropBox -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | bndrs, pair db_fvs _ => Core.intersectsDVarSet db_fvs bndrs
    end.

#[global] Definition sepBindsByDropPoint
   : Platform.Platform ->
     bool ->
     RevFloatInBinds ->
     FreeVarSet ->
     list FreeVarSet -> (RevFloatInBinds * list RevFloatInBinds)%type :=
  fun platform is_case floaters here_fvs fork_fvs =>
    let n_alts := Coq.Lists.List.length fork_fvs in
    let go
     : RevFloatInBinds ->
       DropBox -> list DropBox -> (RevFloatInBinds * list RevFloatInBinds)%type :=
      fix go (arg_1__ : RevFloatInBinds) (arg_2__ : DropBox) (arg_3__ : list DropBox)
        : (RevFloatInBinds * list RevFloatInBinds)%type
        := match arg_1__, arg_2__, arg_3__ with
           | nil, here_box, fork_boxes =>
               pair (dropBoxFloats here_box) (GHC.Base.map dropBoxFloats fork_boxes)
           | cons (FB bndrs bind_fvs bind as bind_w_fvs) binds, here_box, fork_boxes =>
               let insert : DropBox -> DropBox :=
                 fun '(pair fvs drops) =>
                   pair (Core.unionDVarSet fvs bind_fvs) (cons bind_w_fvs drops) in
               let insert_maybe :=
                 fun arg_8__ arg_9__ =>
                   match arg_8__, arg_9__ with
                   | box, true => insert box
                   | box, false => box
                   end in
               let used_in_flags :=
                 match fork_boxes with
                 | nil => nil
                 | cons _ nil => cons true nil
                 | _ => GHC.Base.map (usedInDropBox bndrs) fork_boxes
                 end in
               let n_used_alts := Util.count GHC.Base.id used_in_flags in
               let cant_push :=
                 if is_case : bool
                 then orb (andb (n_alts GHC.Base.> #1) (n_used_alts GHC.Base.== n_alts)) (andb
                           (n_used_alts GHC.Base.> #1) (negb (floatIsDupable platform bind))) else
                 orb (floatIsCase bind) (n_used_alts GHC.Base.> #1) in
               let new_fork_boxes :=
                 Util.zipWithEqual (GHC.Base.hs_string__ "FloatIn.sepBinds") insert_maybe
                 fork_boxes used_in_flags in
               let used_here := usedInDropBox bndrs here_box in
               let drop_here := orb used_here cant_push in
               if drop_here : bool then go binds (insert here_box) fork_boxes else
               go binds here_box new_fork_boxes
           end in
    if Data.Foldable.null floaters : bool
    then pair nil (Coq.Lists.List.flat_map (fun _ => cons nil nil) fork_fvs) else
    go floaters (initDropBox here_fvs) (GHC.Base.map initDropBox fork_fvs).

#[global] Definition fiBind
   : Platform.Platform ->
     RevFloatInBinds ->
     CoreFVs.CoreBindWithFVs ->
     Core.DVarSet -> (RevFloatInBinds * FloatInBind * RevFloatInBinds)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | platform
    , to_drop
    , Core.AnnNonRec id (pair rhs_fvs rhs as ann_rhs)
    , body_fvs =>
        let rule_fvs := CoreFVs.bndrRuleAndUnfoldingVarsDSet id in
        let extra_fvs :=
          if noFloatIntoRhs BasicTypes.NonRecursive id rhs : bool
          then Core.unionDVarSet rule_fvs rhs_fvs else
          rule_fvs in
        let body_fvs2 := Core.delDVarSet body_fvs id in
        match sepBindsByDropPoint platform false to_drop extra_fvs (cons rhs_fvs (cons
                                                                          body_fvs2 nil)) with
        | pair shared_binds (cons rhs_binds (cons body_binds nil)) =>
            let rhs' := fiRhs platform rhs_binds id ann_rhs in
            let rhs_fvs' :=
              Core.unionDVarSet (Core.unionDVarSet rhs_fvs (floatedBindsFVs rhs_binds))
                                rule_fvs in
            pair (pair shared_binds (FB (Core.unitDVarSet id) rhs_fvs' (MkCore.FloatLet
                                                                        (Core.NonRec id rhs')))) body_binds
        | _ => GHC.Err.patternFailure
        end
    | platform, to_drop, Core.AnnRec bindings, body_fvs =>
        let fi_bind
         : list RevFloatInBinds ->
           list (Core.Id * CoreFVs.CoreExprWithFVs)%type ->
           list (Core.Id * Core.CoreExpr)%type :=
          fun to_drops pairs =>
            let cont_11__ arg_12__ :=
              let 'pair (pair binder rhs) to_drop := arg_12__ in
              cons (pair binder (fiRhs platform to_drop binder rhs)) nil in
            Coq.Lists.List.flat_map cont_11__ (Util.zipEqual (GHC.Base.hs_string__
                                                              "fi_bind") pairs to_drops) in
        let 'pair ids rhss := GHC.List.unzip bindings in
        let rhss_fvs := GHC.Base.map CoreFVs.freeVarsOf rhss in
        let rule_fvs := Core.mapUnionDVarSet CoreFVs.bndrRuleAndUnfoldingVarsDSet ids in
        let extra_fvs :=
          Core.unionDVarSet rule_fvs (Core.unionDVarSets (let cont_17__ arg_18__ :=
                                                            let 'pair bndr (pair rhs_fvs rhs) := arg_18__ in
                                                            if noFloatIntoRhs BasicTypes.Recursive bndr rhs : bool
                                                            then cons rhs_fvs nil else
                                                            nil in
                                                          Coq.Lists.List.flat_map cont_17__ bindings)) in
        match sepBindsByDropPoint platform false to_drop extra_fvs (cons body_fvs
                                                                         rhss_fvs) with
        | pair shared_binds (cons body_binds rhss_binds) =>
            let rhs_fvs' :=
              Core.unionDVarSet (Core.unionDVarSet (Core.unionDVarSets rhss_fvs)
                                                   (Core.unionDVarSets (GHC.Base.map floatedBindsFVs rhss_binds)))
                                rule_fvs in
            pair (pair shared_binds (FB (Core.mkDVarSet ids) rhs_fvs' (MkCore.FloatLet
                                                                       (Core.Rec (fi_bind rhss_binds bindings)))))
                 body_binds
        | _ => GHC.Err.patternFailure
        end
    end.

Fixpoint wrapFloats (arg_0__ : RevFloatInBinds) (arg_1__ : Core.CoreExpr)
  : Core.CoreExpr
  := match arg_0__, arg_1__ with
     | nil, e => e
     | cons (FB _ _ fl) bs, e => wrapFloats bs (MkCore.wrapFloat fl e)
     end.

(* External variables:
     andb bool cons false floatIsCase list negb nil op_zt__ orb pair true
     BasicTypes.NonRecursive BasicTypes.RecFlag BasicTypes.Recursive BasicTypes.isRec
     Coq.Lists.List.flat_map Coq.Lists.List.length Core.AnnLam Core.AnnNonRec
     Core.AnnRec Core.CoreBndr Core.CoreExpr Core.DIdSet Core.DVarSet Core.Id
     Core.NonRec Core.Rec Core.Var Core.collectAnnBndrs Core.collectNAnnBndrs
     Core.deAnnotate' Core.definitelyUnliftedType Core.delDVarSet
     Core.intersectsDVarSet Core.isId Core.isTyVar Core.mapUnionDVarSet
     Core.mkDVarSet Core.mkLams Core.unionDVarSet Core.unionDVarSets Core.unitDVarSet
     CoreArity.isOneShotBndr CoreFVs.CoreBindWithFVs CoreFVs.CoreExprWithFVs
     CoreFVs.CoreExprWithFVs' CoreFVs.bndrRuleAndUnfoldingVarsDSet CoreFVs.freeVarsOf
     CoreUtils.exprIsDupable CoreUtils.exprIsHNF CoreUtils.exprIsTrivial
     Data.Foldable.all Data.Foldable.any Data.Foldable.null Data.Tuple.snd
     GHC.Base.id GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zg__ GHC.Err.patternFailure GHC.List.reverse GHC.List.unzip
     GHC.Num.fromInteger Id.idJoinPointHood Id.idType Id.isJoinId MkCore.FloatBind
     MkCore.FloatCase MkCore.FloatLet MkCore.wrapFloat Outputable.JoinPoint
     Platform.Platform Util.count Util.zipEqual Util.zipWithEqual
*)
