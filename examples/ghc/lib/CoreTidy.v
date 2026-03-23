(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Core.
Require Data.Traversable.
Require GHC.Core.TyCo.Tidy.
Require GHC.Prim.
Require GHC.Types.Tickish.
Require Id.
Require Maybes.
Require Name.
Require NameSet.
Require OccName.
Require SrcLoc.
Require UniqFM.
Require Unique.
Require Util.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom tidyBind : Core.TidyEnv ->
                 Core.CoreBind -> (Core.TidyEnv * Core.CoreBind)%type.

Axiom computeCbvInfo : forall `{GHC.Prim.HasCallStack},
                       Core.Id -> Core.CoreExpr -> Core.Id.

#[global] Definition tidyCbvInfoTop `{Util.HasDebugCallStack}
   : NameSet.NameSet -> Core.Id -> Core.CoreExpr -> Core.Id :=
  fun boot_exports id rhs =>
    if NameSet.elemNameSet (Id.idName id) boot_exports : bool then id else
    computeCbvInfo id rhs.

#[global] Definition tidyCbvInfoLocal `{Util.HasDebugCallStack}
   : Core.Id -> Core.CoreExpr -> Core.Id :=
  fun id rhs => computeCbvInfo id rhs.

Axiom tidyExpr : Core.TidyEnv -> Core.CoreExpr -> Core.CoreExpr.

#[global] Definition op_zeZC__ {a} {b} : a -> (a -> b) -> b :=
  fun m k => GHC.Prim.seq m (k m).

Notation "'_=:_'" := (op_zeZC__).

Infix "=:" := (_=:_) (at level 99).

#[global] Definition tidyIdBndr
   : Core.TidyEnv -> Core.Id -> (Core.TidyEnv * Core.Id)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair tidy_env var_env as env), id =>
        let 'pair tidy_env' occ' := OccName.tidyOccName tidy_env (Name.getOccName id) in
        let old_info := Core.idInfo id in
        let old_unf := Core.realUnfoldingInfo old_info in
        let new_unf := Core.trimUnfolding old_unf in
        let new_info :=
          Core.setOneShotInfo (Core.setUnfoldingInfo (Core.setOccInfo Core.vanillaIdInfo
                                                                      (Core.occInfo old_info)) new_unf)
                              (Core.oneShotInfo old_info) in
        let name' := Name.mkInternalName (Id.idUnique id) occ' SrcLoc.noSrcSpan in
        let mult' := GHC.Core.TyCo.Tidy.tidyType env (Id.idMult id) in
        let ty' := GHC.Core.TyCo.Tidy.tidyType env (Id.idType id) in
        let id' := Id.mkLocalIdWithInfo name' mult' ty' new_info in
        let var_env' := Core.extendVarEnv var_env id id' in
        pair (pair tidy_env' var_env') id'
    end.

#[global] Definition tidyBndr
   : Core.TidyEnv -> Core.Var -> (Core.TidyEnv * Core.Var)%type :=
  fun env var =>
    if Core.isTyCoVar var : bool then GHC.Core.TyCo.Tidy.tidyVarBndr env var else
    tidyIdBndr env var.

#[global] Definition tidyBndrs
   : Core.TidyEnv -> list Core.Var -> (Core.TidyEnv * list Core.Var)%type :=
  fun env vars => Data.Traversable.mapAccumL tidyBndr env vars.

#[global] Definition tidyAlt : Core.TidyEnv -> Core.CoreAlt -> Core.CoreAlt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | env, Core.Mk_Alt con vs rhs =>
        tidyBndrs env vs =:
        (fun '(pair env' vs) => (Core.Mk_Alt con vs (tidyExpr env' rhs)))
    end.

Axiom tidyTickish : Core.TidyEnv ->
                    GHC.Types.Tickish.CoreTickish -> GHC.Types.Tickish.CoreTickish.

(* Skipping definition `CoreTidy.tidyRules' *)

(* Skipping definition `CoreTidy.tidyRule' *)

#[global] Definition tidyNameOcc : Core.TidyEnv -> Name.Name -> Name.Name :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, n =>
        match UniqFM.lookupUFM_Directly var_env (Unique.getUnique n) with
        | None => n
        | Some v => Id.idName v
        end
    end.

#[global] Definition tidyVarOcc : Core.TidyEnv -> Core.Var -> Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, v => Maybes.orElse (Core.lookupVarEnv var_env v) v
    end.

Axiom tidyLetBndr : Core.TidyEnv ->
                    Core.TidyEnv -> Core.Id -> (Core.TidyEnv * Core.Id)%type.

#[global] Definition tidyNestedUnfolding
   : Core.TidyEnv -> Core.Unfolding -> Core.Unfolding :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Core.NoUnfolding => Core.NoUnfolding
    end.

Module Notations.
Notation "'_CoreTidy.=:_'" := (op_zeZC__).
Infix "CoreTidy.=:" := (_=:_) (at level 99).
End Notations.

(* External variables:
     None Some bool list op_zt__ pair Core.CoreAlt Core.CoreBind Core.CoreExpr
     Core.Id Core.Mk_Alt Core.NoUnfolding Core.TidyEnv Core.Unfolding Core.Var
     Core.extendVarEnv Core.idInfo Core.isTyCoVar Core.lookupVarEnv Core.occInfo
     Core.oneShotInfo Core.realUnfoldingInfo Core.setOccInfo Core.setOneShotInfo
     Core.setUnfoldingInfo Core.trimUnfolding Core.vanillaIdInfo
     Data.Traversable.mapAccumL GHC.Core.TyCo.Tidy.tidyType
     GHC.Core.TyCo.Tidy.tidyVarBndr GHC.Prim.HasCallStack GHC.Prim.seq
     GHC.Types.Tickish.CoreTickish Id.idMult Id.idName Id.idType Id.idUnique
     Id.mkLocalIdWithInfo Maybes.orElse Name.Name Name.getOccName Name.mkInternalName
     NameSet.NameSet NameSet.elemNameSet OccName.tidyOccName SrcLoc.noSrcSpan
     UniqFM.lookupUFM_Directly Unique.getUnique Util.HasDebugCallStack
*)
