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
Require BinNums.
Require Core.
Require CoreFVs.
Require CoreMonad.
Require GHC.Base.
Require GHC.Types.Cpr.
Require HsToCoq.Err.
Require UniqSupply.

(* Converted type declarations: *)

#[global] Definition LvlM :=
  UniqSupply.UniqSM%type.

Inductive LevelType : Type := | BndrLvl : LevelType | JoinCeilLvl : LevelType.

Inductive Level : Type :=
  | Mk_Level : BinNums.N -> BinNums.N -> LevelType -> Level.

Inductive FloatSpec : Type :=
  | FloatMe : Level -> FloatSpec
  | StayPut : Level -> FloatSpec.

#[global] Definition LevelledBind :=
  (Core.TaggedBind FloatSpec)%type.

#[global] Definition LevelledBndr :=
  (Core.TaggedBndr FloatSpec)%type.

#[global] Definition LevelledExpr :=
  (Core.TaggedExpr FloatSpec)%type.

Inductive LevelEnv : Type :=
  | LE (le_switches : CoreMonad.FloatOutSwitches) (le_ctxt_lvl : Level)
  (le_lvl_env : Core.VarEnv Level) (le_join_ceil : Level) (le_subst : Core.Subst)
  (le_env : Core.IdEnv (list Core.OutVar * LevelledExpr)%type)
   : LevelEnv.

Instance Default__LevelType : HsToCoq.Err.Default LevelType :=
  HsToCoq.Err.Build_Default _ BndrLvl.

#[global] Definition le_ctxt_lvl (arg_0__ : LevelEnv) :=
  let 'LE _ le_ctxt_lvl _ _ _ _ := arg_0__ in
  le_ctxt_lvl.

#[global] Definition le_env (arg_0__ : LevelEnv) :=
  let 'LE _ _ _ _ _ le_env := arg_0__ in
  le_env.

#[global] Definition le_join_ceil (arg_0__ : LevelEnv) :=
  let 'LE _ _ _ le_join_ceil _ _ := arg_0__ in
  le_join_ceil.

#[global] Definition le_lvl_env (arg_0__ : LevelEnv) :=
  let 'LE _ _ le_lvl_env _ _ _ := arg_0__ in
  le_lvl_env.

#[global] Definition le_subst (arg_0__ : LevelEnv) :=
  let 'LE _ _ _ _ le_subst _ := arg_0__ in
  le_subst.

#[global] Definition le_switches (arg_0__ : LevelEnv) :=
  let 'LE le_switches _ _ _ _ _ := arg_0__ in
  le_switches.

(* Midamble *)

(* GHC 9.10: Eq instances needed by FloatOut.v *)
Definition Eq__LevelType_op_zeze (a b : LevelType) : bool :=
  match a, b with
  | BndrLvl, BndrLvl => true
  | JoinCeilLvl, JoinCeilLvl => true
  | _, _ => false
  end.

#[global]
Instance Eq__LevelType : GHC.Base.Eq_ LevelType :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq__LevelType_op_zeze ;
           GHC.Base.op_zsze____ := fun a b => negb (Eq__LevelType_op_zeze a b) |}.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SetLevels.Outputable__FloatSpec' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SetLevels.Outputable__Level' *)

Instance Eq___Level : GHC.Base.Eq_ Level.
Proof.
Admitted.

Axiom floatSpecLevel : FloatSpec -> Level.

Axiom tOP_LEVEL : Level.

Axiom incMajorLvl : Level -> Level.

Axiom incMinorLvl : Level -> Level.

Axiom asJoinCeilLvl : Level -> Level.

Axiom maxLvl : Level -> Level -> Level.

Axiom ltLvl : Level -> Level -> bool.

Axiom ltMajLvl : Level -> Level -> bool.

Axiom isTopLvl : Level -> bool.

Axiom isJoinCeilLvl : Level -> bool.

Axiom setLevels : CoreMonad.FloatOutSwitches ->
                  Core.CoreProgram -> UniqSupply.UniqSupply -> list LevelledBind.

Axiom lvlTopBind : LevelEnv -> Core.Bind Core.Id -> LvlM LevelledBind.

Axiom lvl_top : LevelEnv ->
                BasicTypes.RecFlag ->
                Core.Id -> Core.CoreExpr -> LvlM (LevelledBndr * LevelledExpr)%type.

Axiom lvlExpr : LevelEnv -> CoreFVs.CoreExprWithFVs -> LvlM LevelledExpr.

Axiom lvlNonTailExpr : LevelEnv -> CoreFVs.CoreExprWithFVs -> LvlM LevelledExpr.

Axiom lvlApp : LevelEnv ->
               CoreFVs.CoreExprWithFVs ->
               (CoreFVs.CoreExprWithFVs * list CoreFVs.CoreExprWithFVs)%type ->
               LvlM LevelledExpr.

Axiom lvlCase : LevelEnv ->
                Core.DVarSet ->
                LevelledExpr ->
                Core.Id ->
                AxiomatizedTypes.Type_ -> list CoreFVs.CoreAltWithFVs -> LvlM LevelledExpr.

Axiom lvlNonTailMFE : LevelEnv ->
                      bool -> CoreFVs.CoreExprWithFVs -> LvlM LevelledExpr.

Axiom lvlMFE : LevelEnv -> bool -> CoreFVs.CoreExprWithFVs -> LvlM LevelledExpr.

Axiom hasFreeJoin : LevelEnv -> Core.DVarSet -> bool.

Axiom annotateBotStr : Core.Id ->
                       BasicTypes.Arity ->
                       option (BasicTypes.Arity * Core.DmdSig * GHC.Types.Cpr.CprSig)%type -> Core.Id.

Axiom notWorthFloating : Core.CoreExpr -> list Core.Var -> bool.

Axiom lvlBind : LevelEnv ->
                CoreFVs.CoreBindWithFVs -> LvlM (LevelledBind * LevelEnv)%type.

Axiom profitableFloat : LevelEnv -> Level -> bool.

(* Skipping definition `SetLevels.lvlRhs' *)

(* Skipping definition `SetLevels.lvlFloatRhs' *)

Axiom substAndLvlBndrs : BasicTypes.RecFlag ->
                         LevelEnv -> Level -> list Core.InVar -> (LevelEnv * list LevelledBndr)%type.

Axiom substBndrsSL : BasicTypes.RecFlag ->
                     LevelEnv -> list Core.InVar -> (LevelEnv * list Core.OutVar)%type.

Axiom lvlLamBndrs : LevelEnv ->
                    Level -> list Core.OutVar -> (LevelEnv * list LevelledBndr)%type.

Axiom lvlJoinBndrs : LevelEnv ->
                     Level ->
                     BasicTypes.RecFlag -> list Core.OutVar -> (LevelEnv * list LevelledBndr)%type.

Axiom lvlBndrs : LevelEnv ->
                 Level -> list Core.CoreBndr -> (LevelEnv * list LevelledBndr)%type.

Axiom stayPut : Level -> Core.OutVar -> LevelledBndr.

Axiom destLevel : LevelEnv ->
                  Core.DVarSet -> Core.TyCoVarSet -> bool -> bool -> bool -> Level.

Axiom isFunction : CoreFVs.CoreExprWithFVs -> bool.

Axiom countFreeIds : Core.DVarSet -> nat.

Axiom initialEnv : CoreMonad.FloatOutSwitches -> Core.CoreProgram -> LevelEnv.

Axiom addLvl : Level -> Core.VarEnv Level -> Core.OutVar -> Core.VarEnv Level.

Axiom addLvls : Level ->
                Core.VarEnv Level -> list Core.OutVar -> Core.VarEnv Level.

Axiom floatLams : LevelEnv -> option nat.

Axiom floatConsts : LevelEnv -> bool.

Axiom floatOverSat : LevelEnv -> bool.

Axiom floatTopLvlOnly : LevelEnv -> bool.

Axiom incMinorLvlFrom : LevelEnv -> Level.

Axiom extendCaseBndrEnv : LevelEnv ->
                          Core.Id -> Core.Expr LevelledBndr -> LevelEnv.

Axiom placeJoinCeiling : LevelEnv -> LevelEnv.

Axiom maxFvLevel : (Core.Var -> bool) -> LevelEnv -> Core.DVarSet -> Level.

Axiom maxFvLevel' : (Core.Var -> bool) -> LevelEnv -> Core.TyCoVarSet -> Level.

Axiom maxIn : (Core.Var -> bool) -> LevelEnv -> Core.InVar -> Level -> Level.

Axiom lookupVar : LevelEnv -> Core.Id -> LevelledExpr.

Axiom joinCeilingLevel : LevelEnv -> Level.

Axiom abstractVars : Level -> LevelEnv -> Core.DVarSet -> list Core.OutVar.

Axiom initLvl : forall {a}, UniqSupply.UniqSupply -> UniqSupply.UniqSM a -> a.

Axiom newPolyBndrs : Level ->
                     LevelEnv ->
                     list Core.OutVar -> list Core.InId -> LvlM (LevelEnv * list Core.OutId)%type.

(* Skipping definition `SetLevels.newLvlVar' *)

Axiom cloneCaseBndrs : LevelEnv ->
                       Level -> list Core.Var -> LvlM (LevelEnv * list Core.Var)%type.

Axiom cloneLetVars : BasicTypes.RecFlag ->
                     LevelEnv -> Level -> list Core.InVar -> LvlM (LevelEnv * list Core.OutVar)%type.

Axiom add_id : Core.IdEnv (list Core.Var * LevelledExpr)%type ->
               (Core.Var * Core.Var)%type -> Core.IdEnv (list Core.Var * LevelledExpr)%type.

Instance Default__Level : HsToCoq.Err.Default Level :=
  HsToCoq.Err.Build_Default _ (Mk_Level HsToCoq.Err.default HsToCoq.Err.default
                                        HsToCoq.Err.default).

(* External variables:
     bool list nat op_zt__ option AxiomatizedTypes.Type_ BasicTypes.Arity
     BasicTypes.RecFlag BinNums.N Core.Bind Core.CoreBndr Core.CoreExpr
     Core.CoreProgram Core.DVarSet Core.DmdSig Core.Expr Core.Id Core.IdEnv Core.InId
     Core.InVar Core.OutId Core.OutVar Core.Subst Core.TaggedBind Core.TaggedBndr
     Core.TaggedExpr Core.TyCoVarSet Core.Var Core.VarEnv CoreFVs.CoreAltWithFVs
     CoreFVs.CoreBindWithFVs CoreFVs.CoreExprWithFVs CoreMonad.FloatOutSwitches
     GHC.Base.Eq_ GHC.Types.Cpr.CprSig HsToCoq.Err.Build_Default HsToCoq.Err.Default
     HsToCoq.Err.default UniqSupply.UniqSM UniqSupply.UniqSupply
*)
