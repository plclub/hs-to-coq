(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require Import AxiomatizedTypes.
Require BasicTypes.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Import Core.
Require Data.Foldable.
Require Data.Maybe.
Require Data.OldList.
Require FieldLabel.
Require GHC.Base.
Require GHC.Types.GREInfo.
Require HsSyn.
Require Name.
Require OccName.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

(* ConLike is defined in Core.v mutual type block *)

(* Midamble — no extra Default instances needed; they are in Core.v *)

Require HsToRocq.Err.

(* Converted value declarations: *)

#[local] Definition Uniquable__ConLike_getUnique : ConLike -> Unique.Unique :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon dc => Unique.getUnique dc
    | PatSynCon ps => Unique.getUnique ps
    end.

#[global]
Program Instance Uniquable__ConLike : Unique.Uniquable ConLike :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__ConLike_getUnique |}.

#[global] Definition eqConLike : ConLike -> ConLike -> bool :=
  fun x y => Unique.getUnique x GHC.Base.== Unique.getUnique y.

#[local] Definition Eq___ConLike_op_zeze__ : ConLike -> ConLike -> bool :=
  eqConLike.

#[local] Definition Eq___ConLike_op_zsze__ : ConLike -> ConLike -> bool :=
  fun x y => negb (Eq___ConLike_op_zeze__ x y).

#[global]
Program Instance Eq___ConLike : GHC.Base.Eq_ ConLike :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ConLike_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ConLike_op_zsze__ |}.

#[local] Definition NamedThing__ConLike_getName : ConLike -> Name.Name :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon dc => Name.getName dc
    | PatSynCon ps => Name.getName ps
    end.

#[local] Definition NamedThing__ConLike_getOccName
   : ConLike -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__ConLike_getName n).

#[global]
Program Instance NamedThing__ConLike : Name.NamedThing ConLike :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__ConLike_getName ;
           Name.getOccName__ := NamedThing__ConLike_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `ConLike.Outputable__ConLike' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `ConLike.OutputableBndr__ConLike' *)

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `ConLike.Data__ConLike' *)

#[global] Definition isVanillaConLike : ConLike -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon con => Core.isVanillaDataCon con
    | PatSynCon ps => Core.isVanillaPatSyn ps
    end.

#[global] Definition conLikeConLikeName
   : ConLike -> GHC.Types.GREInfo.ConLikeName :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon dc => GHC.Types.GREInfo.DataConName (Core.dataConName dc)
    | PatSynCon ps => GHC.Types.GREInfo.PatSynName (Core.patSynName ps)
    end.

#[global] Definition conLikeArity : ConLike -> BasicTypes.Arity :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => Core.dataConSourceArity data_con
    | PatSynCon pat_syn => Core.patSynArity pat_syn
    end.

#[global] Definition conLikeFieldLabels
   : ConLike -> list FieldLabel.FieldLabel :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => Core.dataConFieldLabels data_con
    | PatSynCon pat_syn => Core.patSynFieldLabels pat_syn
    end.

#[global] Definition conLikeConInfo : ConLike -> GHC.Types.GREInfo.ConInfo :=
  fun con =>
    GHC.Types.GREInfo.mkConInfo (conLikeArity con) (conLikeFieldLabels con).

#[global] Definition conLikeInstOrigArgTys
   : ConLike -> list Type_ -> list (Core.Scaled Type_) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RealDataCon data_con, tys => Core.dataConInstOrigArgTys data_con tys
    | PatSynCon pat_syn, tys =>
        GHC.Base.map Core.unrestricted (Core.patSynInstArgTys pat_syn tys)
    end.

#[global] Definition conLikeUserTyVarBinders
   : ConLike -> list Core.InvisTVBinder :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => Core.dataConUserTyVarBinders data_con
    | PatSynCon pat_syn =>
        Coq.Init.Datatypes.app (Core.patSynUnivTyVarBinders pat_syn)
                               (Core.patSynExTyVarBinders pat_syn)
    end.

#[global] Definition conLikeExTyCoVars : ConLike -> list Core.TyCoVar :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon dcon1 => Core.dataConExTyCoVars dcon1
    | PatSynCon psyn1 => Core.patSynExTyVars psyn1
    end.

#[global] Definition conLikeName : ConLike -> Name.Name :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => Core.dataConName data_con
    | PatSynCon pat_syn => Core.patSynName pat_syn
    end.

#[global] Definition conLikeStupidTheta : ConLike -> ThetaType :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => Core.dataConStupidTheta data_con
    | PatSynCon _ => HsToRocq.Err.default
    end.

#[global] Definition conLikeHasBuilder : ConLike -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon _ => true
    | PatSynCon pat_syn => Data.Maybe.isJust (Core.patSynBuilder pat_syn)
    end.

#[global] Definition conLikeImplBangs : ConLike -> list Core.HsImplBang :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => Core.dataConImplBangs data_con
    | PatSynCon pat_syn =>
        Coq.Lists.List.repeat Core.HsLazy (Core.patSynArity pat_syn)
    end.

#[global] Definition conLikeResTy : ConLike -> list Type_ -> Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RealDataCon con, tys => Core.mkTyConApp (Core.dataConTyCon con) tys
    | PatSynCon ps, tys => Core.patSynInstResTy ps tys
    end.

#[global] Definition conLikeFullSig
   : ConLike ->
     (list Core.TyVar * list Core.TyCoVar * list Core.EqSpec * ThetaType * ThetaType
      *
      list (Core.Scaled Type_) *
      Type_)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon con =>
        let 'pair (pair (pair (pair (pair univ_tvs ex_tvs) eq_spec) theta) arg_tys)
           res_ty := Core.dataConFullSig con in
        pair (pair (pair (pair (pair (pair univ_tvs ex_tvs) eq_spec) theta) (HsToRocq.Err.default : ThetaType))
                   arg_tys) res_ty
    | PatSynCon pat_syn =>
        let 'pair (pair (pair (pair (pair univ_tvs req) ex_tvs) prov) arg_tys) res_ty :=
          Core.patSynSig pat_syn in
        pair (pair (pair (pair (pair (pair univ_tvs ex_tvs) (@nil Core.EqSpec)) prov) req) arg_tys)
             res_ty
    end.

#[global] Definition conLikeFieldType
   : ConLike -> HsSyn.FieldLabelString -> Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | PatSynCon ps, label => Core.patSynFieldType ps label
    | RealDataCon dc, label => Core.dataConFieldType dc label
    end.

#[global] Definition conLikesWithFields
   : list ConLike ->
     list HsSyn.FieldLabelString -> (list ConLike * list ConLike)%type :=
  fun con_likes lbls =>
    let has_fld :=
      fun dc lbl =>
        Data.Foldable.any (fun fl => FieldLabel.flLabel fl GHC.Base.== lbl)
        (conLikeFieldLabels dc) in
    let has_flds := fun dc => Data.Foldable.all (has_fld dc) lbls in
    Data.OldList.partition has_flds con_likes.

#[global] Definition conLikeIsInfix : ConLike -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon dc => Core.dataConIsInfix dc
    | PatSynCon ps => Core.patSynIsInfix ps
    end.
