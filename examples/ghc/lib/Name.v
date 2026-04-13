(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require FastString.
Require GHC.Base.
Require GHC.Types.TyThing.
Require HsToRocq.Err.
Require Maybes.
Require Module.
Require OccName.
Require Panic.
Require SrcLoc.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive BuiltInSyntax : Type :=
  | Mk_BuiltInSyntax : BuiltInSyntax
  | UserSyntax : BuiltInSyntax.

Inductive NameSort : Type :=
  | External : Module.Module -> NameSort
  | WiredIn
   : Module.Module -> GHC.Types.TyThing.TyThing -> BuiltInSyntax -> NameSort
  | Internal : NameSort
  | System : NameSort.

Inductive Name : Type :=
  | Mk_Name (n_sort : NameSort) (n_occ : OccName.OccName) (n_uniq : Unique.Unique)
  (n_loc : SrcLoc.SrcSpan)
   : Name.

Record NamedThing__Dict (a : Type) := NamedThing__Dict_Build {
  getName__ : a -> Name ;
  getOccName__ : a -> OccName.OccName }.

#[global] Definition NamedThing (a : Type) :=
  forall r__, (NamedThing__Dict a -> r__) -> r__.
Existing Class NamedThing.

#[global] Definition getName `{g__0__ : NamedThing a} : a -> Name :=
  g__0__ _ (getName__ a).

#[global] Definition getOccName `{g__0__ : NamedThing a}
   : a -> OccName.OccName :=
  g__0__ _ (getOccName__ a).

Instance Default__BuiltInSyntax : HsToRocq.Err.Default BuiltInSyntax :=
  HsToRocq.Err.Build_Default _ Mk_BuiltInSyntax.

Instance Default__NameSort : HsToRocq.Err.Default NameSort :=
  HsToRocq.Err.Build_Default _ Internal.

#[global] Definition n_loc (arg_0__ : Name) :=
  let 'Mk_Name _ _ _ n_loc := arg_0__ in
  n_loc.

#[global] Definition n_occ (arg_0__ : Name) :=
  let 'Mk_Name _ n_occ _ _ := arg_0__ in
  n_occ.

#[global] Definition n_sort (arg_0__ : Name) :=
  let 'Mk_Name n_sort _ _ _ := arg_0__ in
  n_sort.

#[global] Definition n_uniq (arg_0__ : Name) :=
  let 'Mk_Name _ _ n_uniq _ := arg_0__ in
  n_uniq.

(* Midamble *)

(* ------------- Name midamble.v ------------ *)
Require Import HsToRocq.Err.
#[global] Instance Default__Name : Default Name := Build_Default _ (Mk_Name default default default default).



(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Name.Outputable__NameSort' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Name.NFData__Name' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Name.NFData__FieldLabel' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Name.NFData__NameSort' *)

#[global] Definition nameOccName : Name -> OccName.OccName :=
  fun name => n_occ name.

#[local] Definition HasOccName__Name_occName : Name -> OccName.OccName :=
  nameOccName.

#[global]
Program Instance HasOccName__Name : OccName.HasOccName Name :=
  fun _ k__ => k__ {| OccName.occName__ := HasOccName__Name_occName |}.

#[global] Definition cmpName : Name -> Name -> comparison :=
  fun n1 n2 => Unique.nonDetCmpUnique (n_uniq n1) (n_uniq n2).

#[local] Definition Eq___Name_op_zeze__ : Name -> Name -> bool :=
  fun a b => match cmpName a b with | Eq => true | _ => false end.

#[local] Definition Eq___Name_op_zsze__ : Name -> Name -> bool :=
  fun a b => match cmpName a b with | Eq => false | _ => true end.

#[global]
Program Instance Eq___Name : GHC.Base.Eq_ Name :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Name_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Name_op_zsze__ |}.

#[local] Definition Ord__Name_compare : Name -> Name -> comparison :=
  cmpName.

#[local] Definition Ord__Name_op_zl__ : Name -> Name -> bool :=
  fun x y => Ord__Name_compare x y GHC.Base.== Lt.

#[local] Definition Ord__Name_op_zlze__ : Name -> Name -> bool :=
  fun x y => Ord__Name_compare x y GHC.Base./= Gt.

#[local] Definition Ord__Name_op_zg__ : Name -> Name -> bool :=
  fun x y => Ord__Name_compare x y GHC.Base.== Gt.

#[local] Definition Ord__Name_op_zgze__ : Name -> Name -> bool :=
  fun x y => Ord__Name_compare x y GHC.Base./= Lt.

#[local] Definition Ord__Name_max : Name -> Name -> Name :=
  fun x y => if Ord__Name_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__Name_min : Name -> Name -> Name :=
  fun x y => if Ord__Name_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__Name : GHC.Base.Ord Name :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Name_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Name_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Name_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Name_op_zgze__ ;
           GHC.Base.compare__ := Ord__Name_compare ;
           GHC.Base.max__ := Ord__Name_max ;
           GHC.Base.min__ := Ord__Name_min |}.

#[global] Definition nameUnique : Name -> Unique.Unique :=
  fun name => n_uniq name.

#[local] Definition Uniquable__Name_getUnique : Name -> Unique.Unique :=
  nameUnique.

#[global]
Program Instance Uniquable__Name : Unique.Uniquable Name :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__Name_getUnique |}.

#[local] Definition NamedThing__Name_getName : Name -> Name :=
  fun n => n.

#[local] Definition NamedThing__Name_getOccName : Name -> OccName.OccName :=
  fun n => nameOccName (NamedThing__Name_getName n).

#[global]
Program Instance NamedThing__Name : NamedThing Name :=
  fun _ k__ =>
    k__ {| getName__ := NamedThing__Name_getName ;
           getOccName__ := NamedThing__Name_getOccName |}.

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `Name.Data__Name' *)

(* Skipping all instances of class `Binary.Binary', including
   `Name.Binary__Name' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Name.Outputable__Name' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `Name.OutputableBndr__Name' *)

#[local] Definition NamedThing__Located_getName {inst_e : Type} `{NamedThing
  inst_e}
   : SrcLoc.Located inst_e -> Name :=
  getName GHC.Base.∘ SrcLoc.unLoc.

#[local] Definition NamedThing__Located_getOccName {inst_e : Type} `{NamedThing
  inst_e}
   : SrcLoc.Located inst_e -> OccName.OccName :=
  fun n => nameOccName (NamedThing__Located_getName n).

#[global]
Program Instance NamedThing__Located {e : Type} `{NamedThing e}
   : NamedThing (SrcLoc.Located e) :=
  fun _ k__ =>
    k__ {| getName__ := NamedThing__Located_getName ;
           getOccName__ := NamedThing__Located_getOccName |}.

#[global] Definition nameNameSpace : Name -> OccName.NameSpace :=
  fun name => OccName.occNameSpace (n_occ name).

#[global] Definition nameSrcLoc : Name -> SrcLoc.SrcLoc :=
  fun name => SrcLoc.srcSpanStart (n_loc name).

#[global] Definition nameSrcSpan : Name -> SrcLoc.SrcSpan :=
  fun name => n_loc name.

#[global] Definition isWiredInName : Name -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name (WiredIn _ _ _) _ _ _ => true
    | _ => false
    end.

#[global] Definition isWiredIn {thing : Type} `{NamedThing thing}
   : thing -> bool :=
  isWiredInName GHC.Base.∘ getName.

(* Skipping definition `Name.wiredInNameTyThing_maybe' *)

#[global] Definition isBuiltInSyntax : Name -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name (WiredIn _ _ Mk_BuiltInSyntax) _ _ _ => true
    | _ => false
    end.

(* Skipping definition `Name.isTupleTyConName' *)

(* Skipping definition `Name.isSumTyConName' *)

(* Skipping definition `Name.isUnboxedTupleDataConLikeName' *)

#[global] Definition isExternalName : Name -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name (External _) _ _ _ => true
    | Mk_Name (WiredIn _ _ _) _ _ _ => true
    | _ => false
    end.

#[global] Definition isInternalName : Name -> bool :=
  fun name => negb (isExternalName name).

(* Skipping definition `Name.isHoleName' *)

(* Skipping definition `Name.isDynLinkName' *)

#[global] Definition nameModule_maybe : Name -> option Module.Module :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name (External mod_) _ _ _ => Some mod_
    | Mk_Name (WiredIn mod_ _ _) _ _ _ => Some mod_
    | _ => None
    end.

#[global] Definition nameModule : Name -> Module.Module :=
  fun nm => Maybes.orElse (nameModule_maybe nm) (Panic.panic default).

#[global] Definition is_interactive_or_from
   : Module.Module -> Module.Module -> bool :=
  fun from mod_ => orb (from GHC.Base.== mod_) (Module.isInteractiveModule mod_).

(* Skipping definition `Name.namePun_maybe' *)

#[global] Definition nameIsLocalOrFrom : Module.Module -> Name -> bool :=
  fun from name =>
    match nameModule_maybe name with
    | Some mod_ => is_interactive_or_from from mod_
    | _ => true
    end.

#[global] Definition nameIsExternalOrFrom : Module.Module -> Name -> bool :=
  fun from name =>
    match nameModule_maybe name with
    | Some mod_ => is_interactive_or_from from mod_
    | _ => false
    end.

#[global] Definition nameIsHomePackage : Module.Module -> Name -> bool :=
  fun this_mod =>
    let this_pkg := Module.moduleUnit this_mod in
    fun nm =>
      match n_sort nm with
      | External nm_mod => Module.moduleUnit nm_mod GHC.Base.== this_pkg
      | WiredIn nm_mod _ _ => Module.moduleUnit nm_mod GHC.Base.== this_pkg
      | Internal => true
      | System => false
      end.

#[global] Definition nameIsHomePackageImport : Module.Module -> Name -> bool :=
  fun this_mod =>
    let this_pkg := Module.moduleUnit this_mod in
    fun nm =>
      match nameModule_maybe nm with
      | None => false
      | Some nm_mod =>
          andb (nm_mod GHC.Base./= this_mod) (Module.moduleUnit nm_mod GHC.Base.==
                this_pkg)
      end.

(* Skipping definition `Name.nameIsFromExternalPackage' *)

#[global] Definition isTyVarName : Name -> bool :=
  fun name => OccName.isTvOcc (nameOccName name).

#[global] Definition isTyConName : Name -> bool :=
  fun name => OccName.isTcOcc (nameOccName name).

#[global] Definition isDataConName : Name -> bool :=
  fun name => OccName.isDataOcc (nameOccName name).

#[global] Definition isValName : Name -> bool :=
  fun name => OccName.isValOcc (nameOccName name).

#[global] Definition isVarName : Name -> bool :=
  OccName.isVarOcc GHC.Base.∘ nameOccName.

#[global] Definition isFieldName : Name -> bool :=
  OccName.isFieldOcc GHC.Base.∘ nameOccName.

#[global] Definition isSystemName : Name -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name System _ _ _ => true
    | _ => false
    end.

#[global] Definition mkInternalName
   : Unique.Unique -> OccName.OccName -> SrcLoc.SrcSpan -> Name :=
  fun uniq occ loc => Mk_Name Internal occ uniq loc.

#[global] Definition mkClonedInternalName : Unique.Unique -> Name -> Name :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | uniq, Mk_Name _ occ _ loc => Mk_Name Internal occ uniq loc
    end.

#[global] Definition mkDerivedInternalName
   : (OccName.OccName -> OccName.OccName) -> Unique.Unique -> Name -> Name :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | derive_occ, uniq, Mk_Name _ occ _ loc =>
        Mk_Name Internal (derive_occ occ) uniq loc
    end.

#[global] Definition mkExternalName
   : Unique.Unique ->
     Module.Module -> OccName.OccName -> SrcLoc.SrcSpan -> Name :=
  fun uniq mod_ occ loc => Mk_Name (External mod_) occ uniq loc.

(* Skipping definition `Name.mkWiredInName' *)

#[global] Definition mkSystemNameAt
   : Unique.Unique -> OccName.OccName -> SrcLoc.SrcSpan -> Name :=
  fun uniq occ loc => Mk_Name System occ uniq loc.

#[global] Definition mkSystemName : Unique.Unique -> OccName.OccName -> Name :=
  fun uniq occ => mkSystemNameAt uniq occ SrcLoc.noSrcSpan.

#[global] Definition mkSystemVarName
   : Unique.Unique -> FastString.FastString -> Name :=
  fun uniq fs => mkSystemName uniq (OccName.mkVarOccFS fs).

#[global] Definition mkSysTvName
   : Unique.Unique -> FastString.FastString -> Name :=
  fun uniq fs => mkSystemName uniq (OccName.mkTyVarOccFS fs).

#[global] Definition mkFCallName
   : Unique.Unique -> FastString.FastString -> Name :=
  fun uniq str => mkInternalName uniq (OccName.mkVarOccFS str) SrcLoc.noSrcSpan.

#[global] Definition setNameUnique : Name -> Unique.Unique -> Name :=
  fun name uniq =>
    let 'Mk_Name n_sort_0__ n_occ_1__ n_uniq_2__ n_loc_3__ := name in
    Mk_Name n_sort_0__ n_occ_1__ uniq n_loc_3__.

#[global] Definition setNameLoc : Name -> SrcLoc.SrcSpan -> Name :=
  fun name loc =>
    let 'Mk_Name n_sort_0__ n_occ_1__ n_uniq_2__ n_loc_3__ := name in
    Mk_Name n_sort_0__ n_occ_1__ n_uniq_2__ loc.

#[global] Definition tidyNameOcc : Name -> OccName.OccName -> Name :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_Name System _ _ _ as name), occ =>
        let 'Mk_Name n_sort_2__ n_occ_3__ n_uniq_4__ n_loc_5__ := name in
        Mk_Name Internal occ n_uniq_4__ n_loc_5__
    | name, occ =>
        let 'Mk_Name n_sort_9__ n_occ_10__ n_uniq_11__ n_loc_12__ := name in
        Mk_Name n_sort_9__ occ n_uniq_11__ n_loc_12__
    end.

#[global] Definition localiseName : Name -> Name :=
  fun '(Mk_Name n_sort_0__ n_occ_1__ n_uniq_2__ n_loc_3__) =>
    Mk_Name Internal n_occ_1__ n_uniq_2__ n_loc_3__.

(* Skipping definition `Name.stableNameCmp' *)

(* Skipping definition `Name.pprName' *)

(* Skipping definition `Name.pprFullName' *)

(* Skipping definition `Name.pprTickyName' *)

(* Skipping definition `Name.pprNameUnqualified' *)

(* Skipping definition `Name.pprExternal' *)

(* Skipping definition `Name.pprInternal' *)

(* Skipping definition `Name.pprSystem' *)

(* Skipping definition `Name.pprModulePrefix' *)

(* Skipping definition `Name.pprUnique' *)

(* Skipping definition `Name.ppr_underscore_unique' *)

(* Skipping definition `Name.ppr_occ_name' *)

(* Skipping definition `Name.pprDefinedAt' *)

(* Skipping definition `Name.pprNameDefnLoc' *)

(* Skipping definition `Name.nameStableString' *)

(* Skipping definition `Name.nameSortStableString' *)

#[global] Definition getSrcLoc {a : Type} `{NamedThing a}
   : a -> SrcLoc.SrcLoc :=
  nameSrcLoc GHC.Base.∘ getName.

#[global] Definition getSrcSpan {a : Type} `{NamedThing a}
   : a -> SrcLoc.SrcSpan :=
  nameSrcSpan GHC.Base.∘ getName.

#[global] Definition getOccString {a : Type} `{NamedThing a}
   : a -> GHC.Base.String :=
  OccName.occNameString GHC.Base.∘ getOccName.

#[global] Definition getOccFS {a : Type} `{NamedThing a}
   : a -> FastString.FastString :=
  OccName.occNameFS GHC.Base.∘ getOccName.

(* Skipping definition `Name.pprInfixName' *)

(* Skipping definition `Name.pprPrefixName' *)

(* External variables:
     Gt Lt None Some Type andb bool comparison default false negb option orb true
     FastString.FastString GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String
     GHC.Base.compare__ GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zl____ GHC.Base.op_zlze____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Types.TyThing.TyThing HsToRocq.Err.Build_Default HsToRocq.Err.Default
     Maybes.orElse Module.Module Module.isInteractiveModule Module.moduleUnit
     OccName.HasOccName OccName.NameSpace OccName.OccName OccName.isDataOcc
     OccName.isFieldOcc OccName.isTcOcc OccName.isTvOcc OccName.isValOcc
     OccName.isVarOcc OccName.mkTyVarOccFS OccName.mkVarOccFS OccName.occNameFS
     OccName.occNameSpace OccName.occNameString OccName.occName__ Panic.panic
     SrcLoc.Located SrcLoc.SrcLoc SrcLoc.SrcSpan SrcLoc.noSrcSpan SrcLoc.srcSpanStart
     SrcLoc.unLoc Unique.Uniquable Unique.Unique Unique.getUnique__
     Unique.nonDetCmpUnique
*)
