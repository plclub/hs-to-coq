(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Data.Foldable.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require HsToCoq.Err.
Require UniqFM.
Require UniqSet.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition TidyOccEnv :=
  (UniqFM.UniqFM GHC.Num.Int)%type.

Inductive OccEnv a : Type := | A : (UniqFM.UniqFM a) -> OccEnv a.

Inductive NameSpace : Type :=
  | VarName : NameSpace
  | DataName : NameSpace
  | TvName : NameSpace
  | TcClsName : NameSpace.

Inductive OccName : Type :=
  | Mk_OccName (occNameSpace : NameSpace) (occNameFS : FastString.FastString)
   : OccName.

Definition OccSet :=
  (UniqSet.UniqSet OccName)%type.

Record HasOccName__Dict (name : Type) := HasOccName__Dict_Build {
  occName__ : name -> OccName }.

Definition HasOccName (name : Type) :=
  forall r__, (HasOccName__Dict name -> r__) -> r__.
Existing Class HasOccName.

Definition occName `{g__0__ : HasOccName name} : name -> OccName :=
  g__0__ _ (occName__ name).

Arguments A {_} _.

Instance Default__NameSpace : HsToCoq.Err.Default NameSpace :=
  HsToCoq.Err.Build_Default _ VarName.

Definition occNameFS (arg_0__ : OccName) :=
  let 'Mk_OccName _ occNameFS := arg_0__ in
  occNameFS.

Definition occNameSpace (arg_0__ : OccName) :=
  let 'Mk_OccName occNameSpace _ := arg_0__ in
  occNameSpace.

(* Midamble *)

Require Import HsToCoq.Err.

Instance Default__OccName : Default OccName := 
    Build_Default _ (Mk_OccName default default).

(* Converted value declarations: *)

Local Definition Eq___NameSpace_op_zeze__ : NameSpace -> NameSpace -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | VarName, VarName => true
    | DataName, DataName => true
    | TvName, TvName => true
    | TcClsName, TcClsName => true
    | _, _ => false
    end.

Local Definition Eq___NameSpace_op_zsze__ : NameSpace -> NameSpace -> bool :=
  fun x y => negb (Eq___NameSpace_op_zeze__ x y).

Program Instance Eq___NameSpace : GHC.Base.Eq_ NameSpace :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___NameSpace_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___NameSpace_op_zsze__ |}.

Local Definition Ord__NameSpace_compare
   : NameSpace -> NameSpace -> comparison :=
  fun x y =>
    match x, y with
    | VarName, VarName => Eq
    | VarName, _ => Lt
    | _, VarName => Gt
    | DataName, DataName => Eq
    | _, DataName => Lt
    | DataName, _ => Gt
    | TvName, TvName => Eq
    | _, TvName => Lt
    | TvName, _ => Gt
    | TcClsName, TcClsName => Eq
    end.

Local Definition Ord__NameSpace_op_zl__ : NameSpace -> NameSpace -> bool :=
  fun x y => match Ord__NameSpace_compare x y with | Lt => true | _ => false end.

Local Definition Ord__NameSpace_op_zlze__ : NameSpace -> NameSpace -> bool :=
  fun x y =>
    match Ord__NameSpace_compare x y with
    | Lt => true
    | Eq => true
    | _ => false
    end.

Local Definition Ord__NameSpace_op_zg__ : NameSpace -> NameSpace -> bool :=
  fun x y => match Ord__NameSpace_compare x y with | Gt => true | _ => false end.

Local Definition Ord__NameSpace_op_zgze__ : NameSpace -> NameSpace -> bool :=
  fun x y =>
    match Ord__NameSpace_compare x y with
    | Gt => true
    | Eq => true
    | _ => false
    end.

Local Definition Ord__NameSpace_max : NameSpace -> NameSpace -> NameSpace :=
  fun x y => if Ord__NameSpace_op_zlze__ x y : bool then y else x.

Local Definition Ord__NameSpace_min : NameSpace -> NameSpace -> NameSpace :=
  fun x y => if Ord__NameSpace_op_zlze__ x y : bool then x else y.

Program Instance Ord__NameSpace : GHC.Base.Ord NameSpace :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__NameSpace_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__NameSpace_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__NameSpace_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__NameSpace_op_zgze__ ;
           GHC.Base.compare__ := Ord__NameSpace_compare ;
           GHC.Base.max__ := Ord__NameSpace_max ;
           GHC.Base.min__ := Ord__NameSpace_min |}.

(* Skipping all instances of class `Data.Data.Data', including
   `OccName.Data__OccEnv' *)

Local Definition Eq___OccName_op_zeze__ : OccName -> OccName -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OccName sp1 s1, Mk_OccName sp2 s2 =>
        andb (s1 GHC.Base.== s2) (sp1 GHC.Base.== sp2)
    end.

Local Definition Eq___OccName_op_zsze__ : OccName -> OccName -> bool :=
  fun x y => negb (Eq___OccName_op_zeze__ x y).

Program Instance Eq___OccName : GHC.Base.Eq_ OccName :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___OccName_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___OccName_op_zsze__ |}.

Local Definition Ord__OccName_compare : OccName -> OccName -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OccName sp1 s1, Mk_OccName sp2 s2 =>
        Util.thenCmp (GHC.Base.compare s1 s2) (GHC.Base.compare sp1 sp2)
    end.

Local Definition Ord__OccName_op_zl__ : OccName -> OccName -> bool :=
  fun x y => Ord__OccName_compare x y GHC.Base.== Lt.

Local Definition Ord__OccName_op_zlze__ : OccName -> OccName -> bool :=
  fun x y => Ord__OccName_compare x y GHC.Base./= Gt.

Local Definition Ord__OccName_op_zg__ : OccName -> OccName -> bool :=
  fun x y => Ord__OccName_compare x y GHC.Base.== Gt.

Local Definition Ord__OccName_op_zgze__ : OccName -> OccName -> bool :=
  fun x y => Ord__OccName_compare x y GHC.Base./= Lt.

Local Definition Ord__OccName_max : OccName -> OccName -> OccName :=
  fun x y => if Ord__OccName_op_zlze__ x y : bool then y else x.

Local Definition Ord__OccName_min : OccName -> OccName -> OccName :=
  fun x y => if Ord__OccName_op_zlze__ x y : bool then x else y.

Program Instance Ord__OccName : GHC.Base.Ord OccName :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__OccName_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__OccName_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__OccName_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__OccName_op_zgze__ ;
           GHC.Base.compare__ := Ord__OccName_compare ;
           GHC.Base.max__ := Ord__OccName_max ;
           GHC.Base.min__ := Ord__OccName_min |}.

(* Skipping all instances of class `Data.Data.Data', including
   `OccName.Data__OccName' *)

Local Definition HasOccName__OccName_occName : OccName -> OccName :=
  GHC.Base.id.

Program Instance HasOccName__OccName : HasOccName OccName :=
  fun _ k__ => k__ {| occName__ := HasOccName__OccName_occName |}.

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `OccName.NFData__OccName' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccName.Outputable__OccName' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `OccName.OutputableBndr__OccName' *)

Local Definition Uniquable__OccName_getUnique : OccName -> Unique.Unique :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName VarName fs => Unique.mkVarOccUnique fs
    | Mk_OccName DataName fs => Unique.mkDataOccUnique fs
    | Mk_OccName TvName fs => Unique.mkTvOccUnique fs
    | Mk_OccName TcClsName fs => Unique.mkTcOccUnique fs
    end.

Program Instance Uniquable__OccName : Unique.Uniquable OccName :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__OccName_getUnique |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `OccName.Outputable__OccEnv' *)

(* Skipping all instances of class `Binary.Binary', including
   `OccName.Binary__NameSpace' *)

(* Skipping all instances of class `Binary.Binary', including
   `OccName.Binary__OccName' *)

Definition tcName : NameSpace :=
  TcClsName.

Definition clsName : NameSpace :=
  TcClsName.

Definition tcClsName : NameSpace :=
  TcClsName.

Definition dataName : NameSpace :=
  DataName.

Definition srcDataName : NameSpace :=
  DataName.

Definition tvName : NameSpace :=
  TvName.

Definition varName : NameSpace :=
  VarName.

Definition isDataConNameSpace : NameSpace -> bool :=
  fun arg_0__ => match arg_0__ with | DataName => true | _ => false end.

Definition isTcClsNameSpace : NameSpace -> bool :=
  fun arg_0__ => match arg_0__ with | TcClsName => true | _ => false end.

Definition isTvNameSpace : NameSpace -> bool :=
  fun arg_0__ => match arg_0__ with | TvName => true | _ => false end.

Definition isVarNameSpace : NameSpace -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TvName => true
    | VarName => true
    | _ => false
    end.

Definition isValNameSpace : NameSpace -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | DataName => true
    | VarName => true
    | _ => false
    end.

(* Skipping definition `OccName.pprNameSpace' *)

(* Skipping definition `OccName.pprNonVarNameSpace' *)

(* Skipping definition `OccName.pprNameSpaceBrief' *)

Definition demoteNameSpace : NameSpace -> option NameSpace :=
  fun arg_0__ =>
    match arg_0__ with
    | VarName => None
    | DataName => None
    | TvName => None
    | TcClsName => Some DataName
    end.

(* Skipping definition `OccName.pprOccName' *)

Definition mkOccName : NameSpace -> GHC.Base.String -> OccName :=
  fun occ_sp str => Mk_OccName occ_sp (FastString.mkFastString str).

Definition mkOccNameFS : NameSpace -> FastString.FastString -> OccName :=
  fun occ_sp fs => Mk_OccName occ_sp fs.

Definition mkVarOcc : GHC.Base.String -> OccName :=
  fun s => mkOccName varName s.

Definition mkVarOccFS : FastString.FastString -> OccName :=
  fun fs => mkOccNameFS varName fs.

Definition mkDataOcc : GHC.Base.String -> OccName :=
  mkOccName dataName.

Definition mkDataOccFS : FastString.FastString -> OccName :=
  mkOccNameFS dataName.

Definition mkTyVarOcc : GHC.Base.String -> OccName :=
  mkOccName tvName.

Definition mkTyVarOccFS : FastString.FastString -> OccName :=
  fun fs => mkOccNameFS tvName fs.

Definition mkTcOcc : GHC.Base.String -> OccName :=
  mkOccName tcName.

Definition mkTcOccFS : FastString.FastString -> OccName :=
  mkOccNameFS tcName.

Definition mkClsOcc : GHC.Base.String -> OccName :=
  mkOccName clsName.

Definition mkClsOccFS : FastString.FastString -> OccName :=
  mkOccNameFS clsName.

Definition demoteOccName : OccName -> option OccName :=
  fun '(Mk_OccName space name) =>
    demoteNameSpace space GHC.Base.>>=
    (fun space' => GHC.Base.return_ (Mk_OccName space' name)).

Definition otherNameSpace : NameSpace -> NameSpace :=
  fun arg_0__ =>
    match arg_0__ with
    | VarName => DataName
    | DataName => VarName
    | TvName => TcClsName
    | TcClsName => TvName
    end.

Definition nameSpacesRelated : NameSpace -> NameSpace -> bool :=
  fun ns1 ns2 => orb (ns1 GHC.Base.== ns2) (otherNameSpace ns1 GHC.Base.== ns2).

Definition emptyOccEnv {a : Type} : OccEnv a :=
  A UniqFM.emptyUFM.

Definition unitOccSet : OccName -> OccSet :=
  UniqSet.unitUniqSet.

Definition unitOccEnv {a : Type} : OccName -> a -> OccEnv a :=
  fun x y => A (UniqFM.unitUFM x y).

Definition mkOccSet : list OccName -> OccSet :=
  UniqSet.mkUniqSet.

Definition mkOccEnv_C {a : Type}
   : (a -> a -> a) -> list (OccName * a)%type -> OccEnv a :=
  fun comb l => A (UniqFM.addListToUFM_C comb UniqFM.emptyUFM l).

Definition mkOccEnv {a : Type} : list (OccName * a)%type -> OccEnv a :=
  fun l => A (UniqFM.listToUFM l).

Definition lookupOccEnv {a : Type} : OccEnv a -> OccName -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | A x, y => UniqFM.lookupUFM x y
    end.

Definition initTidyOccEnv : list OccName -> TidyOccEnv :=
  let add :=
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | env, Mk_OccName _ fs => UniqFM.addToUFM env fs #1
      end in
  Data.Foldable.foldl add UniqFM.emptyUFM.

Definition foldOccEnv {a : Type} {b : Type}
   : (a -> b -> b) -> b -> OccEnv a -> b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | a, b, A c => UniqFM.foldUFM a b c
    end.

Definition filterOccSet : (OccName -> bool) -> OccSet -> OccSet :=
  UniqSet.filterUniqSet.

Definition extendOccSetList : OccSet -> list OccName -> OccSet :=
  UniqSet.addListToUniqSet.

Definition extendOccSet : OccSet -> OccName -> OccSet :=
  UniqSet.addOneToUniqSet.

Definition extendOccEnv_C {a : Type}
   : (a -> a -> a) -> OccEnv a -> OccName -> a -> OccEnv a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, A x, y, z => A (UniqFM.addToUFM_C f x y z)
    end.

Definition extendOccEnv_Acc {a : Type} {b : Type}
   : (a -> b -> b) -> (a -> b) -> OccEnv b -> OccName -> a -> OccEnv b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | f, g, A x, y, z => A (UniqFM.addToUFM_Acc f g x y z)
    end.

Definition extendOccEnvList {a : Type}
   : OccEnv a -> list (OccName * a)%type -> OccEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | A x, l => A (UniqFM.addListToUFM x l)
    end.

Definition extendOccEnv {a : Type} : OccEnv a -> OccName -> a -> OccEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | A x, y, z => A (UniqFM.addToUFM x y z)
    end.

Definition elemOccEnv {a : Type} : OccName -> OccEnv a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, A y => UniqFM.elemUFM x y
    end.

Definition occEnvElts {a : Type} : OccEnv a -> list a :=
  fun '(A x) => UniqFM.eltsUFM x.

Definition plusOccEnv {a : Type} : OccEnv a -> OccEnv a -> OccEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | A x, A y => A (UniqFM.plusUFM x y)
    end.

Definition plusOccEnv_C {a : Type}
   : (a -> a -> a) -> OccEnv a -> OccEnv a -> OccEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, A x, A y => A (UniqFM.plusUFM_C f x y)
    end.

Definition mapOccEnv {a : Type} {b : Type} : (a -> b) -> OccEnv a -> OccEnv b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, A x => A (UniqFM.mapUFM f x)
    end.

Definition delFromOccEnv {a : Type} : OccEnv a -> OccName -> OccEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | A x, y => A (UniqFM.delFromUFM x y)
    end.

Definition delListFromOccEnv {a : Type}
   : OccEnv a -> list OccName -> OccEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | A x, y => A (UniqFM.delListFromUFM x y)
    end.

Definition filterOccEnv {elt : Type}
   : (elt -> bool) -> OccEnv elt -> OccEnv elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, A y => A (UniqFM.filterUFM x y)
    end.

Definition alterOccEnv {elt : Type}
   : (option elt -> option elt) -> OccEnv elt -> OccName -> OccEnv elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | fn, A y, k => A (UniqFM.alterUFM fn y k)
    end.

(* Skipping definition `OccName.pprOccEnv' *)

Definition emptyOccSet : OccSet :=
  UniqSet.emptyUniqSet.

Definition unionOccSets : OccSet -> OccSet -> OccSet :=
  UniqSet.unionUniqSets.

Definition unionManyOccSets : list OccSet -> OccSet :=
  UniqSet.unionManyUniqSets.

Definition minusOccSet : OccSet -> OccSet -> OccSet :=
  UniqSet.minusUniqSet.

Definition elemOccSet : OccName -> OccSet -> bool :=
  UniqSet.elementOfUniqSet.

Definition isEmptyOccSet : OccSet -> bool :=
  UniqSet.isEmptyUniqSet.

Definition intersectOccSet : OccSet -> OccSet -> OccSet :=
  UniqSet.intersectUniqSets.

Definition intersectsOccSet : OccSet -> OccSet -> bool :=
  fun s1 s2 => negb (isEmptyOccSet (intersectOccSet s1 s2)).

Definition occNameString : OccName -> GHC.Base.String :=
  fun '(Mk_OccName _ s) => FastString.unpackFS s.

Definition setOccNameSpace : NameSpace -> OccName -> OccName :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | sp, Mk_OccName _ occ => Mk_OccName sp occ
    end.

Definition isVarOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName VarName _ => true
    | _ => false
    end.

Definition isTvOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName TvName _ => true
    | _ => false
    end.

Definition isTcOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName TcClsName _ => true
    | _ => false
    end.

Definition isValOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName VarName _ => true
    | Mk_OccName DataName _ => true
    | _ => false
    end.

Definition isDataOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName DataName _ => true
    | _ => false
    end.

Axiom isDataSymOcc : OccName -> bool.

Axiom isSymOcc : OccName -> bool.

(* Skipping definition `OccName.parenSymOcc' *)

Axiom startsWithUnderscore : OccName -> bool.

Definition mk_deriv
   : NameSpace ->
     FastString.FastString -> list FastString.FastString -> OccName :=
  fun occ_sp sys_prefix str =>
    mkOccNameFS occ_sp (FastString.concatFS (cons sys_prefix str)).

Axiom isDerivedOccName : OccName -> bool.

Axiom isDefaultMethodOcc : OccName -> bool.

Axiom isTypeableBindOcc : OccName -> bool.

Definition mk_simple_deriv
   : NameSpace -> FastString.FastString -> OccName -> OccName :=
  fun sp px occ => mk_deriv sp px (cons (occNameFS occ) nil).

Definition mkDataConWrapperOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$W").

Definition mkWorkerOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$w").

Definition mkMatcherOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$m").

Definition mkBuilderOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$b").

Definition mkDefaultMethodOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$dm").

Definition mkClassOpAuxOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$c").

Definition mkDictOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$d").

Definition mkIPOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$i").

Definition mkSpecOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$s").

Definition mkForeignExportOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$f").

Definition mkRepEqOcc : OccName -> OccName :=
  mk_simple_deriv tvName (GHC.Base.hs_string__ "$r").

Definition mkClassDataConOcc : OccName -> OccName :=
  mk_simple_deriv dataName (GHC.Base.hs_string__ "C:").

Definition mkNewTyCoOcc : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "N:").

Definition mkInstTyCoOcc : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "D:").

Definition mkEqPredCoOcc : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "$co").

Definition mkCon2TagOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$con2tag_").

Definition mkTag2ConOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$tag2con_").

Definition mkMaxTagOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$maxtag_").

Definition mkTyConRepOcc : OccName -> OccName :=
  fun occ =>
    let prefix :=
      if isDataOcc occ : bool then GHC.Base.hs_string__ "$tc'" else
      GHC.Base.hs_string__ "$tc" in
    mk_simple_deriv varName prefix occ.

Definition mkGenR : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "Rep_").

Definition mkGen1R : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "Rep1_").

Definition mk_simple_deriv_with
   : NameSpace ->
     FastString.FastString -> option GHC.Base.String -> OccName -> OccName :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | sp, px, None, occ => mk_deriv sp px (cons (occNameFS occ) nil)
    | sp, px, Some with_, occ =>
        mk_deriv sp px (cons (FastString.fsLit with_) (cons (FastString.fsLit
                                                             (GHC.Base.hs_string__ "_")) (cons (occNameFS occ) nil)))
    end.

Definition mkVectOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with varName (GHC.Base.hs_string__ "$v").

Definition mkVectTyConOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with tcName (GHC.Base.hs_string__ "V:").

Definition mkVectDataConOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with dataName (GHC.Base.hs_string__ "VD:").

Definition mkVectIsoOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with varName (GHC.Base.hs_string__ "$vi").

Definition mkPADFunOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with varName (GHC.Base.hs_string__ "$pa").

Definition mkPReprTyConOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with tcName (GHC.Base.hs_string__ "VR:").

Definition mkPDataTyConOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with tcName (GHC.Base.hs_string__ "VP:").

Definition mkPDatasTyConOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with tcName (GHC.Base.hs_string__ "VPs:").

Definition mkPDataDataConOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with dataName (GHC.Base.hs_string__ "VPD:").

Definition mkPDatasDataConOcc : option GHC.Base.String -> OccName -> OccName :=
  mk_simple_deriv_with dataName (GHC.Base.hs_string__ "VPDs:").

Definition mkRecFldSelOcc : GHC.Base.String -> OccName :=
  fun s =>
    mk_deriv varName (GHC.Base.hs_string__ "$sel") (cons (FastString.fsLit s) nil).

Definition mkDataConWorkerOcc : OccName -> OccName :=
  fun datacon_occ => setOccNameSpace varName datacon_occ.

Axiom mkSuperDictAuxOcc : GHC.Num.Int -> OccName -> OccName.

Axiom mkSuperDictSelOcc : GHC.Num.Int -> OccName -> OccName.

Axiom mkLocalOcc : Unique.Unique -> OccName -> OccName.

Axiom chooseUniqueOcc : NameSpace -> GHC.Base.String -> OccSet -> OccName.

Definition mkInstTyTcOcc : GHC.Base.String -> OccSet -> OccName :=
  fun str =>
    chooseUniqueOcc tcName (cons (GHC.Char.hs_char__ "R") (cons (GHC.Char.hs_char__
                                                                 ":") str)).

Definition mkDFunOcc : GHC.Base.String -> bool -> OccSet -> OccName :=
  fun info_str is_boot set =>
    let prefix :=
      if is_boot : bool then GHC.Base.hs_string__ "$fx" else
      GHC.Base.hs_string__ "$f" in
    chooseUniqueOcc VarName (Coq.Init.Datatypes.app prefix info_str) set.

Definition mkDataTOcc : OccName -> OccSet -> OccName :=
  fun occ =>
    chooseUniqueOcc VarName (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "$t")
                                                    (occNameString occ)).

Definition mkDataCOcc : OccName -> OccSet -> OccName :=
  fun occ =>
    chooseUniqueOcc VarName (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "$c")
                                                    (occNameString occ)).

Definition mkMethodOcc : OccName -> OccName :=
  fun arg_0__ =>
    match arg_0__ with
    | (Mk_OccName VarName _ as occ) => occ
    | occ => mk_simple_deriv varName (GHC.Base.hs_string__ "$m") occ
    end.

Definition emptyTidyOccEnv : TidyOccEnv :=
  UniqFM.emptyUFM.

Definition avoidClashesOccEnv : TidyOccEnv -> list OccName -> TidyOccEnv :=
  fun env occs =>
    let fix go arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | env, _, nil => env
         | env, seenOnce, cons (Mk_OccName _ fs) occs =>
             if UniqFM.elemUFM fs env : bool then go env seenOnce occs else
             if UniqFM.elemUFM fs seenOnce : bool
             then go (UniqFM.addToUFM env fs #1) seenOnce occs else
             go env (UniqFM.addToUFM seenOnce fs tt) occs
         end in
    go env UniqFM.emptyUFM occs.

Axiom tidyOccName : TidyOccEnv -> OccName -> (TidyOccEnv * OccName)%type.

(* External variables:
     Eq Gt Lt None Some Type andb bool comparison cons false list negb nil op_zt__
     option orb true tt Coq.Init.Datatypes.app Data.Foldable.foldl
     FastString.FastString FastString.concatFS FastString.fsLit
     FastString.mkFastString FastString.unpackFS GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.String GHC.Base.compare GHC.Base.compare__ GHC.Base.id GHC.Base.max__
     GHC.Base.min__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____
     GHC.Base.op_zgze____ GHC.Base.op_zgzgze__ GHC.Base.op_zl____
     GHC.Base.op_zlze____ GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.return_
     GHC.Num.Int GHC.Num.fromInteger HsToCoq.Err.Build_Default HsToCoq.Err.Default
     UniqFM.UniqFM UniqFM.addListToUFM UniqFM.addListToUFM_C UniqFM.addToUFM
     UniqFM.addToUFM_Acc UniqFM.addToUFM_C UniqFM.alterUFM UniqFM.delFromUFM
     UniqFM.delListFromUFM UniqFM.elemUFM UniqFM.eltsUFM UniqFM.emptyUFM
     UniqFM.filterUFM UniqFM.foldUFM UniqFM.listToUFM UniqFM.lookupUFM UniqFM.mapUFM
     UniqFM.plusUFM UniqFM.plusUFM_C UniqFM.unitUFM UniqSet.UniqSet
     UniqSet.addListToUniqSet UniqSet.addOneToUniqSet UniqSet.elementOfUniqSet
     UniqSet.emptyUniqSet UniqSet.filterUniqSet UniqSet.intersectUniqSets
     UniqSet.isEmptyUniqSet UniqSet.minusUniqSet UniqSet.mkUniqSet
     UniqSet.unionManyUniqSets UniqSet.unionUniqSets UniqSet.unitUniqSet
     Unique.Uniquable Unique.Unique Unique.getUnique__ Unique.mkDataOccUnique
     Unique.mkTcOccUnique Unique.mkTvOccUnique Unique.mkVarOccUnique Util.thenCmp
*)
