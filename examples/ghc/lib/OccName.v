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
Require Data.Maybe.
Require FastString.
Require FastStringEnv.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require HsToCoq.Err.
Require UniqFM.
Require UniqSet.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

#[global] Definition TidyOccEnv :=
  (UniqFM.UniqFM FastString.FastString GHC.Num.Int)%type.

Inductive NameSpace : Type :=
  | VarName : NameSpace
  | FldName (fldParent : FastString.FastString) : NameSpace
  | DataName : NameSpace
  | TvName : NameSpace
  | TcClsName : NameSpace.

Inductive OccEnv a : Type :=
  | MkOccEnv
   : (FastStringEnv.FastStringEnv (UniqFM.UniqFM NameSpace a)) -> OccEnv a.

Inductive OccName : Type :=
  | Mk_OccName (occNameSpace : NameSpace) (occNameFS : FastString.FastString)
   : OccName.

Inductive OccSet : Type :=
  | Mk_OccSet
   : (FastStringEnv.FastStringEnv (UniqSet.UniqSet NameSpace)) -> OccSet.

Record HasOccName__Dict (name : Type) := HasOccName__Dict_Build {
  occName__ : name -> OccName }.

#[global] Definition HasOccName (name : Type) :=
  forall r__, (HasOccName__Dict name -> r__) -> r__.
Existing Class HasOccName.

#[global] Definition occName `{g__0__ : HasOccName name} : name -> OccName :=
  g__0__ _ (occName__ name).

Arguments MkOccEnv {_} _.

Instance Default__NameSpace : HsToCoq.Err.Default NameSpace :=
  HsToCoq.Err.Build_Default _ VarName.

#[global] Definition fldParent (arg_0__ : NameSpace) :=
  match arg_0__ with
  | VarName =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `fldParent' has no match in constructor `VarName' of type `NameSpace'")
  | FldName fldParent => fldParent
  | DataName =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `fldParent' has no match in constructor `DataName' of type `NameSpace'")
  | TvName =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `fldParent' has no match in constructor `TvName' of type `NameSpace'")
  | TcClsName =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `fldParent' has no match in constructor `TcClsName' of type `NameSpace'")
  end.

#[global] Definition occNameFS (arg_0__ : OccName) :=
  let 'Mk_OccName _ occNameFS := arg_0__ in
  occNameFS.

#[global] Definition occNameSpace (arg_0__ : OccName) :=
  let 'Mk_OccName occNameSpace _ := arg_0__ in
  occNameSpace.

(* Midamble *)

Require Import HsToCoq.Err.
Require Import Coq.NArith.BinNat.

Instance Default__OccName : Default OccName :=
    Build_Default _ (Mk_OccName default default).

(* GHC 9.10: FldName constructor added - need manual Eq instance *)
#[local] Definition Eq__NameSpace_op_zeze : NameSpace -> NameSpace -> bool :=
  fun x y => match x, y with
    | VarName, VarName => true
    | FldName a, FldName b => (a GHC.Base.== b)
    | DataName, DataName => true
    | TvName, TvName => true
    | TcClsName, TcClsName => true
    | _, _ => false
  end.

#[global]
Instance Eq___NameSpace : GHC.Base.Eq_ NameSpace :=
  fun _ k => k {|
    GHC.Base.op_zeze____ := Eq__NameSpace_op_zeze ;
    GHC.Base.op_zsze____ := fun x y => negb (Eq__NameSpace_op_zeze x y)
  |}.

(* GHC 9.10: Uniquable__NameSpace references GHC.Builtin.Uniques - provide stub *)
#[global]
Instance Uniquable__NameSpace : Unique.Uniquable NameSpace :=
  fun _ k => k {|
    Unique.getUnique__ := fun ns => match ns with
      | VarName   => Unique.mkUniqueGrimily 1%N
      | FldName _ => Unique.mkUniqueGrimily 2%N
      | DataName  => Unique.mkUniqueGrimily 3%N
      | TvName    => Unique.mkUniqueGrimily 4%N
      | TcClsName => Unique.mkUniqueGrimily 5%N
    end
  |}.

(* Converted value declarations: *)

#[local] Definition Functor__OccEnv_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> OccEnv a -> OccEnv b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkOccEnv a1 => MkOccEnv (GHC.Base.fmap (fun b1 => GHC.Base.fmap f b1) a1)
      end.

#[local] Definition Functor__OccEnv_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> OccEnv b -> OccEnv a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | z, MkOccEnv a1 =>
          MkOccEnv (GHC.Base.fmap (fun b1 => GHC.Base.op_zlzd__ z b1) a1)
      end.

#[global]
Program Instance Functor__OccEnv : GHC.Base.Functor OccEnv :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__OccEnv_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__OccEnv_op_zlzd__ |}.

#[local] Definition Ord__NameSpace_compare
   : NameSpace -> NameSpace -> comparison :=
  fun x y =>
    match x, y with
    | VarName, VarName => Eq
    | VarName, _ => Lt
    | _, VarName => Gt
    | FldName a, FldName b => GHC.Base.compare a b
    | FldName _, _ => Lt
    | _, FldName _ => Gt
    | DataName, DataName => Eq
    | _, DataName => Lt
    | DataName, _ => Gt
    | TvName, TvName => Eq
    | _, TvName => Lt
    | TvName, _ => Gt
    | TcClsName, TcClsName => Eq
    end.

#[local] Definition Ord__NameSpace_op_zl__ : NameSpace -> NameSpace -> bool :=
  fun x y => Ord__NameSpace_compare x y GHC.Base.== Lt.

#[local] Definition Ord__NameSpace_op_zlze__ : NameSpace -> NameSpace -> bool :=
  fun x y => Ord__NameSpace_compare x y GHC.Base./= Gt.

#[local] Definition Ord__NameSpace_op_zg__ : NameSpace -> NameSpace -> bool :=
  fun x y => Ord__NameSpace_compare x y GHC.Base.== Gt.

#[local] Definition Ord__NameSpace_op_zgze__ : NameSpace -> NameSpace -> bool :=
  fun x y => Ord__NameSpace_compare x y GHC.Base./= Lt.

#[local] Definition Ord__NameSpace_max : NameSpace -> NameSpace -> NameSpace :=
  fun x y => if Ord__NameSpace_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__NameSpace_min : NameSpace -> NameSpace -> NameSpace :=
  fun x y => if Ord__NameSpace_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__NameSpace : GHC.Base.Ord NameSpace :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__NameSpace_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__NameSpace_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__NameSpace_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__NameSpace_op_zgze__ ;
           GHC.Base.compare__ := Ord__NameSpace_compare ;
           GHC.Base.max__ := Ord__NameSpace_max ;
           GHC.Base.min__ := Ord__NameSpace_min |}.

(* Skipping instance `OccName.Uniquable__NameSpace' of class
   `Unique.Uniquable' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `OccName.NFData__NameSpace' *)

#[local] Definition Eq___OccName_op_zeze__ : OccName -> OccName -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OccName sp1 s1, Mk_OccName sp2 s2 =>
        andb (s1 GHC.Base.== s2) (sp1 GHC.Base.== sp2)
    end.

#[local] Definition Eq___OccName_op_zsze__ : OccName -> OccName -> bool :=
  fun x y => negb (Eq___OccName_op_zeze__ x y).

#[global]
Program Instance Eq___OccName : GHC.Base.Eq_ OccName :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___OccName_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___OccName_op_zsze__ |}.

#[local] Definition Ord__OccName_compare : OccName -> OccName -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OccName sp1 s1, Mk_OccName sp2 s2 =>
        FastString.lexicalCompareFS s1 s2 GHC.Base.<<>> GHC.Base.compare sp1 sp2
    end.

#[local] Definition Ord__OccName_op_zl__ : OccName -> OccName -> bool :=
  fun x y => Ord__OccName_compare x y GHC.Base.== Lt.

#[local] Definition Ord__OccName_op_zlze__ : OccName -> OccName -> bool :=
  fun x y => Ord__OccName_compare x y GHC.Base./= Gt.

#[local] Definition Ord__OccName_op_zg__ : OccName -> OccName -> bool :=
  fun x y => Ord__OccName_compare x y GHC.Base.== Gt.

#[local] Definition Ord__OccName_op_zgze__ : OccName -> OccName -> bool :=
  fun x y => Ord__OccName_compare x y GHC.Base./= Lt.

#[local] Definition Ord__OccName_max : OccName -> OccName -> OccName :=
  fun x y => if Ord__OccName_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__OccName_min : OccName -> OccName -> OccName :=
  fun x y => if Ord__OccName_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__OccName : GHC.Base.Ord OccName :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__OccName_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__OccName_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__OccName_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__OccName_op_zgze__ ;
           GHC.Base.compare__ := Ord__OccName_compare ;
           GHC.Base.max__ := Ord__OccName_max ;
           GHC.Base.min__ := Ord__OccName_min |}.

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `OccName.Data__OccName' *)

#[local] Definition HasOccName__OccName_occName : OccName -> OccName :=
  GHC.Base.id.

#[global]
Program Instance HasOccName__OccName : HasOccName OccName :=
  fun _ k__ => k__ {| occName__ := HasOccName__OccName_occName |}.

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `OccName.NFData__OccName' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccName.Outputable__OccName' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `OccName.OutputableBndr__OccName' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccName.Outputable__OccEnv' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `OccName.NFData__OccEnv' *)

(* Skipping all instances of class `Binary.Binary', including
   `OccName.Binary__NameSpace' *)

(* Skipping all instances of class `Binary.Binary', including
   `OccName.Binary__OccName' *)

#[global] Definition tcName : NameSpace :=
  TcClsName.

#[global] Definition clsName : NameSpace :=
  TcClsName.

#[global] Definition tcClsName : NameSpace :=
  TcClsName.

#[global] Definition dataName : NameSpace :=
  DataName.

#[global] Definition srcDataName : NameSpace :=
  DataName.

#[global] Definition tvName : NameSpace :=
  TvName.

#[global] Definition varName : NameSpace :=
  VarName.

#[global] Definition fieldName : FastString.FastString -> NameSpace :=
  FldName.

#[global] Definition isDataConNameSpace : NameSpace -> bool :=
  fun arg_0__ => match arg_0__ with | DataName => true | _ => false end.

#[global] Definition isTcClsNameSpace : NameSpace -> bool :=
  fun arg_0__ => match arg_0__ with | TcClsName => true | _ => false end.

#[global] Definition isTvNameSpace : NameSpace -> bool :=
  fun arg_0__ => match arg_0__ with | TvName => true | _ => false end.

#[global] Definition isVarNameSpace : NameSpace -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TvName => true
    | VarName => true
    | FldName _ => true
    | _ => false
    end.

#[global] Definition isTermVarOrFieldNameSpace : NameSpace -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | VarName => true
    | FldName _ => true
    | _ => false
    end.

#[global] Definition isValNameSpace : NameSpace -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | DataName => true
    | VarName => true
    | FldName _ => true
    | _ => false
    end.

#[global] Definition isFieldNameSpace : NameSpace -> bool :=
  fun arg_0__ => match arg_0__ with | FldName _ => true | _ => false end.

(* Skipping definition `OccName.pprNameSpace' *)

(* Skipping definition `OccName.pprNonVarNameSpace' *)

(* Skipping definition `OccName.pprNameSpaceBrief' *)

#[global] Definition demoteNameSpace : NameSpace -> option NameSpace :=
  fun arg_0__ =>
    match arg_0__ with
    | VarName => None
    | DataName => None
    | TvName => None
    | TcClsName => Some DataName
    | FldName _ => None
    end.

#[global] Definition demoteTvNameSpace : NameSpace -> option NameSpace :=
  fun arg_0__ =>
    match arg_0__ with
    | TvName => Some VarName
    | VarName => None
    | DataName => None
    | TcClsName => None
    | FldName _ => None
    end.

#[global] Definition promoteNameSpace : NameSpace -> option NameSpace :=
  fun arg_0__ =>
    match arg_0__ with
    | DataName => Some TcClsName
    | VarName => Some TvName
    | TcClsName => None
    | TvName => None
    | FldName _ => None
    end.

(* Skipping definition `OccName.pprOccName' *)

#[global] Definition occNameMangledFS : OccName -> FastString.FastString :=
  fun '(Mk_OccName ns fs) =>
    match ns with
    | FldName con =>
        FastString.concatFS (cons (FastString.fsLit (GHC.Base.hs_string__ "$fld:"))
                                  (cons con (cons (GHC.Base.hs_string__ ":") (cons fs nil))))
    | _ => fs
    end.

#[global] Definition mkOccName : NameSpace -> GHC.Base.String -> OccName :=
  fun occ_sp str => Mk_OccName occ_sp (FastString.mkFastString str).

#[global] Definition mkOccNameFS
   : NameSpace -> FastString.FastString -> OccName :=
  fun occ_sp fs => Mk_OccName occ_sp fs.

#[global] Definition mkVarOcc : GHC.Base.String -> OccName :=
  fun s => mkOccName varName s.

#[global] Definition mkVarOccFS : FastString.FastString -> OccName :=
  fun fs => mkOccNameFS varName fs.

#[global] Definition mkRecFieldOcc
   : FastString.FastString -> GHC.Base.String -> OccName :=
  fun dc => mkOccName (fieldName dc).

#[global] Definition mkRecFieldOccFS
   : FastString.FastString -> FastString.FastString -> OccName :=
  fun dc => mkOccNameFS (fieldName dc).

#[global] Definition varToRecFieldOcc `{Util.HasDebugCallStack}
   : FastString.FastString -> OccName -> OccName :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dc, Mk_OccName ns s =>
        let makes_sense :=
          match ns with
          | VarName => true
          | FldName _ => true
          | _ => false
          end in
        mkRecFieldOccFS dc s
    end.

#[global] Definition recFieldToVarOcc `{Util.HasDebugCallStack}
   : OccName -> OccName :=
  fun '(Mk_OccName _ns s) => mkVarOccFS s.

#[global] Definition mkDataOcc : GHC.Base.String -> OccName :=
  mkOccName dataName.

#[global] Definition mkDataOccFS : FastString.FastString -> OccName :=
  mkOccNameFS dataName.

#[global] Definition mkTyVarOcc : GHC.Base.String -> OccName :=
  mkOccName tvName.

#[global] Definition mkTyVarOccFS : FastString.FastString -> OccName :=
  fun fs => mkOccNameFS tvName fs.

#[global] Definition mkTcOcc : GHC.Base.String -> OccName :=
  mkOccName tcName.

#[global] Definition mkTcOccFS : FastString.FastString -> OccName :=
  mkOccNameFS tcName.

#[global] Definition mkClsOcc : GHC.Base.String -> OccName :=
  mkOccName clsName.

#[global] Definition mkClsOccFS : FastString.FastString -> OccName :=
  mkOccNameFS clsName.

#[global] Definition demoteOccName : OccName -> option OccName :=
  fun '(Mk_OccName space name) =>
    demoteNameSpace space GHC.Base.>>=
    (fun space' => GHC.Base.return_ (Mk_OccName space' name)).

#[global] Definition demoteOccTvName : OccName -> option OccName :=
  fun '(Mk_OccName space name) =>
    demoteTvNameSpace space GHC.Base.>>=
    (fun space' => GHC.Base.return_ (Mk_OccName space' name)).

(* Skipping definition `OccName.promoteOccName' *)

#[global] Definition emptyOccEnv {a : Type} : OccEnv a :=
  MkOccEnv FastStringEnv.emptyFsEnv.

#[global] Definition extendOccEnv {a : Type}
   : OccEnv a -> OccName -> a -> OccEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | MkOccEnv as_, Mk_OccName ns s, a =>
        MkOccEnv (FastStringEnv.extendFsEnv_C UniqFM.plusUFM as_ s (UniqFM.unitUFM ns
                                               a))
    end.

#[global] Definition unitOccSet : OccName -> OccSet :=
  fun '(Mk_OccName ns s) =>
    Mk_OccSet (FastStringEnv.unitFsEnv s (UniqSet.unitUniqSet ns)).

#[global] Definition unitOccEnv {a : Type} : OccName -> a -> OccEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OccName ns s, a =>
        MkOccEnv (FastStringEnv.unitFsEnv s (UniqFM.unitUFM ns a))
    end.

#[global] Definition extendOccEnv_Acc {a : Type} {b : Type}
   : (a -> b -> b) -> (a -> b) -> OccEnv b -> OccName -> a -> OccEnv b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, g, MkOccEnv env, Mk_OccName ns s =>
        let g' := fun a => UniqFM.unitUFM ns (g a) in
        let f' : a -> UniqFM.UniqFM NameSpace b -> UniqFM.UniqFM NameSpace b :=
          fun a bs =>
            UniqFM.alterUFM (Some GHC.Base.∘
                             (fun arg_5__ => match arg_5__ with | None => g a | Some b => f a b end)) bs
            ns in
        MkOccEnv GHC.Base.∘ FastStringEnv.extendFsEnv_Acc f' g' env s
    end.

#[global] Definition extendOccEnvList {a : Type}
   : OccEnv a -> list (OccName * a)%type -> OccEnv a :=
  Data.Foldable.foldl' (fun arg_0__ arg_1__ =>
                          match arg_0__, arg_1__ with
                          | env, pair occ a => extendOccEnv env occ a
                          end).

#[global] Definition emptyOccSet : OccSet :=
  Mk_OccSet FastStringEnv.emptyFsEnv.

#[global] Definition extendOccSet : OccSet -> OccName -> OccSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OccSet occs, Mk_OccName ns s =>
        Mk_OccSet (FastStringEnv.extendFsEnv occs s (UniqSet.unitUniqSet ns))
    end.

#[global] Definition extendOccSetList : OccSet -> list OccName -> OccSet :=
  Data.Foldable.foldl' extendOccSet.

#[global] Definition mkOccSet : list OccName -> OccSet :=
  extendOccSetList emptyOccSet.

#[global] Definition mkOccEnv_C {a : Type}
   : (a -> a -> a) -> list (OccName * a)%type -> OccEnv a :=
  fun f elts =>
    let g :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | env, pair (Mk_OccName ns s) a =>
            FastStringEnv.extendFsEnv_C (UniqFM.plusUFM_C (GHC.Base.flip f)) env s
            (UniqFM.unitUFM ns a)
        end in
    MkOccEnv (Data.Foldable.foldl' g FastStringEnv.emptyFsEnv elts).

#[global] Definition mkOccEnv {a : Type}
   : list (OccName * a)%type -> OccEnv a :=
  extendOccEnvList emptyOccEnv.

#[global] Definition lookupOccEnv {a : Type}
   : OccEnv a -> OccName -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkOccEnv as_, Mk_OccName ns s =>
        FastStringEnv.lookupFsEnv as_ s GHC.Base.>>= (fun m => UniqFM.lookupUFM m ns)
    end.

#[global] Definition lookupOccEnv_AllNameSpaces {a : Type}
   : OccEnv a -> OccName -> list a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkOccEnv as_, Mk_OccName _ s =>
        match FastStringEnv.lookupFsEnv as_ s with
        | None => nil
        | Some r => UniqFM.nonDetEltsUFM r
        end
    end.

(* Skipping definition `OccName.lookupOccEnv_WithFields' *)

(* Skipping definition `OccName.lookupFieldsOccEnv' *)

#[global] Definition elemOccEnv {a : Type} : OccName -> OccEnv a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OccName ns s, MkOccEnv as_ =>
        match FastStringEnv.lookupFsEnv as_ s with
        | None => false
        | Some m => UniqFM.elemUFM ns m
        end
    end.

#[global] Definition nonDetFoldOccEnv {a : Type} {b : Type}
   : (a -> b -> b) -> b -> OccEnv a -> b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, b0, MkOccEnv as_ =>
        FastStringEnv.nonDetFoldFsEnv (GHC.Base.flip (UniqFM.nonDetFoldUFM f)) b0 as_
    end.

#[global] Definition nonDetOccEnvElts {a : Type} : OccEnv a -> list a :=
  nonDetFoldOccEnv cons nil.

#[global] Definition plusOccEnv {a : Type} : OccEnv a -> OccEnv a -> OccEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkOccEnv env1, MkOccEnv env2 =>
        MkOccEnv (FastStringEnv.plusFsEnv_C UniqFM.plusUFM env1 env2)
    end.

#[global] Definition plusOccEnv_C {a : Type}
   : (a -> a -> a) -> OccEnv a -> OccEnv a -> OccEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, MkOccEnv env1, MkOccEnv env2 =>
        MkOccEnv (FastStringEnv.plusFsEnv_C (UniqFM.plusUFM_C f) env1 env2)
    end.

#[global] Definition mapOccEnv {a : Type} {b : Type}
   : (a -> b) -> OccEnv a -> OccEnv b :=
  GHC.Base.fmap.

#[global] Definition mapMaybeOccEnv {a : Type} {b : Type}
   : (a -> option b) -> OccEnv a -> OccEnv b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MkOccEnv env =>
        let g :=
          fun as_ =>
            let 'm' := UniqFM.mapMaybeUFM f as_ in
            if UniqFM.isNullUFM m' : bool then None else
            Some m' in
        MkOccEnv (UniqFM.mapMaybeUFM g env)
    end.

#[global] Definition delFromOccEnv {a : Type}
   : OccEnv a -> OccName -> OccEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkOccEnv env1, Mk_OccName ns s =>
        let f
         : option (UniqFM.UniqFM NameSpace a) -> option (UniqFM.UniqFM NameSpace a) :=
          fun arg_2__ =>
            match arg_2__ with
            | None => None
            | Some m =>
                let 'm' := UniqFM.delFromUFM m ns in
                if UniqFM.isNullUFM m' : bool then None else
                Some m'
            end in
        MkOccEnv (FastStringEnv.alterFsEnv f env1 s)
    end.

#[global] Definition delListFromOccEnv {a : Type}
   : OccEnv a -> list OccName -> OccEnv a :=
  Data.Foldable.foldl' delFromOccEnv.

#[global] Definition filterOccEnv {a : Type}
   : (a -> bool) -> OccEnv a -> OccEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MkOccEnv env =>
        let g : UniqFM.UniqFM NameSpace a -> option (UniqFM.UniqFM NameSpace a) :=
          fun ms =>
            let 'm' := UniqFM.filterUFM f ms in
            if UniqFM.isNullUFM m' : bool then None else
            Some m' in
        MkOccEnv (FastStringEnv.mapMaybeFsEnv g env)
    end.

#[global] Definition alterOccEnv {a : Type}
   : (option a -> option a) -> OccEnv a -> OccName -> OccEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, MkOccEnv env, Mk_OccName ns s =>
        let g
         : option (UniqFM.UniqFM NameSpace a) -> option (UniqFM.UniqFM NameSpace a) :=
          fun arg_3__ =>
            match arg_3__ with
            | None => GHC.Base.fmap (UniqFM.unitUFM ns) (f None)
            | Some m =>
                let 'm' := UniqFM.alterUFM f m ns in
                if UniqFM.isNullUFM m' : bool then None else
                Some m'
            end in
        MkOccEnv (FastStringEnv.alterFsEnv g env s)
    end.

#[global] Definition intersectOccEnv_C {a : Type} {b : Type} {c : Type}
   : (a -> b -> c) -> OccEnv a -> OccEnv b -> OccEnv c :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, MkOccEnv as_, MkOccEnv bs =>
        MkOccEnv (UniqFM.intersectUFM_C (UniqFM.intersectUFM_C f) as_ bs)
    end.

#[global] Definition minusOccEnv_C_Ns {a : Type} {b : Type}
   : (UniqFM.UniqFM NameSpace a ->
      UniqFM.UniqFM NameSpace b -> UniqFM.UniqFM NameSpace a) ->
     OccEnv a -> OccEnv b -> OccEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, MkOccEnv as_, MkOccEnv bs =>
        let g
         : UniqFM.UniqFM NameSpace a ->
           UniqFM.UniqFM NameSpace b -> option (UniqFM.UniqFM NameSpace a) :=
          fun as_ bs =>
            let m := f as_ bs in if UniqFM.isNullUFM m : bool then None else Some m in
        MkOccEnv (UniqFM.minusUFM_C g as_ bs)
    end.

#[global] Definition minusOccEnv {a : Type} {b : Type}
   : OccEnv a -> OccEnv b -> OccEnv a :=
  minusOccEnv_C_Ns UniqFM.minusUFM.

#[global] Definition minusOccEnv_C {a : Type} {b : Type}
   : (a -> b -> option a) -> OccEnv a -> OccEnv b -> OccEnv a :=
  fun f => minusOccEnv_C_Ns (UniqFM.minusUFM_C f).

(* Skipping definition `OccName.pprOccEnv' *)

#[global] Definition strictMapOccEnv {a : Type} {b : Type}
   : (a -> b) -> OccEnv a -> OccEnv b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MkOccEnv as_ =>
        MkOccEnv (FastStringEnv.strictMapFsEnv (UniqFM.strictMapUFM f) as_)
    end.

#[global] Definition forceOccEnv {a : Type} : (a -> unit) -> OccEnv a -> unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nf, MkOccEnv fs => UniqFM.seqEltsUFM (UniqFM.seqEltsUFM nf) fs
    end.

#[global] Definition unionOccSets : OccSet -> OccSet -> OccSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OccSet xs, Mk_OccSet ys =>
        Mk_OccSet (FastStringEnv.plusFsEnv_C UniqSet.unionUniqSets xs ys)
    end.

#[global] Definition unionManyOccSets : list OccSet -> OccSet :=
  Data.Foldable.foldl' unionOccSets emptyOccSet.

#[global] Definition elemOccSet : OccName -> OccSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OccName ns s, Mk_OccSet occs =>
        Data.Maybe.maybe false (UniqSet.elementOfUniqSet ns) (FastStringEnv.lookupFsEnv
                                                              occs s)
    end.

#[global] Definition isEmptyOccSet : OccSet -> bool :=
  fun '(Mk_OccSet occs) => UniqFM.isNullUFM occs.

#[global] Definition occNameString : OccName -> GHC.Base.String :=
  fun '(Mk_OccName _ s) => FastString.unpackFS s.

#[global] Definition setOccNameSpace : NameSpace -> OccName -> OccName :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | sp, Mk_OccName _ occ => Mk_OccName sp occ
    end.

#[global] Definition isVarOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName VarName _ => true
    | _ => false
    end.

#[global] Definition isTvOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName TvName _ => true
    | _ => false
    end.

#[global] Definition isTcOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName TcClsName _ => true
    | _ => false
    end.

#[global] Definition isFieldOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName (FldName _) _ => true
    | _ => false
    end.

#[global] Definition fieldOcc_maybe : OccName -> option FastString.FastString :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName (FldName con) _ => Some con
    | _ => None
    end.

#[global] Definition isValOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName VarName _ => true
    | Mk_OccName DataName _ => true
    | Mk_OccName (FldName _) _ => true
    | _ => false
    end.

#[global] Definition isDataOcc : OccName -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccName DataName _ => true
    | _ => false
    end.

Axiom isDataSymOcc : OccName -> bool.

Axiom isSymOcc : OccName -> bool.

(* Skipping definition `OccName.parenSymOcc' *)

Axiom startsWithUnderscore : OccName -> bool.

#[global] Definition isUnderscore : OccName -> bool :=
  fun occ =>
    occNameFS occ GHC.Base.== FastString.fsLit (GHC.Base.hs_string__ "_").

#[global] Definition mk_deriv
   : NameSpace ->
     FastString.FastString -> list FastString.FastString -> OccName :=
  fun occ_sp sys_prefix str =>
    mkOccNameFS occ_sp (FastString.concatFS (cons sys_prefix str)).

Axiom isDerivedOccName : OccName -> bool.

Axiom isDefaultMethodOcc : OccName -> bool.

Axiom isTypeableBindOcc : OccName -> bool.

#[global] Definition mk_simple_deriv
   : NameSpace -> FastString.FastString -> OccName -> OccName :=
  fun sp px occ => mk_deriv sp px (cons (occNameFS occ) nil).

#[global] Definition mkDataConWrapperOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$W").

#[global] Definition mkWorkerOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$w").

#[global] Definition mkMatcherOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$m").

#[global] Definition mkBuilderOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$b").

#[global] Definition mkDefaultMethodOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$dm").

#[global] Definition mkClassOpAuxOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$c").

#[global] Definition mkDictOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$d").

#[global] Definition mkIPOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$i").

#[global] Definition mkSpecOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$s").

#[global] Definition mkForeignExportOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$f").

#[global] Definition mkRepEqOcc : OccName -> OccName :=
  mk_simple_deriv tvName (GHC.Base.hs_string__ "$r").

#[global] Definition mkClassDataConOcc : OccName -> OccName :=
  mk_simple_deriv dataName (GHC.Base.hs_string__ "C:").

#[global] Definition mkNewTyCoOcc : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "N:").

#[global] Definition mkInstTyCoOcc : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "D:").

#[global] Definition mkEqPredCoOcc : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "$co").

#[global] Definition mkCon2TagOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$con2tag_").

#[global] Definition mkTag2ConOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$tag2con_").

#[global] Definition mkMaxTagOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$maxtag_").

#[global] Definition mkDataTOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$t").

#[global] Definition mkDataCOcc : OccName -> OccName :=
  mk_simple_deriv varName (GHC.Base.hs_string__ "$c").

#[global] Definition mkTyConRepOcc : OccName -> OccName :=
  fun occ =>
    let prefix :=
      if isDataOcc occ : bool then GHC.Base.hs_string__ "$tc'" else
      GHC.Base.hs_string__ "$tc" in
    mk_simple_deriv varName prefix occ.

#[global] Definition mkGenR : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "Rep_").

#[global] Definition mkGen1R : OccName -> OccName :=
  mk_simple_deriv tcName (GHC.Base.hs_string__ "Rep1_").

#[global] Definition mkDataConWorkerOcc : OccName -> OccName :=
  fun datacon_occ => setOccNameSpace varName datacon_occ.

Axiom mkSuperDictAuxOcc : GHC.Num.Int -> OccName -> OccName.

Axiom mkSuperDictSelOcc : GHC.Num.Int -> OccName -> OccName.

Axiom mkLocalOcc : Unique.Unique -> OccName -> OccName.

Axiom chooseUniqueOcc : NameSpace -> GHC.Base.String -> OccSet -> OccName.

#[global] Definition mkInstTyTcOcc : GHC.Base.String -> OccSet -> OccName :=
  fun str =>
    chooseUniqueOcc tcName (cons (GHC.Char.hs_char__ "R") (cons (GHC.Char.hs_char__
                                                                 ":") str)).

#[global] Definition mkDFunOcc : GHC.Base.String -> bool -> OccSet -> OccName :=
  fun info_str is_boot set =>
    let prefix :=
      if is_boot : bool then GHC.Base.hs_string__ "$fx" else
      GHC.Base.hs_string__ "$f" in
    chooseUniqueOcc VarName (Coq.Init.Datatypes.app prefix info_str) set.

#[global] Definition mkMethodOcc : OccName -> OccName :=
  fun arg_0__ =>
    match arg_0__ with
    | (Mk_OccName VarName _ as occ) => occ
    | occ => mk_simple_deriv varName (GHC.Base.hs_string__ "$m") occ
    end.

#[global] Definition emptyTidyOccEnv : TidyOccEnv :=
  UniqFM.emptyUFM.

#[global] Definition initTidyOccEnv : list OccName -> TidyOccEnv :=
  let add :=
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | env, Mk_OccName _ fs => UniqFM.addToUFM env fs #1
      end in
  Data.Foldable.foldl' add UniqFM.emptyUFM.

#[global] Definition delTidyOccEnvList
   : TidyOccEnv -> list FastString.FastString -> TidyOccEnv :=
  UniqFM.delListFromUFM.

#[global] Definition avoidClashesOccEnv
   : TidyOccEnv -> list OccName -> TidyOccEnv :=
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

#[global] Definition mainOcc : OccName :=
  mkVarOccFS (FastString.fsLit (GHC.Base.hs_string__ "main")).

(* Skipping definition `OccName.ppMainFn' *)

(* External variables:
     Eq Gt Lt None Some Type andb bool comparison cons false list negb nil op_zt__
     option pair true tt unit Coq.Init.Datatypes.app Data.Foldable.foldl'
     Data.Maybe.maybe FastString.FastString FastString.concatFS FastString.fsLit
     FastString.lexicalCompareFS FastString.mkFastString FastString.unpackFS
     FastStringEnv.FastStringEnv FastStringEnv.alterFsEnv FastStringEnv.emptyFsEnv
     FastStringEnv.extendFsEnv FastStringEnv.extendFsEnv_Acc
     FastStringEnv.extendFsEnv_C FastStringEnv.lookupFsEnv
     FastStringEnv.mapMaybeFsEnv FastStringEnv.nonDetFoldFsEnv
     FastStringEnv.plusFsEnv_C FastStringEnv.strictMapFsEnv FastStringEnv.unitFsEnv
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Ord GHC.Base.String GHC.Base.compare
     GHC.Base.compare__ GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzgze__ GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.return_ GHC.Err.error GHC.Num.Int
     GHC.Num.fromInteger HsToCoq.Err.Build_Default HsToCoq.Err.Default UniqFM.UniqFM
     UniqFM.addToUFM UniqFM.alterUFM UniqFM.delFromUFM UniqFM.delListFromUFM
     UniqFM.elemUFM UniqFM.emptyUFM UniqFM.filterUFM UniqFM.intersectUFM_C
     UniqFM.isNullUFM UniqFM.lookupUFM UniqFM.mapMaybeUFM UniqFM.minusUFM
     UniqFM.minusUFM_C UniqFM.nonDetEltsUFM UniqFM.nonDetFoldUFM UniqFM.plusUFM
     UniqFM.plusUFM_C UniqFM.seqEltsUFM UniqFM.strictMapUFM UniqFM.unitUFM
     UniqSet.UniqSet UniqSet.elementOfUniqSet UniqSet.unionUniqSets
     UniqSet.unitUniqSet Unique.Unique Util.HasDebugCallStack
*)
