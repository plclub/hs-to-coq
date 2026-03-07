(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Function.
Require Data.Map.Internal.
Require Data.OldList.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require HsToCoq.Err.
Require Panic.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive UnhelpfulSpanReason : Type :=
  | UnhelpfulNoLocationInfo : UnhelpfulSpanReason
  | UnhelpfulWiredIn : UnhelpfulSpanReason
  | UnhelpfulInteractive : UnhelpfulSpanReason
  | UnhelpfulGenerated : UnhelpfulSpanReason
  | UnhelpfulOther : FastString.FastString -> UnhelpfulSpanReason.

Inductive RealSrcSpan : Type :=
  | RealSrcSpan' (srcSpanFile : FastString.FastString) (srcSpanSLine
    : GHC.Num.Int) (srcSpanSCol : GHC.Num.Int) (srcSpanELine : GHC.Num.Int)
  (srcSpanECol : GHC.Num.Int)
   : RealSrcSpan.

Inductive RealSrcLoc : Type :=
  | ASrcLoc
   : FastString.LexicalFastString -> GHC.Num.Int -> GHC.Num.Int -> RealSrcLoc.

Inductive NoComments : Type := | Mk_NoComments : NoComments.

Inductive GenLocated l e : Type := | L : l -> e -> GenLocated l e.

#[global] Definition RealLocated :=
  (GenLocated RealSrcSpan)%type.

Inductive DeltaPos : Type :=
  | SameLine (deltaColumn : GHC.Num.Int) : DeltaPos
  | DifferentLine (deltaLine : GHC.Num.Int) (deltaColumn : GHC.Num.Int)
   : DeltaPos.

Inductive BufPos : Type := | Mk_BufPos (bufPos : GHC.Num.Int) : BufPos.

Inductive BufSpan : Type :=
  | Mk_BufSpan (bufSpanStart : BufPos) (bufSpanEnd : BufPos) : BufSpan.

Inductive PsSpan : Type :=
  | Mk_PsSpan (psRealSpan : RealSrcSpan) (psBufSpan : BufSpan) : PsSpan.

#[global] Definition PsLocated :=
  (GenLocated PsSpan)%type.

Inductive SrcSpan : Type :=
  | ARealSrcSpan : RealSrcSpan -> (option BufSpan) -> SrcSpan
  | UnhelpfulSpan : UnhelpfulSpanReason -> SrcSpan.

Inductive EpaLocation' a : Type :=
  | EpaSpan : SrcSpan -> EpaLocation' a
  | EpaDelta : DeltaPos -> a -> EpaLocation' a.

#[global] Definition NoCommentsLocation :=
  (EpaLocation' NoComments)%type.

#[global] Definition Located :=
  (GenLocated SrcSpan)%type.

Inductive PsLoc : Type :=
  | Mk_PsLoc (psRealLoc : RealSrcLoc) (psBufPos : BufPos) : PsLoc.

Inductive SrcLoc : Type :=
  | ARealSrcLoc : RealSrcLoc -> (option BufPos) -> SrcLoc
  | UnhelpfulLoc : FastString.FastString -> SrcLoc.

Arguments L {_} {_} _ _.

Arguments EpaSpan {_} _.

Arguments EpaDelta {_} _ _.

Instance Default__UnhelpfulSpanReason
   : HsToCoq.Err.Default UnhelpfulSpanReason :=
  HsToCoq.Err.Build_Default _ UnhelpfulNoLocationInfo.

Instance Default__NoComments : HsToCoq.Err.Default NoComments :=
  HsToCoq.Err.Build_Default _ Mk_NoComments.

Instance Default__DeltaPos : HsToCoq.Err.Default DeltaPos :=
  HsToCoq.Err.Build_Default _ (SameLine HsToCoq.Err.default).

Instance Default__BufPos : HsToCoq.Err.Default BufPos :=
  HsToCoq.Err.Build_Default _ (Mk_BufPos HsToCoq.Err.default).

#[global] Definition srcSpanECol (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ _ _ _ srcSpanECol := arg_0__ in
  srcSpanECol.

#[global] Definition srcSpanELine (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ _ _ srcSpanELine _ := arg_0__ in
  srcSpanELine.

#[global] Definition srcSpanFile (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' srcSpanFile _ _ _ _ := arg_0__ in
  srcSpanFile.

#[global] Definition srcSpanSCol (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ _ srcSpanSCol _ _ := arg_0__ in
  srcSpanSCol.

#[global] Definition srcSpanSLine (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ srcSpanSLine _ _ _ := arg_0__ in
  srcSpanSLine.

#[global] Definition deltaColumn (arg_0__ : DeltaPos) :=
  match arg_0__ with
  | SameLine deltaColumn => deltaColumn
  | DifferentLine _ deltaColumn => deltaColumn
  end.

#[global] Definition deltaLine (arg_0__ : DeltaPos) :=
  match arg_0__ with
  | SameLine _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `deltaLine' has no match in constructor `SameLine' of type `DeltaPos'")
  | DifferentLine deltaLine _ => deltaLine
  end.

#[global] Definition psBufSpan (arg_0__ : PsSpan) :=
  let 'Mk_PsSpan _ psBufSpan := arg_0__ in
  psBufSpan.

#[global] Definition psRealSpan (arg_0__ : PsSpan) :=
  let 'Mk_PsSpan psRealSpan _ := arg_0__ in
  psRealSpan.

#[global] Definition bufPos (arg_0__ : BufPos) :=
  let 'Mk_BufPos bufPos := arg_0__ in
  bufPos.

#[global] Definition psBufPos (arg_0__ : PsLoc) :=
  let 'Mk_PsLoc _ psBufPos := arg_0__ in
  psBufPos.

#[global] Definition psRealLoc (arg_0__ : PsLoc) :=
  let 'Mk_PsLoc psRealLoc _ := arg_0__ in
  psRealLoc.

(* Midamble *)

(* Default values *)
Require Import HsToCoq.Err.
Instance Default__SrcSpan : Default SrcSpan := Build_Default _ (UnhelpfulSpan default).

Instance Default__RealSrcLoc : Default RealSrcLoc :=
  Build_Default _ (ASrcLoc (@default _ FastString.instance_FastString_Default)
                   HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__RealSrcSpan : Default RealSrcSpan :=
  Build_Default _ (RealSrcSpan' (@default _ FastString.instance_FastString_Default)
                   HsToCoq.Err.default  HsToCoq.Err.default
                   HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__BufSpan : Default BufSpan :=
  Build_Default _ (Mk_BufSpan HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__PsSpan : Default PsSpan :=
  Build_Default _ (Mk_PsSpan HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__PsLoc : Default PsLoc :=
  Build_Default _ (Mk_PsLoc HsToCoq.Err.default HsToCoq.Err.default).


(* Field accessors for redefined BufSpan *)
Definition bufSpanStart (arg_0__ : BufSpan) : BufPos :=
  let 'Mk_BufSpan bufSpanStart _ := arg_0__ in bufSpanStart.
Definition bufSpanEnd (arg_0__ : BufSpan) : BufPos :=
  let 'Mk_BufSpan _ bufSpanEnd := arg_0__ in bufSpanEnd.

Import GHC.Base.ManualNotations.

Definition Eq__RealSrcLoc_op_zeze : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b =>
    let 'ASrcLoc a1 a2 a3 := a in
    let 'ASrcLoc b1 b2 b3 := b in
    andb (andb (a1 GHC.Base.== b1) (a2 GHC.Base.== b2)) (a3 GHC.Base.== b3).

#[global]
Program Instance Eq__RealSrcLoc : GHC.Base.Eq_ RealSrcLoc :=
  fun _ k => k {|
    GHC.Base.op_zeze____ := Eq__RealSrcLoc_op_zeze ;
    GHC.Base.op_zsze____ := fun a b => negb (Eq__RealSrcLoc_op_zeze a b)
  |}.

Definition Ord__RealSrcLoc_compare : RealSrcLoc -> RealSrcLoc -> comparison :=
  fun a b =>
    let 'ASrcLoc a1 a2 a3 := a in
    let 'ASrcLoc b1 b2 b3 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => Lt
    | Eq =>
        match (GHC.Base.compare a2 b2) with
        | Lt => Lt
        | Eq => GHC.Base.compare a3 b3
        | Gt => Gt
        end
    | Gt => Gt
    end.

Definition Ord__RealSrcLoc_op_zl : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b => Ord__RealSrcLoc_compare a b GHC.Base.== Lt.

#[global]
Program Instance Ord__RealSrcLoc : GHC.Base.Ord RealSrcLoc :=
  fun _ k => k {|
    GHC.Base.op_zl____ := fun a b => Ord__RealSrcLoc_compare a b GHC.Base.== Lt ;
    GHC.Base.op_zlze____ := fun a b => Ord__RealSrcLoc_compare a b GHC.Base./= Gt ;
    GHC.Base.op_zg____ := fun a b => Ord__RealSrcLoc_compare a b GHC.Base.== Gt ;
    GHC.Base.op_zgze____ := fun a b => Ord__RealSrcLoc_compare a b GHC.Base./= Lt ;
    GHC.Base.compare__ := Ord__RealSrcLoc_compare ;
    GHC.Base.max__ := fun a b => if Ord__RealSrcLoc_compare a b GHC.Base./= Gt : bool then b else a ;
    GHC.Base.min__ := fun a b => if Ord__RealSrcLoc_compare a b GHC.Base./= Gt : bool then a else b
  |}.

Definition Eq__RealSrcSpan_op_zeze : RealSrcSpan -> RealSrcSpan -> bool :=
  fun a b =>
    let 'RealSrcSpan' fa la ca la2 ca2 := a in
    let 'RealSrcSpan' fb lb cb lb2 cb2 := b in
    andb (andb (andb (andb (fa GHC.Base.== fb) (la GHC.Base.== lb)) (ca GHC.Base.== cb))
               (la2 GHC.Base.== lb2)) (ca2 GHC.Base.== cb2).

#[global]
Program Instance Eq__RealSrcSpan : GHC.Base.Eq_ RealSrcSpan :=
  fun _ k => k {|
    GHC.Base.op_zeze____ := Eq__RealSrcSpan_op_zeze ;
    GHC.Base.op_zsze____ := fun a b => negb (Eq__RealSrcSpan_op_zeze a b)
  |}.

(* Converted value declarations: *)

#[local] Definition Functor__GenLocated_fmap {inst_l : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> GenLocated inst_l a -> GenLocated inst_l b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, L a1 a2 => L a1 (f a2)
      end.

#[local] Definition Functor__GenLocated_op_zlzd__ {inst_l : Type}
   : forall {a : Type},
     forall {b : Type}, a -> GenLocated inst_l b -> GenLocated inst_l a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | z, L a1 a2 => L a1 z end.

#[global]
Program Instance Functor__GenLocated {l : Type}
   : GHC.Base.Functor (GenLocated l) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} =>
             Functor__GenLocated_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__GenLocated_op_zlzd__ |}.

#[local] Definition Foldable__GenLocated_foldMap {inst_l : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GenLocated inst_l a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, L a1 a2 => f a2 end.

#[local] Definition Foldable__GenLocated_fold {inst_l : Type}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, GenLocated inst_l m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__GenLocated_foldMap GHC.Base.id.

#[local] Definition Foldable__GenLocated_foldl {inst_l : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GenLocated inst_l a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__GenLocated_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                     (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                      GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__GenLocated_foldr {inst_l : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GenLocated inst_l a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, L a1 a2 => f a2 z
      end.

#[local] Definition Foldable__GenLocated_length {inst_l : Type}
   : forall {a : Type}, GenLocated inst_l a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__GenLocated_foldl (fun arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | c, _ => c GHC.Num.+ #1
                                  end) #0.

#[local] Definition Foldable__GenLocated_null {inst_l : Type}
   : forall {a : Type}, GenLocated inst_l a -> bool :=
  fun {a : Type} => fun '(L _ _) => false.

#[local] Definition Foldable__GenLocated_product {inst_l : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, GenLocated inst_l a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__GenLocated_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__GenLocated_sum {inst_l : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, GenLocated inst_l a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__GenLocated_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__GenLocated_toList {inst_l : Type}
   : forall {a : Type}, GenLocated inst_l a -> list a :=
  fun {a : Type} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__GenLocated_foldr c n t)).

#[global]
Program Instance Foldable__GenLocated {l : Type}
   : Data.Foldable.Foldable (GenLocated l) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__GenLocated_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__GenLocated_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} =>
             Foldable__GenLocated_foldl ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} =>
             Foldable__GenLocated_foldr ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__GenLocated_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__GenLocated_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__GenLocated_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__GenLocated_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__GenLocated_toList |}.

#[local] Definition Traversable__GenLocated_traverse {inst_l : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GenLocated inst_l a -> f (GenLocated inst_l b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, L a1 a2 => GHC.Base.fmap (fun b2 => L a1 b2) (f a2)
      end.

#[local] Definition Traversable__GenLocated_mapM {inst_l : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GenLocated inst_l a -> m (GenLocated inst_l b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__GenLocated_traverse.

#[local] Definition Traversable__GenLocated_sequenceA {inst_l : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     GenLocated inst_l (f a) -> f (GenLocated inst_l a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__GenLocated_traverse GHC.Base.id.

#[local] Definition Traversable__GenLocated_sequence {inst_l : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     GenLocated inst_l (m a) -> m (GenLocated inst_l a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__GenLocated_sequenceA.

#[global]
Program Instance Traversable__GenLocated {l : Type}
   : Data.Traversable.Traversable (GenLocated l) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__GenLocated_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__GenLocated_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__GenLocated_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__GenLocated_traverse |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__RealSrcLoc' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__SrcLoc' *)

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `SrcLoc.Data__RealSrcSpan' *)

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `SrcLoc.Data__SrcSpan' *)

(* Skipping instance `SrcLoc.Semigroup__BufSpan' of class
   `GHC.Base.Semigroup' *)

(* Skipping all instances of class `Json.ToJson', including
   `SrcLoc.ToJson__SrcSpan' *)

(* Skipping all instances of class `Json.ToJson', including
   `SrcLoc.ToJson__RealSrcSpan' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `SrcLoc.NFData__SrcSpan' *)

#[global] Definition Ord__RealSrcSpan_compare
   : RealSrcSpan -> RealSrcSpan -> comparison :=
  fun a b =>
    let 'RealSrcSpan' fa la ca la2 ca2 := a in
    let 'RealSrcSpan' fb lb cb lb2 cb2 := b in
    match Ord__RealSrcLoc_compare (ASrcLoc fa la ca) (ASrcLoc fb lb cb) with
    | Eq => Ord__RealSrcLoc_compare (ASrcLoc fa la2 ca2) (ASrcLoc fb lb2 cb2)
    | x => x
    end.

#[local] Definition Ord__RealSrcSpan_op_zl__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base.== Lt.

#[local] Definition Ord__RealSrcSpan_op_zlze__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base./= Gt.

#[local] Definition Ord__RealSrcSpan_op_zg__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base.== Gt.

#[local] Definition Ord__RealSrcSpan_op_zgze__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base./= Lt.

#[local] Definition Ord__RealSrcSpan_max
   : RealSrcSpan -> RealSrcSpan -> RealSrcSpan :=
  fun x y => if Ord__RealSrcSpan_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__RealSrcSpan_min
   : RealSrcSpan -> RealSrcSpan -> RealSrcSpan :=
  fun x y => if Ord__RealSrcSpan_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__RealSrcSpan : GHC.Base.Ord RealSrcSpan :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__RealSrcSpan_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__RealSrcSpan_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__RealSrcSpan_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__RealSrcSpan_op_zgze__ ;
           GHC.Base.compare__ := Ord__RealSrcSpan_compare ;
           GHC.Base.max__ := Ord__RealSrcSpan_max ;
           GHC.Base.min__ := Ord__RealSrcSpan_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `SrcLoc.Show__RealSrcLoc' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `SrcLoc.Show__RealSrcSpan' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__RealSrcSpan' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__SrcSpan' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__UnhelpfulSpanReason' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `SrcLoc.NFData__GenLocated' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__Located' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__GenLocated__RealSrcSpan' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__NoComments' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__EpaLocation'' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `SrcLoc.Outputable__DeltaPos' *)

#[global] Definition mkRealSrcLoc
   : FastString.FastString -> GHC.Num.Int -> GHC.Num.Int -> RealSrcLoc :=
  fun x line col => ASrcLoc x line col.

#[global] Definition mkSrcLoc
   : FastString.FastString -> GHC.Num.Int -> GHC.Num.Int -> SrcLoc :=
  fun x line col => ARealSrcLoc (mkRealSrcLoc x line col) None.

#[global] Definition leftmostColumn : GHC.Num.Int :=
  #1.

#[global] Definition getBufPos : SrcLoc -> option BufPos :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcLoc _ mbpos => mbpos
    | UnhelpfulLoc _ => None
    end.

#[global] Definition noSrcLoc : SrcLoc :=
  UnhelpfulLoc (FastString.fsLit (GHC.Base.hs_string__ "<no location info>")).

#[global] Definition generatedSrcLoc : SrcLoc :=
  UnhelpfulLoc (FastString.fsLit (GHC.Base.hs_string__
                                  "<compiler-generated code>")).

#[global] Definition interactiveSrcLoc : SrcLoc :=
  UnhelpfulLoc (FastString.fsLit (GHC.Base.hs_string__ "<interactive>")).

#[global] Definition mkGeneralSrcLoc : FastString.FastString -> SrcLoc :=
  UnhelpfulLoc.

#[global] Definition srcLocFile : RealSrcLoc -> FastString.FastString :=
  fun '(ASrcLoc fname _ _) => fname.

#[global] Definition srcLocLine : RealSrcLoc -> GHC.Num.Int :=
  fun '(ASrcLoc _ l _) => l.

#[global] Definition srcLocCol : RealSrcLoc -> GHC.Num.Int :=
  fun '(ASrcLoc _ _ c) => c.

(* Skipping definition `SrcLoc.advanceSrcLoc' *)

(* Skipping definition `SrcLoc.advance_tabstop' *)

#[global] Definition advanceBufPos : BufPos -> BufPos :=
  fun '(Mk_BufPos i) => Mk_BufPos (i GHC.Num.+ #1).

(* Skipping definition `SrcLoc.sortLocated' *)

#[global] Definition getLoc {l : Type} {e : Type} : GenLocated l e -> l :=
  fun '(L l _) => l.

#[global] Definition sortRealLocated {a : Type}
   : list (RealLocated a) -> list (RealLocated a) :=
  Data.OldList.sortBy (Data.Function.on GHC.Base.compare getLoc).

#[global] Definition lookupSrcLoc {a : Type}
   : SrcLoc -> Data.Map.Internal.Map RealSrcLoc a -> option a :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcLoc l _ => Data.Map.Internal.lookup l
    | UnhelpfulLoc _ => GHC.Base.const None
    end.

#[global] Definition lookupSrcSpan {a : Type}
   : SrcSpan -> Data.Map.Internal.Map RealSrcSpan a -> option a :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan l _ => Data.Map.Internal.lookup l
    | UnhelpfulSpan _ => GHC.Base.const None
    end.

#[global] Definition removeBufSpan : SrcSpan -> SrcSpan :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan s _ => ARealSrcSpan s None
    | s => s
    end.

#[global] Definition getBufSpan : SrcSpan -> option BufSpan :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan _ mbspan => mbspan
    | UnhelpfulSpan _ => None
    end.

#[global] Definition noSrcSpan : SrcSpan :=
  UnhelpfulSpan UnhelpfulNoLocationInfo.

#[global] Definition wiredInSrcSpan : SrcSpan :=
  UnhelpfulSpan UnhelpfulWiredIn.

#[global] Definition interactiveSrcSpan : SrcSpan :=
  UnhelpfulSpan UnhelpfulInteractive.

#[global] Definition generatedSrcSpan : SrcSpan :=
  UnhelpfulSpan UnhelpfulGenerated.

#[global] Definition isGeneratedSrcSpan : SrcSpan -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | UnhelpfulSpan UnhelpfulGenerated => true
    | _ => false
    end.

#[global] Definition isNoSrcSpan : SrcSpan -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | UnhelpfulSpan UnhelpfulNoLocationInfo => true
    | _ => false
    end.

#[global] Definition mkGeneralSrcSpan : FastString.FastString -> SrcSpan :=
  UnhelpfulSpan GHC.Base.∘ UnhelpfulOther.

#[global] Definition realSrcLocSpan : RealSrcLoc -> RealSrcSpan :=
  fun '(ASrcLoc file line col) => RealSrcSpan' file line col line col.

#[global] Definition srcLocSpan : SrcLoc -> SrcSpan :=
  fun arg_0__ =>
    match arg_0__ with
    | UnhelpfulLoc str => UnhelpfulSpan (UnhelpfulOther str)
    | ARealSrcLoc l mb =>
        ARealSrcSpan (realSrcLocSpan l) (GHC.Base.fmap (fun b => Mk_BufSpan b b) mb)
    end.

#[global] Definition mkRealSrcSpan : RealSrcLoc -> RealSrcLoc -> RealSrcSpan :=
  fun loc1 loc2 =>
    let file := srcLocFile loc1 in
    let col2 := srcLocCol loc2 in
    let col1 := srcLocCol loc1 in
    let line2 := srcLocLine loc2 in
    let line1 := srcLocLine loc1 in RealSrcSpan' file line1 col1 line2 col2.

#[global] Definition isOneLineRealSpan : RealSrcSpan -> bool :=
  fun '(RealSrcSpan' _ line1 _ line2 _) => line1 GHC.Base.== line2.

#[global] Definition isPointRealSpan : RealSrcSpan -> bool :=
  fun '(RealSrcSpan' _ line1 col1 line2 col2) =>
    andb (line1 GHC.Base.== line2) (col1 GHC.Base.== col2).

#[global] Definition mkSrcSpan : SrcLoc -> SrcLoc -> SrcSpan :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UnhelpfulLoc str, _ => UnhelpfulSpan (UnhelpfulOther str)
    | _, UnhelpfulLoc str => UnhelpfulSpan (UnhelpfulOther str)
    | ARealSrcLoc loc1 mbpos1, ARealSrcLoc loc2 mbpos2 =>
        ARealSrcSpan (mkRealSrcSpan loc1 loc2) (GHC.Base.liftA2 Mk_BufSpan mbpos1
                                                mbpos2)
    end.

(* Skipping definition `SrcLoc.combineSrcSpans' *)

(* Skipping definition `SrcLoc.combineRealSrcSpans' *)

(* Skipping definition `SrcLoc.combineBufSpans' *)

#[global] Definition srcSpanStartCol : RealSrcSpan -> GHC.Num.Int :=
  fun '(RealSrcSpan' _ _ l _ _) => l.

#[global] Definition srcSpanStartLine : RealSrcSpan -> GHC.Num.Int :=
  fun '(RealSrcSpan' _ l _ _ _) => l.

#[global] Definition realSrcSpanStart : RealSrcSpan -> RealSrcLoc :=
  fun s => mkRealSrcLoc (srcSpanFile s) (srcSpanStartLine s) (srcSpanStartCol s).

#[global] Definition srcSpanFirstCharacter : SrcSpan -> SrcSpan :=
  fun arg_0__ =>
    match arg_0__ with
    | (UnhelpfulSpan _ as l) => l
    | ARealSrcSpan span mbspan =>
        let mkBufSpan :=
          fun bspan =>
            let '(Mk_BufPos i as bpos1) := bufSpanStart bspan in
            let bpos2 := Mk_BufPos (i GHC.Num.+ #1) in Mk_BufSpan bpos1 bpos2 in
        let '(ASrcLoc f l c as loc1) := realSrcSpanStart span in
        let loc2 := ASrcLoc f l (c GHC.Num.+ #1) in
        ARealSrcSpan (mkRealSrcSpan loc1 loc2) (GHC.Base.fmap mkBufSpan mbspan)
    end.

#[global] Definition isGoodSrcSpan : SrcSpan -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan _ _ => true
    | UnhelpfulSpan _ => false
    end.

#[global] Definition srcSpanEndLine : RealSrcSpan -> GHC.Num.Int :=
  fun '(RealSrcSpan' _ _ _ l _) => l.

#[global] Definition isOneLineSpan : SrcSpan -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan s _ => srcSpanStartLine s GHC.Base.== srcSpanEndLine s
    | UnhelpfulSpan _ => false
    end.

#[global] Definition srcSpanEndCol : RealSrcSpan -> GHC.Num.Int :=
  fun '(RealSrcSpan' _ _ _ _ c) => c.

#[global] Definition isZeroWidthSpan : SrcSpan -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan s _ =>
        andb (srcSpanStartLine s GHC.Base.== srcSpanEndLine s) (srcSpanStartCol s
              GHC.Base.==
              srcSpanEndCol s)
    | UnhelpfulSpan _ => false
    end.

(* Skipping definition `SrcLoc.containsSpan' *)

#[global] Definition unhelpfulSpanFS
   : UnhelpfulSpanReason -> FastString.FastString :=
  fun r =>
    match r with
    | UnhelpfulOther s => s
    | UnhelpfulNoLocationInfo =>
        FastString.fsLit (GHC.Base.hs_string__ "<no location info>")
    | UnhelpfulWiredIn =>
        FastString.fsLit (GHC.Base.hs_string__ "<wired into compiler>")
    | UnhelpfulInteractive =>
        FastString.fsLit (GHC.Base.hs_string__ "<interactive>")
    | UnhelpfulGenerated => FastString.fsLit (GHC.Base.hs_string__ "<generated>")
    end.

#[global] Definition srcSpanStart : SrcSpan -> SrcLoc :=
  fun arg_0__ =>
    match arg_0__ with
    | UnhelpfulSpan r => UnhelpfulLoc (unhelpfulSpanFS r)
    | ARealSrcSpan s b =>
        ARealSrcLoc (realSrcSpanStart s) (GHC.Base.fmap bufSpanStart b)
    end.

#[global] Definition realSrcSpanEnd : RealSrcSpan -> RealSrcLoc :=
  fun s => mkRealSrcLoc (srcSpanFile s) (srcSpanEndLine s) (srcSpanEndCol s).

#[global] Definition srcSpanEnd : SrcSpan -> SrcLoc :=
  fun arg_0__ =>
    match arg_0__ with
    | UnhelpfulSpan r => UnhelpfulLoc (unhelpfulSpanFS r)
    | ARealSrcSpan s b =>
        ARealSrcLoc (realSrcSpanEnd s) (GHC.Base.fmap bufSpanEnd b)
    end.

#[global] Definition srcSpanFileName_maybe
   : SrcSpan -> option FastString.FastString :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan s _ => Some (srcSpanFile s)
    | UnhelpfulSpan _ => None
    end.

#[global] Definition srcSpanToRealSrcSpan : SrcSpan -> option RealSrcSpan :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan ss _ => Some ss
    | _ => None
    end.

#[global] Definition pprUnhelpfulSpanReason
   : UnhelpfulSpanReason -> GHC.Base.String :=
  fun r => Panic.someSDoc.

(* Skipping definition `SrcLoc.pprUserSpan' *)

(* Skipping definition `SrcLoc.pprUserRealSpan' *)

#[global] Definition unLoc {l : Type} {e : Type} : GenLocated l e -> e :=
  fun '(L _ e) => e.

#[global] Definition noLoc {e : Type} : e -> Located e :=
  fun e => L noSrcSpan e.

#[global] Definition mkGeneralLocated {e : Type}
   : GHC.Base.String -> e -> Located e :=
  fun s e => L (mkGeneralSrcSpan (FastString.fsLit s)) e.

(* Skipping definition `SrcLoc.combineLocs' *)

(* Skipping definition `SrcLoc.addCLoc' *)

#[global] Definition eqLocated {a : Type} {l : Type} `{GHC.Base.Eq_ a}
   : GenLocated l a -> GenLocated l a -> bool :=
  fun a b => unLoc a GHC.Base.== unLoc b.

#[global] Definition cmpLocated {a : Type} {l : Type} `{GHC.Base.Ord a}
   : GenLocated l a -> GenLocated l a -> comparison :=
  fun a b => GHC.Base.compare (unLoc a) (unLoc b).

(* Skipping definition `SrcLoc.cmpBufSpan' *)

(* Skipping definition `SrcLoc.pprLocated' *)

(* Skipping definition `SrcLoc.pprLocatedAlways' *)

#[global] Definition compareSrcSpanBy
   : (RealSrcSpan -> RealSrcSpan -> comparison) ->
     SrcSpan -> SrcSpan -> comparison :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | cmp, ARealSrcSpan a _, ARealSrcSpan b _ => cmp a b
    | _, ARealSrcSpan _ _, UnhelpfulSpan _ => Lt
    | _, UnhelpfulSpan _, ARealSrcSpan _ _ => Gt
    | _, UnhelpfulSpan _, UnhelpfulSpan _ => Eq
    end.

#[global] Definition rightmost_smallest : SrcSpan -> SrcSpan -> comparison :=
  compareSrcSpanBy (GHC.Base.flip GHC.Base.compare).

(* Skipping definition `SrcLoc.leftmost_smallest' *)

(* Skipping definition `SrcLoc.leftmost_largest' *)

(* Skipping definition `SrcLoc.spans' *)

(* Skipping definition `SrcLoc.isSubspanOf' *)

#[global] Definition isRealSubspanOf : RealSrcSpan -> RealSrcSpan -> bool :=
  fun src parent =>
    if srcSpanFile parent GHC.Base./= srcSpanFile src : bool then false else
    andb (realSrcSpanStart parent GHC.Base.<= realSrcSpanStart src) (realSrcSpanEnd
          parent GHC.Base.>=
          realSrcSpanEnd src).

#[global] Definition getRealSrcSpan {a : Type} : RealLocated a -> RealSrcSpan :=
  fun '(L l _) => l.

#[global] Definition unRealSrcSpan {a : Type} : RealLocated a -> a :=
  fun '(L _ e) => e.

#[global] Definition mkSrcSpanPs : PsSpan -> SrcSpan :=
  fun '(Mk_PsSpan r b) => ARealSrcSpan r (Some b).

#[global] Definition psLocatedToLocated {a : Type} : PsLocated a -> Located a :=
  fun '(L sp a) => L (mkSrcSpanPs sp) a.

(* Skipping definition `SrcLoc.advancePsLoc' *)

#[global] Definition mkPsSpan : PsLoc -> PsLoc -> PsSpan :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_PsLoc r1 b1, Mk_PsLoc r2 b2 =>
        Mk_PsSpan (mkRealSrcSpan r1 r2) (Mk_BufSpan b1 b2)
    end.

#[global] Definition psSpanStart : PsSpan -> PsLoc :=
  fun '(Mk_PsSpan r b) => Mk_PsLoc (realSrcSpanStart r) (bufSpanStart b).

#[global] Definition psSpanEnd : PsSpan -> PsLoc :=
  fun '(Mk_PsSpan r b) => Mk_PsLoc (realSrcSpanEnd r) (bufSpanEnd b).

#[global] Definition deltaPos : GHC.Num.Int -> GHC.Num.Int -> DeltaPos :=
  fun l c =>
    let 'num_0__ := l in
    if num_0__ GHC.Base.== #0 : bool then SameLine c else
    DifferentLine l c.

#[global] Definition getDeltaLine : DeltaPos -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
    | SameLine _ => #0
    | DifferentLine r _ => r
    end.

(* External variables:
     Eq Gt Lt None Ord__RealSrcLoc_compare Some Type andb bool bufSpanEnd
     bufSpanStart comparison false list option true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.Function.on Data.Map.Internal.Map
     Data.Map.Internal.lookup Data.OldList.sortBy Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ FastString.FastString FastString.LexicalFastString
     FastString.fsLit GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.String GHC.Base.build'
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2 GHC.Base.max__ GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg____ GHC.Base.op_zgze__
     GHC.Base.op_zgze____ GHC.Base.op_zl____ GHC.Base.op_zlzd____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zsze__ GHC.Err.error GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__ HsToCoq.Err.Build_Default
     HsToCoq.Err.Default HsToCoq.Err.default Panic.someSDoc
*)
