(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require GHC.Base.
Require GHC.Prim.
Require HsToRocq.Unpeel.
Require UniqFM.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UniqSet a : Type :=
  | Mk_UniqSet (getUniqSet' : UniqFM.UniqFM a a) : UniqSet a.

Arguments Mk_UniqSet {_} _.

#[global] Definition getUniqSet' {a} (arg_0__ : UniqSet a) :=
  let 'Mk_UniqSet getUniqSet' := arg_0__ in
  getUniqSet'.

(* Converted value declarations: *)

#[local] Definition Semigroup__UniqSet_op_zlzlzgzg__ {inst_a : Type}
   : UniqSet inst_a -> UniqSet inst_a -> UniqSet inst_a :=
  fun arg_0__ arg_1__ =>
    Mk_UniqSet (_GHC.Base.<<>>_ (getUniqSet' arg_0__) (getUniqSet' arg_1__)).

#[global]
Program Instance Semigroup__UniqSet {a : Type}
   : GHC.Base.Semigroup (UniqSet a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__UniqSet_op_zlzlzgzg__ |}.

Instance Unpeel_UniqSet ele
   : HsToRocq.Unpeel.Unpeel (UniqSet ele) (UniqFM.UniqFM ele ele) :=
  HsToRocq.Unpeel.Build_Unpeel _ _ (fun '(Mk_UniqSet y) => y) Mk_UniqSet.

#[local] Definition Monoid__UniqSet_mappend {inst_a}
   : UniqSet inst_a -> UniqSet inst_a -> UniqSet inst_a :=
  fun x y => Mk_UniqSet (GHC.Base.mappend (getUniqSet' x) (getUniqSet' y)).

#[local] Definition Monoid__UniqSet_mconcat {inst_a}
   : list (UniqSet inst_a) -> UniqSet inst_a :=
  fun xs =>
    Data.Foldable.foldr (fun x y =>
                           Mk_UniqSet (getUniqSet' x GHC.Base.<<>> getUniqSet' y)) (Mk_UniqSet
                         GHC.Base.mempty) xs.

#[local] Definition Monoid__UniqSet_mempty {inst_a} : UniqSet inst_a :=
  Mk_UniqSet GHC.Base.mempty.

#[global]
Program Instance Monoid__UniqSet {a : Type} : GHC.Base.Monoid (UniqSet a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__UniqSet_mappend ;
           GHC.Base.mconcat__ := Monoid__UniqSet_mconcat ;
           GHC.Base.mempty__ := Monoid__UniqSet_mempty |}.

(* Skipping instance `UniqSet.Eq___UniqSet' of class `GHC.Base.Eq_' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `UniqSet.Outputable__UniqSet' *)

#[global] Definition emptyUniqSet {a : Type} : UniqSet a :=
  Mk_UniqSet UniqFM.emptyUFM.

#[global] Definition unitUniqSet {a : Type} `{Unique.Uniquable a}
   : a -> UniqSet a :=
  fun x => Mk_UniqSet (UniqFM.unitUFM x x).

#[global] Definition addOneToUniqSet {a : Type} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet set, x => Mk_UniqSet (UniqFM.addToUFM set x x)
    end.

#[global] Definition mkUniqSet {a : Type} `{Unique.Uniquable a}
   : list a -> UniqSet a :=
  Data.Foldable.foldl' addOneToUniqSet emptyUniqSet.

#[global] Definition addListToUniqSet {a : Type} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  Data.Foldable.foldl' addOneToUniqSet.

#[global] Definition delOneFromUniqSet {a : Type} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, a => Mk_UniqSet (UniqFM.delFromUFM s a)
    end.

#[global] Definition delOneFromUniqSet_Directly {a : Type}
   : UniqSet a -> Unique.Unique -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, u => Mk_UniqSet (UniqFM.delFromUFM_Directly s u)
    end.

#[global] Definition delListFromUniqSet {a : Type} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, l => Mk_UniqSet (UniqFM.delListFromUFM s l)
    end.

#[global] Definition delListFromUniqSet_Directly {a : Type}
   : UniqSet a -> list Unique.Unique -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, l => Mk_UniqSet (UniqFM.delListFromUFM_Directly s l)
    end.

#[global] Definition unionUniqSets {a : Type}
   : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => Mk_UniqSet (UniqFM.plusUFM s t)
    end.

#[global] Definition unionManyUniqSets {a} (xs : list (UniqSet a))
   : UniqSet a :=
  match xs with
  | nil => emptyUniqSet
  | cons uset usets => Data.Foldable.foldr unionUniqSets uset usets
  end.

#[global] Definition minusUniqSet {a : Type}
   : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => Mk_UniqSet (UniqFM.minusUFM s t)
    end.

#[global] Definition intersectUniqSets {a : Type}
   : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => Mk_UniqSet (UniqFM.intersectUFM s t)
    end.

#[global] Definition disjointUniqSets {a : Type}
   : UniqSet a -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => UniqFM.disjointUFM s t
    end.

#[global] Definition restrictUniqSetToUFM {key : Type} {b : Type}
   : UniqSet key -> UniqFM.UniqFM key b -> UniqSet key :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, m => Mk_UniqSet (UniqFM.intersectUFM s m)
    end.

#[global] Definition uniqSetMinusUFM {key : Type} {b : Type}
   : UniqSet key -> UniqFM.UniqFM key b -> UniqSet key :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, t => Mk_UniqSet (UniqFM.minusUFM s t)
    end.

(* Skipping definition `UniqSet.uniqSetMinusUDFM' *)

#[global] Definition elementOfUniqSet {a : Type} `{Unique.Uniquable a}
   : a -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_UniqSet s => UniqFM.elemUFM a s
    end.

#[global] Definition elemUniqSet_Directly {a : Type}
   : Unique.Unique -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_UniqSet s => UniqFM.elemUFM_Directly a s
    end.

#[global] Definition filterUniqSet {a : Type}
   : (a -> bool) -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => Mk_UniqSet (UniqFM.filterUFM p s)
    end.

#[global] Definition filterUniqSet_Directly {elt : Type}
   : (Unique.Unique -> elt -> bool) -> UniqSet elt -> UniqSet elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_UniqSet s => Mk_UniqSet (UniqFM.filterUFM_Directly f s)
    end.

#[global] Definition partitionUniqSet {a : Type}
   : (a -> bool) -> UniqSet a -> (UniqSet a * UniqSet a)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => GHC.Prim.coerce (UniqFM.partitionUFM p s)
    end.

#[global] Definition uniqSetAny {a : Type} : (a -> bool) -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => UniqFM.anyUFM p s
    end.

#[global] Definition uniqSetAll {a : Type} : (a -> bool) -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => UniqFM.allUFM p s
    end.

#[global] Definition sizeUniqSet {a : Type} : UniqSet a -> nat :=
  fun '(Mk_UniqSet s) => UniqFM.sizeUFM s.

#[global] Definition isEmptyUniqSet {a : Type} : UniqSet a -> bool :=
  fun '(Mk_UniqSet s) => UniqFM.isNullUFM s.

#[global] Definition lookupUniqSet {key : Type} `{Unique.Uniquable key}
   : UniqSet key -> key -> option key :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, k => UniqFM.lookupUFM s k
    end.

#[global] Definition lookupUniqSet_Directly {a : Type}
   : UniqSet a -> Unique.Unique -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, k => UniqFM.lookupUFM_Directly s k
    end.

#[global] Definition nonDetEltsUniqSet {elt : Type} : UniqSet elt -> list elt :=
  UniqFM.nonDetEltsUFM GHC.Base.∘ getUniqSet'.

#[global] Definition nonDetKeysUniqSet {elt : Type}
   : UniqSet elt -> list Unique.Unique :=
  UniqFM.nonDetKeysUFM GHC.Base.∘ getUniqSet'.

#[global] Definition nonDetStrictFoldUniqSet {elt : Type} {a : Type}
   : (elt -> a -> a) -> a -> UniqSet elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | c, n, Mk_UniqSet s => UniqFM.nonDetStrictFoldUFM c n s
    end.

#[global] Definition mapUniqSet {b : Type} {a : Type} `{Unique.Uniquable b}
   : (a -> b) -> UniqSet a -> UniqSet b :=
  fun f => mkUniqSet GHC.Base.∘ (GHC.Base.map f GHC.Base.∘ nonDetEltsUniqSet).

#[global] Definition getUniqSet {a : Type} : UniqSet a -> UniqFM.UniqFM a a :=
  getUniqSet'.

#[global] Definition unsafeUFMToUniqSet {a : Type}
   : UniqFM.UniqFM a a -> UniqSet a :=
  Mk_UniqSet.

(* Skipping definition `UniqSet.pprUniqSet' *)

(* External variables:
     Type bool cons list nat op_zt__ option Data.Foldable.foldl' Data.Foldable.foldr
     GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.map GHC.Base.mappend
     GHC.Base.mappend__ GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__
     GHC.Base.op_z2218U__ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Prim.coerce HsToRocq.Unpeel.Build_Unpeel HsToRocq.Unpeel.Unpeel
     UniqFM.UniqFM UniqFM.addToUFM UniqFM.allUFM UniqFM.anyUFM UniqFM.delFromUFM
     UniqFM.delFromUFM_Directly UniqFM.delListFromUFM UniqFM.delListFromUFM_Directly
     UniqFM.disjointUFM UniqFM.elemUFM UniqFM.elemUFM_Directly UniqFM.emptyUFM
     UniqFM.filterUFM UniqFM.filterUFM_Directly UniqFM.intersectUFM UniqFM.isNullUFM
     UniqFM.lookupUFM UniqFM.lookupUFM_Directly UniqFM.minusUFM UniqFM.nonDetEltsUFM
     UniqFM.nonDetKeysUFM UniqFM.nonDetStrictFoldUFM UniqFM.partitionUFM
     UniqFM.plusUFM UniqFM.sizeUFM UniqFM.unitUFM Unique.Uniquable Unique.Unique
*)
