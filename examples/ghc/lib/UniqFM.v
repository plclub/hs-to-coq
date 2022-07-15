(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require Data.IntSet.Internal.
Require GHC.Base.
Require GHC.Prim.
Require HsToCoq.Unpeel.
Require IntMap.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UniqFM ele : Type := | UFM : (IntMap.IntMap ele) -> UniqFM ele.

Arguments UFM {_} _.

(* Midamble *)

Require GHC.Err.

Instance Default__UniqFM {a} : Err.Default (UniqFM a) :=
  Err.Build_Default _ (UFM IntMap.empty).

(* Converted value declarations: *)

(* Skipping all instances of class `Data.Data.Data', including
   `UniqFM.Data__UniqFM' *)

Instance Unpeel_UniqFM ele
   : HsToCoq.Unpeel.Unpeel (UniqFM ele) (IntMap.IntMap ele) :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun '(UFM y) => y) UFM.

Local Definition Eq___UniqFM_op_zeze__ {inst_ele : Type} `{GHC.Base.Eq_
  inst_ele}
   : UniqFM inst_ele -> UniqFM inst_ele -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___UniqFM_op_zsze__ {inst_ele : Type} `{GHC.Base.Eq_
  inst_ele}
   : UniqFM inst_ele -> UniqFM inst_ele -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___UniqFM {ele : Type} `{GHC.Base.Eq_ ele}
   : GHC.Base.Eq_ (UniqFM ele) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___UniqFM_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___UniqFM_op_zsze__ |}.

Local Definition Functor__UniqFM_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> UniqFM a -> UniqFM b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__UniqFM_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> UniqFM b -> UniqFM a :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__UniqFM : GHC.Base.Functor UniqFM :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__UniqFM_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__UniqFM_op_zlzd__ |}.

Definition plusUFM {elt : Type} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (IntMap.union y x)
    end.

Local Definition Semigroup__UniqFM_op_zlzlzgzg__ {inst_a : Type}
   : UniqFM inst_a -> UniqFM inst_a -> UniqFM inst_a :=
  plusUFM.

Program Instance Semigroup__UniqFM {a : Type} : GHC.Base.Semigroup (UniqFM a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__UniqFM_op_zlzlzgzg__ |}.

Local Definition Monoid__UniqFM_mappend {inst_a : Type}
   : UniqFM inst_a -> UniqFM inst_a -> UniqFM inst_a :=
  _GHC.Base.<<>>_.

Definition emptyUFM {elt : Type} : UniqFM elt :=
  UFM IntMap.empty.

Local Definition Monoid__UniqFM_mempty {inst_a : Type} : UniqFM inst_a :=
  emptyUFM.

Local Definition Monoid__UniqFM_mconcat {inst_a : Type}
   : list (UniqFM inst_a) -> UniqFM inst_a :=
  GHC.Base.foldr Monoid__UniqFM_mappend Monoid__UniqFM_mempty.

Program Instance Monoid__UniqFM {a : Type} : GHC.Base.Monoid (UniqFM a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__UniqFM_mappend ;
           GHC.Base.mconcat__ := Monoid__UniqFM_mconcat ;
           GHC.Base.mempty__ := Monoid__UniqFM_mempty |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `UniqFM.Outputable__UniqFM' *)

Definition isNullUFM {elt : Type} : UniqFM elt -> bool :=
  fun '(UFM m) => IntMap.null m.

Definition unitUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : key -> elt -> UniqFM elt :=
  fun k v => UFM (IntMap.singleton (Unique.getWordKey (Unique.getUnique k)) v).

Definition unitDirectlyUFM {elt : Type} : Unique.Unique -> elt -> UniqFM elt :=
  fun u v => UFM (IntMap.singleton (Unique.getWordKey u) v).

Definition addToUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : UniqFM elt -> key -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, k, v =>
        UFM (IntMap.insert (Unique.getWordKey (Unique.getUnique k)) v m)
    end.

Definition listToUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : list (key * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUFM m k v
                         end) emptyUFM.

Definition addToUFM_Directly {elt : Type}
   : UniqFM elt -> Unique.Unique -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, u, v => UFM (IntMap.insert (Unique.getWordKey u) v m)
    end.

Definition listToUFM_Directly {elt : Type}
   : list (Unique.Unique * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair u v => addToUFM_Directly m u v
                         end) emptyUFM.

Definition addToUFM_C {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> UniqFM elt -> key -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, UFM m, k, v =>
        UFM (IntMap.insertWith (GHC.Base.flip f) (Unique.getWordKey (Unique.getUnique
                                                                     k)) v m)
    end.

Definition listToUFM_C {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | m, pair k v => addToUFM_C f m k v
                           end) emptyUFM.

Definition addListToUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : UniqFM elt -> list (key * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUFM m k v
                         end).

Definition addListToUFM_Directly {elt : Type}
   : UniqFM elt -> list (Unique.Unique * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUFM_Directly m k v
                         end).

Definition addToUFM_Acc {key : Type} {elt : Type} {elts : Type}
  `{Unique.Uniquable key}
   : (elt -> elts -> elts) ->
     (elt -> elts) -> UniqFM elts -> key -> elt -> UniqFM elts :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | exi, new, UFM m, k, v =>
        UFM (IntMap.insertWith (fun _new old => exi v old) (Unique.getWordKey
                                                            (Unique.getUnique k)) (new v) m)
    end.

Definition alterUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (option elt -> option elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k => UFM (IntMap.alter f (Unique.getWordKey (Unique.getUnique k)) m)
    end.

Definition addListToUFM_C {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> UniqFM elt -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | m, pair k v => addToUFM_C f m k v
                           end).

Definition adjustUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (elt -> elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k =>
        UFM (IntMap.adjust f (Unique.getWordKey (Unique.getUnique k)) m)
    end.

Definition adjustUFM_Directly {elt : Type}
   : (elt -> elt) -> UniqFM elt -> Unique.Unique -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, u => UFM (IntMap.adjust f (Unique.getWordKey u) m)
    end.

Definition delFromUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k => UFM (IntMap.delete (Unique.getWordKey (Unique.getUnique k)) m)
    end.

Definition delListFromUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : UniqFM elt -> list key -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM.

Definition delFromUFM_Directly {elt : Type}
   : UniqFM elt -> Unique.Unique -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => UFM (IntMap.delete (Unique.getWordKey u) m)
    end.

Definition delListFromUFM_Directly {elt : Type}
   : UniqFM elt -> list Unique.Unique -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM_Directly.

Definition plusUFM_C {elt : Type}
   : (elt -> elt -> elt) -> UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (IntMap.unionWith f x y)
    end.

Axiom plusUFM_CD : forall {elt : Type},
                   (elt -> elt -> elt) -> UniqFM elt -> elt -> UniqFM elt -> elt -> UniqFM elt.

Axiom plusMaybeUFM_C : forall {elt : Type},
                       (elt -> elt -> option elt) -> UniqFM elt -> UniqFM elt -> UniqFM elt.

Definition plusUFMList {elt : Type} : list (UniqFM elt) -> UniqFM elt :=
  Data.Foldable.foldl' plusUFM emptyUFM.

Definition minusUFM {elt1 : Type} {elt2 : Type}
   : UniqFM elt1 -> UniqFM elt2 -> UniqFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (IntMap.difference x y)
    end.

Definition intersectUFM {elt1 : Type} {elt2 : Type}
   : UniqFM elt1 -> UniqFM elt2 -> UniqFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (IntMap.intersection x y)
    end.

Definition intersectUFM_C {elt1 : Type} {elt2 : Type} {elt3 : Type}
   : (elt1 -> elt2 -> elt3) -> UniqFM elt1 -> UniqFM elt2 -> UniqFM elt3 :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (IntMap.intersectionWith f x y)
    end.

Definition disjointUFM {elt1 : Type} {elt2 : Type}
   : UniqFM elt1 -> UniqFM elt2 -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => IntMap.null (IntMap.intersection x y)
    end.

Definition foldUFM {elt : Type} {a : Type}
   : (elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m => IntMap.foldr k z m
    end.

Definition mapUFM {elt1 : Type} {elt2 : Type}
   : (elt1 -> elt2) -> UniqFM elt1 -> UniqFM elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m => UFM (IntMap.map f m)
    end.

Definition mapUFM_Directly {elt1 : Type} {elt2 : Type}
   : (Unique.Unique -> elt1 -> elt2) -> UniqFM elt1 -> UniqFM elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m => UFM (IntMap.mapWithKey (f GHC.Base.∘ Unique.getUnique) m)
    end.

Definition filterUFM {elt : Type} : (elt -> bool) -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => UFM (IntMap.filter p m)
    end.

Definition filterUFM_Directly {elt : Type}
   : (Unique.Unique -> elt -> bool) -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => UFM (IntMap.filterWithKey (p GHC.Base.∘ Unique.getUnique) m)
    end.

Definition partitionUFM {elt : Type}
   : (elt -> bool) -> UniqFM elt -> (UniqFM elt * UniqFM elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m =>
        let 'pair left_ right_ := IntMap.partition p m in
        pair (UFM left_) (UFM right_)
    end.

Definition sizeUFM {elt : Type} : UniqFM elt -> nat :=
  fun '(UFM m) => IntMap.size m.

Definition elemUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : key -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, UFM m => IntMap.member (Unique.getWordKey (Unique.getUnique k)) m
    end.

Definition elemUFM_Directly {elt : Type}
   : Unique.Unique -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | u, UFM m => IntMap.member (Unique.getWordKey u) m
    end.

Definition lookupUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : UniqFM elt -> key -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k => IntMap.lookup (Unique.getWordKey (Unique.getUnique k)) m
    end.

Definition lookupUFM_Directly {elt : Type}
   : UniqFM elt -> Unique.Unique -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => IntMap.lookup (Unique.getWordKey u) m
    end.

Definition lookupWithDefaultUFM {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : UniqFM elt -> elt -> key -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, k =>
        IntMap.findWithDefault v (Unique.getWordKey (Unique.getUnique k)) m
    end.

Definition lookupWithDefaultUFM_Directly {elt : Type}
   : UniqFM elt -> elt -> Unique.Unique -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, u => IntMap.findWithDefault v (Unique.getWordKey u) m
    end.

Definition eltsUFM {elt : Type} : UniqFM elt -> list elt :=
  fun '(UFM m) => IntMap.elems m.

Definition ufmToSet_Directly {elt : Type}
   : UniqFM elt -> Data.IntSet.Internal.IntSet :=
  fun '(UFM m) => IntMap.keysSet m.

Definition anyUFM {elt : Type} : (elt -> bool) -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => IntMap.foldr (orb GHC.Base.∘ p) false m
    end.

Definition allUFM {elt : Type} : (elt -> bool) -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => IntMap.foldr (andb GHC.Base.∘ p) true m
    end.

Definition nonDetEltsUFM {elt : Type} : UniqFM elt -> list elt :=
  fun '(UFM m) => IntMap.elems m.

Definition seqEltsUFM {elt : Type} : (list elt -> unit) -> UniqFM elt -> unit :=
  fun seqList => seqList GHC.Base.∘ nonDetEltsUFM.

Definition nonDetKeysUFM {elt : Type} : UniqFM elt -> list Unique.Unique :=
  fun '(UFM m) => GHC.Base.map Unique.getUnique (IntMap.keys m).

Definition nonDetFoldUFM {elt : Type} {a : Type}
   : (elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m => IntMap.foldr k z m
    end.

Definition nonDetFoldUFM_Directly {elt : Type} {a : Type}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m => IntMap.foldrWithKey (k GHC.Base.∘ Unique.getUnique) z m
    end.

Definition nonDetUFMToList {elt : Type}
   : UniqFM elt -> list (Unique.Unique * elt)%type :=
  fun '(UFM m) =>
    GHC.Base.map (fun '(pair k v) => pair (Unique.getUnique k) v) (IntMap.toList m).

Definition ufmToIntMap {elt : Type} : UniqFM elt -> IntMap.IntMap elt :=
  fun '(UFM m) => m.

(* Skipping definition `UniqFM.equalKeysUFM' *)

(* Skipping definition `UniqFM.pprUniqFM' *)

(* Skipping definition `UniqFM.pprUFM' *)

Definition pprUFMWithKeys {a : Type}
   : UniqFM a ->
     (list (Unique.Unique * a)%type -> GHC.Base.String) -> GHC.Base.String :=
  fun ufm pp => pp (nonDetUFMToList ufm).

(* Skipping definition `UniqFM.pluralUFM' *)

(* External variables:
     Type andb bool false list nat op_zt__ option orb pair true unit
     Data.Foldable.foldl Data.Foldable.foldl' Data.IntSet.Internal.IntSet
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.String
     GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr GHC.Base.map
     GHC.Base.mappend__ GHC.Base.mconcat__ GHC.Base.mempty__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Prim.coerce HsToCoq.Unpeel.Build_Unpeel
     HsToCoq.Unpeel.Unpeel IntMap.IntMap IntMap.adjust IntMap.alter IntMap.delete
     IntMap.difference IntMap.elems IntMap.empty IntMap.filter IntMap.filterWithKey
     IntMap.findWithDefault IntMap.foldr IntMap.foldrWithKey IntMap.insert
     IntMap.insertWith IntMap.intersection IntMap.intersectionWith IntMap.keys
     IntMap.keysSet IntMap.lookup IntMap.map IntMap.mapWithKey IntMap.member
     IntMap.null IntMap.partition IntMap.singleton IntMap.size IntMap.toList
     IntMap.union IntMap.unionWith Unique.Uniquable Unique.Unique Unique.getUnique
     Unique.getWordKey
*)
