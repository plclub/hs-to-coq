(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require BinNat.
Require Data.Foldable.
Require Data.IntMap.Internal.
Require Data.IntSet.Internal.
Require GHC.Base.
Require GHC.Data.Word64Map.Internal.
Require GHC.Prim.
Require HsToCoq.Unpeel.
Require IntMap.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UniqFM (key : Type) (ele : Type) : Type :=
  | UFM : GHC.Data.Word64Map.Internal.Word64Map ele -> UniqFM key ele.

Inductive NonDetUniqFM (key : Type) (ele : Type) : Type :=
  | Mk_NonDetUniqFM (getNonDet : UniqFM key ele) : NonDetUniqFM key ele.

Inductive Edit (a : Type) : Type :=
  | Removed : a -> Edit a
  | Added : a -> Edit a
  | Changed : a -> a -> Edit a.

(* Midamble *)

Arguments UFM {_} {_} _.
Arguments Mk_NonDetUniqFM {_} {_} _.
Arguments Removed {_} _.
Arguments Added {_} _.
Arguments Changed {_} _ _.

Require GHC.Err.
Require Data.IntMap.Internal.

#[global] Instance Default__UniqFM {key} {ele} : Err.Default (UniqFM key ele) :=
  Err.Build_Default _ (UFM Data.IntMap.Internal.empty).

(* Functor/Semigroup/Monoid instances for UniqFM *)
#[global]
Program Instance Functor__UniqFM {key : Type} : GHC.Base.Functor (UniqFM key) :=
  fun _ k__ => k__ {|
    GHC.Base.fmap__ := fun {a} {b} f '(UFM m) => UFM (GHC.Base.fmap f m) ;
    GHC.Base.op_zlzd____ := fun {a} {b} x '(UFM m) => UFM (GHC.Base.op_zlzd__ x m)
  |}.

#[global]
Program Instance Semigroup__UniqFM {key : Type} {a : Type}
  : GHC.Base.Semigroup (UniqFM key a) :=
  fun _ k__ => k__ {|
    GHC.Base.op_zlzlzgzg____ := fun '(UFM m1) '(UFM m2) =>
      UFM (Data.IntMap.Internal.union m1 m2)
  |}.

#[global]
Program Instance Monoid__UniqFM {key : Type} {a : Type}
  : GHC.Base.Monoid (UniqFM key a) :=
  fun _ k__ => k__ {|
    GHC.Base.mappend__ := fun x y => GHC.Base.op_zlzlzgzg__ x y ;
    GHC.Base.mconcat__ := fun xs => Data.Foldable.foldr GHC.Base.op_zlzlzgzg__ (UFM Data.IntMap.Internal.empty) xs ;
    GHC.Base.mempty__ := UFM Data.IntMap.Internal.empty
  |}.

(* Manual definitions for functions that use GHC.Prim.coerce *)
#[global] Definition addToUFM_L {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (key -> elt -> elt -> elt) ->
     key -> elt -> UniqFM key elt -> (option elt * UniqFM key elt)%type :=
  fun f k v '(UFM m) =>
    let '(old, m') :=
      Data.IntMap.Internal.insertLookupWithKey
        (fun _ _n _o => f k _o _n)
        (Unique.getWordKey (Unique.getUnique k)) v m
    in (old, UFM m').

#[global] Definition mergeUFM {elta : Type} {eltb : Type} {eltc : Type} {key : Type}
   : (elta -> eltb -> option eltc) ->
     (UniqFM key elta -> UniqFM key eltc) ->
     (UniqFM key eltb -> UniqFM key eltc) ->
     UniqFM key elta -> UniqFM key eltb -> UniqFM key eltc :=
  fun f g h '(UFM xm) '(UFM ym) =>
    UFM (Data.IntMap.Internal.mergeWithKey
      (fun _ x y => f x y)
      (fun m => match g (UFM m) with | UFM r => r end)
      (fun m => match h (UFM m) with | UFM r => r end)
      xm ym).

(* Converted value declarations: *)

(* Skipping instance `UniqFM.Functor__NonDetUniqFM' of class
   `GHC.Base.Functor' *)

(* Skipping instance `UniqFM.Functor__UniqFM' of class `GHC.Base.Functor' *)

(* Skipping instance `UniqFM.Foldable__NonDetUniqFM' of class
   `Data.Foldable.Foldable' *)

(* Skipping instance `UniqFM.Traversable__NonDetUniqFM' of class
   `Data.Traversable.Traversable' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `UniqFM.Outputable__Edit' *)

(* Skipping instance `UniqFM.Semigroup__UniqFM' of class `GHC.Base.Semigroup' *)

(* Skipping instance `UniqFM.Monoid__UniqFM' of class `GHC.Base.Monoid' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `UniqFM.Outputable__UniqFM' *)

#[global] Definition emptyUFM {key : Type} {elt : Type}
   : UniqFM key elt :=
  UFM Data.IntMap.Internal.empty.

#[global] Definition isNullUFM {key : Type} {elt : Type}
   : UniqFM key elt -> bool :=
  fun '(UFM m) => Data.IntMap.Internal.null m.

#[global] Definition unitUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : key -> elt -> UniqFM key elt :=
  fun k v =>
    UFM (Data.IntMap.Internal.singleton (Unique.getWordKey (Unique.getUnique k)) v).

#[global] Definition unitDirectlyUFM {elt : Type} {key : Type}
   : Unique.Unique -> elt -> UniqFM key elt :=
  fun u v => UFM (Data.IntMap.Internal.singleton (Unique.getWordKey u) v).

#[global] Definition addToUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : UniqFM key elt -> key -> elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, k, v =>
        UFM (Data.IntMap.Internal.insert (Unique.getWordKey (Unique.getUnique k)) v m)
    end.

#[global] Definition zipToUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : list key -> list elt -> UniqFM key elt :=
  fun ks vs =>
    let fix innerZip arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | ufm, cons k kList, cons v vList => innerZip (addToUFM ufm k v) kList vList
         | ufm, _, _ => ufm
         end in
    innerZip emptyUFM ks vs.

#[global] Definition listToUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : list (key * elt)%type -> UniqFM key elt :=
  Data.Foldable.foldl' (fun arg_0__ arg_1__ =>
                          match arg_0__, arg_1__ with
                          | m, pair k v => addToUFM m k v
                          end) emptyUFM.

#[global] Definition addToUFM_Directly {key : Type} {elt : Type}
   : UniqFM key elt -> Unique.Unique -> elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, u, v => UFM (Data.IntMap.Internal.insert (Unique.getWordKey u) v m)
    end.

#[global] Definition listToUFM_Directly {elt : Type} {key : Type}
   : list (Unique.Unique * elt)%type -> UniqFM key elt :=
  Data.Foldable.foldl' (fun arg_0__ arg_1__ =>
                          match arg_0__, arg_1__ with
                          | m, pair u v => addToUFM_Directly m u v
                          end) emptyUFM.

#[global] Definition listToIdentityUFM {key : Type} `{Unique.Uniquable key}
   : list key -> UniqFM key key :=
  Data.Foldable.foldl' (fun m x => addToUFM m x x) emptyUFM.

#[global] Definition addToUFM_C {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : (elt -> elt -> elt) -> UniqFM key elt -> key -> elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, UFM m, k, v =>
        UFM (Data.IntMap.Internal.insertWith (GHC.Base.flip f) (Unique.getWordKey
                                                                (Unique.getUnique k)) v m)
    end.

#[global] Definition listToUFM_C {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : (elt -> elt -> elt) -> list (key * elt)%type -> UniqFM key elt :=
  fun f =>
    Data.Foldable.foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | m, pair k v => addToUFM_C f m k v
                            end) emptyUFM.

#[global] Definition addListToUFM {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : UniqFM key elt -> list (key * elt)%type -> UniqFM key elt :=
  Data.Foldable.foldl' (fun arg_0__ arg_1__ =>
                          match arg_0__, arg_1__ with
                          | m, pair k v => addToUFM m k v
                          end).

#[global] Definition addListToUFM_Directly {key : Type} {elt : Type}
   : UniqFM key elt -> list (Unique.Unique * elt)%type -> UniqFM key elt :=
  Data.Foldable.foldl' (fun arg_0__ arg_1__ =>
                          match arg_0__, arg_1__ with
                          | m, pair k v => addToUFM_Directly m k v
                          end).

#[global] Definition addToUFM_Acc {key : Type} {elt : Type} {elts : Type}
  `{Unique.Uniquable key}
   : (elt -> elts -> elts) ->
     (elt -> elts) -> UniqFM key elts -> key -> elt -> UniqFM key elts :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | exi, new, UFM m, k, v =>
        UFM (Data.IntMap.Internal.insertWith (fun _new old => exi v old)
             (Unique.getWordKey (Unique.getUnique k)) (new v) m)
    end.

(* Skipping definition `UniqFM.addToUFM_L' *)

#[global] Definition alterUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (option elt -> option elt) -> UniqFM key elt -> key -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k =>
        UFM (Data.IntMap.Internal.alter f (Unique.getWordKey (Unique.getUnique k)) m)
    end.

#[global] Definition alterUFM_Directly {elt : Type} {key : Type}
   : (option elt -> option elt) ->
     UniqFM key elt -> Unique.Unique -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k => UFM (Data.IntMap.Internal.alter f (Unique.getWordKey k) m)
    end.

#[global] Definition addListToUFM_C {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : (elt -> elt -> elt) ->
     UniqFM key elt -> list (key * elt)%type -> UniqFM key elt :=
  fun f =>
    Data.Foldable.foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | m, pair k v => addToUFM_C f m k v
                            end).

#[global] Definition adjustUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (elt -> elt) -> UniqFM key elt -> key -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k =>
        UFM (Data.IntMap.Internal.adjust f (Unique.getWordKey (Unique.getUnique k)) m)
    end.

#[global] Definition adjustUFM_Directly {elt : Type} {key : Type}
   : (elt -> elt) -> UniqFM key elt -> Unique.Unique -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, u => UFM (Data.IntMap.Internal.adjust f (Unique.getWordKey u) m)
    end.

#[global] Definition delFromUFM {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : UniqFM key elt -> key -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k =>
        UFM (Data.IntMap.Internal.delete (Unique.getWordKey (Unique.getUnique k)) m)
    end.

#[global] Definition delListFromUFM {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : UniqFM key elt -> list key -> UniqFM key elt :=
  Data.Foldable.foldl' delFromUFM.

#[global] Definition delFromUFM_Directly {key : Type} {elt : Type}
   : UniqFM key elt -> Unique.Unique -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => UFM (Data.IntMap.Internal.delete (Unique.getWordKey u) m)
    end.

#[global] Definition delListFromUFM_Directly {key : Type} {elt : Type}
   : UniqFM key elt -> list Unique.Unique -> UniqFM key elt :=
  Data.Foldable.foldl' delFromUFM_Directly.

#[global] Definition plusUFM {key : Type} {elt : Type}
   : UniqFM key elt -> UniqFM key elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (Data.IntMap.Internal.union y x)
    end.

#[global] Definition plusUFM_C {elt : Type} {key : Type}
   : (elt -> elt -> elt) -> UniqFM key elt -> UniqFM key elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (Data.IntMap.Internal.unionWith f x y)
    end.

#[global] Definition plusUFM_CD {elta : Type} {eltb : Type} {eltc
   : Type} {key : Type}
   : (elta -> eltb -> eltc) ->
     UniqFM key elta -> elta -> UniqFM key eltb -> eltb -> UniqFM key eltc :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | f, UFM xm, dx, UFM ym, dy =>
        UFM (Data.IntMap.Internal.mergeWithKey (fun arg_5__ arg_6__ arg_7__ =>
                                                  match arg_5__, arg_6__, arg_7__ with
                                                  | _, x, y => Some (f x y)
                                                  end) (Data.IntMap.Internal.map (fun x => f x dy))
                                               (Data.IntMap.Internal.map (fun y => f dx y)) xm ym)
    end.

#[global] Definition plusUFM_CD2 {elta : Type} {eltb : Type} {eltc
   : Type} {key : Type}
   : (option elta -> option eltb -> eltc) ->
     UniqFM key elta -> UniqFM key eltb -> UniqFM key eltc :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM xm, UFM ym =>
        UFM (Data.IntMap.Internal.mergeWithKey (fun arg_3__ arg_4__ arg_5__ =>
                                                  match arg_3__, arg_4__, arg_5__ with
                                                  | _, x, y => Some (f (Some x) (Some y))
                                                  end) (Data.IntMap.Internal.map (fun x => f (Some x) None))
                                               (Data.IntMap.Internal.map (fun y => f None (Some y))) xm ym)
    end.

(* Skipping definition `UniqFM.mergeUFM' *)

#[global] Definition plusMaybeUFM_C {elt : Type} {key : Type}
   : (elt -> elt -> option elt) ->
     UniqFM key elt -> UniqFM key elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM xm, UFM ym =>
        UFM (Data.IntMap.Internal.mergeWithKey (fun arg_3__ arg_4__ arg_5__ =>
                                                  match arg_3__, arg_4__, arg_5__ with
                                                  | _, x, y => f x y
                                                  end) GHC.Base.id GHC.Base.id xm ym)
    end.

#[global] Definition plusUFMList {key : Type} {elt : Type}
   : list (UniqFM key elt) -> UniqFM key elt :=
  Data.Foldable.foldl' plusUFM emptyUFM.

#[global] Definition ufmToIntMap {key : Type} {elt : Type}
   : UniqFM key elt -> IntMap.IntMap elt :=
  fun '(UFM m) => m.

#[global] Definition unsafeIntMapToUFM {elt : Type} {key : Type}
   : IntMap.IntMap elt -> UniqFM key elt :=
  UFM.

#[global] Definition plusUFMListWith {elt : Type} {key : Type}
   : (elt -> elt -> elt) -> list (UniqFM key elt) -> UniqFM key elt :=
  fun f xs =>
    unsafeIntMapToUFM (Data.IntMap.Internal.unionsWith f (GHC.Base.map ufmToIntMap
                                                        xs)).

#[global] Definition sequenceUFMList {key : Type} {elt : Type}
   : list (UniqFM key elt) -> UniqFM key (list elt) :=
  let cons_ : option elt -> option (list elt) -> list elt :=
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Some x, Some ys => cons x ys
      | None, Some ys => ys
      | Some x, None => cons x nil
      | None, None => nil
      end in
  Data.Foldable.foldr (plusUFM_CD2 cons_) emptyUFM.

#[global] Definition minusUFM {key : Type} {elt1 : Type} {elt2 : Type}
   : UniqFM key elt1 -> UniqFM key elt2 -> UniqFM key elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (Data.IntMap.Internal.difference x y)
    end.

#[global] Definition minusUFM_C {elt1 : Type} {elt2 : Type} {key : Type}
   : (elt1 -> elt2 -> option elt1) ->
     UniqFM key elt1 -> UniqFM key elt2 -> UniqFM key elt1 :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (Data.IntMap.Internal.differenceWith f x y)
    end.

#[global] Definition intersectUFM {key : Type} {elt1 : Type} {elt2
   : Type}
   : UniqFM key elt1 -> UniqFM key elt2 -> UniqFM key elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (Data.IntMap.Internal.intersection x y)
    end.

#[global] Definition intersectUFM_C {elt1 : Type} {elt2 : Type} {elt3
   : Type} {key : Type}
   : (elt1 -> elt2 -> elt3) ->
     UniqFM key elt1 -> UniqFM key elt2 -> UniqFM key elt3 :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (Data.IntMap.Internal.intersectionWith f x y)
    end.

#[global] Definition disjointUFM {key : Type} {elt1 : Type} {elt2
   : Type}
   : UniqFM key elt1 -> UniqFM key elt2 -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => Data.IntMap.Internal.disjoint x y
    end.

#[global] Definition nonDetFoldUFM {elt : Type} {a : Type} {key : Type}
   : (elt -> a -> a) -> a -> UniqFM key elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, z, UFM m => Data.IntMap.Internal.foldr f z m
    end.

#[global] Definition nonDetFoldWithKeyUFM {elt : Type} {a : Type}
  {key : Type}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM key elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, z, UFM m =>
        let f' := fun k e a => f (Unique.mkUniqueGrimily k) e a in
        Data.IntMap.Internal.foldrWithKey f' z m
    end.

#[global] Definition mapUFM {elt1 : Type} {elt2 : Type} {key : Type}
   : (elt1 -> elt2) -> UniqFM key elt1 -> UniqFM key elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m => UFM (Data.IntMap.Internal.map f m)
    end.

#[global] Definition mapMaybeUFM {elt1 : Type} {elt2 : Type} {key
   : Type}
   : (elt1 -> option elt2) -> UniqFM key elt1 -> UniqFM key elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m => UFM (Data.IntMap.Internal.mapMaybe f m)
    end.

#[global] Definition mapMaybeWithKeyUFM {elt1 : Type} {elt2 : Type}
  {key : Type}
   : (Unique.Unique -> elt1 -> option elt2) ->
     UniqFM key elt1 -> UniqFM key elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m =>
        UFM (Data.IntMap.Internal.mapMaybeWithKey (f GHC.Base.∘ Unique.mkUniqueGrimily)
             m)
    end.

#[global] Definition mapUFM_Directly {elt1 : Type} {elt2 : Type} {key
   : Type}
   : (Unique.Unique -> elt1 -> elt2) -> UniqFM key elt1 -> UniqFM key elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m =>
        UFM (Data.IntMap.Internal.mapWithKey (f GHC.Base.∘ Unique.mkUniqueGrimily) m)
    end.

#[global] Definition strictMapUFM {a : Type} {b : Type} {k2 : Type}
   : (a -> b) -> UniqFM k2 a -> UniqFM k2 b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM a => UFM (Data.IntMap.Internal.map f a)
    end.

#[global] Definition filterUFM {elt : Type} {key : Type}
   : (elt -> bool) -> UniqFM key elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => UFM (Data.IntMap.Internal.filter p m)
    end.

#[global] Definition filterUFM_Directly {elt : Type} {key : Type}
   : (Unique.Unique -> elt -> bool) -> UniqFM key elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m =>
        UFM (Data.IntMap.Internal.filterWithKey (p GHC.Base.∘ Unique.mkUniqueGrimily) m)
    end.

#[global] Definition partitionUFM {elt : Type} {key : Type}
   : (elt -> bool) -> UniqFM key elt -> (UniqFM key elt * UniqFM key elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m =>
        let 'pair left_ right_ := Data.IntMap.Internal.partition p m in
        pair (UFM left_) (UFM right_)
    end.

#[global] Definition sizeUFM {key : Type} {elt : Type}
   : UniqFM key elt -> nat :=
  fun '(UFM m) => BinNat.N.to_nat (Data.IntMap.Internal.size m).

#[global] Definition elemUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : key -> UniqFM key elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, UFM m =>
        Data.IntMap.Internal.member (Unique.getWordKey (Unique.getUnique k)) m
    end.

#[global] Definition elemUFM_Directly {key : Type} {elt : Type}
   : Unique.Unique -> UniqFM key elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | u, UFM m => Data.IntMap.Internal.member (Unique.getWordKey u) m
    end.

#[global] Definition lookupUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : UniqFM key elt -> key -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k =>
        Data.IntMap.Internal.lookup (Unique.getWordKey (Unique.getUnique k)) m
    end.

#[global] Definition lookupUFM_Directly {key : Type} {elt : Type}
   : UniqFM key elt -> Unique.Unique -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => Data.IntMap.Internal.lookup (Unique.getWordKey u) m
    end.

#[global] Definition lookupWithDefaultUFM {key : Type} {elt : Type}
  `{Unique.Uniquable key}
   : UniqFM key elt -> elt -> key -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, k =>
        Data.IntMap.Internal.findWithDefault v (Unique.getWordKey (Unique.getUnique k))
        m
    end.

#[global] Definition lookupWithDefaultUFM_Directly {key : Type} {elt
   : Type}
   : UniqFM key elt -> elt -> Unique.Unique -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, u => Data.IntMap.Internal.findWithDefault v (Unique.getWordKey u) m
    end.

#[global] Definition ufmToSet_Directly {key : Type} {elt : Type}
   : UniqFM key elt -> Data.IntSet.Internal.IntSet :=
  fun '(UFM m) => Data.IntMap.Internal.keysSet m.

#[global] Definition anyUFM {elt : Type} {key : Type}
   : (elt -> bool) -> UniqFM key elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => Data.IntMap.Internal.foldr (orb GHC.Base.∘ p) false m
    end.

#[global] Definition allUFM {elt : Type} {key : Type}
   : (elt -> bool) -> UniqFM key elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => Data.IntMap.Internal.foldr (andb GHC.Base.∘ p) true m
    end.

#[global] Definition seqEltsUFM {elt : Type} {key : Type}
   : (elt -> unit) -> UniqFM key elt -> unit :=
  fun seqElt => nonDetFoldUFM (fun v rest => GHC.Prim.seq (seqElt v) rest) tt.

#[global] Definition nonDetEltsUFM {key : Type} {elt : Type}
   : UniqFM key elt -> list elt :=
  fun '(UFM m) => Data.IntMap.Internal.elems m.

#[global] Definition nonDetKeysUFM {key : Type} {elt : Type}
   : UniqFM key elt -> list Unique.Unique :=
  fun '(UFM m) =>
    GHC.Base.map Unique.mkUniqueGrimily (Data.IntMap.Internal.keys m).

#[global] Definition nonDetStrictFoldUFM {elt : Type} {a : Type} {key
   : Type}
   : (elt -> a -> a) -> a -> UniqFM key elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m => Data.IntMap.Internal.foldl' (GHC.Base.flip k) z m
    end.

#[global] Definition nonDetStrictFoldUFM_DirectlyM {m : Type -> Type}
  {b : Type} {elt : Type} {key : Type} `{GHC.Base.Monad m}
   : (Unique.Unique -> b -> elt -> m b) -> b -> UniqFM key elt -> m b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, z0, UFM xs =>
        let c := fun u x k z => f (Unique.mkUniqueGrimily u) z x GHC.Base.>>= k in
        Data.IntMap.Internal.foldrWithKey c GHC.Base.return_ xs z0
    end.

#[global] Definition nonDetStrictFoldUFM_Directly {elt : Type} {a
   : Type} {key : Type}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM key elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m =>
        Data.IntMap.Internal.foldlWithKey' (fun z' i x =>
                                              k (Unique.mkUniqueGrimily i) x z') z m
    end.

#[global] Definition nonDetUFMToList {key : Type} {elt : Type}
   : UniqFM key elt -> list (Unique.Unique * elt)%type :=
  fun '(UFM m) =>
    GHC.Base.map (fun '(pair k v) => pair (Unique.mkUniqueGrimily k) v)
    (Data.IntMap.Internal.toList m).

#[global] Definition unsafeCastUFMKey {key1 : Type} {elt
   : Type} {key2 : Type}
   : UniqFM key1 elt -> UniqFM key2 elt :=
  fun '(UFM m) => UFM m.

(* Skipping definition `UniqFM.equalKeysUFM' *)

#[global] Definition diffUFM {a : Type} {key : Type} `{GHC.Base.Eq_ a}
   : UniqFM key a -> UniqFM key a -> UniqFM key (Edit a) :=
  let both :=
    fun x y => if x GHC.Base.== y : bool then None else Some (Changed x y) in
  mergeUFM both (mapUFM Removed) (mapUFM Added).

(* Skipping definition `UniqFM.pprUniqFM' *)

(* Skipping definition `UniqFM.pprUFM' *)

#[global] Definition pprUFMWithKeys {key : Type} {a : Type}
   : UniqFM key a ->
     (list (Unique.Unique * a)%type -> GHC.Base.String) -> GHC.Base.String :=
  fun ufm pp => pp (nonDetUFMToList ufm).

(* Skipping definition `UniqFM.pluralUFM' *)

Instance Unpeel_UniqFM key ele
   : HsToCoq.Unpeel.Unpeel (UniqFM key ele) (GHC.Data.Word64Map.Internal.Word64Map
                            ele) :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun '(UFM y) => y) UFM.

(* External variables:
     None Some Type andb bool cons false list mergeUFM nat nil op_zt__ option orb
     pair true tt unit BinNat.N.to_nat Data.Foldable.foldl' Data.Foldable.foldr
     Data.IntMap.Internal.adjust Data.IntMap.Internal.alter
     Data.IntMap.Internal.delete Data.IntMap.Internal.difference
     Data.IntMap.Internal.differenceWith Data.IntMap.Internal.disjoint
     Data.IntMap.Internal.elems Data.IntMap.Internal.empty
     Data.IntMap.Internal.filter Data.IntMap.Internal.filterWithKey
     Data.IntMap.Internal.findWithDefault Data.IntMap.Internal.foldl'
     Data.IntMap.Internal.foldlWithKey' Data.IntMap.Internal.foldr
     Data.IntMap.Internal.foldrWithKey Data.IntMap.Internal.insert
     Data.IntMap.Internal.insertWith Data.IntMap.Internal.intersection
     Data.IntMap.Internal.intersectionWith Data.IntMap.Internal.keys
     Data.IntMap.Internal.keysSet Data.IntMap.Internal.lookup
     Data.IntMap.Internal.map Data.IntMap.Internal.mapMaybe
     Data.IntMap.Internal.mapMaybeWithKey Data.IntMap.Internal.mapWithKey
     Data.IntMap.Internal.member Data.IntMap.Internal.mergeWithKey
     Data.IntMap.Internal.null Data.IntMap.Internal.partition
     Data.IntMap.Internal.singleton Data.IntMap.Internal.size
     Data.IntMap.Internal.toList Data.IntMap.Internal.union
     Data.IntMap.Internal.unionWith Data.IntMap.Internal.unionsWith
     Data.IntSet.Internal.IntSet GHC.Base.Eq_ GHC.Base.Monad GHC.Base.String
     GHC.Base.flip GHC.Base.id GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Data.Word64Map.Internal.Word64Map
     GHC.Prim.seq HsToCoq.Unpeel.Build_Unpeel HsToCoq.Unpeel.Unpeel IntMap.IntMap
     Unique.Uniquable Unique.Unique Unique.getUnique Unique.getWordKey
     Unique.mkUniqueGrimily
*)
