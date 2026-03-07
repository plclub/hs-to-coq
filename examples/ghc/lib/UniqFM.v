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
Require Data.Functor.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Data.Word64Map.Internal.
Require GHC.Data.Word64Map.Strict.Internal.
Require GHC.Data.Word64Set.Internal.
Require GHC.Num.
Require GHC.Prim.
Require HsToCoq.Unpeel.
Require IntMap.
Require Unique.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive UniqFM key ele : Type :=
  | UFM : (GHC.Data.Word64Map.Internal.Word64Map ele) -> UniqFM key ele.

Inductive NonDetUniqFM key ele : Type :=
  | NonDetUniqFM (getNonDet : UniqFM key ele) : NonDetUniqFM key ele.

Inductive Edit a : Type :=
  | Removed : a -> Edit a
  | Added : a -> Edit a
  | Changed : a -> a -> Edit a.

Arguments UFM {_} {_} _.

Arguments NonDetUniqFM {_} {_} _.

Arguments Removed {_} _.

Arguments Added {_} _.

Arguments Changed {_} _ _.

#[global] Definition getNonDet {key} {ele} (arg_0__ : NonDetUniqFM key ele) :=
  let 'NonDetUniqFM getNonDet := arg_0__ in
  getNonDet.

(* Midamble *)

Require GHC.Err.

Instance Default__UniqFM {a} : Err.Default (UniqFM a) :=
  Err.Build_Default _ (UFM IntMap.empty).

(* Converted value declarations: *)

#[local] Definition Functor__NonDetUniqFM_fmap {inst_k : Type} {inst_key
   : inst_k}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> NonDetUniqFM inst_key a -> NonDetUniqFM inst_key b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce (GHC.Base.fmap).

#[local] Definition Functor__NonDetUniqFM_op_zlzd__ {inst_k : Type} {inst_key
   : inst_k}
   : forall {a : Type},
     forall {b : Type}, a -> NonDetUniqFM inst_key b -> NonDetUniqFM inst_key a :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce (GHC.Base.op_zlzd__).

#[global]
Program Instance Functor__NonDetUniqFM {k : Type} {key : k}
   : GHC.Base.Functor (NonDetUniqFM key) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} =>
             Functor__NonDetUniqFM_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__NonDetUniqFM_op_zlzd__ |}.

#[local] Definition Functor__UniqFM_fmap {inst_k : Type} {inst_key : inst_k}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> UniqFM inst_key a -> UniqFM inst_key b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce (GHC.Base.fmap).

#[local] Definition Functor__UniqFM_op_zlzd__ {inst_k : Type} {inst_key
   : inst_k}
   : forall {a : Type},
     forall {b : Type}, a -> UniqFM inst_key b -> UniqFM inst_key a :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce (GHC.Base.op_zlzd__).

#[global]
Program Instance Functor__UniqFM {k : Type} {key : k}
   : GHC.Base.Functor (UniqFM key) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__UniqFM_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__UniqFM_op_zlzd__ |}.

#[local] Definition Foldable__NonDetUniqFM_foldr {inst_k : Type} {inst_key
   : inst_k}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> NonDetUniqFM inst_key a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, NonDetUniqFM (UFM m) => Data.Foldable.foldr f z m
      end.

#[local] Definition Foldable__NonDetUniqFM_foldMap {inst_k : Type} {inst_key
   : inst_k}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> NonDetUniqFM inst_key a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__NonDetUniqFM_foldr (GHC.Base.mappend GHC.Base.∘ f) GHC.Base.mempty.

#[local] Definition Foldable__NonDetUniqFM_fold {inst_k : Type} {inst_key
   : inst_k}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, NonDetUniqFM inst_key m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Foldable__NonDetUniqFM_foldMap GHC.Base.id.

#[local] Definition Foldable__NonDetUniqFM_foldl {inst_k : Type} {inst_key
   : inst_k}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> NonDetUniqFM inst_key a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__NonDetUniqFM_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                       (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                        GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__NonDetUniqFM_length {inst_k : Type} {inst_key
   : inst_k}
   : forall {a : Type}, NonDetUniqFM inst_key a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__NonDetUniqFM_foldl (fun arg_0__ arg_1__ =>
                                    match arg_0__, arg_1__ with
                                    | c, _ => c GHC.Num.+ #1
                                    end) #0.

#[local] Definition Foldable__NonDetUniqFM_null {inst_k : Type} {inst_key
   : inst_k}
   : forall {a : Type}, NonDetUniqFM inst_key a -> bool :=
  fun {a : Type} =>
    Foldable__NonDetUniqFM_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__NonDetUniqFM_product {inst_k : Type} {inst_key
   : inst_k}
   : forall {a : Type}, forall `{GHC.Num.Num a}, NonDetUniqFM inst_key a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__NonDetUniqFM_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__NonDetUniqFM_sum {inst_k : Type} {inst_key
   : inst_k}
   : forall {a : Type}, forall `{GHC.Num.Num a}, NonDetUniqFM inst_key a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__NonDetUniqFM_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__NonDetUniqFM_toList {inst_k : Type} {inst_key
   : inst_k}
   : forall {a : Type}, NonDetUniqFM inst_key a -> list a :=
  fun {a : Type} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__NonDetUniqFM_foldr c n t)).

#[global]
Program Instance Foldable__NonDetUniqFM {k : Type} {key : k}
   : Data.Foldable.Foldable (NonDetUniqFM key) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__NonDetUniqFM_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__NonDetUniqFM_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} =>
             Foldable__NonDetUniqFM_foldl ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} =>
             Foldable__NonDetUniqFM_foldr ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__NonDetUniqFM_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__NonDetUniqFM_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__NonDetUniqFM_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__NonDetUniqFM_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__NonDetUniqFM_toList |}.

#[local] Definition Traversable__NonDetUniqFM_traverse {inst_k : Type} {inst_key
   : inst_k}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> NonDetUniqFM inst_key a -> f (NonDetUniqFM inst_key b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, NonDetUniqFM (UFM m) =>
          Data.Functor.op_zlzdzg__ (NonDetUniqFM GHC.Base.∘ UFM)
                                   (Data.Traversable.traverse f m)
      end.

#[local] Definition Traversable__NonDetUniqFM_mapM {inst_k : Type} {inst_key
   : inst_k}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> NonDetUniqFM inst_key a -> m (NonDetUniqFM inst_key b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__NonDetUniqFM_traverse.

#[local] Definition Traversable__NonDetUniqFM_sequenceA {inst_k : Type}
  {inst_key : inst_k}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     NonDetUniqFM inst_key (f a) -> f (NonDetUniqFM inst_key a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__NonDetUniqFM_traverse GHC.Base.id.

#[local] Definition Traversable__NonDetUniqFM_sequence {inst_k : Type} {inst_key
   : inst_k}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     NonDetUniqFM inst_key (m a) -> m (NonDetUniqFM inst_key a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__NonDetUniqFM_sequenceA.

#[global]
Program Instance Traversable__NonDetUniqFM {k : Type} {key : k}
   : Data.Traversable.Traversable (NonDetUniqFM key) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__NonDetUniqFM_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__NonDetUniqFM_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__NonDetUniqFM_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__NonDetUniqFM_traverse |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `UniqFM.Outputable__Edit' *)

#[global] Definition plusUFM {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> UniqFM key elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (GHC.Data.Word64Map.Internal.union y x)
    end.

#[local] Definition Semigroup__UniqFM_op_zlzlzgzg__ {inst_k : Type} {inst_key
   : inst_k} {inst_a : Type}
   : UniqFM inst_key inst_a -> UniqFM inst_key inst_a -> UniqFM inst_key inst_a :=
  plusUFM.

#[global]
Program Instance Semigroup__UniqFM {k : Type} {key : k} {a : Type}
   : GHC.Base.Semigroup (UniqFM key a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__UniqFM_op_zlzlzgzg__ |}.

#[local] Definition Monoid__UniqFM_mappend {inst_k : Type} {inst_key : inst_k}
  {inst_a : Type}
   : UniqFM inst_key inst_a -> UniqFM inst_key inst_a -> UniqFM inst_key inst_a :=
  _GHC.Base.<<>>_.

#[global] Definition emptyUFM {k : Type} {key : k} {elt : Type}
   : UniqFM key elt :=
  UFM GHC.Data.Word64Map.Internal.empty.

#[local] Definition Monoid__UniqFM_mempty {inst_k : Type} {inst_key : inst_k}
  {inst_a : Type}
   : UniqFM inst_key inst_a :=
  emptyUFM.

#[local] Definition Monoid__UniqFM_mconcat {inst_k : Type} {inst_key : inst_k}
  {inst_a : Type}
   : list (UniqFM inst_key inst_a) -> UniqFM inst_key inst_a :=
  GHC.Base.foldr Monoid__UniqFM_mappend Monoid__UniqFM_mempty.

#[global]
Program Instance Monoid__UniqFM {k : Type} {key : k} {a : Type}
   : GHC.Base.Monoid (UniqFM key a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__UniqFM_mappend ;
           GHC.Base.mconcat__ := Monoid__UniqFM_mconcat ;
           GHC.Base.mempty__ := Monoid__UniqFM_mempty |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `UniqFM.Outputable__UniqFM' *)

#[global] Definition isNullUFM {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> bool :=
  fun '(UFM m) => GHC.Data.Word64Map.Internal.null m.

#[global] Definition unitUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : key -> elt -> UniqFM key elt :=
  fun k v =>
    UFM (GHC.Data.Word64Map.Internal.singleton (Unique.getWordKey (Unique.getUnique
                                                                   k)) v).

#[global] Definition unitDirectlyUFM {k : Type} {elt : Type} {key : k}
   : Unique.Unique -> elt -> UniqFM key elt :=
  fun u v => UFM (GHC.Data.Word64Map.Internal.singleton (Unique.getWordKey u) v).

#[global] Definition addToUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : UniqFM key elt -> key -> elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, k, v =>
        UFM (GHC.Data.Word64Map.Internal.insert (Unique.getWordKey (Unique.getUnique k))
             v m)
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

#[global] Definition addToUFM_Directly {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> Unique.Unique -> elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, u, v =>
        UFM (GHC.Data.Word64Map.Internal.insert (Unique.getWordKey u) v m)
    end.

#[global] Definition listToUFM_Directly {k : Type} {elt : Type} {key : k}
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
        UFM (GHC.Data.Word64Map.Internal.insertWith (GHC.Base.flip f) (Unique.getWordKey
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

#[global] Definition addListToUFM_Directly {k : Type} {key : k} {elt : Type}
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
        UFM (GHC.Data.Word64Map.Internal.insertWith (fun _new old => exi v old)
             (Unique.getWordKey (Unique.getUnique k)) (new v) m)
    end.

#[global] Definition addToUFM_L {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : (key -> elt -> elt -> elt) ->
     key -> elt -> UniqFM key elt -> (option elt * UniqFM key elt)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, k, v, UFM m =>
        GHC.Prim.coerce (GHC.Data.Word64Map.Internal.insertLookupWithKey (fun arg_4__
                                                                          arg_5__
                                                                          arg_6__ =>
                                                                            match arg_4__, arg_5__, arg_6__ with
                                                                            | _, _n, _o => f k _o _n
                                                                            end) (Unique.getWordKey (Unique.getUnique
                                                                                                     k)) v m)
    end.

#[global] Definition alterUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (option elt -> option elt) -> UniqFM key elt -> key -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k =>
        UFM (GHC.Data.Word64Map.Internal.alter f (Unique.getWordKey (Unique.getUnique
                                                                     k)) m)
    end.

#[global] Definition alterUFM_Directly {k : Type} {elt : Type} {key : k}
   : (option elt -> option elt) ->
     UniqFM key elt -> Unique.Unique -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k =>
        UFM (GHC.Data.Word64Map.Internal.alter f (Unique.getWordKey k) m)
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
        UFM (GHC.Data.Word64Map.Internal.adjust f (Unique.getWordKey (Unique.getUnique
                                                                      k)) m)
    end.

#[global] Definition adjustUFM_Directly {k : Type} {elt : Type} {key : k}
   : (elt -> elt) -> UniqFM key elt -> Unique.Unique -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, u =>
        UFM (GHC.Data.Word64Map.Internal.adjust f (Unique.getWordKey u) m)
    end.

#[global] Definition delFromUFM {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : UniqFM key elt -> key -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k =>
        UFM (GHC.Data.Word64Map.Internal.delete (Unique.getWordKey (Unique.getUnique k))
             m)
    end.

#[global] Definition delListFromUFM {key : Type} {elt : Type} `{Unique.Uniquable
  key}
   : UniqFM key elt -> list key -> UniqFM key elt :=
  Data.Foldable.foldl' delFromUFM.

#[global] Definition delFromUFM_Directly {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> Unique.Unique -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => UFM (GHC.Data.Word64Map.Internal.delete (Unique.getWordKey u) m)
    end.

#[global] Definition delListFromUFM_Directly {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> list Unique.Unique -> UniqFM key elt :=
  Data.Foldable.foldl' delFromUFM_Directly.

#[global] Definition plusUFM_C {k : Type} {elt : Type} {key : k}
   : (elt -> elt -> elt) -> UniqFM key elt -> UniqFM key elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (GHC.Data.Word64Map.Internal.unionWith f x y)
    end.

Axiom plusUFM_CD : forall {k : Type},
                   forall {elta : Type},
                   forall {eltb : Type},
                   forall {eltc : Type},
                   forall {key : k},
                   (elta -> eltb -> eltc) ->
                   UniqFM key elta -> elta -> UniqFM key eltb -> eltb -> UniqFM key eltc.

#[global] Definition plusUFM_CD2 {k : Type} {elta : Type} {eltb : Type} {eltc
   : Type} {key : k}
   : (option elta -> option eltb -> eltc) ->
     UniqFM key elta -> UniqFM key eltb -> UniqFM key eltc :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM xm, UFM ym =>
        UFM (GHC.Data.Word64Map.Strict.Internal.mergeWithKey (fun arg_3__
                                                              arg_4__
                                                              arg_5__ =>
                                                                match arg_3__, arg_4__, arg_5__ with
                                                                | _, x, y => Some (f (Some x) (Some y))
                                                                end) (GHC.Data.Word64Map.Strict.Internal.map (fun x =>
                                                                                                                f (Some
                                                                                                                   x)
                                                                                                                  None))
                                                             (GHC.Data.Word64Map.Strict.Internal.map (fun y =>
                                                                                                        f None (Some
                                                                                                           y))) xm ym)
    end.

#[global] Definition mergeUFM {k : Type} {elta : Type} {eltb : Type} {eltc
   : Type} {key : k}
   : (elta -> eltb -> option eltc) ->
     (UniqFM key elta -> UniqFM key eltc) ->
     (UniqFM key eltb -> UniqFM key eltc) ->
     UniqFM key elta -> UniqFM key eltb -> UniqFM key eltc :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | f, g, h, UFM xm, UFM ym =>
        UFM (GHC.Data.Word64Map.Strict.Internal.mergeWithKey (fun arg_5__
                                                              arg_6__
                                                              arg_7__ =>
                                                                match arg_5__, arg_6__, arg_7__ with
                                                                | _, x, y => (f x y)
                                                                end) (GHC.Prim.coerce g) (GHC.Prim.coerce h) xm ym)
    end.

Axiom plusMaybeUFM_C : forall {k : Type},
                       forall {elt : Type},
                       forall {key : k},
                       (elt -> elt -> option elt) ->
                       UniqFM key elt -> UniqFM key elt -> UniqFM key elt.

#[global] Definition plusUFMList {k : Type} {key : k} {elt : Type}
   : list (UniqFM key elt) -> UniqFM key elt :=
  Data.Foldable.foldl' plusUFM emptyUFM.

#[global] Definition ufmToIntMap {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> GHC.Data.Word64Map.Internal.Word64Map elt :=
  fun '(UFM m) => m.

#[global] Definition unsafeIntMapToUFM {k : Type} {elt : Type} {key : k}
   : GHC.Data.Word64Map.Internal.Word64Map elt -> UniqFM key elt :=
  UFM.

#[global] Definition plusUFMListWith {k : Type} {elt : Type} {key : k}
   : (elt -> elt -> elt) -> list (UniqFM key elt) -> UniqFM key elt :=
  fun f xs =>
    unsafeIntMapToUFM (GHC.Data.Word64Map.Internal.unionsWith f (GHC.Base.map
                                                               ufmToIntMap xs)).

#[global] Definition sequenceUFMList {k : Type} {key : k} {elt : Type}
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

#[global] Definition minusUFM {k : Type} {key : k} {elt1 : Type} {elt2 : Type}
   : UniqFM key elt1 -> UniqFM key elt2 -> UniqFM key elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (GHC.Data.Word64Map.Internal.difference x y)
    end.

#[global] Definition minusUFM_C {k : Type} {elt1 : Type} {elt2 : Type} {key : k}
   : (elt1 -> elt2 -> option elt1) ->
     UniqFM key elt1 -> UniqFM key elt2 -> UniqFM key elt1 :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (GHC.Data.Word64Map.Internal.differenceWith f x y)
    end.

#[global] Definition intersectUFM {k : Type} {key : k} {elt1 : Type} {elt2
   : Type}
   : UniqFM key elt1 -> UniqFM key elt2 -> UniqFM key elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (GHC.Data.Word64Map.Internal.intersection x y)
    end.

#[global] Definition intersectUFM_C {k : Type} {elt1 : Type} {elt2 : Type} {elt3
   : Type} {key : k}
   : (elt1 -> elt2 -> elt3) ->
     UniqFM key elt1 -> UniqFM key elt2 -> UniqFM key elt3 :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (GHC.Data.Word64Map.Internal.intersectionWith f x y)
    end.

#[global] Definition disjointUFM {k : Type} {key : k} {elt1 : Type} {elt2
   : Type}
   : UniqFM key elt1 -> UniqFM key elt2 -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => GHC.Data.Word64Map.Internal.disjoint x y
    end.

#[global] Definition nonDetFoldUFM {k : Type} {elt : Type} {a : Type} {key : k}
   : (elt -> a -> a) -> a -> UniqFM key elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, z, UFM m => GHC.Data.Word64Map.Internal.foldr f z m
    end.

#[global] Definition nonDetFoldWithKeyUFM {k : Type} {elt : Type} {a : Type}
  {key : k}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM key elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, z, UFM m =>
        let f' := fun k e a => f (Unique.mkUniqueGrimily k) e a in
        GHC.Data.Word64Map.Internal.foldrWithKey f' z m
    end.

#[global] Definition mapUFM {k : Type} {elt1 : Type} {elt2 : Type} {key : k}
   : (elt1 -> elt2) -> UniqFM key elt1 -> UniqFM key elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m => UFM (GHC.Data.Word64Map.Internal.map f m)
    end.

#[global] Definition mapMaybeUFM {k : Type} {elt1 : Type} {elt2 : Type} {key
   : k}
   : (elt1 -> option elt2) -> UniqFM key elt1 -> UniqFM key elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m => UFM (GHC.Data.Word64Map.Internal.mapMaybe f m)
    end.

#[global] Definition mapMaybeWithKeyUFM {k : Type} {elt1 : Type} {elt2 : Type}
  {key : k}
   : (Unique.Unique -> elt1 -> option elt2) ->
     UniqFM key elt1 -> UniqFM key elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m =>
        UFM (GHC.Data.Word64Map.Internal.mapMaybeWithKey (f GHC.Base.∘
                                                          Unique.mkUniqueGrimily) m)
    end.

#[global] Definition mapUFM_Directly {k : Type} {elt1 : Type} {elt2 : Type} {key
   : k}
   : (Unique.Unique -> elt1 -> elt2) -> UniqFM key elt1 -> UniqFM key elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m =>
        UFM (GHC.Data.Word64Map.Internal.mapWithKey (f GHC.Base.∘
                                                     Unique.mkUniqueGrimily) m)
    end.

#[global] Definition strictMapUFM {k1 : Type} {a : Type} {b : Type} {k2 : k1}
   : (a -> b) -> UniqFM k2 a -> UniqFM k2 b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM a => UFM (GHC.Data.Word64Map.Strict.Internal.map f a)
    end.

#[global] Definition filterUFM {k : Type} {elt : Type} {key : k}
   : (elt -> bool) -> UniqFM key elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => UFM (GHC.Data.Word64Map.Internal.filter p m)
    end.

#[global] Definition filterUFM_Directly {k : Type} {elt : Type} {key : k}
   : (Unique.Unique -> elt -> bool) -> UniqFM key elt -> UniqFM key elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m =>
        UFM (GHC.Data.Word64Map.Internal.filterWithKey (p GHC.Base.∘
                                                        Unique.mkUniqueGrimily) m)
    end.

#[global] Definition partitionUFM {k : Type} {elt : Type} {key : k}
   : (elt -> bool) -> UniqFM key elt -> (UniqFM key elt * UniqFM key elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m =>
        let 'pair left_ right_ := GHC.Data.Word64Map.Internal.partition p m in
        pair (UFM left_) (UFM right_)
    end.

#[global] Definition sizeUFM {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> nat :=
  fun '(UFM m) => GHC.Data.Word64Map.Internal.size m.

#[global] Definition elemUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : key -> UniqFM key elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, UFM m =>
        GHC.Data.Word64Map.Internal.member (Unique.getWordKey (Unique.getUnique k)) m
    end.

#[global] Definition elemUFM_Directly {k : Type} {key : k} {elt : Type}
   : Unique.Unique -> UniqFM key elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | u, UFM m => GHC.Data.Word64Map.Internal.member (Unique.getWordKey u) m
    end.

#[global] Definition lookupUFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : UniqFM key elt -> key -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k =>
        GHC.Data.Word64Map.Internal.lookup (Unique.getWordKey (Unique.getUnique k)) m
    end.

#[global] Definition lookupUFM_Directly {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> Unique.Unique -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => GHC.Data.Word64Map.Internal.lookup (Unique.getWordKey u) m
    end.

#[global] Definition lookupWithDefaultUFM {key : Type} {elt : Type}
  `{Unique.Uniquable key}
   : UniqFM key elt -> elt -> key -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, k =>
        GHC.Data.Word64Map.Internal.findWithDefault v (Unique.getWordKey
                                                       (Unique.getUnique k)) m
    end.

#[global] Definition lookupWithDefaultUFM_Directly {k : Type} {key : k} {elt
   : Type}
   : UniqFM key elt -> elt -> Unique.Unique -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, u =>
        GHC.Data.Word64Map.Internal.findWithDefault v (Unique.getWordKey u) m
    end.

#[global] Definition ufmToSet_Directly {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> GHC.Data.Word64Set.Internal.Word64Set :=
  fun '(UFM m) => GHC.Data.Word64Map.Internal.keysSet m.

#[global] Definition anyUFM {k : Type} {elt : Type} {key : k}
   : (elt -> bool) -> UniqFM key elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => GHC.Data.Word64Map.Internal.foldr (orb GHC.Base.∘ p) false m
    end.

#[global] Definition allUFM {k : Type} {elt : Type} {key : k}
   : (elt -> bool) -> UniqFM key elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => GHC.Data.Word64Map.Internal.foldr (andb GHC.Base.∘ p) true m
    end.

#[global] Definition seqEltsUFM {k : Type} {elt : Type} {key : k}
   : (elt -> unit) -> UniqFM key elt -> unit :=
  fun seqElt => nonDetFoldUFM (fun v rest => GHC.Prim.seq (seqElt v) rest) tt.

#[global] Definition nonDetEltsUFM {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> list elt :=
  fun '(UFM m) => GHC.Data.Word64Map.Internal.elems m.

#[global] Definition nonDetKeysUFM {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> list Unique.Unique :=
  fun '(UFM m) =>
    GHC.Base.map Unique.mkUniqueGrimily (GHC.Data.Word64Map.Internal.keys m).

#[global] Definition nonDetStrictFoldUFM {k : Type} {elt : Type} {a : Type} {key
   : k}
   : (elt -> a -> a) -> a -> UniqFM key elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m => GHC.Data.Word64Map.Internal.foldl' (GHC.Base.flip k) z m
    end.

#[global] Definition nonDetStrictFoldUFM_DirectlyM {k : Type} {m : Type -> Type}
  {b : Type} {elt : Type} {key : k} `{GHC.Base.Monad m}
   : (Unique.Unique -> b -> elt -> m b) -> b -> UniqFM key elt -> m b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, z0, UFM xs =>
        let c := fun u x k z => f (Unique.mkUniqueGrimily u) z x GHC.Base.>>= k in
        GHC.Data.Word64Map.Internal.foldrWithKey c GHC.Base.return_ xs z0
    end.

#[global] Definition nonDetStrictFoldUFM_Directly {k : Type} {elt : Type} {a
   : Type} {key : k}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM key elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m =>
        GHC.Data.Word64Map.Internal.foldlWithKey' (fun z' i x =>
                                                     k (Unique.mkUniqueGrimily i) x z') z m
    end.

#[global] Definition nonDetUFMToList {k : Type} {key : k} {elt : Type}
   : UniqFM key elt -> list (Unique.Unique * elt)%type :=
  fun '(UFM m) =>
    GHC.Base.map (fun '(pair k v) => pair (Unique.mkUniqueGrimily k) v)
    (GHC.Data.Word64Map.Internal.toList m).

#[global] Definition unsafeCastUFMKey {k1 : Type} {k2 : Type} {key1 : k1} {elt
   : Type} {key2 : k2}
   : UniqFM key1 elt -> UniqFM key2 elt :=
  fun '(UFM m) => UFM m.

(* Skipping definition `UniqFM.equalKeysUFM' *)

#[global] Definition diffUFM {k : Type} {a : Type} {key : k} `{GHC.Base.Eq_ a}
   : UniqFM key a -> UniqFM key a -> UniqFM key (Edit a) :=
  let both :=
    fun x y => if x GHC.Base.== y : bool then None else Some (Changed x y) in
  mergeUFM both (mapUFM Removed) (mapUFM Added).

(* Skipping definition `UniqFM.pprUniqFM' *)

(* Skipping definition `UniqFM.pprUFM' *)

#[global] Definition pprUFMWithKeys {k : Type} {key : k} {a : Type}
   : UniqFM key a ->
     (list (Unique.Unique * a)%type -> GHC.Base.String) -> GHC.Base.String :=
  fun ufm pp => pp (nonDetUFMToList ufm).

(* Skipping definition `UniqFM.pluralUFM' *)

Instance Unpeel_UniqFM ele
   : HsToCoq.Unpeel.Unpeel (UniqFM ele) (IntMap.IntMap ele) :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun '(UFM y) => y) UFM.

(* External variables:
     None Some Type andb bool cons false list nat nil op_zt__ option orb pair true tt
     unit Coq.Program.Basics.compose Data.Foldable.Foldable Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl' Data.Foldable.foldl__
     Data.Foldable.foldr Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.Functor.op_zlzdzg__ Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Semigroup
     GHC.Base.String GHC.Base.build' GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.foldr GHC.Base.id GHC.Base.map GHC.Base.mappend GHC.Base.mappend__
     GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zgzgze__ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.return_
     GHC.Data.Word64Map.Internal.Word64Map GHC.Data.Word64Map.Internal.adjust
     GHC.Data.Word64Map.Internal.alter GHC.Data.Word64Map.Internal.delete
     GHC.Data.Word64Map.Internal.difference
     GHC.Data.Word64Map.Internal.differenceWith GHC.Data.Word64Map.Internal.disjoint
     GHC.Data.Word64Map.Internal.elems GHC.Data.Word64Map.Internal.empty
     GHC.Data.Word64Map.Internal.filter GHC.Data.Word64Map.Internal.filterWithKey
     GHC.Data.Word64Map.Internal.findWithDefault GHC.Data.Word64Map.Internal.foldl'
     GHC.Data.Word64Map.Internal.foldlWithKey' GHC.Data.Word64Map.Internal.foldr
     GHC.Data.Word64Map.Internal.foldrWithKey GHC.Data.Word64Map.Internal.insert
     GHC.Data.Word64Map.Internal.insertLookupWithKey
     GHC.Data.Word64Map.Internal.insertWith GHC.Data.Word64Map.Internal.intersection
     GHC.Data.Word64Map.Internal.intersectionWith GHC.Data.Word64Map.Internal.keys
     GHC.Data.Word64Map.Internal.keysSet GHC.Data.Word64Map.Internal.lookup
     GHC.Data.Word64Map.Internal.map GHC.Data.Word64Map.Internal.mapMaybe
     GHC.Data.Word64Map.Internal.mapMaybeWithKey
     GHC.Data.Word64Map.Internal.mapWithKey GHC.Data.Word64Map.Internal.member
     GHC.Data.Word64Map.Internal.null GHC.Data.Word64Map.Internal.partition
     GHC.Data.Word64Map.Internal.singleton GHC.Data.Word64Map.Internal.size
     GHC.Data.Word64Map.Internal.toList GHC.Data.Word64Map.Internal.union
     GHC.Data.Word64Map.Internal.unionWith GHC.Data.Word64Map.Internal.unionsWith
     GHC.Data.Word64Map.Strict.Internal.map
     GHC.Data.Word64Map.Strict.Internal.mergeWithKey
     GHC.Data.Word64Set.Internal.Word64Set GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.coerce GHC.Prim.seq
     HsToCoq.Unpeel.Build_Unpeel HsToCoq.Unpeel.Unpeel IntMap.IntMap Unique.Uniquable
     Unique.Unique Unique.getUnique Unique.getWordKey Unique.mkUniqueGrimily
*)
