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
Require Data.IntSet.Internal.
Require Data.Map.Internal.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.Num.
Require IntMap.
Require Literal.
Require UniqFM.
Require Unique.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

#[global] Definition XT a :=
  (option a -> option a)%type.

Class TrieMap (m : Type -> Type) `{GHC.Base.Functor m} := {
  Key : Type ;
  alterTM : forall {b : Type}, Key -> XT b -> m b -> m b ;
  emptyTM : forall {a : Type}, m a ;
  filterTM : forall {a : Type}, (a -> bool) -> m a -> m a ;
  foldTM : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> m a -> b -> b ;
  lookupTM : forall {b : Type}, Key -> m b -> option b }.

Arguments Key _ {_} {_}.

Inductive MaybeMap m a : Type :=
  | MM (mm_nothing : option a) (mm_just : m a) : MaybeMap m a.

#[global] Definition LiteralMap :=
  (Data.Map.Internal.Map Literal.Literal)%type.

Axiom ListMap : forall (m : Type -> Type) (a : Type), Type.

Axiom GenMap : forall (m : Type -> Type) (a : Type), Type.

Arguments MM {_} {_} _ _.

#[global] Definition mm_just {m} {a} (arg_0__ : MaybeMap m a) :=
  let 'MM _ mm_just := arg_0__ in
  mm_just.

#[global] Definition mm_nothing {m} {a} (arg_0__ : MaybeMap m a) :=
  let 'MM mm_nothing _ := arg_0__ in
  mm_nothing.

(* Midamble *)

Instance Eq___DeBruijn__unit : GHC.Base.Eq_ (DeBruijn unit).
Proof.
Admitted.

(* Converted value declarations: *)

#[local] Definition TrieMap__IntMap_Key : Type :=
  Data.IntSet.Internal.Key.

#[global] Definition xtInt {a}
   : Data.IntSet.Internal.Key -> XT a -> IntMap.IntMap a -> IntMap.IntMap a :=
  fun k f m => IntMap.alter f k m.

#[local] Definition TrieMap__IntMap_alterTM
   : forall {b : Type},
     TrieMap__IntMap_Key -> XT b -> IntMap.IntMap b -> IntMap.IntMap b :=
  fun {b : Type} => xtInt.

#[local] Definition TrieMap__IntMap_emptyTM
   : forall {a : Type}, IntMap.IntMap a :=
  fun {a : Type} => IntMap.empty.

#[local] Definition TrieMap__IntMap_filterTM
   : forall {a : Type}, (a -> bool) -> IntMap.IntMap a -> IntMap.IntMap a :=
  fun {a : Type} => fun f m => IntMap.filter f m.

#[local] Definition TrieMap__IntMap_foldTM
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> IntMap.IntMap a -> b -> b :=
  fun {a : Type} {b : Type} => fun k m z => IntMap.foldr k z m.

#[local] Definition TrieMap__IntMap_lookupTM
   : forall {b : Type}, TrieMap__IntMap_Key -> IntMap.IntMap b -> option b :=
  fun {b : Type} => fun k m => IntMap.lookup k m.

#[global]
Program Instance TrieMap__IntMap : TrieMap IntMap.IntMap :=
  {
  Key := TrieMap__IntMap_Key ;
  alterTM := fun {b : Type} => TrieMap__IntMap_alterTM ;
  emptyTM := fun {a : Type} => TrieMap__IntMap_emptyTM ;
  filterTM := fun {a : Type} => TrieMap__IntMap_filterTM ;
  foldTM := fun {a : Type} {b : Type} => TrieMap__IntMap_foldTM ;
  lookupTM := fun {b : Type} => TrieMap__IntMap_lookupTM }.

#[local] Definition TrieMap__Map_Key {k : Type} `{GHC.Base.Ord k} : Type :=
  k.

#[local] Definition TrieMap__Map_alterTM {inst_k : Type} `{GHC.Base.Ord inst_k}
   : forall {b : Type},
     TrieMap__Map_Key ->
     XT b -> Data.Map.Internal.Map inst_k b -> Data.Map.Internal.Map inst_k b :=
  fun {b : Type} => fun k f m => Data.Map.Internal.alter f k m.

#[local] Definition TrieMap__Map_emptyTM {inst_k : Type} `{GHC.Base.Ord inst_k}
   : forall {a : Type}, Data.Map.Internal.Map inst_k a :=
  fun {a : Type} => Data.Map.Internal.empty.

#[local] Definition TrieMap__Map_filterTM {inst_k : Type} `{GHC.Base.Ord inst_k}
   : forall {a : Type},
     (a -> bool) ->
     Data.Map.Internal.Map inst_k a -> Data.Map.Internal.Map inst_k a :=
  fun {a : Type} => fun f m => Data.Map.Internal.filter f m.

#[local] Definition TrieMap__Map_foldTM {inst_k : Type} `{GHC.Base.Ord inst_k}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> Data.Map.Internal.Map inst_k a -> b -> b :=
  fun {a : Type} {b : Type} => fun k m z => Data.Map.Internal.foldr k z m.

#[local] Definition TrieMap__Map_lookupTM {inst_k : Type} `{GHC.Base.Ord inst_k}
   : forall {b : Type},
     TrieMap__Map_Key -> Data.Map.Internal.Map inst_k b -> option b :=
  fun {b : Type} => Data.Map.Internal.lookup.

#[global]
Program Instance TrieMap__Map {k : Type} `{GHC.Base.Ord k}
   : TrieMap (Data.Map.Internal.Map k) :=
  {
  Key := TrieMap__Map_Key ;
  alterTM := fun {b : Type} => TrieMap__Map_alterTM ;
  emptyTM := fun {a : Type} => TrieMap__Map_emptyTM ;
  filterTM := fun {a : Type} => TrieMap__Map_filterTM ;
  foldTM := fun {a : Type} {b : Type} => TrieMap__Map_foldTM ;
  lookupTM := fun {b : Type} => TrieMap__Map_lookupTM }.

#[local] Definition TrieMap__UniqFM_Key {key : Type} `{Unique.Uniquable key}
   : Type :=
  key.

#[local] Definition TrieMap__UniqFM_alterTM {inst_key : Type} `{Unique.Uniquable
  inst_key}
   : forall {b : Type},
     TrieMap__UniqFM_Key ->
     XT b -> UniqFM.UniqFM inst_key b -> UniqFM.UniqFM inst_key b :=
  fun {b : Type} => fun k f m => UniqFM.alterUFM f m k.

#[local] Definition TrieMap__UniqFM_emptyTM {inst_key : Type} `{Unique.Uniquable
  inst_key}
   : forall {a : Type}, UniqFM.UniqFM inst_key a :=
  fun {a : Type} => UniqFM.emptyUFM.

#[local] Definition TrieMap__UniqFM_filterTM {inst_key : Type}
  `{Unique.Uniquable inst_key}
   : forall {a : Type},
     (a -> bool) -> UniqFM.UniqFM inst_key a -> UniqFM.UniqFM inst_key a :=
  fun {a : Type} => fun f m => UniqFM.filterUFM f m.

#[local] Definition TrieMap__UniqFM_foldTM {inst_key : Type} `{Unique.Uniquable
  inst_key}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> UniqFM.UniqFM inst_key a -> b -> b :=
  fun {a : Type} {b : Type} => fun k m z => UniqFM.nonDetFoldUFM k z m.

#[local] Definition TrieMap__UniqFM_lookupTM {inst_key : Type}
  `{Unique.Uniquable inst_key}
   : forall {b : Type},
     TrieMap__UniqFM_Key -> UniqFM.UniqFM inst_key b -> option b :=
  fun {b : Type} => fun k m => UniqFM.lookupUFM m k.

#[global]
Program Instance TrieMap__UniqFM {key : Type} `{Unique.Uniquable key}
   : TrieMap (UniqFM.UniqFM key) :=
  {
  Key := TrieMap__UniqFM_Key ;
  alterTM := fun {b : Type} => TrieMap__UniqFM_alterTM ;
  emptyTM := fun {a : Type} => TrieMap__UniqFM_emptyTM ;
  filterTM := fun {a : Type} => TrieMap__UniqFM_filterTM ;
  foldTM := fun {a : Type} {b : Type} => TrieMap__UniqFM_foldTM ;
  lookupTM := fun {b : Type} => TrieMap__UniqFM_lookupTM }.

#[local] Definition Functor__MaybeMap_fmap {inst_m : Type -> Type}
  `{GHC.Base.Functor inst_m}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> MaybeMap inst_m a -> MaybeMap inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MM mn mj => MM (GHC.Base.fmap f mn) (GHC.Base.fmap f mj)
      end.

#[local] Definition Functor__MaybeMap_op_zlzd__ {inst_m : Type -> Type}
  `{GHC.Base.Functor inst_m}
   : forall {a : Type},
     forall {b : Type}, a -> MaybeMap inst_m b -> MaybeMap inst_m a :=
  fun {a : Type} {b : Type} => Functor__MaybeMap_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__MaybeMap {m : Type -> Type} `{GHC.Base.Functor m}
   : GHC.Base.Functor (MaybeMap m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__MaybeMap_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__MaybeMap_op_zlzd__ |}.

#[local] Definition TrieMap__MaybeMap_Key {m : Type -> Type} `{TrieMap m}
   : Type :=
  option (Key m).

#[global] Definition op_zbzg__ {a : Type} {b : Type} : a -> (a -> b) -> b :=
  fun x f => f x.

Notation "'_|>_'" := (op_zbzg__).

Infix "|>" := (_|>_) (at level 99).

#[global] Definition xtMaybe {k} {m} {a}
   : (forall {b}, k -> XT b -> m b -> m b) ->
     option k -> XT a -> MaybeMap m a -> MaybeMap m a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _, None, f, m =>
        let 'MM mm_nothing_4__ mm_just_5__ := m in
        MM (f (mm_nothing m)) mm_just_5__
    | tr, Some x, f, m =>
        let 'MM mm_nothing_9__ mm_just_10__ := m in
        MM mm_nothing_9__ (mm_just m |> tr _ x f)
    end.

#[local] Definition TrieMap__MaybeMap_alterTM {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {b : Type},
     TrieMap__MaybeMap_Key -> XT b -> MaybeMap inst_m b -> MaybeMap inst_m b :=
  fun {b : Type} => xtMaybe (fun {b} => alterTM).

#[local] Definition TrieMap__MaybeMap_emptyTM {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, MaybeMap inst_m a :=
  fun {a : Type} => MM None emptyTM.

#[global] Definition filterMaybe {a : Type}
   : (a -> bool) -> option a -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, None => None
    | f, (Some x as input) => if f x : bool then input else None
    end.

#[global] Definition ftMaybe {m} {a} `{TrieMap m}
   : (a -> bool) -> MaybeMap m a -> MaybeMap m a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MM mn mj => MM (filterMaybe f mn) (filterTM f mj)
    end.

#[local] Definition TrieMap__MaybeMap_filterTM {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, (a -> bool) -> MaybeMap inst_m a -> MaybeMap inst_m a :=
  fun {a : Type} => ftMaybe.

#[global] Definition foldMaybe {a : Type} {b : Type}
   : (a -> b -> b) -> option a -> b -> b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, None, b => b
    | k, Some a, b => k a b
    end.

#[global] Definition fdMaybe {m} {a} {b} `{TrieMap m}
   : (a -> b -> b) -> MaybeMap m a -> b -> b :=
  fun k m => foldMaybe k (mm_nothing m) GHC.Base.∘ foldTM k (mm_just m).

#[local] Definition TrieMap__MaybeMap_foldTM {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> MaybeMap inst_m a -> b -> b :=
  fun {a : Type} {b : Type} => fdMaybe.

#[global] Definition op_zgzizg__ {a : Type} {b : Type} {c : Type}
   : (a -> b) -> (b -> c) -> a -> c :=
  fun f g x => g (f x).

Notation "'_>.>_'" := (op_zgzizg__).

Infix ">.>" := (op_zgzizg__) (at level 99).

#[global] Definition lkMaybe {k} {m} {a}
   : (forall {b}, k -> m b -> option b) -> option k -> MaybeMap m a -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, None => mm_nothing
    | lk, Some x => op_zgzizg__ mm_just (lk _ x)
    end.

#[local] Definition TrieMap__MaybeMap_lookupTM {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {b : Type}, TrieMap__MaybeMap_Key -> MaybeMap inst_m b -> option b :=
  fun {b : Type} => lkMaybe (fun {b} => lookupTM).

#[global]
Program Instance TrieMap__MaybeMap {m : Type -> Type} `{TrieMap m}
   : TrieMap (MaybeMap m) :=
  {
  Key := TrieMap__MaybeMap_Key ;
  alterTM := fun {b : Type} => TrieMap__MaybeMap_alterTM ;
  emptyTM := fun {a : Type} => TrieMap__MaybeMap_emptyTM ;
  filterTM := fun {a : Type} => TrieMap__MaybeMap_filterTM ;
  foldTM := fun {a : Type} {b : Type} => TrieMap__MaybeMap_foldTM ;
  lookupTM := fun {b : Type} => TrieMap__MaybeMap_lookupTM }.

#[global] Definition foldMapTM {m : Type -> Type} {r : Type} {a : Type}
  `{TrieMap m} `{GHC.Base.Monoid r}
   : (a -> r) -> m a -> r :=
  fun f m => foldTM (fun x r => f x GHC.Base.<<>> r) m GHC.Base.mempty.

#[local] Definition Foldable__MaybeMap_foldMap {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> MaybeMap inst_m a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} => foldMapTM.

#[local] Definition Foldable__MaybeMap_fold {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, MaybeMap inst_m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__MaybeMap_foldMap GHC.Base.id.

#[local] Definition Foldable__MaybeMap_foldl {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> MaybeMap inst_m a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__MaybeMap_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                   (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                    GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__MaybeMap_foldr {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> MaybeMap inst_m a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__MaybeMap_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__MaybeMap_length {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, MaybeMap inst_m a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__MaybeMap_foldl (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

#[local] Definition Foldable__MaybeMap_null {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, MaybeMap inst_m a -> bool :=
  fun {a : Type} => Foldable__MaybeMap_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__MaybeMap_product {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, forall `{GHC.Num.Num a}, MaybeMap inst_m a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__MaybeMap_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__MaybeMap_sum {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, forall `{GHC.Num.Num a}, MaybeMap inst_m a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__MaybeMap_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__MaybeMap_toList {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, MaybeMap inst_m a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__MaybeMap_foldr c n t)).

#[global]
Program Instance Foldable__MaybeMap {m : Type -> Type} `{TrieMap m}
   : Data.Foldable.Foldable (MaybeMap m) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__MaybeMap_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__MaybeMap_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__MaybeMap_foldl ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__MaybeMap_foldr ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__MaybeMap_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__MaybeMap_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__MaybeMap_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__MaybeMap_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__MaybeMap_toList |}.

(* Skipping instance `TrieMap.Functor__ListMap' of class `GHC.Base.Functor' *)

#[local] Definition TrieMap__ListMap_Key {m : Type -> Type} `{TrieMap m}
   : Type :=
  list (Key m).

Axiom xtList : forall {m : Type -> Type},
               forall {k : Type},
               forall {a : Type},
               forall `{TrieMap m},
               (forall {b : Type}, k -> XT b -> m b -> m b) ->
               list k -> XT a -> ListMap m a -> ListMap m a.

#[local] Definition TrieMap__ListMap_alterTM {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {b : Type},
     TrieMap__ListMap_Key -> XT b -> ListMap inst_m b -> ListMap inst_m b :=
  fun {b : Type} => xtList (fun {b} => alterTM).

Axiom TrieMap__ListMap_emptyTM : forall {m} {a} `{TrieMap m}, ListMap m a.

#[local] Definition TrieMap__ListMap_filterTM {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, (a -> bool) -> ListMap inst_m a -> ListMap inst_m a :=
  fun {a : Type} => ftList.

Axiom fdList : forall {m} {a} {b},
               forall `{TrieMap m}, (a -> b -> b) -> ListMap m a -> b -> b.

#[local] Definition TrieMap__ListMap_foldTM {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> ListMap inst_m a -> b -> b :=
  fun {a : Type} {b : Type} => fdList.

Axiom lkList : forall {m : Type -> Type},
               forall {k : Type},
               forall {a : Type},
               forall `{TrieMap m},
               (forall {b : Type}, k -> m b -> option b) -> list k -> ListMap m a -> option a.

#[local] Definition TrieMap__ListMap_lookupTM {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {b : Type}, TrieMap__ListMap_Key -> ListMap inst_m b -> option b :=
  fun {b : Type} => lkList (fun {b} => lookupTM).

#[global]
Program Instance TrieMap__ListMap {m : Type -> Type} `{TrieMap m}
   : TrieMap (ListMap m) :=
  {
  Key := TrieMap__ListMap_Key ;
  alterTM := fun {b : Type} => TrieMap__ListMap_alterTM ;
  emptyTM := fun {a : Type} => TrieMap__ListMap_emptyTM ;
  filterTM := fun {a : Type} => TrieMap__ListMap_filterTM ;
  foldTM := fun {a : Type} {b : Type} => TrieMap__ListMap_foldTM ;
  lookupTM := fun {b : Type} => TrieMap__ListMap_lookupTM }.

#[local] Definition Foldable__ListMap_foldMap {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> ListMap inst_m a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} => foldMapTM.

#[local] Definition Foldable__ListMap_fold {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, ListMap inst_m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__ListMap_foldMap GHC.Base.id.

#[local] Definition Foldable__ListMap_foldl {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> ListMap inst_m a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__ListMap_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__ListMap_foldr {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> ListMap inst_m a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__ListMap_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__ListMap_length {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, ListMap inst_m a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__ListMap_foldl (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | c, _ => c GHC.Num.+ #1
                               end) #0.

#[local] Definition Foldable__ListMap_null {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, ListMap inst_m a -> bool :=
  fun {a : Type} => Foldable__ListMap_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__ListMap_product {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, forall `{GHC.Num.Num a}, ListMap inst_m a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__ListMap_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__ListMap_sum {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, forall `{GHC.Num.Num a}, ListMap inst_m a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__ListMap_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__ListMap_toList {inst_m : Type -> Type} `{TrieMap
  inst_m}
   : forall {a : Type}, ListMap inst_m a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__ListMap_foldr c n t)).

#[global]
Program Instance Foldable__ListMap {m : Type -> Type} `{TrieMap m}
   : Data.Foldable.Foldable (ListMap m) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__ListMap_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__ListMap_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__ListMap_foldl ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__ListMap_foldr ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__ListMap_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__ListMap_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__ListMap_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__ListMap_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__ListMap_toList |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `TrieMap.Outputable__ListMap' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `TrieMap.Outputable__GenMap' *)

Axiom mapG : forall {m : Type -> Type},
             forall {a : Type},
             forall {b : Type},
             forall `{GHC.Base.Functor m}, (a -> b) -> GenMap m a -> GenMap m b.

#[local] Definition Functor__GenMap_fmap {inst_m : Type -> Type}
  `{GHC.Base.Functor inst_m}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> GenMap inst_m a -> GenMap inst_m b :=
  fun {a : Type} {b : Type} => mapG.

#[local] Definition Functor__GenMap_op_zlzd__ {inst_m : Type -> Type}
  `{GHC.Base.Functor inst_m}
   : forall {a : Type},
     forall {b : Type}, a -> GenMap inst_m b -> GenMap inst_m a :=
  fun {a : Type} {b : Type} => Functor__GenMap_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__GenMap {m : Type -> Type} `{GHC.Base.Functor m}
   : GHC.Base.Functor (GenMap m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__GenMap_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__GenMap_op_zlzd__ |}.

Axiom GenMap__EmptyMap : forall {m} {a}, GenMap m a.

Axiom fdG : forall {m : Type -> Type},
            forall {a : Type},
            forall {b : Type}, forall `{TrieMap m}, (a -> b -> b) -> GenMap m a -> b -> b.

Axiom lkG : forall {m} {a} `{TrieMap m} `{GHC.Base.Eq_ (Key m)},
            Key m -> GenMap m a -> option a.

Axiom xtG : forall {m} {a} `{TrieMap m} `{GHC.Base.Eq_ (Key m)},
            Key m -> XT a -> GenMap m a -> GenMap m a.

Instance TrieMap__GenMap {m} `{TrieMap m} `{GHC.Base.Eq_ (Key m)}
   : TrieMap (GenMap m) :=
  Build_TrieMap (GenMap m) (Key m) (fun {b} => xtG) (fun {a} => GenMap__EmptyMap)
                (fun {a} {b} => fdG) (fun {a} => lkG) (fun {a} {b} => mapG).

#[local] Definition Foldable__GenMap_foldMap {inst_m : Type -> Type}
  `{GHC.Base.Eq_ (Key inst_m)} `{TrieMap inst_m}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GenMap inst_m a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} => foldMapTM.

#[local] Definition Foldable__GenMap_fold {inst_m : Type -> Type} `{GHC.Base.Eq_
  (Key inst_m)} `{TrieMap inst_m}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, GenMap inst_m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__GenMap_foldMap GHC.Base.id.

#[local] Definition Foldable__GenMap_foldl {inst_m : Type -> Type}
  `{GHC.Base.Eq_ (Key inst_m)} `{TrieMap inst_m}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GenMap inst_m a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__GenMap_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                 (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                  GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__GenMap_foldr {inst_m : Type -> Type}
  `{GHC.Base.Eq_ (Key inst_m)} `{TrieMap inst_m}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GenMap inst_m a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__GenMap_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__GenMap_length {inst_m : Type -> Type}
  `{GHC.Base.Eq_ (Key inst_m)} `{TrieMap inst_m}
   : forall {a : Type}, GenMap inst_m a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__GenMap_foldl (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

#[local] Definition Foldable__GenMap_null {inst_m : Type -> Type} `{GHC.Base.Eq_
  (Key inst_m)} `{TrieMap inst_m}
   : forall {a : Type}, GenMap inst_m a -> bool :=
  fun {a : Type} => Foldable__GenMap_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__GenMap_product {inst_m : Type -> Type}
  `{GHC.Base.Eq_ (Key inst_m)} `{TrieMap inst_m}
   : forall {a : Type}, forall `{GHC.Num.Num a}, GenMap inst_m a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__GenMap_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__GenMap_sum {inst_m : Type -> Type} `{GHC.Base.Eq_
  (Key inst_m)} `{TrieMap inst_m}
   : forall {a : Type}, forall `{GHC.Num.Num a}, GenMap inst_m a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__GenMap_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__GenMap_toList {inst_m : Type -> Type}
  `{GHC.Base.Eq_ (Key inst_m)} `{TrieMap inst_m}
   : forall {a : Type}, GenMap inst_m a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__GenMap_foldr c n t)).

#[global]
Program Instance Foldable__GenMap {m : Type -> Type} `{GHC.Base.Eq_ (Key m)}
  `{TrieMap m}
   : Data.Foldable.Foldable (GenMap m) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__GenMap_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__GenMap_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__GenMap_foldl ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__GenMap_foldr ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__GenMap_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__GenMap_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__GenMap_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__GenMap_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__GenMap_toList |}.

#[global] Definition insertTM {m : Type -> Type} {a : Type} `{TrieMap m}
   : Key m -> a -> m a -> m a :=
  fun k v m => alterTM k (fun arg_0__ => Some v) m.

#[global] Definition deleteTM {m : Type -> Type} {a : Type} `{TrieMap m}
   : Key m -> m a -> m a :=
  fun k m => alterTM k (fun arg_0__ => None) m.

#[global] Definition isEmptyTM {m : Type -> Type} {a : Type} `{TrieMap m}
   : m a -> bool :=
  fun m => foldTM (fun arg_0__ arg_1__ => false) m true.

#[global] Definition deMaybe {m} {a} `{TrieMap m} : option (m a) -> m a :=
  fun arg_0__ => match arg_0__ with | None => emptyTM | Some m => m end.

#[global] Definition op_zbzgzg__ {m2 : Type -> Type} {a : Type} {m1
   : Type -> Type} `{TrieMap m2}
   : (XT (m2 a) -> m1 (m2 a) -> m1 (m2 a)) ->
     (m2 a -> m2 a) -> m1 (m2 a) -> m1 (m2 a) :=
  fun f g => f (Some GHC.Base.∘ (g GHC.Base.∘ deMaybe)).

Notation "'_|>>_'" := (op_zbzgzg__).

Infix "|>>" := (_|>>_) (at level 99).

(* Skipping definition `TrieMap.ftList' *)

#[global] Definition ftG {m} {a} `{TrieMap m}
   : (a -> bool) -> GenMap m a -> GenMap m a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, EmptyMap => EmptyMap
    | f, (SingletonMap _ v as input) => if f v : bool then input else EmptyMap
    | f, MultiMap m => MultiMap (filterTM f m)
    end.

Instance TrieMap__CoercionMapG : TrieMap CoercionMapG := TrieMap__GenMap.

Instance TrieMap__TypeMapG : TrieMap TypeMapG := TrieMap__GenMap.

Instance TrieMap__CoreMapG : TrieMap CoreMapG := TrieMap__GenMap.

Module Notations.
Notation "'_TrieMap.|>_'" := (op_zbzg__).
Infix "TrieMap.|>" := (_|>_) (at level 99).
Notation "'_TrieMap.>.>_'" := (op_zgzizg__).
Infix "TrieMap.>.>" := (op_zgzizg__) (at level 99).
Notation "'_TrieMap.|>>_'" := (op_zbzgzg__).
Infix "TrieMap.|>>" := (_|>>_) (at level 99).
End Notations.

(* External variables:
     Build_TrieMap CoercionMapG CoreMapG EmptyMap Key MultiMap None SingletonMap Some
     Type TypeMapG bool false ftList list option true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.IntSet.Internal.Key Data.Map.Internal.Map
     Data.Map.Internal.alter Data.Map.Internal.empty Data.Map.Internal.filter
     Data.Map.Internal.foldr Data.Map.Internal.lookup Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monoid
     GHC.Base.Ord GHC.Base.build' GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.mempty GHC.Base.op_z2218U__
     GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__ GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__ IntMap.IntMap IntMap.alter IntMap.empty
     IntMap.filter IntMap.foldr IntMap.lookup Literal.Literal UniqFM.UniqFM
     UniqFM.alterUFM UniqFM.emptyUFM UniqFM.filterUFM UniqFM.lookupUFM
     UniqFM.nonDetFoldUFM Unique.Uniquable
*)
