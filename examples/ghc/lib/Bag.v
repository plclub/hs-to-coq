(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BinInt.
Require Control.Monad.
Require Coq.Program.Basics.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.Maybe.
Require Data.OldList.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require MonadUtils.
Require Util.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Bag a : Type :=
  | EmptyBag : Bag a
  | UnitBag : a -> Bag a
  | TwoBags : (Bag a) -> (Bag a) -> Bag a
  | ListBag : (GHC.Base.NonEmpty a) -> Bag a.

Arguments EmptyBag {_}.

Arguments UnitBag {_} _.

Arguments TwoBags {_} _ _.

Arguments ListBag {_} _.

(* Midamble *)

Require ZArith.BinInt.

Instance Default_Bag {a} : HsToCoq.Err.Default (Bag a):=
  HsToCoq.Err.Build_Default _ EmptyBag.

(* Converted value declarations: *)

Fixpoint Foldable__Bag_foldMap {m : Type} {a : Type} `{GHC.Base.Monoid m} (f
                                 : a -> m) (arg_1__ : Bag a) : m
  := match arg_1__ with
     | EmptyBag => GHC.Base.mempty
     | UnitBag x => f x
     | TwoBags b1 b2 =>
         GHC.Base.mappend (Foldable__Bag_foldMap f b1) (Foldable__Bag_foldMap f b2)
     | ListBag ne => Data.Foldable.foldMap f ne
     end.

#[local] Definition Foldable__Bag_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Bag m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Bag_foldMap GHC.Base.id.

#[local] Definition Foldable__Bag_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Bag a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Bag_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

Fixpoint Foldable__Bag_foldr {a : Type} {b : Type} (f : a -> b -> b) (z : b)
                             (arg_2__ : Bag a) : b
  := match arg_2__ with
     | EmptyBag => z
     | UnitBag a1 => f a1 z
     | TwoBags b1 b2 => Foldable__Bag_foldr f (Foldable__Bag_foldr f z b2) b1
     | ListBag a1 => Data.Foldable.foldr f z a1
     end.

#[local] Definition Foldable__Bag_length
   : forall {a : Type}, Bag a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Bag_foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | c, _ => c GHC.Num.+ #1
                           end) #0.

Fixpoint Foldable__Bag_null {a : Type} (arg_0__ : Bag a) : bool
  := match arg_0__ with
     | EmptyBag => true
     | UnitBag _ => false
     | TwoBags a1 a2 => andb (Foldable__Bag_null a1) (Foldable__Bag_null a2)
     | ListBag a1 => Data.Foldable.null a1
     end.

#[local] Definition Foldable__Bag_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Bag a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Bag_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Bag_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Bag a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Bag_foldMap
                                Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Bag_toList : forall {a : Type}, Bag a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Bag_foldr c n t)).

#[global]
Program Instance Foldable__Bag : Data.Foldable.Foldable Bag :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__Bag_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Bag_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__Bag_foldl ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__Bag_foldr ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__Bag_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__Bag_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Bag_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Bag_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__Bag_toList |}.

Fixpoint Functor__Bag_fmap {a : Type} {b : Type} (f : a -> b) (arg_1__ : Bag a)
  : Bag b
  := match arg_1__ with
     | EmptyBag => EmptyBag
     | UnitBag a1 => UnitBag (f a1)
     | TwoBags a1 a2 => TwoBags (Functor__Bag_fmap f a1) (Functor__Bag_fmap f a2)
     | ListBag a1 => ListBag (GHC.Base.fmap f a1)
     end.

Fixpoint Functor__Bag_op_zlzd__ {a : Type} {b : Type} (z : a) (arg_1__ : Bag b)
  : Bag a
  := match arg_1__ with
     | EmptyBag => EmptyBag
     | UnitBag _ => UnitBag z
     | TwoBags a1 a2 =>
         TwoBags (Functor__Bag_op_zlzd__ z a1) (Functor__Bag_op_zlzd__ z a2)
     | ListBag a1 => ListBag (GHC.Base.op_zlzd__ z a1)
     end.

#[global]
Program Instance Functor__Bag : GHC.Base.Functor Bag :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Bag_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Bag_op_zlzd__ |}.

Fixpoint Traversable__Bag_traverse {f : Type -> Type} {a : Type} {b : Type}
                                   `{GHC.Base.Applicative f} (fn : a -> f b) (arg_1__ : Bag a) : f (Bag b)
  := match arg_1__ with
     | EmptyBag => GHC.Base.pure EmptyBag
     | UnitBag a1 => GHC.Base.fmap (fun b1 => UnitBag b1) (fn a1)
     | TwoBags a1 a2 =>
         GHC.Base.liftA2 (fun b1 b2 => TwoBags b1 b2) (Traversable__Bag_traverse fn a1)
                         (Traversable__Bag_traverse fn a2)
     | ListBag a1 =>
         GHC.Base.fmap (fun b1 => ListBag b1) (Data.Traversable.traverse fn a1)
     end.

#[local] Definition Traversable__Bag_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Bag a -> m (Bag b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Bag_traverse.

#[local] Definition Traversable__Bag_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Applicative f}, Bag (f a) -> f (Bag a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Bag_traverse GHC.Base.id.

#[local] Definition Traversable__Bag_sequence
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, Bag (m a) -> m (Bag a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Bag_sequenceA.

#[global]
Program Instance Traversable__Bag : Data.Traversable.Traversable Bag :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Bag_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Bag_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Bag_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Bag_traverse |}.

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Bag.NFData__Bag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Bag.Outputable__Bag' *)

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `Bag.Data__Bag' *)

(* Skipping instance `Bag.IsList__Bag' of class `GHC.Internal.IsList.IsList' *)

#[global] Definition unionBags {a : Type} : Bag a -> Bag a -> Bag a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | EmptyBag, b => b
    | b, EmptyBag => b
    | b1, b2 => TwoBags b1 b2
    end.

#[local] Definition Semigroup__Bag_op_zlzlzgzg__ {inst_a : Type}
   : Bag inst_a -> Bag inst_a -> Bag inst_a :=
  unionBags.

#[global]
Program Instance Semigroup__Bag {a : Type} : GHC.Base.Semigroup (Bag a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Bag_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Bag_mappend {inst_a : Type}
   : Bag inst_a -> Bag inst_a -> Bag inst_a :=
  _GHC.Base.<<>>_.

#[global] Definition emptyBag {a : Type} : Bag a :=
  EmptyBag.

#[local] Definition Monoid__Bag_mempty {inst_a : Type} : Bag inst_a :=
  emptyBag.

#[local] Definition Monoid__Bag_mconcat {inst_a : Type}
   : list (Bag inst_a) -> Bag inst_a :=
  GHC.Base.foldr Monoid__Bag_mappend Monoid__Bag_mempty.

#[global]
Program Instance Monoid__Bag {a : Type} : GHC.Base.Monoid (Bag a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Bag_mappend ;
           GHC.Base.mconcat__ := Monoid__Bag_mconcat ;
           GHC.Base.mempty__ := Monoid__Bag_mempty |}.

#[global] Definition unitBag {a : Type} : a -> Bag a :=
  UnitBag.

Fixpoint lengthBag {a : Type} (arg_0__ : Bag a) : nat
  := match arg_0__ with
     | EmptyBag => #0
     | UnitBag _ => #1
     | TwoBags b1 b2 => lengthBag b1 GHC.Num.+ lengthBag b2
     | ListBag xs => BinInt.Z.to_nat (Data.Foldable.length xs)
     end.

Fixpoint elemBag {a : Type} `{GHC.Base.Eq_ a} (arg_0__ : a) (arg_1__ : Bag a)
  : bool
  := match arg_0__, arg_1__ with
     | _, EmptyBag => false
     | x, UnitBag y => x GHC.Base.== y
     | x, TwoBags b1 b2 => orb (elemBag x b1) (elemBag x b2)
     | x, ListBag ys => Data.Foldable.any (_GHC.Base.==_ x) ys
     end.

#[global] Definition unionManyBags {a : Type} : list (Bag a) -> Bag a :=
  fun xs => Data.Foldable.foldr unionBags EmptyBag xs.

#[global] Definition consBag {a : Type} : a -> Bag a -> Bag a :=
  fun elt bag => unionBags (unitBag elt) bag.

#[global] Definition snocBag {a : Type} : Bag a -> a -> Bag a :=
  fun bag elt => unionBags bag (unitBag elt).

#[global] Definition isEmptyBag {a : Type} : Bag a -> bool :=
  fun arg_0__ => match arg_0__ with | EmptyBag => true | _ => false end.

#[global] Definition isSingletonBag {a : Type} : Bag a -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | EmptyBag => false
    | UnitBag _ => true
    | TwoBags _ _ => false
    | ListBag (GHC.Base.NEcons _ xs) => Data.Foldable.null xs
    end.

#[global] Definition listToBag {a : Type} : list a -> Bag a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => EmptyBag
    | cons x nil => UnitBag x
    | cons x xs => ListBag (GHC.Base.NEcons x xs)
    end.

Fixpoint filterBag {a : Type} (arg_0__ : a -> bool) (arg_1__ : Bag a) : Bag a
  := match arg_0__, arg_1__ with
     | _, EmptyBag => EmptyBag
     | pred, (UnitBag val as b) => if pred val : bool then b else EmptyBag
     | pred, TwoBags b1 b2 =>
         let sat2 := filterBag pred b2 in
         let sat1 := filterBag pred b1 in unionBags sat1 sat2
     | pred, ListBag vs =>
         listToBag (GHC.List.filter pred (let 'GHC.Base.NEcons a as_ := vs in
                                          cons a as_))
     end.

Fixpoint filterBagM {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} (arg_0__
                      : a -> m bool) (arg_1__ : Bag a) : m (Bag a)
  := match arg_0__, arg_1__ with
     | _, EmptyBag => GHC.Base.return_ EmptyBag
     | pred, (UnitBag val as b) =>
         pred val GHC.Base.>>=
         (fun flag =>
            if flag : bool
            then GHC.Base.return_ b
            else GHC.Base.return_ EmptyBag)
     | pred, TwoBags b1 b2 =>
         filterBagM pred b1 GHC.Base.>>=
         (fun sat1 =>
            filterBagM pred b2 GHC.Base.>>=
            (fun sat2 => GHC.Base.return_ (unionBags sat1 sat2)))
     | pred, ListBag vs =>
         Control.Monad.filterM pred (let 'GHC.Base.NEcons a as_ := vs in cons a as_)
         GHC.Base.>>=
         (fun sat => GHC.Base.return_ (listToBag sat))
     end.

(* Skipping definition `Bag.lookupBag' *)

#[global] Definition lookup_one {a} {b} `{GHC.Base.Eq_ a}
   : a -> (a * b)%type -> option b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, pair k' v => if k GHC.Base.== k' : bool then Some v else None
    end.

Fixpoint allBag {a : Type} (arg_0__ : a -> bool) (arg_1__ : Bag a) : bool
  := match arg_0__, arg_1__ with
     | _, EmptyBag => true
     | p, UnitBag v => p v
     | p, TwoBags b1 b2 => andb (allBag p b1) (allBag p b2)
     | p, ListBag xs => Data.Foldable.all p xs
     end.

Fixpoint anyBag {a : Type} (arg_0__ : a -> bool) (arg_1__ : Bag a) : bool
  := match arg_0__, arg_1__ with
     | _, EmptyBag => false
     | p, UnitBag v => p v
     | p, TwoBags b1 b2 => orb (anyBag p b1) (anyBag p b2)
     | p, ListBag xs => Data.Foldable.any p xs
     end.

Fixpoint anyBagM {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} (arg_0__
                   : a -> m bool) (arg_1__ : Bag a) : m bool
  := match arg_0__, arg_1__ with
     | _, EmptyBag => GHC.Base.return_ false
     | p, UnitBag v => p v
     | p, TwoBags b1 b2 =>
         anyBagM p b1 GHC.Base.>>=
         (fun flag => if flag : bool then GHC.Base.return_ true else anyBagM p b2)
     | p, ListBag xs => MonadUtils.anyM p xs
     end.

#[global] Definition concatBag {a : Type} : Bag (Bag a) -> Bag a :=
  Data.Foldable.foldr unionBags emptyBag.

#[global] Definition catBagMaybes {a : Type} : Bag (option a) -> Bag a :=
  fun bs =>
    let add :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | None, rs => rs
        | Some x, rs => consBag x rs
        end in
    Data.Foldable.foldr add emptyBag bs.

Fixpoint partitionBag {a : Type} (arg_0__ : a -> bool) (arg_1__ : Bag a) : (Bag
                                                                            a *
                                                                            Bag a)%type
  := match arg_0__, arg_1__ with
     | _, EmptyBag => pair EmptyBag EmptyBag
     | pred, (UnitBag val as b) =>
         if pred val : bool
         then pair b EmptyBag
         else pair EmptyBag b
     | pred, TwoBags b1 b2 =>
         let 'pair sat2 fail2 := partitionBag pred b2 in
         let 'pair sat1 fail1 := partitionBag pred b1 in
         pair (unionBags sat1 sat2) (unionBags fail1 fail2)
     | pred, ListBag vs =>
         let 'pair sats fails := Data.OldList.partition pred (let 'GHC.Base.NEcons a
                                                                 as_ := vs in
                                                              cons a as_) in
         pair (listToBag sats) (listToBag fails)
     end.

Fixpoint partitionBagWith {a : Type} {b : Type} {c : Type} (arg_0__
                            : a -> Data.Either.Either b c) (arg_1__ : Bag a) : (Bag b * Bag c)%type
  := match arg_0__, arg_1__ with
     | _, EmptyBag => pair EmptyBag EmptyBag
     | pred, UnitBag val =>
         match pred val with
         | Data.Either.Left a => pair (UnitBag a) EmptyBag
         | Data.Either.Right b => pair EmptyBag (UnitBag b)
         end
     | pred, TwoBags b1 b2 =>
         let 'pair sat2 fail2 := partitionBagWith pred b2 in
         let 'pair sat1 fail1 := partitionBagWith pred b1 in
         pair (unionBags sat1 sat2) (unionBags fail1 fail2)
     | pred, ListBag vs =>
         let 'pair sats fails := Util.partitionWith pred (let 'GHC.Base.NEcons a as_ :=
                                                            vs in
                                                          cons a as_) in
         pair (listToBag sats) (listToBag fails)
     end.

Fixpoint foldBag {r : Type} {a : Type} (arg_0__ : r -> r -> r) (arg_1__
                   : a -> r) (arg_2__ : r) (arg_3__ : Bag a) : r
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, _, e, EmptyBag => e
     | t, u, e, UnitBag x => t (u x) e
     | t, u, e, TwoBags b1 b2 => foldBag t u (foldBag t u e b2) b1
     | t, u, e, ListBag xs => Data.Foldable.foldr (t GHC.Base.∘ u) e xs
     end.

#[global] Definition mapBag {a : Type} {b : Type}
   : (a -> b) -> Bag a -> Bag b :=
  GHC.Base.fmap.

Fixpoint concatMapBag {a : Type} {b : Type} (arg_0__ : a -> Bag b) (arg_1__
                        : Bag a) : Bag b
  := match arg_0__, arg_1__ with
     | _, EmptyBag => EmptyBag
     | f, UnitBag x => f x
     | f, TwoBags b1 b2 => unionBags (concatMapBag f b1) (concatMapBag f b2)
     | f, ListBag xs => Data.Foldable.foldr (unionBags GHC.Base.∘ f) emptyBag xs
     end.

Fixpoint concatMapBagPair {a : Type} {b : Type} {c : Type} (arg_0__
                            : a -> (Bag b * Bag c)%type) (arg_1__ : Bag a) : (Bag b * Bag c)%type
  := match arg_0__, arg_1__ with
     | _, EmptyBag => pair EmptyBag EmptyBag
     | f, UnitBag x => f x
     | f, TwoBags b1 b2 =>
         let 'pair r2 s2 := concatMapBagPair f b2 in
         let 'pair r1 s1 := concatMapBagPair f b1 in
         pair (unionBags r1 r2) (unionBags s1 s2)
     | f, ListBag xs =>
         let go :=
           fun arg_7__ arg_8__ =>
             match arg_7__, arg_8__ with
             | a, pair s1 s2 =>
                 let 'pair r1 r2 := f a in
                 pair (unionBags r1 s1) (unionBags r2 s2)
             end in
         Data.Foldable.foldr go (pair emptyBag emptyBag) xs
     end.

Fixpoint mapMaybeBag {a : Type} {b : Type} (arg_0__ : a -> option b) (arg_1__
                       : Bag a) : Bag b
  := match arg_0__, arg_1__ with
     | _, EmptyBag => EmptyBag
     | f, UnitBag x => match f x with | None => EmptyBag | Some y => UnitBag y end
     | f, TwoBags b1 b2 => unionBags (mapMaybeBag f b1) (mapMaybeBag f b2)
     | f, ListBag xs =>
         listToBag (Data.Maybe.mapMaybe f (let 'GHC.Base.NEcons a as_ := xs in
                                         cons a as_))
     end.

Fixpoint mapMaybeBagM {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad
                      m} (arg_0__ : a -> m (option b)) (arg_1__ : Bag a) : m (Bag b)
  := match arg_0__, arg_1__ with
     | _, EmptyBag => GHC.Base.return_ EmptyBag
     | f, UnitBag x =>
         f x GHC.Base.>>=
         (fun r =>
            GHC.Base.return_ (match r with | None => EmptyBag | Some y => UnitBag y end))
     | f, TwoBags b1 b2 =>
         mapMaybeBagM f b1 GHC.Base.>>=
         (fun r1 =>
            mapMaybeBagM f b2 GHC.Base.>>= (fun r2 => GHC.Base.return_ (unionBags r1 r2)))
     | f, ListBag xs =>
         Data.Functor.op_zlzdzg__ listToBag (MonadUtils.mapMaybeM f (let 'GHC.Base.NEcons
                                                                        a as_ := xs in
                                                                     cons a as_))
     end.

Fixpoint mapBagM {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m}
                 (arg_0__ : a -> m b) (arg_1__ : Bag a) : m (Bag b)
  := match arg_0__, arg_1__ with
     | _, EmptyBag => GHC.Base.return_ EmptyBag
     | f, UnitBag x => f x GHC.Base.>>= (fun r => GHC.Base.return_ (UnitBag r))
     | f, TwoBags b1 b2 =>
         mapBagM f b1 GHC.Base.>>=
         (fun r1 =>
            mapBagM f b2 GHC.Base.>>= (fun r2 => GHC.Base.return_ (TwoBags r1 r2)))
     | f, ListBag xs =>
         Data.Traversable.mapM f xs GHC.Base.>>=
         (fun rs => GHC.Base.return_ (ListBag rs))
     end.

Fixpoint mapBagM_ {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m}
                  (arg_0__ : a -> m b) (arg_1__ : Bag a) : m unit
  := match arg_0__, arg_1__ with
     | _, EmptyBag => GHC.Base.return_ tt
     | f, UnitBag x => f x GHC.Base.>> GHC.Base.return_ tt
     | f, TwoBags b1 b2 => mapBagM_ f b1 GHC.Base.>> mapBagM_ f b2
     | f, ListBag xs => Data.Foldable.mapM_ f xs
     end.

Fixpoint flatMapBagM {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad
                     m} (arg_0__ : a -> m (Bag b)) (arg_1__ : Bag a) : m (Bag b)
  := match arg_0__, arg_1__ with
     | _, EmptyBag => GHC.Base.return_ EmptyBag
     | f, UnitBag x => f x
     | f, TwoBags b1 b2 =>
         flatMapBagM f b1 GHC.Base.>>=
         (fun r1 =>
            flatMapBagM f b2 GHC.Base.>>= (fun r2 => GHC.Base.return_ (unionBags r1 r2)))
     | f, ListBag xs =>
         let k :=
           fun x b2 => f x GHC.Base.>>= (fun b1 => GHC.Base.return_ (unionBags b1 b2)) in
         Data.Foldable.foldrM k EmptyBag xs
     end.

(* Skipping definition `Bag.flatMapBagPairM' *)

(* Skipping definition `Bag.mapAndUnzipBagM' *)

Fixpoint mapAccumBagL {acc : Type} {x : Type} {y : Type} (arg_0__
                        : acc -> x -> (acc * y)%type) (arg_1__ : acc) (arg_2__ : Bag x) : (acc *
                                                                                           Bag y)%type
  := match arg_0__, arg_1__, arg_2__ with
     | _, s, EmptyBag => pair s EmptyBag
     | f, s, UnitBag x => let 'pair s1 x1 := f s x in pair s1 (UnitBag x1)
     | f, s, TwoBags b1 b2 =>
         let 'pair s1 b1' := mapAccumBagL f s b1 in
         let 'pair s2 b2' := mapAccumBagL f s1 b2 in
         pair s2 (TwoBags b1' b2')
     | f, s, ListBag xs =>
         let 'pair s' xs' := Data.Traversable.mapAccumL f s xs in
         pair s' (ListBag xs')
     end.

Fixpoint mapAccumBagLM {m : Type -> Type} {acc : Type} {x : Type} {y : Type}
                       `{GHC.Base.Monad m} (arg_0__ : acc -> x -> m (acc * y)%type) (arg_1__ : acc)
                       (arg_2__ : Bag x) : m (acc * Bag y)%type
  := match arg_0__, arg_1__, arg_2__ with
     | _, s, EmptyBag => GHC.Base.return_ (pair s EmptyBag)
     | f, s, UnitBag x =>
         let cont_4__ arg_5__ :=
           let 'pair s1 x1 := arg_5__ in
           GHC.Base.return_ (pair s1 (UnitBag x1)) in
         f s x GHC.Base.>>= cont_4__
     | f, s, TwoBags b1 b2 =>
         let cont_7__ arg_8__ :=
           let 'pair s1 b1' := arg_8__ in
           let cont_9__ arg_10__ :=
             let 'pair s2 b2' := arg_10__ in
             GHC.Base.return_ (pair s2 (TwoBags b1' b2')) in
           mapAccumBagLM f s1 b2 GHC.Base.>>= cont_9__ in
         mapAccumBagLM f s b1 GHC.Base.>>= cont_7__
     | f, s, ListBag xs =>
         let cont_12__ arg_13__ :=
           let 'pair s' xs' := arg_13__ in
           GHC.Base.return_ (pair s' (ListBag xs')) in
         MonadUtils.mapAccumLM f s xs GHC.Base.>>= cont_12__
     end.

#[global] Definition nonEmptyToBag {a : Type} : GHC.Base.NonEmpty a -> Bag a :=
  fun arg_0__ =>
    match arg_0__ with
    | GHC.Base.NEcons x nil => UnitBag x
    | xs => ListBag xs
    end.

#[global] Definition bagToList {a : Type} : Bag a -> list a :=
  fun b => Data.Foldable.foldr cons nil b.

(* Skipping definition `Bag.unzipBag' *)

Fixpoint headMaybe {a : Type} (arg_0__ : Bag a) : option a
  := match arg_0__ with
     | EmptyBag => None
     | UnitBag v => Some v
     | TwoBags b1 _ => headMaybe b1
     | ListBag (GHC.Base.NEcons v _) => Some v
     end.

(* Skipping definition `Bag.pprBag' *)

(* External variables:
     None Some Type andb bool cons false list nat nil op_zt__ option orb pair true tt
     unit BinInt.Z.to_nat Control.Monad.filterM Coq.Program.Basics.compose
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Foldable.Foldable
     Data.Foldable.all Data.Foldable.any Data.Foldable.foldMap
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl__
     Data.Foldable.foldr Data.Foldable.foldrM Data.Foldable.foldr__
     Data.Foldable.length Data.Foldable.length__ Data.Foldable.mapM_
     Data.Foldable.null Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ Data.Functor.op_zlzdzg__
     Data.Maybe.mapMaybe Data.OldList.partition Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapAccumL Data.Traversable.mapM Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.NEcons
     GHC.Base.NonEmpty GHC.Base.Semigroup GHC.Base.build' GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2 GHC.Base.mappend
     GHC.Base.mappend__ GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Base.pure GHC.Base.return_ GHC.List.filter
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ MonadUtils.anyM
     MonadUtils.mapAccumLM MonadUtils.mapMaybeM Util.partitionWith
*)
