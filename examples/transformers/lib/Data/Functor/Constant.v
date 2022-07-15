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
Require Data.Bifoldable.
Require Data.Bifunctor.
Require Data.Bitraversable.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Constant {k : Type} (a : Type) (b : k) : Type :=
  | Mk_Constant (getConstant : a) : Constant a b.

Arguments Mk_Constant {_} {_} {_} _.

Definition getConstant {k : Type} {a : Type} {b : k} (arg_0__ : Constant a b) :=
  let 'Mk_Constant getConstant := arg_0__ in
  getConstant.

(* Midamble *)

Require Import GHC.Prim.

Instance Default_Constant {k} {a : Type} {b : k} `{HsToCoq.Err.Default a} : HsToCoq.Err.Default (Constant a b) := Err.Build_Default _ (Mk_Constant Err.default).

Instance Unpeel_Constant {k} {a : Type} {b : k} : HsToCoq.Unpeel.Unpeel (Constant a b) a :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getConstant Mk_Constant.

(* Converted value declarations: *)

Local Definition Eq___Constant_op_zeze__ {inst_a : Type} {inst_k : Type} {inst_b
   : inst_k} `{GHC.Base.Eq_ inst_a}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Constant_op_zsze__ {inst_a : Type} {inst_k : Type} {inst_b
   : inst_k} `{GHC.Base.Eq_ inst_a}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Constant {a : Type} {k : Type} {b : k} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Constant a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Constant_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Constant_op_zsze__ |}.

Local Definition Ord__Constant_op_zl__ {inst_a : Type} {inst_k : Type} {inst_b
   : inst_k} `{GHC.Base.Ord inst_a}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Constant_op_zlze__ {inst_a : Type} {inst_k : Type} {inst_b
   : inst_k} `{GHC.Base.Ord inst_a}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Constant_op_zg__ {inst_a : Type} {inst_k : Type} {inst_b
   : inst_k} `{GHC.Base.Ord inst_a}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Constant_op_zgze__ {inst_a : Type} {inst_k : Type} {inst_b
   : inst_k} `{GHC.Base.Ord inst_a}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Constant_compare {inst_a : Type} {inst_k : Type} {inst_b
   : inst_k} `{GHC.Base.Ord inst_a}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Constant_max {inst_a : Type} {inst_k : Type} {inst_b
   : inst_k} `{GHC.Base.Ord inst_a}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> Constant inst_a inst_b :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Constant_min {inst_a : Type} {inst_k : Type} {inst_b
   : inst_k} `{GHC.Base.Ord inst_a}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> Constant inst_a inst_b :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Constant {a : Type} {k : Type} {b : k} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Constant a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Constant_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Constant_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Constant_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Constant_op_zgze__ ;
           GHC.Base.compare__ := Ord__Constant_compare ;
           GHC.Base.max__ := Ord__Constant_max ;
           GHC.Base.min__ := Ord__Constant_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Constant.Read__Constant' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Constant.Show__Constant' *)

Local Definition Eq2__Constant_liftEq2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     forall {d : Type},
     (a -> b -> bool) -> (c -> d -> bool) -> Constant a c -> Constant b d -> bool :=
  fun {a : Type} {b : Type} {c : Type} {d : Type} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | eq, _, Mk_Constant x, Mk_Constant y => eq x y
      end.

Program Instance Eq2__Constant : Data.Functor.Classes.Eq2 Constant :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq2__ := fun {a : Type}
           {b : Type}
           {c : Type}
           {d : Type} =>
             Eq2__Constant_liftEq2 |}.

Local Definition Ord2__Constant_liftCompare2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     forall {d : Type},
     (a -> b -> comparison) ->
     (c -> d -> comparison) -> Constant a c -> Constant b d -> comparison :=
  fun {a : Type} {b : Type} {c : Type} {d : Type} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | comp, _, Mk_Constant x, Mk_Constant y => comp x y
      end.

Program Instance Ord2__Constant : Data.Functor.Classes.Ord2 Constant :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare2__ := fun {a : Type}
           {b : Type}
           {c : Type}
           {d : Type} =>
             Ord2__Constant_liftCompare2 |}.

(* Skipping all instances of class `Data.Functor.Classes.Read2', including
   `Data.Functor.Constant.Read2__Constant' *)

(* Skipping all instances of class `Data.Functor.Classes.Show2', including
   `Data.Functor.Constant.Show2__Constant' *)

Local Definition Eq1__Constant_liftEq {inst_a : Type} `{(GHC.Base.Eq_ inst_a)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> bool) -> Constant inst_a a -> Constant inst_a b -> bool :=
  fun {a : Type} {b : Type} => Data.Functor.Classes.liftEq2 _GHC.Base.==_.

Program Instance Eq1__Constant {a : Type} `{(GHC.Base.Eq_ a)}
   : Data.Functor.Classes.Eq1 (Constant a) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a : Type} {b : Type} =>
             Eq1__Constant_liftEq |}.

Local Definition Ord1__Constant_liftCompare {inst_a : Type} `{(GHC.Base.Ord
   inst_a)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) ->
     Constant inst_a a -> Constant inst_a b -> comparison :=
  fun {a : Type} {b : Type} => Data.Functor.Classes.liftCompare2 GHC.Base.compare.

Program Instance Ord1__Constant {a : Type} `{(GHC.Base.Ord a)}
   : Data.Functor.Classes.Ord1 (Constant a) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a : Type} {b : Type} =>
             Ord1__Constant_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Constant.Read1__Constant' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Constant.Show1__Constant' *)

Local Definition Functor__Constant_fmap {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Constant inst_a a -> Constant inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant x => Mk_Constant x
      end.

Local Definition Functor__Constant_op_zlzd__ {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, a -> Constant inst_a b -> Constant inst_a a :=
  fun {a : Type} {b : Type} => Functor__Constant_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Constant {a : Type} : GHC.Base.Functor (Constant a) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Constant_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__Constant_op_zlzd__ |}.

Local Definition Foldable__Constant_foldMap {inst_a : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Constant inst_a a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant _ => GHC.Base.mempty
      end.

Local Definition Foldable__Constant_fold {inst_a : Type}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Constant inst_a m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Constant_foldMap GHC.Base.id.

Local Definition Foldable__Constant_foldl {inst_a : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Constant inst_a a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Constant_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                   (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                    GHC.Base.flip f)) t)) z.

Local Definition Foldable__Constant_foldr {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Constant inst_a a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Constant_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Constant_foldl' {inst_a : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Constant inst_a a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__Constant_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Constant_foldr' {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Constant inst_a a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__Constant_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Constant_length {inst_a : Type}
   : forall {a : Type}, Constant inst_a a -> GHC.Num.Int :=
  fun {a : Type} => fun '(Mk_Constant _) => #0.

Local Definition Foldable__Constant_null {inst_a : Type}
   : forall {a : Type}, Constant inst_a a -> bool :=
  fun {a : Type} => fun '(Mk_Constant _) => true.

Local Definition Foldable__Constant_product {inst_a : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Constant inst_a a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Constant_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Constant_sum {inst_a : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Constant inst_a a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Constant_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Constant_toList {inst_a : Type}
   : forall {a : Type}, Constant inst_a a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Constant_foldr c n t)).

Program Instance Foldable__Constant {a : Type}
   : Data.Foldable.Foldable (Constant a) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__Constant_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Constant_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__Constant_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} =>
             Foldable__Constant_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__Constant_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} =>
             Foldable__Constant_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__Constant_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__Constant_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Constant_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Constant_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__Constant_toList |}.

Local Definition Traversable__Constant_traverse {inst_a : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Constant inst_a a -> f (Constant inst_a b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant x => GHC.Base.pure (Mk_Constant x)
      end.

Local Definition Traversable__Constant_mapM {inst_a : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Constant inst_a a -> m (Constant inst_a b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Constant_traverse.

Local Definition Traversable__Constant_sequenceA {inst_a : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Constant inst_a (f a) -> f (Constant inst_a a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Constant_traverse GHC.Base.id.

Local Definition Traversable__Constant_sequence {inst_a : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, Constant inst_a (m a) -> m (Constant inst_a a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Constant_sequenceA.

Program Instance Traversable__Constant {a : Type}
   : Data.Traversable.Traversable (Constant a) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Constant_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Constant_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Constant_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Constant_traverse |}.

Local Definition Semigroup__Constant_op_zlzlzgzg__ {inst_k : Type} {inst_a
   : Type} {inst_b : inst_k} `{(GHC.Base.Semigroup inst_a)}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> Constant inst_a inst_b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Constant x, Mk_Constant y => Mk_Constant (x GHC.Base.<<>> y)
    end.

Program Instance Semigroup__Constant {k : Type} {a : Type} {b : k}
  `{(GHC.Base.Semigroup a)}
   : GHC.Base.Semigroup (Constant a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Constant_op_zlzlzgzg__ |}.

Local Definition Applicative__Constant_op_zlztzg__ {inst_a : Type}
  `{(GHC.Base.Monoid inst_a)}
   : forall {a : Type},
     forall {b : Type},
     Constant inst_a (a -> b) -> Constant inst_a a -> Constant inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Constant x, Mk_Constant y => Mk_Constant (GHC.Base.mappend x y)
      end.

Local Definition Applicative__Constant_liftA2 {inst_a : Type} `{(GHC.Base.Monoid
   inst_a)}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) -> Constant inst_a a -> Constant inst_a b -> Constant inst_a c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Constant_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Constant_op_ztzg__ {inst_a : Type}
  `{(GHC.Base.Monoid inst_a)}
   : forall {a : Type},
     forall {b : Type},
     Constant inst_a a -> Constant inst_a b -> Constant inst_a b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Constant_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Constant_pure {inst_a : Type} `{(GHC.Base.Monoid
   inst_a)}
   : forall {a : Type}, a -> Constant inst_a a :=
  fun {a : Type} => fun arg_0__ => Mk_Constant GHC.Base.mempty.

Program Instance Applicative__Constant {a : Type} `{(GHC.Base.Monoid a)}
   : GHC.Base.Applicative (Constant a) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Constant_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Constant_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Constant_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Constant_pure |}.

Local Definition Monoid__Constant_mappend {inst_k : Type} {inst_a : Type}
  {inst_b : inst_k} `{(GHC.Base.Monoid inst_a)}
   : Constant inst_a inst_b -> Constant inst_a inst_b -> Constant inst_a inst_b :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Constant_mempty {inst_k : Type} {inst_a : Type} {inst_b
   : inst_k} `{(GHC.Base.Monoid inst_a)}
   : Constant inst_a inst_b :=
  Mk_Constant GHC.Base.mempty.

Local Definition Monoid__Constant_mconcat {inst_k : Type} {inst_a : Type}
  {inst_b : inst_k} `{(GHC.Base.Monoid inst_a)}
   : list (Constant inst_a inst_b) -> Constant inst_a inst_b :=
  GHC.Base.foldr Monoid__Constant_mappend Monoid__Constant_mempty.

Program Instance Monoid__Constant {k : Type} {a : Type} {b : k}
  `{(GHC.Base.Monoid a)}
   : GHC.Base.Monoid (Constant a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Constant_mappend ;
           GHC.Base.mconcat__ := Monoid__Constant_mconcat ;
           GHC.Base.mempty__ := Monoid__Constant_mempty |}.

Local Definition Bifunctor__Constant_first
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b) -> Constant a c -> Constant b c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Constant x => Mk_Constant (f x)
      end.

Local Definition Bifunctor__Constant_second
   : forall {b : Type},
     forall {c : Type},
     forall {a : Type}, (b -> c) -> Constant a b -> Constant a c :=
  fun {b : Type} {c : Type} {a : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant x => Mk_Constant x
      end.

Local Definition Bifunctor__Constant_bimap
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     forall {d : Type}, (a -> b) -> (c -> d) -> Constant a c -> Constant b d :=
  fun {a : Type} {b : Type} {c : Type} {d : Type} =>
    fun f g => Bifunctor__Constant_first f GHC.Base.∘ Bifunctor__Constant_second g.

Program Instance Bifunctor__Constant : Data.Bifunctor.Bifunctor Constant :=
  fun _ k__ =>
    k__ {| Data.Bifunctor.bimap__ := fun {a : Type}
           {b : Type}
           {c : Type}
           {d : Type} =>
             Bifunctor__Constant_bimap ;
           Data.Bifunctor.first__ := fun {a : Type} {b : Type} {c : Type} =>
             Bifunctor__Constant_first ;
           Data.Bifunctor.second__ := fun {b : Type} {c : Type} {a : Type} =>
             Bifunctor__Constant_second |}.

Local Definition Bifoldable__Constant_bifoldMap
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (b -> m) -> Constant a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Mk_Constant a => f a
      end.

Local Definition Bifoldable__Constant_bifold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Constant m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__Constant_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__Constant_bifoldl
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type}, (c -> a -> c) -> (c -> b -> c) -> c -> Constant a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__Constant_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                       (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                        GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__Constant_bifoldr
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type}, (a -> c -> c) -> (b -> c -> c) -> c -> Constant a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__Constant_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__Constant : Data.Bifoldable.Bifoldable Constant :=
  fun _ k__ =>
    k__ {| Data.Bifoldable.bifold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Bifoldable__Constant_bifold ;
           Data.Bifoldable.bifoldMap__ := fun {m : Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monoid m} =>
             Bifoldable__Constant_bifoldMap ;
           Data.Bifoldable.bifoldl__ := fun {c : Type} {a : Type} {b : Type} =>
             Bifoldable__Constant_bifoldl ;
           Data.Bifoldable.bifoldr__ := fun {a : Type} {c : Type} {b : Type} =>
             Bifoldable__Constant_bifoldr |}.

Local Definition Bitraversable__Constant_bitraverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) -> (b -> f d) -> Constant a b -> f (Constant c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Mk_Constant a => Mk_Constant Data.Functor.<$> f a
      end.

Program Instance Bitraversable__Constant
   : Data.Bitraversable.Bitraversable Constant :=
  fun _ k__ =>
    k__ {| Data.Bitraversable.bitraverse__ := fun {f : Type -> Type}
           {a : Type}
           {c : Type}
           {b : Type}
           {d : Type}
           `{GHC.Base.Applicative f} =>
             Bitraversable__Constant_bitraverse |}.

(* External variables:
     Type bool comparison list true Coq.Program.Basics.compose
     Data.Bifoldable.Bifoldable Data.Bifoldable.bifoldMap__ Data.Bifoldable.bifold__
     Data.Bifoldable.bifoldl__ Data.Bifoldable.bifoldr__ Data.Bifunctor.Bifunctor
     Data.Bifunctor.bimap__ Data.Bifunctor.first__ Data.Bifunctor.second__
     Data.Bitraversable.Bitraversable Data.Bitraversable.bitraverse__
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1 Data.Functor.Classes.Eq2
     Data.Functor.Classes.Ord1 Data.Functor.Classes.Ord2
     Data.Functor.Classes.liftCompare2 Data.Functor.Classes.liftCompare2__
     Data.Functor.Classes.liftCompare__ Data.Functor.Classes.liftEq2
     Data.Functor.Classes.liftEq2__ Data.Functor.Classes.liftEq__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.build'
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2__ GHC.Base.mappend
     GHC.Base.mappend__ GHC.Base.max GHC.Base.max__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__
     GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zl__
     GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Prim.coerce
*)
