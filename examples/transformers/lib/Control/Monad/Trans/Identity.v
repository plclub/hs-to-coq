(* Default settings (from HsToRocq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Fail.
Require Control.Monad.Signatures.
Require Control.Monad.Trans.Class.
Require Coq.Program.Basics.
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

(* Converted type declarations: *)

Inductive IdentityT {k : Type} (f : k -> Type) (a : k) : Type :=
  | Mk_IdentityT (runIdentityT : f a) : IdentityT f a.

Arguments Mk_IdentityT {_} {_} {_} _.

#[global] Definition runIdentityT {k : Type} {f : k -> Type} {a : k} (arg_0__
    : IdentityT f a) :=
  let 'Mk_IdentityT runIdentityT := arg_0__ in
  runIdentityT.

(* Converted value declarations: *)

#[local] Definition Eq1__IdentityT_liftEq {inst_f : Type -> Type}
  `{(Data.Functor.Classes.Eq1 inst_f)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> bool) -> IdentityT inst_f a -> IdentityT inst_f b -> bool :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_IdentityT x, Mk_IdentityT y => Data.Functor.Classes.liftEq eq x y
      end.

#[global]
Program Instance Eq1__IdentityT {f : Type -> Type} `{(Data.Functor.Classes.Eq1
   f)}
   : Data.Functor.Classes.Eq1 (IdentityT f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun (a : Type) (b : Type) =>
             Eq1__IdentityT_liftEq |}.

#[local] Definition Ord1__IdentityT_liftCompare {inst_f : Type -> Type}
  `{(Data.Functor.Classes.Ord1 inst_f)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) ->
     IdentityT inst_f a -> IdentityT inst_f b -> comparison :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_IdentityT x, Mk_IdentityT y =>
          Data.Functor.Classes.liftCompare comp x y
      end.

#[global]
Program Instance Ord1__IdentityT {f : Type -> Type} `{(Data.Functor.Classes.Ord1
   f)}
   : Data.Functor.Classes.Ord1 (IdentityT f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun (a : Type) (b : Type) =>
             Ord1__IdentityT_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Control.Monad.Trans.Identity.Read1__IdentityT' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Control.Monad.Trans.Identity.Show1__IdentityT' *)

#[local] Definition Eq___IdentityT_op_zeze__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : IdentityT inst_f inst_a -> IdentityT inst_f inst_a -> bool :=
  Data.Functor.Classes.eq1.

#[local] Definition Eq___IdentityT_op_zsze__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : IdentityT inst_f inst_a -> IdentityT inst_f inst_a -> bool :=
  fun x y => negb (Eq___IdentityT_op_zeze__ x y).

#[global]
Program Instance Eq___IdentityT {f : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Eq1 f} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (IdentityT f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___IdentityT_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___IdentityT_op_zsze__ |}.

#[local] Definition Ord__IdentityT_compare {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : IdentityT inst_f inst_a -> IdentityT inst_f inst_a -> comparison :=
  Data.Functor.Classes.compare1.

#[local] Definition Ord__IdentityT_op_zl__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : IdentityT inst_f inst_a -> IdentityT inst_f inst_a -> bool :=
  fun x y => Ord__IdentityT_compare x y GHC.Base.== Lt.

#[local] Definition Ord__IdentityT_op_zlze__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : IdentityT inst_f inst_a -> IdentityT inst_f inst_a -> bool :=
  fun x y => Ord__IdentityT_compare x y GHC.Base./= Gt.

#[local] Definition Ord__IdentityT_op_zg__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : IdentityT inst_f inst_a -> IdentityT inst_f inst_a -> bool :=
  fun x y => Ord__IdentityT_compare x y GHC.Base.== Gt.

#[local] Definition Ord__IdentityT_op_zgze__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : IdentityT inst_f inst_a -> IdentityT inst_f inst_a -> bool :=
  fun x y => Ord__IdentityT_compare x y GHC.Base./= Lt.

#[local] Definition Ord__IdentityT_max {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : IdentityT inst_f inst_a ->
     IdentityT inst_f inst_a -> IdentityT inst_f inst_a :=
  fun x y => if Ord__IdentityT_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__IdentityT_min {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : IdentityT inst_f inst_a ->
     IdentityT inst_f inst_a -> IdentityT inst_f inst_a :=
  fun x y => if Ord__IdentityT_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__IdentityT {f : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Ord1 f} `{GHC.Base.Ord a}
   : GHC.Base.Ord (IdentityT f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__IdentityT_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__IdentityT_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__IdentityT_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__IdentityT_op_zgze__ ;
           GHC.Base.compare__ := Ord__IdentityT_compare ;
           GHC.Base.max__ := Ord__IdentityT_max ;
           GHC.Base.min__ := Ord__IdentityT_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Control.Monad.Trans.Identity.Read__IdentityT' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Monad.Trans.Identity.Show__IdentityT' *)

#[global] Definition mapIdentityT {k1 : Type} {k2 : Type} {m : k1 -> Type} {a
   : k1} {n : k2 -> Type} {b : k2}
   : (m a -> n b) -> IdentityT m a -> IdentityT n b :=
  fun f => Mk_IdentityT GHC.Base.∘ (f GHC.Base.∘ runIdentityT).

#[local] Definition Functor__IdentityT_fmap {inst_m : Type -> Type}
  `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> IdentityT inst_m a -> IdentityT inst_m b :=
  fun {a : Type} {b : Type} => fun f => mapIdentityT (GHC.Base.fmap f).

#[local] Definition Functor__IdentityT_op_zlzd__ {inst_m : Type -> Type}
  `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type}, a -> IdentityT inst_m b -> IdentityT inst_m a :=
  fun {a : Type} {b : Type} => Functor__IdentityT_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__IdentityT {m : Type -> Type} `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (IdentityT m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__IdentityT_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__IdentityT_op_zlzd__ |}.

#[local] Definition Foldable__IdentityT_foldMap {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> IdentityT inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_IdentityT t => Data.Foldable.foldMap f t
      end.

#[local] Definition Foldable__IdentityT_fold {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, IdentityT inst_f m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__IdentityT_foldMap GHC.Base.id.

#[local] Definition Foldable__IdentityT_foldr {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> IdentityT inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_IdentityT t => Data.Foldable.foldr f z t
      end.

#[local] Definition Foldable__IdentityT_foldl' {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> IdentityT inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__IdentityT_foldr (fun arg_0__ arg_1__ =>
                                     match arg_0__, arg_1__ with
                                     | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                     end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__IdentityT_foldMap' {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> IdentityT inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__IdentityT_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__IdentityT_foldl {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> IdentityT inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_IdentityT t => Data.Foldable.foldl f z t
      end.

#[local] Definition Foldable__IdentityT_foldr' {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> IdentityT inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__IdentityT_foldl (fun arg_0__ arg_1__ =>
                                     match arg_0__, arg_1__ with
                                     | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                     end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__IdentityT_length {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, IdentityT inst_f a -> GHC.Num.Int :=
  fun {a : Type} => fun '(Mk_IdentityT t) => Data.Foldable.length t.

#[local] Definition Foldable__IdentityT_null {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, IdentityT inst_f a -> bool :=
  fun {a : Type} => fun '(Mk_IdentityT t) => Data.Foldable.null t.

#[local] Definition Foldable__IdentityT_product {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, IdentityT inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__IdentityT_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__IdentityT_sum {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, IdentityT inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__IdentityT_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__IdentityT_toList {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, IdentityT inst_f a -> list a :=
  fun {a : Type} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__IdentityT_foldr c n t)).

#[global]
Program Instance Foldable__IdentityT {f : Type -> Type}
  `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (IdentityT f) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__IdentityT_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__IdentityT_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__IdentityT_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) =>
             Foldable__IdentityT_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) =>
             Foldable__IdentityT_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) =>
             Foldable__IdentityT_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) =>
             Foldable__IdentityT_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__IdentityT_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__IdentityT_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__IdentityT_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__IdentityT_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__IdentityT_toList |}.

(* Skipping all instances of class `Data.Foldable1.Foldable1', including
   `Control.Monad.Trans.Identity.Foldable1__IdentityT' *)

#[local] Definition Traversable__IdentityT_traverse {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> IdentityT inst_f a -> f (IdentityT inst_f b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_IdentityT a =>
          Data.Functor.op_zlzdzg__ Mk_IdentityT (Data.Traversable.traverse f a)
      end.

#[local] Definition Traversable__IdentityT_mapM {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> IdentityT inst_f a -> m (IdentityT inst_f b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__IdentityT_traverse.

#[local] Definition Traversable__IdentityT_sequenceA {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     IdentityT inst_f (f a) -> f (IdentityT inst_f a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__IdentityT_traverse GHC.Base.id.

#[local] Definition Traversable__IdentityT_sequence {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, IdentityT inst_f (m a) -> m (IdentityT inst_f a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__IdentityT_sequenceA.

#[global]
Program Instance Traversable__IdentityT {f : Type -> Type}
  `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (IdentityT f) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__IdentityT_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__IdentityT_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__IdentityT_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__IdentityT_traverse |}.

#[global] Definition lift2IdentityT {m n p : Type -> Type} {a b c : Type}
   : (m a -> n b -> p c) -> IdentityT m a -> IdentityT n b -> IdentityT p c :=
  fun f a b => Mk_IdentityT (f (runIdentityT a) (runIdentityT b)).

#[local] Definition Applicative__IdentityT_op_zlztzg__ {inst_m : Type -> Type}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a : Type},
     forall {b : Type},
     IdentityT inst_m (a -> b) -> IdentityT inst_m a -> IdentityT inst_m b :=
  fun {a : Type} {b : Type} => lift2IdentityT _GHC.Base.<*>_.

#[local] Definition Applicative__IdentityT_liftA2 {inst_m : Type -> Type}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     IdentityT inst_m a -> IdentityT inst_m b -> IdentityT inst_m c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__IdentityT_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__IdentityT_op_ztzg__ {inst_m : Type -> Type}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a : Type},
     forall {b : Type},
     IdentityT inst_m a -> IdentityT inst_m b -> IdentityT inst_m b :=
  fun {a : Type} {b : Type} => lift2IdentityT _GHC.Base.*>_.

#[local] Definition Applicative__IdentityT_pure {inst_m : Type -> Type}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a : Type}, a -> IdentityT inst_m a :=
  fun {a : Type} => fun x => Mk_IdentityT (GHC.Base.pure x).

#[global]
Program Instance Applicative__IdentityT {m : Type -> Type}
  `{(GHC.Base.Applicative m)}
   : GHC.Base.Applicative (IdentityT m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__IdentityT_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__IdentityT_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__IdentityT_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__IdentityT_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Monad.Trans.Identity.Alternative__IdentityT' *)

#[local] Definition Monad__IdentityT_op_zgzgze__ {inst_m : Type -> Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type},
     forall {b : Type},
     IdentityT inst_m a -> (a -> IdentityT inst_m b) -> IdentityT inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k =>
      Mk_IdentityT ((runIdentityT GHC.Base.∘ k) GHC.Base.=<< runIdentityT m).

#[local] Definition Monad__IdentityT_op_zgzg__ {inst_m : Type -> Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type},
     forall {b : Type},
     IdentityT inst_m a -> IdentityT inst_m b -> IdentityT inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__IdentityT_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__IdentityT_return_ {inst_m : Type -> Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type}, a -> IdentityT inst_m a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__IdentityT {m : Type -> Type} `{(GHC.Base.Monad m)}
   : GHC.Base.Monad (IdentityT m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__IdentityT_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__IdentityT_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__IdentityT_return_ |}.

#[local] Definition MonadFail__IdentityT_fail {inst_m : Type -> Type}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a : Type}, GHC.Base.String -> IdentityT inst_m a :=
  fun {a : Type} => fun msg => Mk_IdentityT (Control.Monad.Fail.fail msg).

#[global]
Program Instance MonadFail__IdentityT {m : Type -> Type}
  `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (IdentityT m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun (a : Type) =>
             MonadFail__IdentityT_fail |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Monad.Trans.Identity.MonadPlus__IdentityT' *)

(* Skipping all instances of class `GHC.Internal.Control.Monad.Fix.MonadFix',
   including `Control.Monad.Trans.Identity.MonadFix__IdentityT' *)

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `Control.Monad.Trans.Identity.MonadIO__IdentityT' *)

(* Skipping all instances of class `Control.Monad.Zip.MonadZip', including
   `Control.Monad.Trans.Identity.MonadZip__IdentityT' *)

#[local] Definition MonadTrans__IdentityT_lift
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, m a -> IdentityT m a :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} => Mk_IdentityT.

#[global]
Program Instance MonadTrans__IdentityT
   : Control.Monad.Trans.Class.MonadTrans IdentityT :=
  fun _ k__ =>
    k__ {| Control.Monad.Trans.Class.lift__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             MonadTrans__IdentityT_lift |}.

(* Skipping all instances of class `Data.Functor.Contravariant.Contravariant',
   including `Control.Monad.Trans.Identity.Contravariant__IdentityT' *)

#[global] Definition liftCallCC {m : Type -> Type} {a : Type} {b : Type}
   : Control.Monad.Signatures.CallCC m a b ->
     Control.Monad.Signatures.CallCC (IdentityT m) a b :=
  fun callCC f =>
    Mk_IdentityT (callCC (fun c => runIdentityT (f (Mk_IdentityT GHC.Base.∘ c)))).

(* Skipping definition `Control.Monad.Trans.Identity.liftCatch' *)

(* External variables:
     Gt Lt Type bool comparison list negb Control.Monad.Fail.MonadFail
     Control.Monad.Fail.fail Control.Monad.Fail.fail__
     Control.Monad.Signatures.CallCC Control.Monad.Trans.Class.MonadTrans
     Control.Monad.Trans.Class.lift__ Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap'__
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length
     Data.Foldable.length__ Data.Foldable.null Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1 Data.Functor.Classes.Ord1
     Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.String GHC.Base.build' GHC.Base.compare__ GHC.Base.const GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.mempty
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zezlzl__ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____ GHC.Base.op_zl____
     GHC.Base.op_zlzd____ GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.op_ztzg__ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Base.return___ GHC.Num.Int GHC.Num.Num GHC.Prim.seq
*)
