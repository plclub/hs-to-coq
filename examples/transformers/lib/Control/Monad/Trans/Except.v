(* Default settings (from HsToCoq.Coq.Preamble) *)

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
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Classes.
Require Data.Functor.Identity.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive ExceptT e m a : Type :=
  | Mk_ExceptT : (m (Data.Either.Either e a)) -> ExceptT e m a.

Definition Except e :=
  (ExceptT e Data.Functor.Identity.Identity)%type.

Arguments Mk_ExceptT {_} {_} {_} _.

(* Converted value declarations: *)

Local Definition Eq1__ExceptT_liftEq {inst_e : Type} {inst_m : Type -> Type}
  `{GHC.Base.Eq_ inst_e} `{Data.Functor.Classes.Eq1 inst_m}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> bool) ->
     ExceptT inst_e inst_m a -> ExceptT inst_e inst_m b -> bool :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_ExceptT x, Mk_ExceptT y =>
          (@Data.Functor.Classes.liftEq inst_m _ _ _ (Data.Functor.Classes.liftEq eq)) x y
      end.

Program Instance Eq1__ExceptT {e : Type} {m : Type -> Type} `{GHC.Base.Eq_ e}
  `{Data.Functor.Classes.Eq1 m}
   : Data.Functor.Classes.Eq1 (ExceptT e m) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a : Type} {b : Type} =>
             Eq1__ExceptT_liftEq |}.

Local Definition Ord1__ExceptT_liftCompare {inst_e : Type} {inst_m
   : Type -> Type} `{GHC.Base.Ord inst_e} `{Data.Functor.Classes.Ord1 inst_m}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) ->
     ExceptT inst_e inst_m a -> ExceptT inst_e inst_m b -> comparison :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_ExceptT x, Mk_ExceptT y =>
          (@Data.Functor.Classes.liftCompare inst_m _ _ _ _
           (Data.Functor.Classes.liftCompare comp)) x y
      end.

Program Instance Ord1__ExceptT {e : Type} {m : Type -> Type} `{GHC.Base.Ord e}
  `{Data.Functor.Classes.Ord1 m}
   : Data.Functor.Classes.Ord1 (ExceptT e m) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a : Type} {b : Type} =>
             Ord1__ExceptT_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Control.Monad.Trans.Except.Read1__ExceptT' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Control.Monad.Trans.Except.Show1__ExceptT' *)

Local Definition Eq___ExceptT_op_zeze__ {inst_e : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Eq_ inst_e} `{Data.Functor.Classes.Eq1 inst_m}
  `{GHC.Base.Eq_ inst_a}
   : ExceptT inst_e inst_m inst_a -> ExceptT inst_e inst_m inst_a -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___ExceptT_op_zsze__ {inst_e : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Eq_ inst_e} `{Data.Functor.Classes.Eq1 inst_m}
  `{GHC.Base.Eq_ inst_a}
   : ExceptT inst_e inst_m inst_a -> ExceptT inst_e inst_m inst_a -> bool :=
  fun x y => negb (Eq___ExceptT_op_zeze__ x y).

Program Instance Eq___ExceptT {e : Type} {m : Type -> Type} {a : Type}
  `{GHC.Base.Eq_ e} `{Data.Functor.Classes.Eq1 m} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (ExceptT e m a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ExceptT_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ExceptT_op_zsze__ |}.

Local Definition Ord__ExceptT_compare {inst_e : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_e} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : ExceptT inst_e inst_m inst_a -> ExceptT inst_e inst_m inst_a -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__ExceptT_op_zl__ {inst_e : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_e} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : ExceptT inst_e inst_m inst_a -> ExceptT inst_e inst_m inst_a -> bool :=
  fun x y => Ord__ExceptT_compare x y GHC.Base.== Lt.

Local Definition Ord__ExceptT_op_zlze__ {inst_e : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_e} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : ExceptT inst_e inst_m inst_a -> ExceptT inst_e inst_m inst_a -> bool :=
  fun x y => Ord__ExceptT_compare x y GHC.Base./= Gt.

Local Definition Ord__ExceptT_op_zg__ {inst_e : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_e} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : ExceptT inst_e inst_m inst_a -> ExceptT inst_e inst_m inst_a -> bool :=
  fun x y => Ord__ExceptT_compare x y GHC.Base.== Gt.

Local Definition Ord__ExceptT_op_zgze__ {inst_e : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_e} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : ExceptT inst_e inst_m inst_a -> ExceptT inst_e inst_m inst_a -> bool :=
  fun x y => Ord__ExceptT_compare x y GHC.Base./= Lt.

Local Definition Ord__ExceptT_max {inst_e : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_e} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : ExceptT inst_e inst_m inst_a ->
     ExceptT inst_e inst_m inst_a -> ExceptT inst_e inst_m inst_a :=
  fun x y => if Ord__ExceptT_op_zlze__ x y : bool then y else x.

Local Definition Ord__ExceptT_min {inst_e : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_e} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : ExceptT inst_e inst_m inst_a ->
     ExceptT inst_e inst_m inst_a -> ExceptT inst_e inst_m inst_a :=
  fun x y => if Ord__ExceptT_op_zlze__ x y : bool then x else y.

Program Instance Ord__ExceptT {e : Type} {m : Type -> Type} {a : Type}
  `{GHC.Base.Ord e} `{Data.Functor.Classes.Ord1 m} `{GHC.Base.Ord a}
   : GHC.Base.Ord (ExceptT e m a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__ExceptT_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__ExceptT_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__ExceptT_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__ExceptT_op_zgze__ ;
           GHC.Base.compare__ := Ord__ExceptT_compare ;
           GHC.Base.max__ := Ord__ExceptT_max ;
           GHC.Base.min__ := Ord__ExceptT_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Control.Monad.Trans.Except.Read__ExceptT' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Monad.Trans.Except.Show__ExceptT' *)

Definition runExceptT {e : Type} {m : Type -> Type} {a : Type}
   : ExceptT e m a -> m (Data.Either.Either e a) :=
  fun '(Mk_ExceptT m) => m.

Local Definition Functor__ExceptT_fmap {inst_m : Type -> Type} {inst_e : Type}
  `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> ExceptT inst_e inst_m a -> ExceptT inst_e inst_m b :=
  fun {a : Type} {b : Type} =>
    fun f =>
      Mk_ExceptT GHC.Base.∘ (GHC.Base.fmap (GHC.Base.fmap f) GHC.Base.∘ runExceptT).

Local Definition Functor__ExceptT_op_zlzd__ {inst_m : Type -> Type} {inst_e
   : Type} `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type}, a -> ExceptT inst_e inst_m b -> ExceptT inst_e inst_m a :=
  fun {a : Type} {b : Type} => Functor__ExceptT_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__ExceptT {m : Type -> Type} {e : Type}
  `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (ExceptT e m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__ExceptT_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__ExceptT_op_zlzd__ |}.

Local Definition Foldable__ExceptT_foldMap {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> ExceptT inst_e inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_ExceptT a =>
          Data.Foldable.foldMap (Data.Either.either (GHC.Base.const GHC.Base.mempty) f) a
      end.

Local Definition Foldable__ExceptT_fold {inst_f : Type -> Type} {inst_e : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, ExceptT inst_e inst_f m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__ExceptT_foldMap GHC.Base.id.

Local Definition Foldable__ExceptT_foldl {inst_f : Type -> Type} {inst_e : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> ExceptT inst_e inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__ExceptT_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

Local Definition Foldable__ExceptT_foldr {inst_f : Type -> Type} {inst_e : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> ExceptT inst_e inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__ExceptT_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__ExceptT_foldl' {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> ExceptT inst_e inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__ExceptT_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__ExceptT_foldr' {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> ExceptT inst_e inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__ExceptT_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__ExceptT_length {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, ExceptT inst_e inst_f a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__ExceptT_foldl' (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

Local Definition Foldable__ExceptT_null {inst_f : Type -> Type} {inst_e : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, ExceptT inst_e inst_f a -> bool :=
  fun {a : Type} => Foldable__ExceptT_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__ExceptT_product {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, ExceptT inst_e inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__ExceptT_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__ExceptT_sum {inst_f : Type -> Type} {inst_e : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, ExceptT inst_e inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__ExceptT_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__ExceptT_toList {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, ExceptT inst_e inst_f a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__ExceptT_foldr c n t)).

Program Instance Foldable__ExceptT {f : Type -> Type} {e : Type}
  `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (ExceptT e f) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__ExceptT_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__ExceptT_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__ExceptT_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} =>
             Foldable__ExceptT_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__ExceptT_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} =>
             Foldable__ExceptT_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__ExceptT_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__ExceptT_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__ExceptT_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__ExceptT_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__ExceptT_toList |}.

Local Definition Traversable__ExceptT_traverse {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> ExceptT inst_e inst_f a -> f (ExceptT inst_e inst_f b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_ExceptT a =>
          Mk_ExceptT Data.Functor.<$>
          Data.Traversable.traverse (Data.Either.either (GHC.Base.pure GHC.Base.∘
                                                         Data.Either.Left) (GHC.Base.fmap Data.Either.Right GHC.Base.∘
                                                                            f)) a
      end.

Local Definition Traversable__ExceptT_mapM {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> ExceptT inst_e inst_f a -> m (ExceptT inst_e inst_f b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__ExceptT_traverse.

Local Definition Traversable__ExceptT_sequenceA {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     ExceptT inst_e inst_f (f a) -> f (ExceptT inst_e inst_f a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__ExceptT_traverse GHC.Base.id.

Local Definition Traversable__ExceptT_sequence {inst_f : Type -> Type} {inst_e
   : Type} `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     ExceptT inst_e inst_f (m a) -> m (ExceptT inst_e inst_f a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__ExceptT_sequenceA.

Program Instance Traversable__ExceptT {f : Type -> Type} {e : Type}
  `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (ExceptT e f) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__ExceptT_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__ExceptT_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__ExceptT_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__ExceptT_traverse |}.

Local Definition Applicative__ExceptT_op_zlztzg__ {inst_m : Type -> Type}
  {inst_e : Type} `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     ExceptT inst_e inst_m (a -> b) ->
     ExceptT inst_e inst_m a -> ExceptT inst_e inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_ExceptT f, Mk_ExceptT v =>
          Mk_ExceptT (f GHC.Base.>>=
                      (fun mf =>
                         match mf with
                         | Data.Either.Left e => GHC.Base.return_ (Data.Either.Left e)
                         | Data.Either.Right k =>
                             v GHC.Base.>>=
                             (fun mv =>
                                match mv with
                                | Data.Either.Left e => GHC.Base.return_ (Data.Either.Left e)
                                | Data.Either.Right x => GHC.Base.return_ (Data.Either.Right (k x))
                                end)
                         end))
      end.

Local Definition Applicative__ExceptT_liftA2 {inst_m : Type -> Type} {inst_e
   : Type} `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     ExceptT inst_e inst_m a -> ExceptT inst_e inst_m b -> ExceptT inst_e inst_m c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__ExceptT_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__ExceptT_pure {inst_m : Type -> Type} {inst_e
   : Type} `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type}, a -> ExceptT inst_e inst_m a :=
  fun {a : Type} => fun a => Mk_ExceptT (GHC.Base.return_ (Data.Either.Right a)).

Definition Applicative__ExceptT_op_ztzg__ {inst_m} {inst_s} `{_
   : GHC.Base.Monad inst_m}
   : forall {a} {b},
     ExceptT inst_s inst_m a -> ExceptT inst_s inst_m b -> ExceptT inst_s inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Applicative__ExceptT_op_zlztzg__ (Applicative__ExceptT_op_zlztzg__
                                        (Applicative__ExceptT_pure (fun x y => x)) k) m.

Program Instance Applicative__ExceptT {m : Type -> Type} {e : Type}
  `{GHC.Base.Functor m} `{GHC.Base.Monad m}
   : GHC.Base.Applicative (ExceptT e m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__ExceptT_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__ExceptT_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__ExceptT_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__ExceptT_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Monad.Trans.Except.Alternative__ExceptT' *)

Definition Monad__ExceptT_op_zgzgze__ {inst_m} {inst_e} `{_
   : GHC.Base.Monad inst_m}
   : forall {a} {b},
     ExceptT inst_e inst_m a ->
     (a -> ExceptT inst_e inst_m b) -> ExceptT inst_e inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Mk_ExceptT (runExceptT m GHC.Base.>>=
                  (fun a =>
                     match a with
                     | Data.Either.Left e => GHC.Base.return_ (Data.Either.Left e)
                     | Data.Either.Right x => runExceptT (k x)
                     end)).

Local Definition Monad__ExceptT_op_zgzg__ {inst_m : Type -> Type} {inst_e
   : Type} `{(GHC.Base.Monad inst_m)}
   : forall {a : Type},
     forall {b : Type},
     ExceptT inst_e inst_m a -> ExceptT inst_e inst_m b -> ExceptT inst_e inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__ExceptT_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__ExceptT_return_ {inst_m : Type -> Type} {inst_e : Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type}, a -> ExceptT inst_e inst_m a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__ExceptT {m : Type -> Type} {e : Type} `{(GHC.Base.Monad
   m)}
   : GHC.Base.Monad (ExceptT e m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__ExceptT_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__ExceptT_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__ExceptT_return_ |}.

Local Definition MonadTrans__ExceptT_lift {inst_e : Type}
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, m a -> ExceptT inst_e m a :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Mk_ExceptT GHC.Base.∘ GHC.Base.liftM Data.Either.Right.

Program Instance MonadTrans__ExceptT {e : Type}
   : Control.Monad.Trans.Class.MonadTrans (ExceptT e) :=
  fun _ k__ =>
    k__ {| Control.Monad.Trans.Class.lift__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             MonadTrans__ExceptT_lift |}.

Local Definition MonadFail__ExceptT_fail {inst_m : Type -> Type} {inst_e : Type}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a : Type}, GHC.Base.String -> ExceptT inst_e inst_m a :=
  fun {a : Type} => Mk_ExceptT GHC.Base.∘ Control.Monad.Fail.fail.

Program Instance MonadFail__ExceptT {m : Type -> Type} {e : Type}
  `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (ExceptT e m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun {a : Type} =>
             MonadFail__ExceptT_fail |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Monad.Trans.Except.MonadPlus__ExceptT' *)

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Control.Monad.Trans.Except.MonadFix__ExceptT' *)

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `Control.Monad.Trans.Except.MonadIO__ExceptT' *)

(* Skipping all instances of class `Control.Monad.Zip.MonadZip', including
   `Control.Monad.Trans.Except.MonadZip__ExceptT' *)

Definition except {e : Type} {a : Type}
   : Data.Either.Either e a -> Except e a :=
  fun m => Mk_ExceptT (Data.Functor.Identity.Mk_Identity m).

Definition runExcept {e : Type} {a : Type}
   : Except e a -> Data.Either.Either e a :=
  fun '(Mk_ExceptT m) => Data.Functor.Identity.runIdentity m.

Definition mapExceptT {m : Type -> Type} {e : Type} {a : Type} {n
   : Type -> Type} {e' : Type} {b : Type}
   : (m (Data.Either.Either e a) -> n (Data.Either.Either e' b)) ->
     ExceptT e m a -> ExceptT e' n b :=
  fun f m => Mk_ExceptT (f (runExceptT m)).

Definition mapExcept {e : Type} {a : Type} {e' : Type} {b : Type}
   : (Data.Either.Either e a -> Data.Either.Either e' b) ->
     Except e a -> Except e' b :=
  fun f =>
    mapExceptT (Data.Functor.Identity.Mk_Identity GHC.Base.∘
                (f GHC.Base.∘ Data.Functor.Identity.runIdentity)).

Definition withExceptT {m : Type -> Type} {e : Type} {e' : Type} {a : Type}
  `{GHC.Base.Functor m}
   : (e -> e') -> ExceptT e m a -> ExceptT e' m a :=
  fun f =>
    mapExceptT (GHC.Base.fmap (Data.Either.either (Data.Either.Left GHC.Base.∘ f)
                                                  Data.Either.Right)).

Definition withExcept {e : Type} {e' : Type} {a : Type}
   : (e -> e') -> Except e a -> Except e' a :=
  withExceptT.

Definition throwE {m : Type -> Type} {e : Type} {a : Type} `{GHC.Base.Monad m}
   : e -> ExceptT e m a :=
  Mk_ExceptT GHC.Base.∘ (GHC.Base.return_ GHC.Base.∘ Data.Either.Left).

Definition catchE {m : Type -> Type} {e : Type} {a : Type} {e' : Type}
  `{GHC.Base.Monad m}
   : ExceptT e m a -> (e -> ExceptT e' m a) -> ExceptT e' m a :=
  fun m h =>
    Mk_ExceptT (runExceptT m GHC.Base.>>=
                (fun a =>
                   match a with
                   | Data.Either.Left l => runExceptT (h l)
                   | Data.Either.Right r => GHC.Base.return_ (Data.Either.Right r)
                   end)).

Definition liftCallCC {m : Type -> Type} {e : Type} {a : Type} {b : Type}
   : Control.Monad.Signatures.CallCC m (Data.Either.Either e a)
                                     (Data.Either.Either e b) ->
     Control.Monad.Signatures.CallCC (ExceptT e m) a b :=
  fun callCC f =>
    Mk_ExceptT (callCC (fun c =>
                          runExceptT (f (fun a => Mk_ExceptT (c (Data.Either.Right a)))))).

Definition liftListen {m : Type -> Type} {w : Type} {e : Type} {a : Type}
  `{GHC.Base.Monad m}
   : Control.Monad.Signatures.Listen w m (Data.Either.Either e a) ->
     Control.Monad.Signatures.Listen w (ExceptT e m) a :=
  fun listen =>
    mapExceptT (fun m =>
                  let cont_0__ arg_1__ :=
                    let 'pair a w := arg_1__ in
                    GHC.Base.return_ (GHC.Base.fmap (fun r => pair r w) a) in
                  listen m GHC.Base.>>= cont_0__).

Definition liftPass {m : Type -> Type} {w : Type} {e : Type} {a : Type}
  `{GHC.Base.Monad m}
   : Control.Monad.Signatures.Pass w m (Data.Either.Either e a) ->
     Control.Monad.Signatures.Pass w (ExceptT e m) a :=
  fun pass =>
    mapExceptT (fun m =>
                  pass (m GHC.Base.>>=
                        (fun a =>
                           GHC.Base.return_ (match a with
                                             | Data.Either.Left l => pair (Data.Either.Left l) GHC.Base.id
                                             | Data.Either.Right (pair r f) => pair (Data.Either.Right r) f
                                             end)))).

(* External variables:
     Gt Lt Type bool comparison false list negb pair true
     Control.Monad.Fail.MonadFail Control.Monad.Fail.fail Control.Monad.Fail.fail__
     Control.Monad.Signatures.CallCC Control.Monad.Signatures.Listen
     Control.Monad.Signatures.Pass Control.Monad.Trans.Class.MonadTrans
     Control.Monad.Trans.Class.lift__ Coq.Program.Basics.compose Data.Either.Either
     Data.Either.Left Data.Either.Right Data.Either.either Data.Foldable.Foldable
     Data.Foldable.foldMap Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1 Data.Functor.Classes.Ord1
     Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Functor.Identity.runIdentity Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.String GHC.Base.build' GHC.Base.compare__ GHC.Base.const GHC.Base.flip
     GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__ GHC.Base.liftM
     GHC.Base.max__ GHC.Base.mempty GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return_
     GHC.Base.return___ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
