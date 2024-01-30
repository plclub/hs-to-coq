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
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Sum {k : Type} (f : k -> Type) (g : k -> Type) (a : k) : Type :=
  | InL : (f a) -> Sum f g a
  | InR : (g a) -> Sum f g a.

Arguments InL {_} {_} {_} {_} _.

Arguments InR {_} {_} {_} {_} _.

(* Converted value declarations: *)

#[local] Definition Eq1__Sum_liftEq {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> bool) -> Sum inst_f inst_g a -> Sum inst_f inst_g b -> bool :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, InL x1, InL x2 => Data.Functor.Classes.liftEq eq x1 x2
      | _, InL _, InR _ => false
      | _, InR _, InL _ => false
      | eq, InR y1, InR y2 => Data.Functor.Classes.liftEq eq y1 y2
      end.

#[global]
Program Instance Eq1__Sum {f : Type -> Type} {g : Type -> Type}
  `{Data.Functor.Classes.Eq1 f} `{Data.Functor.Classes.Eq1 g}
   : Data.Functor.Classes.Eq1 (Sum f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a : Type} {b : Type} =>
             Eq1__Sum_liftEq |}.

#[local] Definition Ord1__Sum_liftCompare {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) ->
     Sum inst_f inst_g a -> Sum inst_f inst_g b -> comparison :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, InL x1, InL x2 => Data.Functor.Classes.liftCompare comp x1 x2
      | _, InL _, InR _ => Lt
      | _, InR _, InL _ => Gt
      | comp, InR y1, InR y2 => Data.Functor.Classes.liftCompare comp y1 y2
      end.

#[global]
Program Instance Ord1__Sum {f : Type -> Type} {g : Type -> Type}
  `{Data.Functor.Classes.Ord1 f} `{Data.Functor.Classes.Ord1 g}
   : Data.Functor.Classes.Ord1 (Sum f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a : Type} {b : Type} =>
             Ord1__Sum_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Sum.Read1__Sum' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Sum.Show1__Sum' *)

#[local] Definition Eq___Sum_op_zeze__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} {inst_a : Type} `{Data.Functor.Classes.Eq1 inst_f}
  `{Data.Functor.Classes.Eq1 inst_g} `{GHC.Base.Eq_ inst_a}
   : Sum inst_f inst_g inst_a -> Sum inst_f inst_g inst_a -> bool :=
  Data.Functor.Classes.eq1.

#[local] Definition Eq___Sum_op_zsze__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} {inst_a : Type} `{Data.Functor.Classes.Eq1 inst_f}
  `{Data.Functor.Classes.Eq1 inst_g} `{GHC.Base.Eq_ inst_a}
   : Sum inst_f inst_g inst_a -> Sum inst_f inst_g inst_a -> bool :=
  fun x y => negb (Eq___Sum_op_zeze__ x y).

#[global]
Program Instance Eq___Sum {f : Type -> Type} {g : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Eq1 f} `{Data.Functor.Classes.Eq1 g} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Sum f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Sum_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Sum_op_zsze__ |}.

#[local] Definition Ord__Sum_compare {inst_f : Type -> Type} {inst_g
   : Type -> Type} {inst_a : Type} `{Data.Functor.Classes.Ord1 inst_f}
  `{Data.Functor.Classes.Ord1 inst_g} `{GHC.Base.Ord inst_a}
   : Sum inst_f inst_g inst_a -> Sum inst_f inst_g inst_a -> comparison :=
  Data.Functor.Classes.compare1.

#[local] Definition Ord__Sum_op_zl__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} {inst_a : Type} `{Data.Functor.Classes.Ord1 inst_f}
  `{Data.Functor.Classes.Ord1 inst_g} `{GHC.Base.Ord inst_a}
   : Sum inst_f inst_g inst_a -> Sum inst_f inst_g inst_a -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base.== Lt.

#[local] Definition Ord__Sum_op_zlze__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} {inst_a : Type} `{Data.Functor.Classes.Ord1 inst_f}
  `{Data.Functor.Classes.Ord1 inst_g} `{GHC.Base.Ord inst_a}
   : Sum inst_f inst_g inst_a -> Sum inst_f inst_g inst_a -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base./= Gt.

#[local] Definition Ord__Sum_op_zg__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} {inst_a : Type} `{Data.Functor.Classes.Ord1 inst_f}
  `{Data.Functor.Classes.Ord1 inst_g} `{GHC.Base.Ord inst_a}
   : Sum inst_f inst_g inst_a -> Sum inst_f inst_g inst_a -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base.== Gt.

#[local] Definition Ord__Sum_op_zgze__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} {inst_a : Type} `{Data.Functor.Classes.Ord1 inst_f}
  `{Data.Functor.Classes.Ord1 inst_g} `{GHC.Base.Ord inst_a}
   : Sum inst_f inst_g inst_a -> Sum inst_f inst_g inst_a -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base./= Lt.

#[local] Definition Ord__Sum_max {inst_f : Type -> Type} {inst_g : Type -> Type}
  {inst_a : Type} `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1
  inst_g} `{GHC.Base.Ord inst_a}
   : Sum inst_f inst_g inst_a ->
     Sum inst_f inst_g inst_a -> Sum inst_f inst_g inst_a :=
  fun x y => if Ord__Sum_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__Sum_min {inst_f : Type -> Type} {inst_g : Type -> Type}
  {inst_a : Type} `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1
  inst_g} `{GHC.Base.Ord inst_a}
   : Sum inst_f inst_g inst_a ->
     Sum inst_f inst_g inst_a -> Sum inst_f inst_g inst_a :=
  fun x y => if Ord__Sum_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__Sum {f : Type -> Type} {g : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Ord1 f} `{Data.Functor.Classes.Ord1 g} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Sum f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Sum_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Sum_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Sum_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Sum_op_zgze__ ;
           GHC.Base.compare__ := Ord__Sum_compare ;
           GHC.Base.max__ := Ord__Sum_max ;
           GHC.Base.min__ := Ord__Sum_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Sum.Read__Sum' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Sum.Show__Sum' *)

#[local] Definition Functor__Sum_fmap {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Functor inst_f} `{GHC.Base.Functor inst_g}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Sum inst_f inst_g a -> Sum inst_f inst_g b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, InL x => InL (GHC.Base.fmap f x)
      | f, InR y => InR (GHC.Base.fmap f y)
      end.

#[local] Definition Functor__Sum_op_zlzd__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Functor inst_f} `{GHC.Base.Functor inst_g}
   : forall {a : Type},
     forall {b : Type}, a -> Sum inst_f inst_g b -> Sum inst_f inst_g a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | a, InL x => InL (a GHC.Base.<$ x)
      | a, InR y => InR (a GHC.Base.<$ y)
      end.

#[global]
Program Instance Functor__Sum {f : Type -> Type} {g : Type -> Type}
  `{GHC.Base.Functor f} `{GHC.Base.Functor g}
   : GHC.Base.Functor (Sum f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Sum_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Sum_op_zlzd__ |}.

#[local] Definition Foldable__Sum_foldMap {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Sum inst_f inst_g a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, InL x => Data.Foldable.foldMap f x
      | f, InR y => Data.Foldable.foldMap f y
      end.

#[local] Definition Foldable__Sum_fold {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Sum inst_f inst_g m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Sum_foldMap GHC.Base.id.

#[local] Definition Foldable__Sum_foldr {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Sum inst_f inst_g a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Sum_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Sum_foldl' {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Sum inst_f inst_g a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Sum_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__Sum_foldMap' {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Sum inst_f inst_g a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Sum_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Sum_foldl {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Sum inst_f inst_g a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Sum_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Sum_foldr' {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Sum inst_f inst_g a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Sum_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__Sum_length {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, Sum inst_f inst_g a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Sum_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

#[local] Definition Foldable__Sum_null {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, Sum inst_f inst_g a -> bool :=
  fun {a : Type} => Foldable__Sum_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Sum_product {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Sum inst_f inst_g a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Sum_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Sum_sum {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Sum inst_f inst_g a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Sum_foldMap
                                Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Sum_toList {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, Sum inst_f inst_g a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Sum_foldr c n t)).

#[global]
Program Instance Foldable__Sum {f : Type -> Type} {g : Type -> Type}
  `{Data.Foldable.Foldable f} `{Data.Foldable.Foldable g}
   : Data.Foldable.Foldable (Sum f g) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__Sum_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Sum_foldMap ;
           Data.Foldable.foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Sum_foldMap' ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__Sum_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} => Foldable__Sum_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__Sum_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} => Foldable__Sum_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__Sum_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__Sum_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Sum_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Sum_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__Sum_toList |}.

#[local] Definition Traversable__Sum_traverse {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Sum inst_f inst_g a -> f (Sum inst_f inst_g b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, InL x => InL Data.Functor.<$> Data.Traversable.traverse f x
      | f, InR y => InR Data.Functor.<$> Data.Traversable.traverse f y
      end.

#[local] Definition Traversable__Sum_mapM {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Sum inst_f inst_g a -> m (Sum inst_f inst_g b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Sum_traverse.

#[local] Definition Traversable__Sum_sequenceA {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Sum inst_f inst_g (f a) -> f (Sum inst_f inst_g a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Sum_traverse GHC.Base.id.

#[local] Definition Traversable__Sum_sequence {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Sum inst_f inst_g (m a) -> m (Sum inst_f inst_g a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Sum_sequenceA.

#[global]
Program Instance Traversable__Sum {f : Type -> Type} {g : Type -> Type}
  `{Data.Traversable.Traversable f} `{Data.Traversable.Traversable g}
   : Data.Traversable.Traversable (Sum f g) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Sum_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Sum_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Sum_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Sum_traverse |}.

(* External variables:
     Gt Lt Type bool comparison false list negb true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap'__
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr'__ Data.Foldable.foldr__
     Data.Foldable.length__ Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ Data.Functor.op_zlzdzg__
     Data.Functor.Classes.Eq1 Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1
     Data.Functor.Classes.eq1 Data.Functor.Classes.liftCompare
     Data.Functor.Classes.liftCompare__ Data.Functor.Classes.liftEq
     Data.Functor.Classes.liftEq__ Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.build' GHC.Base.compare__ GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.id GHC.Base.max__ GHC.Base.mempty GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Num.Int
     GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
