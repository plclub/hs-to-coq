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
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Reverse {k : Type} (f : k -> Type) (a : k) : Type :=
  | Mk_Reverse (getReverse : f a) : Reverse f a.

Arguments Mk_Reverse {_} {_} {_} _.

Definition getReverse {k : Type} {f : k -> Type} {a : k} (arg_0__
    : Reverse f a) :=
  let 'Mk_Reverse getReverse := arg_0__ in
  getReverse.

(* Converted value declarations: *)

Local Definition Eq1__Reverse_liftEq {inst_f : Type -> Type}
  `{(Data.Functor.Classes.Eq1 inst_f)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> bool) -> Reverse inst_f a -> Reverse inst_f b -> bool :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_Reverse x, Mk_Reverse y => Data.Functor.Classes.liftEq eq x y
      end.

Program Instance Eq1__Reverse {f : Type -> Type} `{(Data.Functor.Classes.Eq1 f)}
   : Data.Functor.Classes.Eq1 (Reverse f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a : Type} {b : Type} =>
             Eq1__Reverse_liftEq |}.

Local Definition Ord1__Reverse_liftCompare {inst_f : Type -> Type}
  `{(Data.Functor.Classes.Ord1 inst_f)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) -> Reverse inst_f a -> Reverse inst_f b -> comparison :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_Reverse x, Mk_Reverse y => Data.Functor.Classes.liftCompare comp x y
      end.

Program Instance Ord1__Reverse {f : Type -> Type} `{(Data.Functor.Classes.Ord1
   f)}
   : Data.Functor.Classes.Ord1 (Reverse f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a : Type} {b : Type} =>
             Ord1__Reverse_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Reverse.Read1__Reverse' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Reverse.Show1__Reverse' *)

Local Definition Eq___Reverse_op_zeze__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : Reverse inst_f inst_a -> Reverse inst_f inst_a -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Reverse_op_zsze__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : Reverse inst_f inst_a -> Reverse inst_f inst_a -> bool :=
  fun x y => negb (Eq___Reverse_op_zeze__ x y).

Program Instance Eq___Reverse {f : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Eq1 f} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Reverse f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Reverse_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Reverse_op_zsze__ |}.

Local Definition Ord__Reverse_compare {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Reverse inst_f inst_a -> Reverse inst_f inst_a -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Reverse_op_zl__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Reverse inst_f inst_a -> Reverse inst_f inst_a -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base.== Lt.

Local Definition Ord__Reverse_op_zlze__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Reverse inst_f inst_a -> Reverse inst_f inst_a -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base./= Gt.

Local Definition Ord__Reverse_op_zg__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Reverse inst_f inst_a -> Reverse inst_f inst_a -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base.== Gt.

Local Definition Ord__Reverse_op_zgze__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Reverse inst_f inst_a -> Reverse inst_f inst_a -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base./= Lt.

Local Definition Ord__Reverse_max {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Reverse inst_f inst_a -> Reverse inst_f inst_a -> Reverse inst_f inst_a :=
  fun x y => if Ord__Reverse_op_zlze__ x y : bool then y else x.

Local Definition Ord__Reverse_min {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Reverse inst_f inst_a -> Reverse inst_f inst_a -> Reverse inst_f inst_a :=
  fun x y => if Ord__Reverse_op_zlze__ x y : bool then x else y.

Program Instance Ord__Reverse {f : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Ord1 f} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Reverse f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Reverse_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Reverse_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Reverse_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Reverse_op_zgze__ ;
           GHC.Base.compare__ := Ord__Reverse_compare ;
           GHC.Base.max__ := Ord__Reverse_max ;
           GHC.Base.min__ := Ord__Reverse_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Reverse.Read__Reverse' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Reverse.Show__Reverse' *)

Local Definition Functor__Reverse_fmap {inst_f : Type -> Type}
  `{(GHC.Base.Functor inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Reverse inst_f a -> Reverse inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Reverse a => Mk_Reverse (GHC.Base.fmap f a)
      end.

Local Definition Functor__Reverse_op_zlzd__ {inst_f : Type -> Type}
  `{(GHC.Base.Functor inst_f)}
   : forall {a : Type},
     forall {b : Type}, a -> Reverse inst_f b -> Reverse inst_f a :=
  fun {a : Type} {b : Type} => Functor__Reverse_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Reverse {f : Type -> Type} `{(GHC.Base.Functor f)}
   : GHC.Base.Functor (Reverse f) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Reverse_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__Reverse_op_zlzd__ |}.

Local Definition Applicative__Reverse_op_zlztzg__ {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type},
     forall {b : Type},
     Reverse inst_f (a -> b) -> Reverse inst_f a -> Reverse inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Reverse f, Mk_Reverse a => Mk_Reverse (f GHC.Base.<*> a)
      end.

Local Definition Applicative__Reverse_liftA2 {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) -> Reverse inst_f a -> Reverse inst_f b -> Reverse inst_f c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Reverse_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Reverse_op_ztzg__ {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type},
     forall {b : Type}, Reverse inst_f a -> Reverse inst_f b -> Reverse inst_f b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Reverse_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Reverse_pure {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type}, a -> Reverse inst_f a :=
  fun {a : Type} => fun a => Mk_Reverse (GHC.Base.pure a).

Program Instance Applicative__Reverse {f : Type -> Type} `{(GHC.Base.Applicative
   f)}
   : GHC.Base.Applicative (Reverse f) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Reverse_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Reverse_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Reverse_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Reverse_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.Functor.Reverse.Alternative__Reverse' *)

Local Definition Monad__Reverse_op_zgzgze__ {inst_m : Type -> Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type},
     forall {b : Type},
     Reverse inst_m a -> (a -> Reverse inst_m b) -> Reverse inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m f => Mk_Reverse (getReverse m GHC.Base.>>= (getReverse GHC.Base.∘ f)).

Local Definition Monad__Reverse_op_zgzg__ {inst_m : Type -> Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type},
     forall {b : Type}, Reverse inst_m a -> Reverse inst_m b -> Reverse inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Reverse_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Reverse_return_ {inst_m : Type -> Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type}, a -> Reverse inst_m a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__Reverse {m : Type -> Type} `{(GHC.Base.Monad m)}
   : GHC.Base.Monad (Reverse m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__Reverse_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__Reverse_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__Reverse_return_ |}.

Local Definition MonadFail__Reverse_fail {inst_m : Type -> Type}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a : Type}, GHC.Base.String -> Reverse inst_m a :=
  fun {a : Type} => fun msg => Mk_Reverse (Control.Monad.Fail.fail msg).

Program Instance MonadFail__Reverse {m : Type -> Type}
  `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (Reverse m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun {a : Type} =>
             MonadFail__Reverse_fail |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Data.Functor.Reverse.MonadPlus__Reverse' *)

Local Definition Foldable__Reverse_foldMap {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Reverse inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Reverse t =>
          Data.SemigroupInternal.getDual (Data.Foldable.foldMap
                                          (Data.SemigroupInternal.Mk_Dual GHC.Base.∘ f) t)
      end.

Local Definition Foldable__Reverse_fold {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Reverse inst_f m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Reverse_foldMap GHC.Base.id.

Local Definition Foldable__Reverse_foldl {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Reverse inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Reverse t => Data.Foldable.foldr (GHC.Base.flip f) z t
      end.

Local Definition Foldable__Reverse_foldr {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Reverse inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Reverse t => Data.Foldable.foldl (GHC.Base.flip f) z t
      end.

Local Definition Foldable__Reverse_foldl' {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Reverse inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__Reverse_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Reverse_foldr' {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Reverse inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__Reverse_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Reverse_length {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, Reverse inst_f a -> GHC.Num.Int :=
  fun {a : Type} => fun '(Mk_Reverse t) => Data.Foldable.length t.

Local Definition Foldable__Reverse_null {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, Reverse inst_f a -> bool :=
  fun {a : Type} => fun '(Mk_Reverse t) => Data.Foldable.null t.

Local Definition Foldable__Reverse_product {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Reverse inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Reverse_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Reverse_sum {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Reverse inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Reverse_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Reverse_toList {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, Reverse inst_f a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Reverse_foldr c n t)).

Program Instance Foldable__Reverse {f : Type -> Type} `{(Data.Foldable.Foldable
   f)}
   : Data.Foldable.Foldable (Reverse f) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__Reverse_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Reverse_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__Reverse_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} =>
             Foldable__Reverse_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__Reverse_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} =>
             Foldable__Reverse_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__Reverse_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__Reverse_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Reverse_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Reverse_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__Reverse_toList |}.

(* Skipping instance `Data.Functor.Reverse.Traversable__Reverse' of class
   `Data.Traversable.Traversable' *)

(* External variables:
     Gt Lt Type bool comparison list negb Control.Monad.Fail.MonadFail
     Control.Monad.Fail.fail Control.Monad.Fail.fail__ Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length Data.Foldable.length__
     Data.Foldable.null Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ Data.Functor.Classes.Eq1
     Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.String GHC.Base.build' GHC.Base.compare__
     GHC.Base.const GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return___ GHC.Num.Int GHC.Num.Num
*)
