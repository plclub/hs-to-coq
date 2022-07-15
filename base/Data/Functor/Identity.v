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
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Identity a : Type := | Mk_Identity (runIdentity : a) : Identity a.

Arguments Mk_Identity {_} _.

Definition runIdentity {a} (arg_0__ : Identity a) :=
  let 'Mk_Identity runIdentity := arg_0__ in
  runIdentity.

(* Midamble *)

Instance Unpeel_Identity a : HsToCoq.Unpeel.Unpeel (Identity a) a :=
 HsToCoq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_Identity x => x end) Mk_Identity.

(* Converted value declarations: *)

(* Skipping all instances of class `Data.Bits.Bits', including
   `Data.Functor.Identity.Bits__Identity' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Functor.Identity.Bounded__Identity' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Functor.Identity.Enum__Identity' *)

Local Definition Eq___Identity_op_zeze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Identity_op_zsze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Identity {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Identity a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Identity_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Identity_op_zsze__ |}.

(* Skipping all instances of class `Data.Bits.FiniteBits', including
   `Data.Functor.Identity.FiniteBits__Identity' *)

(* Skipping all instances of class `GHC.Float.Floating', including
   `Data.Functor.Identity.Floating__Identity' *)

(* Skipping all instances of class `GHC.Real.Fractional', including
   `Data.Functor.Identity.Fractional__Identity' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Functor.Identity.Generic__Identity' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Functor.Identity.Generic1__TYPE__Identity__LiftedRep' *)

(* Skipping all instances of class `GHC.Real.Integral', including
   `Data.Functor.Identity.Integral__Identity' *)

(* Skipping all instances of class `GHC.Arr.Ix', including
   `Data.Functor.Identity.Ix__Identity' *)

Local Definition Semigroup__Identity_op_zlzlzgzg__ {inst_a : Type}
  `{GHC.Base.Semigroup inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__Identity {a : Type} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Identity a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Identity_op_zlzlzgzg__ |}.

Local Definition Monoid__Identity_mappend {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Monoid__Identity_mconcat {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : list (Identity inst_a) -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__Identity_mempty {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : Identity inst_a :=
  GHC.Prim.coerce GHC.Base.mempty.

Program Instance Monoid__Identity {a : Type} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Identity a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Identity_mappend ;
           GHC.Base.mconcat__ := Monoid__Identity_mconcat ;
           GHC.Base.mempty__ := Monoid__Identity_mempty |}.

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.Functor.Identity.Num__Identity' *)

Local Definition Ord__Identity_op_zl__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Identity_op_zlze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Identity_op_zg__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Identity_op_zgze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Identity_compare {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Identity_max {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Identity_min {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Identity {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Identity a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Identity_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Identity_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Identity_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Identity_op_zgze__ ;
           GHC.Base.compare__ := Ord__Identity_compare ;
           GHC.Base.max__ := Ord__Identity_max ;
           GHC.Base.min__ := Ord__Identity_min |}.

(* Skipping all instances of class `GHC.Real.Real', including
   `Data.Functor.Identity.Real__Identity' *)

(* Skipping all instances of class `GHC.Real.RealFrac', including
   `Data.Functor.Identity.RealFrac__Identity' *)

(* Skipping all instances of class `GHC.Float.RealFloat', including
   `Data.Functor.Identity.RealFloat__Identity' *)

(* Skipping all instances of class `Foreign.Storable.Storable', including
   `Data.Functor.Identity.Storable__Identity' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Identity.Read__Identity' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Identity.Show__Identity' *)

Local Definition Foldable__Identity_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Identity a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

Local Definition Foldable__Identity_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Identity m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Identity_foldMap GHC.Base.id.

Local Definition Foldable__Identity_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Identity a -> b :=
  fun {b : Type} {a : Type} => GHC.Prim.coerce.

Local Definition Foldable__Identity_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Identity a -> b :=
  fun {b : Type} {a : Type} => GHC.Prim.coerce.

Local Definition Foldable__Identity_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Identity a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Identity x => f x z
      end.

Local Definition Foldable__Identity_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Identity a -> b :=
  fun {a : Type} {b : Type} => Foldable__Identity_foldr.

Local Definition Foldable__Identity_length
   : forall {a : Type}, Identity a -> GHC.Num.Int :=
  fun {a : Type} => fun arg_0__ => #1.

Local Definition Foldable__Identity_null
   : forall {a : Type}, Identity a -> bool :=
  fun {a : Type} => fun arg_0__ => false.

Local Definition Foldable__Identity_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => runIdentity.

Local Definition Foldable__Identity_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => runIdentity.

Local Definition Foldable__Identity_toList
   : forall {a : Type}, Identity a -> list a :=
  fun {a : Type} => fun '(Mk_Identity x) => cons x nil.

Program Instance Foldable__Identity : Data.Foldable.Foldable Identity :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__Identity_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Identity_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__Identity_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} =>
             Foldable__Identity_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__Identity_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} =>
             Foldable__Identity_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__Identity_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__Identity_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Identity_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Identity_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__Identity_toList |}.

Local Definition Functor__Identity_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Identity a -> Identity b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Functor__Identity_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Identity b -> Identity a :=
  fun {a : Type} {b : Type} => Functor__Identity_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Identity : GHC.Base.Functor Identity :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Identity_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__Identity_op_zlzd__ |}.

Local Definition Applicative__Identity_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Identity a -> Identity b -> Identity c :=
  fun {a : Type} {b : Type} {c : Type} => GHC.Prim.coerce.

Local Definition Applicative__Identity_op_zlztzg__
   : forall {a : Type},
     forall {b : Type}, Identity (a -> b) -> Identity a -> Identity b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Applicative__Identity_op_ztzg__
   : forall {a : Type},
     forall {b : Type}, Identity a -> Identity b -> Identity b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Identity_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Identity_pure
   : forall {a : Type}, a -> Identity a :=
  fun {a : Type} => Mk_Identity.

Program Instance Applicative__Identity : GHC.Base.Applicative Identity :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Identity_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Identity_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Identity_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Identity_pure |}.

Local Definition Monad__Identity_op_zgzgze__
   : forall {a : Type},
     forall {b : Type}, Identity a -> (a -> Identity b) -> Identity b :=
  fun {a : Type} {b : Type} => fun m k => k (runIdentity m).

Local Definition Monad__Identity_op_zgzg__
   : forall {a : Type},
     forall {b : Type}, Identity a -> Identity b -> Identity b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Identity_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Identity_return_ : forall {a : Type}, a -> Identity a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__Identity : GHC.Base.Monad Identity :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__Identity_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__Identity_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__Identity_return_ |}.

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Data.Functor.Identity.MonadFix__Identity' *)

(* External variables:
     Type bool comparison cons false list nil Data.Foldable.Foldable
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr'__ Data.Foldable.foldr__
     Data.Foldable.length__ Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.mappend GHC.Base.mappend__ GHC.Base.max
     GHC.Base.max__ GHC.Base.mconcat GHC.Base.mconcat__ GHC.Base.mempty
     GHC.Base.mempty__ GHC.Base.min GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze____ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Base.return___ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Prim.coerce
*)
