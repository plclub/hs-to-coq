(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* Fix the type parameter of Const *)
Implicit Type b : Type.

(* A hack to make a few kind-polymorpic definitions go through *)
Class unit_class.
Instance unit_class_instance : unit_class := {}.
Implicit Type inst_k: unit_class.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require HsToCoq.Unpeel.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Const {k : Type} (a : Type) (b : k) : Type :=
  | Mk_Const (getConst : a) : Const a b.

Arguments Mk_Const {_} {_} {_} _.

#[global] Definition getConst {k : Type} {a : Type} {b : k} (arg_0__
    : Const a b) :=
  let 'Mk_Const getConst := arg_0__ in
  getConst.

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Const.Read__Const' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Const.Show__Const' *)

#[local] Definition Foldable__Const_foldMap {inst_m : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Const inst_m a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => GHC.Base.mempty.

#[local] Definition Foldable__Const_fold {inst_m : Type}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Const inst_m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Const_foldMap GHC.Base.id.

#[local] Definition Foldable__Const_foldr {inst_m : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Const inst_m a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Const_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Const_foldl' {inst_m : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Const inst_m a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Const_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__Const_foldMap' {inst_m : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Const inst_m a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Const_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Const_foldl {inst_m : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Const inst_m a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Const_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                 GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Const_foldr' {inst_m : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Const inst_m a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Const_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__Const_length {inst_m : Type}
   : forall {a : Type}, Const inst_m a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Const_foldl' (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

#[local] Definition Foldable__Const_null {inst_m : Type}
   : forall {a : Type}, Const inst_m a -> bool :=
  fun {a : Type} => Foldable__Const_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Const_product {inst_m : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Const inst_m a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Const_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Const_sum {inst_m : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Const inst_m a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Const_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Const_toList {inst_m : Type}
   : forall {a : Type}, Const inst_m a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Const_foldr c n t)).

#[global]
Program Instance Foldable__Const {m : Type}
   : Data.Foldable.Foldable (Const m) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__Const_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Const_foldMap ;
           Data.Foldable.foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Const_foldMap' ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__Const_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} => Foldable__Const_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__Const_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} => Foldable__Const_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__Const_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__Const_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Const_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Const_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__Const_toList |}.

#[local] Definition Functor__Const_fmap {inst_m : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Const inst_m a -> Const inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Const v => Mk_Const v
      end.

#[local] Definition Functor__Const_op_zlzd__ {inst_m : Type}
   : forall {a : Type},
     forall {b : Type}, a -> Const inst_m b -> Const inst_m a :=
  fun {a : Type} {b : Type} => Functor__Const_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Const {m : Type} : GHC.Base.Functor (Const m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Const_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__Const_op_zlzd__ |}.

#[local] Definition Applicative__Const_liftA2 {inst_m : Type} `{GHC.Base.Monoid
  inst_m}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) -> Const inst_m a -> Const inst_m b -> Const inst_m c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, Mk_Const x, Mk_Const y => Mk_Const (GHC.Base.mappend x y)
      end.

#[local] Definition Applicative__Const_op_zlztzg__ {inst_m : Type}
  `{GHC.Base.Monoid inst_m}
   : forall {a : Type},
     forall {b : Type}, Const inst_m (a -> b) -> Const inst_m a -> Const inst_m b :=
  fun {a : Type} {b : Type} =>
    GHC.Prim.coerce (GHC.Base.mappend : inst_m -> inst_m -> inst_m).

#[local] Definition Applicative__Const_op_ztzg__ {inst_m : Type}
  `{GHC.Base.Monoid inst_m}
   : forall {a : Type},
     forall {b : Type}, Const inst_m a -> Const inst_m b -> Const inst_m b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Const_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

#[local] Definition Applicative__Const_pure {inst_m : Type} `{GHC.Base.Monoid
  inst_m}
   : forall {a : Type}, a -> Const inst_m a :=
  fun {a : Type} => fun arg_0__ => Mk_Const GHC.Base.mempty.

#[global]
Program Instance Applicative__Const {m : Type} `{GHC.Base.Monoid m}
   : GHC.Base.Applicative (Const m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Const_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Const_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Const_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Const_pure |}.

Instance Unpeel_Const (k a : Type) (b : k)
   : HsToCoq.Unpeel.Unpeel (Const a b) a :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getConst Mk_Const.

(* External variables:
     Type bool false list true Coq.Program.Basics.compose Data.Foldable.Foldable
     Data.Foldable.foldMap'__ Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monoid GHC.Base.build'
     GHC.Base.const GHC.Base.flip GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__
     GHC.Base.mappend GHC.Base.mempty GHC.Base.op_z2218U__ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg____ GHC.Base.pure__ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.op_zp__ GHC.Prim.coerce HsToCoq.Unpeel.Build_Unpeel
     HsToCoq.Unpeel.Unpeel
*)
