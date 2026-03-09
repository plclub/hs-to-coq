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
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Pair a : Type := | Mk_Pair (pFst : a) (pSnd : a) : Pair a.

Arguments Mk_Pair {_} _ _.

#[global] Definition pFst {a} (arg_0__ : Pair a) :=
  let 'Mk_Pair pFst _ := arg_0__ in
  pFst.

#[global] Definition pSnd {a} (arg_0__ : Pair a) :=
  let 'Mk_Pair _ pSnd := arg_0__ in
  pSnd.

(* Converted value declarations: *)

#[local] Definition Foldable__Pair_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Pair a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Pair a1 a2 => GHC.Base.mappend (f a1) (f a2)
      end.

#[local] Definition Foldable__Pair_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Pair m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Pair_foldMap GHC.Base.id.

#[local] Definition Foldable__Pair_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Pair a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Pair_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Pair_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> Pair a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Pair a1 a2 => f a1 (f a2 z)
      end.

#[local] Definition Foldable__Pair_length
   : forall {a : Type}, Pair a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Pair_foldl (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

#[local] Definition Foldable__Pair_null : forall {a : Type}, Pair a -> bool :=
  fun {a : Type} => fun '(Mk_Pair _ _) => false.

#[local] Definition Foldable__Pair_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Pair a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Pair_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Pair_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Pair a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Pair_foldMap
                                Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Pair_toList
   : forall {a : Type}, Pair a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Pair_foldr c n t)).

#[global]
Program Instance Foldable__Pair : Data.Foldable.Foldable Pair :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__Pair_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Pair_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__Pair_foldl ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__Pair_foldr ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__Pair_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__Pair_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Pair_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Pair_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__Pair_toList |}.

#[local] Definition Functor__Pair_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Pair a -> Pair b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Pair a1 a2 => Mk_Pair (f a1) (f a2)
      end.

#[local] Definition Functor__Pair_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Pair b -> Pair a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | z, Mk_Pair a1 a2 => Mk_Pair z z
      end.

#[global]
Program Instance Functor__Pair : GHC.Base.Functor Pair :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Pair_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Pair_op_zlzd__ |}.

#[local] Definition Traversable__Pair_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> Pair a -> f (Pair b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Pair a1 a2 => GHC.Base.liftA2 (fun b1 b2 => Mk_Pair b1 b2) (f a1) (f a2)
      end.

#[local] Definition Traversable__Pair_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Pair a -> m (Pair b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Pair_traverse.

#[local] Definition Traversable__Pair_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Applicative f}, Pair (f a) -> f (Pair a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Pair_traverse GHC.Base.id.

#[local] Definition Traversable__Pair_sequence
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, Pair (m a) -> m (Pair a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Pair_sequenceA.

#[global]
Program Instance Traversable__Pair : Data.Traversable.Traversable Pair :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Pair_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Pair_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Pair_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Pair_traverse |}.

#[local] Definition Applicative__Pair_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Pair (a -> b) -> Pair a -> Pair b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Pair f g, Mk_Pair x y => Mk_Pair (f x) (g y)
      end.

#[local] Definition Applicative__Pair_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Pair a -> Pair b -> Pair c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Pair_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__Pair_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Pair a -> Pair b -> Pair b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Pair_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Pair_pure : forall {a : Type}, a -> Pair a :=
  fun {a : Type} => fun x => Mk_Pair x x.

#[global]
Program Instance Applicative__Pair : GHC.Base.Applicative Pair :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Pair_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Pair_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Pair_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Pair_pure |}.

#[local] Definition Semigroup__Pair_op_zlzlzgzg__ {inst_a : Type}
  `{GHC.Base.Semigroup inst_a}
   : Pair inst_a -> Pair inst_a -> Pair inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Pair a1 b1, Mk_Pair a2 b2 =>
        Mk_Pair (a1 GHC.Base.<<>> a2) (b1 GHC.Base.<<>> b2)
    end.

#[global]
Program Instance Semigroup__Pair {a : Type} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Pair a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Pair_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Pair_mappend {inst_a : Type} `{GHC.Base.Semigroup
  inst_a} `{GHC.Base.Monoid inst_a}
   : Pair inst_a -> Pair inst_a -> Pair inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Pair_mempty {inst_a : Type} `{GHC.Base.Semigroup
  inst_a} `{GHC.Base.Monoid inst_a}
   : Pair inst_a :=
  Mk_Pair GHC.Base.mempty GHC.Base.mempty.

#[local] Definition Monoid__Pair_mconcat {inst_a : Type} `{GHC.Base.Semigroup
  inst_a} `{GHC.Base.Monoid inst_a}
   : list (Pair inst_a) -> Pair inst_a :=
  GHC.Base.foldr Monoid__Pair_mappend Monoid__Pair_mempty.

#[global]
Program Instance Monoid__Pair {a : Type} `{GHC.Base.Semigroup a}
  `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Pair a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Pair_mappend ;
           GHC.Base.mconcat__ := Monoid__Pair_mconcat ;
           GHC.Base.mempty__ := Monoid__Pair_mempty |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Pair.Outputable__Pair' *)

#[global] Definition unPair {a : Type} : Pair a -> (a * a)%type :=
  fun '(Mk_Pair x y) => pair x y.

#[global] Definition toPair {a : Type} : (a * a)%type -> Pair a :=
  fun '(pair x y) => Mk_Pair x y.

#[global] Definition swap {a : Type} : Pair a -> Pair a :=
  fun '(Mk_Pair x y) => Mk_Pair y x.

#[global] Definition pLiftFst {a : Type} : (a -> a) -> Pair a -> Pair a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_Pair a b => Mk_Pair (f a) b
    end.

#[global] Definition pLiftSnd {a : Type} : (a -> a) -> Pair a -> Pair a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_Pair a b => Mk_Pair a (f b)
    end.

(* External variables:
     Type bool false list op_zt__ pair Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.build' GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2 GHC.Base.liftA2__
     GHC.Base.mappend GHC.Base.mappend__ GHC.Base.mconcat__ GHC.Base.mempty
     GHC.Base.mempty__ GHC.Base.op_z2218U__ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg____ GHC.Base.pure__ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.op_zp__
*)
