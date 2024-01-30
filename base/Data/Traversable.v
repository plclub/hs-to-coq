(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Const.
Require Data.Functor.Identity.
Require Data.Functor.Utils.
Require Data.Monoid.
Require Data.Ord.
Require Data.Proxy.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.Prim.
Require GHC.Tuple.
Import Data.Functor.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Record Traversable__Dict (t : Type -> Type) := Traversable__Dict_Build {
  mapM__ : forall {m : Type -> Type},
  forall {a : Type},
  forall {b : Type}, forall `{GHC.Base.Monad m}, (a -> m b) -> t a -> m (t b) ;
  sequence__ : forall {m : Type -> Type},
  forall {a : Type}, forall `{GHC.Base.Monad m}, t (m a) -> m (t a) ;
  sequenceA__ : forall {f : Type -> Type},
  forall {a : Type}, forall `{GHC.Base.Applicative f}, t (f a) -> f (t a) ;
  traverse__ : forall {f : Type -> Type},
  forall {a : Type},
  forall {b : Type},
  forall `{GHC.Base.Applicative f}, (a -> f b) -> t a -> f (t b) }.

#[global] Definition Traversable (t : Type -> Type) `{GHC.Base.Functor t}
  `{Data.Foldable.Foldable t} :=
  forall r__, (Traversable__Dict t -> r__) -> r__.
Existing Class Traversable.

#[global] Definition mapM `{g__0__ : Traversable t}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type}, forall `{GHC.Base.Monad m}, (a -> m b) -> t a -> m (t b) :=
  g__0__ _ (mapM__ t).

#[global] Definition sequence `{g__0__ : Traversable t}
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, t (m a) -> m (t a) :=
  g__0__ _ (sequence__ t).

#[global] Definition sequenceA `{g__0__ : Traversable t}
   : forall {f : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Applicative f}, t (f a) -> f (t a) :=
  g__0__ _ (sequenceA__ t).

#[global] Definition traverse `{g__0__ : Traversable t}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> t a -> f (t b) :=
  g__0__ _ (traverse__ t).

(* Converted value declarations: *)

#[local] Definition Traversable__Down_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Data.Ord.Down a -> f (Data.Ord.Down b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.Ord.Mk_Down a1 => GHC.Base.fmap (fun b1 => Data.Ord.Mk_Down b1) (f a1)
      end.

#[local] Definition Traversable__Down_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Data.Ord.Down a -> m (Data.Ord.Down b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Down_traverse.

#[local] Definition Traversable__Down_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f}, Data.Ord.Down (f a) -> f (Data.Ord.Down a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Down_traverse GHC.Base.id.

#[local] Definition Traversable__Down_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, Data.Ord.Down (m a) -> m (Data.Ord.Down a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Down_sequenceA.

#[global]
Program Instance Traversable__Down : Traversable Data.Ord.Down :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Down_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Down_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Down_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Down_traverse |}.

#[local] Definition Traversable__UWord_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GHC.Generics.UWord a -> f (GHC.Generics.UWord b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UWord a1 => GHC.Base.pure (GHC.Generics.UWord a1)
      end.

#[local] Definition Traversable__UWord_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GHC.Generics.UWord a -> m (GHC.Generics.UWord b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__UWord_traverse.

#[local] Definition Traversable__UWord_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     GHC.Generics.UWord (f a) -> f (GHC.Generics.UWord a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__UWord_traverse GHC.Base.id.

#[local] Definition Traversable__UWord_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     GHC.Generics.UWord (m a) -> m (GHC.Generics.UWord a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__UWord_sequenceA.

#[global]
Program Instance Traversable__UWord : Traversable GHC.Generics.UWord :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__UWord_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__UWord_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__UWord_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__UWord_traverse |}.

#[local] Definition Traversable__UInt_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GHC.Generics.UInt a -> f (GHC.Generics.UInt b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UInt a1 => GHC.Base.pure (GHC.Generics.UInt a1)
      end.

#[local] Definition Traversable__UInt_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GHC.Generics.UInt a -> m (GHC.Generics.UInt b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__UInt_traverse.

#[local] Definition Traversable__UInt_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     GHC.Generics.UInt (f a) -> f (GHC.Generics.UInt a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__UInt_traverse GHC.Base.id.

#[local] Definition Traversable__UInt_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     GHC.Generics.UInt (m a) -> m (GHC.Generics.UInt a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__UInt_sequenceA.

#[global]
Program Instance Traversable__UInt : Traversable GHC.Generics.UInt :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__UInt_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__UInt_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__UInt_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__UInt_traverse |}.

#[local] Definition Traversable__UFloat_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GHC.Generics.UFloat a -> f (GHC.Generics.UFloat b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UFloat a1 => GHC.Base.pure (GHC.Generics.UFloat a1)
      end.

#[local] Definition Traversable__UFloat_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GHC.Generics.UFloat a -> m (GHC.Generics.UFloat b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__UFloat_traverse.

#[local] Definition Traversable__UFloat_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     GHC.Generics.UFloat (f a) -> f (GHC.Generics.UFloat a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__UFloat_traverse GHC.Base.id.

#[local] Definition Traversable__UFloat_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     GHC.Generics.UFloat (m a) -> m (GHC.Generics.UFloat a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__UFloat_sequenceA.

#[global]
Program Instance Traversable__UFloat : Traversable GHC.Generics.UFloat :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__UFloat_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__UFloat_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__UFloat_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__UFloat_traverse |}.

#[local] Definition Traversable__UDouble_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GHC.Generics.UDouble a -> f (GHC.Generics.UDouble b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UDouble a1 => GHC.Base.pure (GHC.Generics.UDouble a1)
      end.

#[local] Definition Traversable__UDouble_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GHC.Generics.UDouble a -> m (GHC.Generics.UDouble b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__UDouble_traverse.

#[local] Definition Traversable__UDouble_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     GHC.Generics.UDouble (f a) -> f (GHC.Generics.UDouble a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__UDouble_traverse GHC.Base.id.

#[local] Definition Traversable__UDouble_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     GHC.Generics.UDouble (m a) -> m (GHC.Generics.UDouble a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__UDouble_sequenceA.

#[global]
Program Instance Traversable__UDouble : Traversable GHC.Generics.UDouble :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__UDouble_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__UDouble_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__UDouble_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__UDouble_traverse |}.

#[local] Definition Traversable__UChar_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GHC.Generics.UChar a -> f (GHC.Generics.UChar b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UChar a1 => GHC.Base.pure (GHC.Generics.UChar a1)
      end.

#[local] Definition Traversable__UChar_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GHC.Generics.UChar a -> m (GHC.Generics.UChar b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__UChar_traverse.

#[local] Definition Traversable__UChar_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     GHC.Generics.UChar (f a) -> f (GHC.Generics.UChar a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__UChar_traverse GHC.Base.id.

#[local] Definition Traversable__UChar_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     GHC.Generics.UChar (m a) -> m (GHC.Generics.UChar a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__UChar_sequenceA.

#[global]
Program Instance Traversable__UChar : Traversable GHC.Generics.UChar :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__UChar_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__UChar_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__UChar_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__UChar_traverse |}.

#[local] Definition Traversable__UAddr_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GHC.Generics.UAddr a -> f (GHC.Generics.UAddr b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UAddr a1 => GHC.Base.pure (GHC.Generics.UAddr a1)
      end.

#[local] Definition Traversable__UAddr_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GHC.Generics.UAddr a -> m (GHC.Generics.UAddr b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__UAddr_traverse.

#[local] Definition Traversable__UAddr_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     GHC.Generics.UAddr (f a) -> f (GHC.Generics.UAddr a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__UAddr_traverse GHC.Base.id.

#[local] Definition Traversable__UAddr_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     GHC.Generics.UAddr (m a) -> m (GHC.Generics.UAddr a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__UAddr_sequenceA.

#[global]
Program Instance Traversable__UAddr : Traversable GHC.Generics.UAddr :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__UAddr_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__UAddr_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__UAddr_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__UAddr_traverse |}.

(* Skipping instance `Data.Traversable.Traversable__op_ZCziZC__' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__op_ZCztZC__' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__op_ZCzpZC__' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__M1' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__K1' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__Rec1' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__Par1' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__V1' of class
   `Data.Traversable.Traversable' *)

#[local] Definition Traversable__Identity_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.Functor.Identity.Identity a -> f (Data.Functor.Identity.Identity b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.Functor.Identity.Mk_Identity a1 =>
          GHC.Base.fmap (fun b1 => Data.Functor.Identity.Mk_Identity b1) (f a1)
      end.

#[local] Definition Traversable__Identity_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.Functor.Identity.Identity a -> m (Data.Functor.Identity.Identity b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Identity_traverse.

#[local] Definition Traversable__Identity_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Data.Functor.Identity.Identity (f a) -> f (Data.Functor.Identity.Identity a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Identity_traverse GHC.Base.id.

#[local] Definition Traversable__Identity_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Data.Functor.Identity.Identity (m a) -> m (Data.Functor.Identity.Identity a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Identity_sequenceA.

#[global]
Program Instance Traversable__Identity
   : Traversable Data.Functor.Identity.Identity :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Identity_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Identity_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Identity_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Identity_traverse |}.

#[local] Definition Traversable__option_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> option a -> f (option b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, None => GHC.Base.pure None
      | f, Some x => Some Data.Functor.<$> f x
      end.

#[local] Definition Traversable__option_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> option a -> m (option b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__option_traverse.

#[local] Definition Traversable__option_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f}, option (f a) -> f (option a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__option_traverse GHC.Base.id.

#[local] Definition Traversable__option_sequence
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, option (m a) -> m (option a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__option_sequenceA.

#[global]
Program Instance Traversable__option : Traversable option :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__option_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__option_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__option_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__option_traverse |}.

#[local] Definition Traversable__list_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> list a -> f (list b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun f =>
      let cons_f := fun x ys => GHC.Base.liftA2 cons (f x) ys in
      GHC.Base.foldr cons_f (GHC.Base.pure nil).

#[local] Definition Traversable__list_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> list a -> m (list b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__list_traverse.

#[local] Definition Traversable__list_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Applicative f}, list (f a) -> f (list a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__list_traverse GHC.Base.id.

#[local] Definition Traversable__list_sequence
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, list (m a) -> m (list a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__list_sequenceA.

#[global]
Program Instance Traversable__list : Traversable list :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__list_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__list_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__list_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__list_traverse |}.

#[local] Definition Traversable__NonEmpty_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GHC.Base.NonEmpty a -> f (GHC.Base.NonEmpty b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Base.NEcons a as_ =>
          GHC.Base.liftA2 GHC.Base.NEcons (f a) (traverse f as_)
      end.

#[local] Definition Traversable__NonEmpty_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GHC.Base.NonEmpty a -> m (GHC.Base.NonEmpty b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__NonEmpty_traverse.

#[local] Definition Traversable__NonEmpty_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     GHC.Base.NonEmpty (f a) -> f (GHC.Base.NonEmpty a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__NonEmpty_traverse GHC.Base.id.

#[local] Definition Traversable__NonEmpty_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     GHC.Base.NonEmpty (m a) -> m (GHC.Base.NonEmpty a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__NonEmpty_sequenceA.

#[global]
Program Instance Traversable__NonEmpty : Traversable GHC.Base.NonEmpty :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__NonEmpty_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__NonEmpty_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__NonEmpty_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__NonEmpty_traverse |}.

#[local] Definition Traversable__Either_traverse {inst_a : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Data.Either.Either inst_a a -> f (Data.Either.Either inst_a b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Data.Either.Left x => GHC.Base.pure (Data.Either.Left x)
      | f, Data.Either.Right y => Data.Either.Right Data.Functor.<$> f y
      end.

#[local] Definition Traversable__Either_mapM {inst_a : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Data.Either.Either inst_a a -> m (Data.Either.Either inst_a b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Either_traverse.

#[local] Definition Traversable__Either_sequenceA {inst_a : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Data.Either.Either inst_a (f a) -> f (Data.Either.Either inst_a a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Either_traverse GHC.Base.id.

#[local] Definition Traversable__Either_sequence {inst_a : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Data.Either.Either inst_a (m a) -> m (Data.Either.Either inst_a a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Either_sequenceA.

#[global]
Program Instance Traversable__Either {a : Type}
   : Traversable (Data.Either.Either a) :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Either_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Either_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Either_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Either_traverse |}.

#[local] Definition Traversable__pair_type_traverse {inst_a : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     GHC.Tuple.pair_type inst_a a -> f (GHC.Tuple.pair_type inst_a b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, pair x y => GHC.Tuple.pair2 x Data.Functor.<$> f y
      end.

#[local] Definition Traversable__pair_type_mapM {inst_a : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     GHC.Tuple.pair_type inst_a a -> m (GHC.Tuple.pair_type inst_a b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__pair_type_traverse.

#[local] Definition Traversable__pair_type_sequenceA {inst_a : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     GHC.Tuple.pair_type inst_a (f a) -> f (GHC.Tuple.pair_type inst_a a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__pair_type_traverse GHC.Base.id.

#[local] Definition Traversable__pair_type_sequence {inst_a : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     GHC.Tuple.pair_type inst_a (m a) -> m (GHC.Tuple.pair_type inst_a a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__pair_type_sequenceA.

#[global]
Program Instance Traversable__pair_type {a : Type}
   : Traversable (GHC.Tuple.pair_type a) :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__pair_type_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__pair_type_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__pair_type_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__pair_type_traverse |}.

(* Skipping instance `Data.Traversable.Traversable__Array' of class
   `Data.Traversable.Traversable' *)

#[local] Definition Traversable__Proxy_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Data.Proxy.Proxy a -> m (Data.Proxy.Proxy b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    fun arg_0__ arg_1__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

#[local] Definition Traversable__Proxy_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, Data.Proxy.Proxy (m a) -> m (Data.Proxy.Proxy a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    fun arg_0__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

#[local] Definition Traversable__Proxy_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Data.Proxy.Proxy (f a) -> f (Data.Proxy.Proxy a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

#[local] Definition Traversable__Proxy_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Data.Proxy.Proxy a -> f (Data.Proxy.Proxy b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

#[global]
Program Instance Traversable__Proxy : Traversable Data.Proxy.Proxy :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Proxy_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Proxy_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Proxy_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Proxy_traverse |}.

#[local] Definition Traversable__Const_traverse {inst_m : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.Functor.Const.Const inst_m a -> f (Data.Functor.Const.Const inst_m b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Data.Functor.Const.Mk_Const m =>
          GHC.Base.pure (Data.Functor.Const.Mk_Const m)
      end.

#[local] Definition Traversable__Const_mapM {inst_m : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.Functor.Const.Const inst_m a -> m (Data.Functor.Const.Const inst_m b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Const_traverse.

#[local] Definition Traversable__Const_sequenceA {inst_m : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Data.Functor.Const.Const inst_m (f a) ->
     f (Data.Functor.Const.Const inst_m a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Const_traverse GHC.Base.id.

#[local] Definition Traversable__Const_sequence {inst_m : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Data.Functor.Const.Const inst_m (m a) ->
     m (Data.Functor.Const.Const inst_m a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Const_sequenceA.

#[global]
Program Instance Traversable__Const {m : Type}
   : Traversable (Data.Functor.Const.Const m) :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Const_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Const_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Const_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Const_traverse |}.

#[local] Definition Traversable__Dual_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.SemigroupInternal.Dual a -> f (Data.SemigroupInternal.Dual b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.SemigroupInternal.Mk_Dual x =>
          Data.SemigroupInternal.Mk_Dual Data.Functor.<$> f x
      end.

#[local] Definition Traversable__Dual_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.SemigroupInternal.Dual a -> m (Data.SemigroupInternal.Dual b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Dual_traverse.

#[local] Definition Traversable__Dual_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Data.SemigroupInternal.Dual (f a) -> f (Data.SemigroupInternal.Dual a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Dual_traverse GHC.Base.id.

#[local] Definition Traversable__Dual_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Data.SemigroupInternal.Dual (m a) -> m (Data.SemigroupInternal.Dual a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Dual_sequenceA.

#[global]
Program Instance Traversable__Dual : Traversable Data.SemigroupInternal.Dual :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Dual_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Dual_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Dual_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Dual_traverse |}.

#[local] Definition Traversable__Sum_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.SemigroupInternal.Sum a -> f (Data.SemigroupInternal.Sum b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.SemigroupInternal.Mk_Sum x =>
          Data.SemigroupInternal.Mk_Sum Data.Functor.<$> f x
      end.

#[local] Definition Traversable__Sum_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.SemigroupInternal.Sum a -> m (Data.SemigroupInternal.Sum b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Sum_traverse.

#[local] Definition Traversable__Sum_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Data.SemigroupInternal.Sum (f a) -> f (Data.SemigroupInternal.Sum a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Sum_traverse GHC.Base.id.

#[local] Definition Traversable__Sum_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Data.SemigroupInternal.Sum (m a) -> m (Data.SemigroupInternal.Sum a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Sum_sequenceA.

#[global]
Program Instance Traversable__Sum : Traversable Data.SemigroupInternal.Sum :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Sum_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Sum_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Sum_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Sum_traverse |}.

#[local] Definition Traversable__Product_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.SemigroupInternal.Product a -> f (Data.SemigroupInternal.Product b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.SemigroupInternal.Mk_Product x =>
          Data.SemigroupInternal.Mk_Product Data.Functor.<$> f x
      end.

#[local] Definition Traversable__Product_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.SemigroupInternal.Product a -> m (Data.SemigroupInternal.Product b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Product_traverse.

#[local] Definition Traversable__Product_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Data.SemigroupInternal.Product (f a) -> f (Data.SemigroupInternal.Product a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Product_traverse GHC.Base.id.

#[local] Definition Traversable__Product_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Data.SemigroupInternal.Product (m a) -> m (Data.SemigroupInternal.Product a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Product_sequenceA.

#[global]
Program Instance Traversable__Product
   : Traversable Data.SemigroupInternal.Product :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Product_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Product_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Product_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Product_traverse |}.

(* Skipping instance `Data.Traversable.Traversable__First' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__Last' of class
   `Data.Traversable.Traversable' *)

#[local] Definition Traversable__Alt_traverse {inst_f : Type -> Type}
  `{(Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.SemigroupInternal.Alt inst_f a ->
     f (Data.SemigroupInternal.Alt inst_f b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.SemigroupInternal.Mk_Alt x =>
          Data.SemigroupInternal.Mk_Alt Data.Functor.<$> traverse f x
      end.

#[local] Definition Traversable__Alt_mapM {inst_f : Type -> Type} `{(Traversable
   inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.SemigroupInternal.Alt inst_f a ->
     m (Data.SemigroupInternal.Alt inst_f b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Alt_traverse.

#[local] Definition Traversable__Alt_sequenceA {inst_f : Type -> Type}
  `{(Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Data.SemigroupInternal.Alt inst_f (f a) ->
     f (Data.SemigroupInternal.Alt inst_f a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Alt_traverse GHC.Base.id.

#[local] Definition Traversable__Alt_sequence {inst_f : Type -> Type}
  `{(Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Data.SemigroupInternal.Alt inst_f (m a) ->
     m (Data.SemigroupInternal.Alt inst_f a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Alt_sequenceA.

#[global]
Program Instance Traversable__Alt {f : Type -> Type} `{(Traversable f)}
   : Traversable (Data.SemigroupInternal.Alt f) :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Alt_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Alt_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Alt_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Alt_traverse |}.

#[local] Definition Traversable__Ap_traverse {inst_f : Type -> Type}
  `{(Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Data.Monoid.Ap inst_f a -> f (Data.Monoid.Ap inst_f b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.Monoid.Mk_Ap x => Data.Monoid.Mk_Ap Data.Functor.<$> traverse f x
      end.

#[local] Definition Traversable__Ap_mapM {inst_f : Type -> Type} `{(Traversable
   inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Data.Monoid.Ap inst_f a -> m (Data.Monoid.Ap inst_f b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Ap_traverse.

#[local] Definition Traversable__Ap_sequenceA {inst_f : Type -> Type}
  `{(Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Data.Monoid.Ap inst_f (f a) -> f (Data.Monoid.Ap inst_f a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Ap_traverse GHC.Base.id.

#[local] Definition Traversable__Ap_sequence {inst_f : Type -> Type}
  `{(Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Data.Monoid.Ap inst_f (m a) -> m (Data.Monoid.Ap inst_f a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Ap_sequenceA.

#[global]
Program Instance Traversable__Ap {f : Type -> Type} `{(Traversable f)}
   : Traversable (Data.Monoid.Ap f) :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Ap_mapM ;
           sequence__ := fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
             Traversable__Ap_sequence ;
           sequenceA__ := fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
             Traversable__Ap_sequenceA ;
           traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Ap_traverse |}.

(* Skipping instance `Data.Traversable.Traversable__ZipList' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__U1' of class
   `Data.Traversable.Traversable' *)

#[global] Definition for_ {t : Type -> Type} {f : Type -> Type} {a : Type} {b
   : Type} `{Traversable t} `{GHC.Base.Applicative f}
   : t a -> (a -> f b) -> f (t b) :=
  GHC.Base.flip traverse.

#[global] Definition forM {t : Type -> Type} {m : Type -> Type} {a : Type} {b
   : Type} `{Traversable t} `{GHC.Base.Monad m}
   : t a -> (a -> m b) -> m (t b) :=
  GHC.Base.flip mapM.

#[global] Definition mapAccumL {t : Type -> Type} {a : Type} {b : Type} {c
   : Type} `{Traversable t}
   : (a -> b -> (a * c)%type) -> a -> t b -> (a * t c)%type :=
  fun f s t =>
    Data.Functor.Utils.runStateL (traverse (Data.Functor.Utils.Mk_StateL GHC.Base.∘
                                            GHC.Base.flip f) t) s.

#[global] Definition mapAccumR {t : Type -> Type} {a : Type} {b : Type} {c
   : Type} `{Traversable t}
   : (a -> b -> (a * c)%type) -> a -> t b -> (a * t c)%type :=
  fun f s t =>
    Data.Functor.Utils.runStateR (traverse (Data.Functor.Utils.Mk_StateR GHC.Base.∘
                                            GHC.Base.flip f) t) s.

#[global] Definition fmapDefault {t : Type -> Type} {a : Type} {b : Type}
  `{Traversable t}
   : (a -> b) -> t a -> t b :=
  GHC.Prim.coerce (traverse : (a -> Data.Functor.Identity.Identity b) ->
                   t a -> Data.Functor.Identity.Identity (t b)).

(* Skipping definition `Data.Traversable.foldMapDefault' *)

(* External variables:
     None Some Type cons list nil op_zt__ option pair Data.Either.Either
     Data.Either.Left Data.Either.Right Data.Foldable.Foldable
     Data.Functor.op_zlzdzg__ Data.Functor.Const.Const Data.Functor.Const.Mk_Const
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Functor.Utils.Mk_StateL Data.Functor.Utils.Mk_StateR
     Data.Functor.Utils.runStateL Data.Functor.Utils.runStateR Data.Monoid.Ap
     Data.Monoid.Mk_Ap Data.Ord.Down Data.Ord.Mk_Down Data.Proxy.Mk_Proxy
     Data.Proxy.Proxy Data.SemigroupInternal.Alt Data.SemigroupInternal.Dual
     Data.SemigroupInternal.Mk_Alt Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.Product Data.SemigroupInternal.Sum GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.NEcons GHC.Base.NonEmpty GHC.Base.flip
     GHC.Base.fmap GHC.Base.foldr GHC.Base.id GHC.Base.liftA2 GHC.Base.op_z2218U__
     GHC.Base.pure GHC.Generics.UAddr GHC.Generics.UChar GHC.Generics.UDouble
     GHC.Generics.UFloat GHC.Generics.UInt GHC.Generics.UWord GHC.Prim.coerce
     GHC.Tuple.pair2 GHC.Tuple.pair_type
*)
