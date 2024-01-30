(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Data.Monoid.
(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Either.
Require Data.Maybe.
Require Data.Monoid.
Require Data.Ord.
Require Data.Proxy.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Tuple.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Record Foldable__Dict (t : Type -> Type) := Foldable__Dict_Build {
  fold__ : forall {m : Type}, forall `{GHC.Base.Monoid m}, t m -> m ;
  foldMap__ : forall {m : Type},
  forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m ;
  foldMap'__ : forall {m : Type},
  forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m ;
  foldl__ : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> t a -> b ;
  foldl'__ : forall {b : Type},
  forall {a : Type}, (b -> a -> b) -> b -> t a -> b ;
  foldr__ : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> t a -> b ;
  foldr'__ : forall {a : Type},
  forall {b : Type}, (a -> b -> b) -> b -> t a -> b ;
  length__ : forall {a : Type}, t a -> GHC.Num.Int ;
  null__ : forall {a : Type}, t a -> bool ;
  product__ : forall {a : Type}, forall `{GHC.Num.Num a}, t a -> a ;
  sum__ : forall {a : Type}, forall `{GHC.Num.Num a}, t a -> a ;
  toList__ : forall {a : Type}, t a -> list a }.

#[global] Definition Foldable (t : Type -> Type) :=
  forall r__, (Foldable__Dict t -> r__) -> r__.
Existing Class Foldable.

#[global] Definition fold `{g__0__ : Foldable t}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, t m -> m :=
  g__0__ _ (fold__ t).

#[global] Definition foldMap `{g__0__ : Foldable t}
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m :=
  g__0__ _ (foldMap__ t).

#[global] Definition foldMap' `{g__0__ : Foldable t}
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m :=
  g__0__ _ (foldMap'__ t).

#[global] Definition foldl `{g__0__ : Foldable t}
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> t a -> b :=
  g__0__ _ (foldl__ t).

#[global] Definition foldl' `{g__0__ : Foldable t}
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> t a -> b :=
  g__0__ _ (foldl'__ t).

#[global] Definition foldr `{g__0__ : Foldable t}
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> t a -> b :=
  g__0__ _ (foldr__ t).

#[global] Definition foldr' `{g__0__ : Foldable t}
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> t a -> b :=
  g__0__ _ (foldr'__ t).

#[global] Definition length `{g__0__ : Foldable t}
   : forall {a : Type}, t a -> GHC.Num.Int :=
  g__0__ _ (length__ t).

#[global] Definition null `{g__0__ : Foldable t}
   : forall {a : Type}, t a -> bool :=
  g__0__ _ (null__ t).

#[global] Definition product `{g__0__ : Foldable t}
   : forall {a : Type}, forall `{GHC.Num.Num a}, t a -> a :=
  g__0__ _ (product__ t).

#[global] Definition sum `{g__0__ : Foldable t}
   : forall {a : Type}, forall `{GHC.Num.Num a}, t a -> a :=
  g__0__ _ (sum__ t).

#[global] Definition toList `{g__0__ : Foldable t}
   : forall {a : Type}, t a -> list a :=
  g__0__ _ (toList__ t).

(* Midamble *)

Definition default_foldable {f:Type -> Type}
  (foldMap : forall m a, forall (S : GHC.Base.Semigroup m) (M : GHC.Base.Monoid m), (a -> m) -> f a -> m)
  (foldr : forall a b, (a -> b -> b) -> b -> f a -> b):=
  let foldl : forall b a, (b -> a -> b) -> b -> f a -> b :=
      (fun b a =>
         fun f  z t => Data.SemigroupInternal.appEndo
                    (Data.SemigroupInternal.getDual
                       (foldMap _ _ _ _ (Coq.Program.Basics.compose
                                   Data.SemigroupInternal.Mk_Dual
                                   (Coq.Program.Basics.compose
                                      Data.SemigroupInternal.Mk_Endo
                                      (GHC.Base.flip f))) t)) z)
  in
  let foldl' : forall b a, (b -> a -> b) -> b -> f a -> b :=
      (fun {b} {a} =>
         fun f  z0  xs =>
           let f' :=  fun  x  k  z => GHC.Base.op_zdzn__ k (f z x)
           in foldr _ _ f' GHC.Base.id xs z0)
  in
  Foldable__Dict_Build
    f
    (* fold *)
    (fun m (S : GHC.Base.Semigroup m) (M : GHC.Base.Monoid m) => foldMap _ _ _ _ GHC.Base.id)
    (* foldMap *)
    (@foldMap)
    (* foldl *)
    (@foldl)
    (* foldl' *)
    (@foldl')
    (* foldr  *)
    (@foldr)
    (* foldr' *)
    (fun a b f z0 xs =>
       let f' := fun k  x  z => GHC.Base.op_zdzn__ k (f x z)
       in
       @foldl _ _ f' GHC.Base.id xs z0)
    (* length *)
    (fun a => @foldl' _ a (fun c  _ => GHC.Num.op_zp__ c (GHC.Num.fromInteger 1))
                    (GHC.Num.fromInteger 0))
    (* null *)
    (fun a => @foldr _ _ (fun arg_61__ arg_62__ => false) true)
    (* product *)
    (fun a `{GHC.Num.Num a} =>
       Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                                  (foldMap _ _ _ _ Data.SemigroupInternal.Mk_Product))
    (* sum *)
    (fun a `{GHC.Num.Num a} =>
       Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                                  (foldMap _ _ _ _ Data.SemigroupInternal.Mk_Sum))
    (* toList *)
    (fun a => fun t => GHC.Base.build (fun _ c n => @foldr _ _ c n t)).

Definition default_foldable_foldMap {f : Type -> Type}
  (foldMap : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> f a -> m)
 :=
  let foldr : forall {a} {b}, (a -> b -> b) -> b -> f a -> b :=
  fun a b f z t =>
    Data.SemigroupInternal.appEndo
      (foldMap
         (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z
  in
  default_foldable (fun {m}{a} `{GHC.Base.Monoid m} => foldMap) foldr.

Definition default_foldable_foldr (f : Type -> Type)
  (foldr : forall {a} {b}, (a -> b -> b) -> b -> f a -> b) :=
  let foldMap :  forall {m} {a} `{GHC.Base.Monoid m}, (a -> m) -> f a -> m :=
  fun m a (S : GHC.Base.Semigroup m) (H : GHC.Base.Monoid m) =>
    fun f => foldr
            (Coq.Program.Basics.compose GHC.Base.mappend
                                        f) GHC.Base.mempty
  in
  default_foldable foldMap (fun {a} {b} => foldr).

(* Converted value declarations: *)

#[local] Definition Foldable__Down_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Ord.Down a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.Ord.Mk_Down a1 => f a1
      end.

#[local] Definition Foldable__Down_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Data.Ord.Down m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Down_foldMap GHC.Base.id.

#[local] Definition Foldable__Down_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.Ord.Down a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Data.Ord.Mk_Down a1 => f a1 z
      end.

#[local] Definition Foldable__Down_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.Ord.Down a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Down_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__Down_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Ord.Down a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Down_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Down_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.Ord.Down a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Down_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Down_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.Ord.Down a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Down_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__Down_length
   : forall {a : Type}, Data.Ord.Down a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Down_foldl' (fun arg_0__ arg_1__ =>
                             match arg_0__, arg_1__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

#[local] Definition Foldable__Down_null
   : forall {a : Type}, Data.Ord.Down a -> bool :=
  fun {a : Type} => fun '(Data.Ord.Mk_Down _) => false.

#[local] Definition Foldable__Down_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Data.Ord.Down a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Down_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Down_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Data.Ord.Down a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Down_foldMap
                                Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Down_toList
   : forall {a : Type}, Data.Ord.Down a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Down_foldr c n t)).

#[global]
Program Instance Foldable__Down : Foldable Data.Ord.Down :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Down_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Down_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Down_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__Down_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__Down_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__Down_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__Down_foldr' ;
           length__ := fun {a : Type} => Foldable__Down_length ;
           null__ := fun {a : Type} => Foldable__Down_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Down_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Down_sum ;
           toList__ := fun {a : Type} => Foldable__Down_toList |}.

#[local] Definition Foldable__UWord_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UWord a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UWord a1 => GHC.Base.mempty
      end.

#[local] Definition Foldable__UWord_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, GHC.Generics.UWord m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UWord_foldMap GHC.Base.id.

#[local] Definition Foldable__UWord_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UWord a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Generics.UWord a1 => z
      end.

#[local] Definition Foldable__UWord_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UWord a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__UWord_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__UWord_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UWord a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__UWord_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__UWord_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UWord a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__UWord_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                 GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__UWord_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UWord a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__UWord_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__UWord_length
   : forall {a : Type}, GHC.Generics.UWord a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__UWord_foldl' (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

#[local] Definition Foldable__UWord_null
   : forall {a : Type}, GHC.Generics.UWord a -> bool :=
  fun {a : Type} => fun '(GHC.Generics.UWord a1) => true.

#[local] Definition Foldable__UWord_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UWord a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__UWord_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__UWord_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UWord a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__UWord_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__UWord_toList
   : forall {a : Type}, GHC.Generics.UWord a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__UWord_foldr c n t)).

#[global]
Program Instance Foldable__UWord : Foldable GHC.Generics.UWord :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UWord_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UWord_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UWord_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__UWord_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__UWord_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__UWord_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__UWord_foldr' ;
           length__ := fun {a : Type} => Foldable__UWord_length ;
           null__ := fun {a : Type} => Foldable__UWord_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UWord_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UWord_sum ;
           toList__ := fun {a : Type} => Foldable__UWord_toList |}.

#[local] Definition Foldable__UInt_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UInt a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UInt a1 => GHC.Base.mempty
      end.

#[local] Definition Foldable__UInt_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, GHC.Generics.UInt m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UInt_foldMap GHC.Base.id.

#[local] Definition Foldable__UInt_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UInt a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Generics.UInt a1 => z
      end.

#[local] Definition Foldable__UInt_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UInt a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__UInt_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__UInt_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UInt a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__UInt_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__UInt_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UInt a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__UInt_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__UInt_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UInt a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__UInt_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__UInt_length
   : forall {a : Type}, GHC.Generics.UInt a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__UInt_foldl' (fun arg_0__ arg_1__ =>
                             match arg_0__, arg_1__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

#[local] Definition Foldable__UInt_null
   : forall {a : Type}, GHC.Generics.UInt a -> bool :=
  fun {a : Type} => fun '(GHC.Generics.UInt a1) => true.

#[local] Definition Foldable__UInt_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UInt a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__UInt_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__UInt_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UInt a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__UInt_foldMap
                                Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__UInt_toList
   : forall {a : Type}, GHC.Generics.UInt a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__UInt_foldr c n t)).

#[global]
Program Instance Foldable__UInt : Foldable GHC.Generics.UInt :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UInt_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UInt_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UInt_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__UInt_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__UInt_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__UInt_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__UInt_foldr' ;
           length__ := fun {a : Type} => Foldable__UInt_length ;
           null__ := fun {a : Type} => Foldable__UInt_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UInt_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UInt_sum ;
           toList__ := fun {a : Type} => Foldable__UInt_toList |}.

#[local] Definition Foldable__UFloat_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UFloat a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UFloat a1 => GHC.Base.mempty
      end.

#[local] Definition Foldable__UFloat_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, GHC.Generics.UFloat m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UFloat_foldMap GHC.Base.id.

#[local] Definition Foldable__UFloat_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UFloat a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Generics.UFloat a1 => z
      end.

#[local] Definition Foldable__UFloat_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UFloat a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__UFloat_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__UFloat_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UFloat a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__UFloat_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__UFloat_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UFloat a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__UFloat_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                 (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                  GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__UFloat_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UFloat a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__UFloat_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__UFloat_length
   : forall {a : Type}, GHC.Generics.UFloat a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__UFloat_foldl' (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | c, _ => c GHC.Num.+ #1
                               end) #0.

#[local] Definition Foldable__UFloat_null
   : forall {a : Type}, GHC.Generics.UFloat a -> bool :=
  fun {a : Type} => fun '(GHC.Generics.UFloat a1) => true.

#[local] Definition Foldable__UFloat_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UFloat a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__UFloat_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__UFloat_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UFloat a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__UFloat_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__UFloat_toList
   : forall {a : Type}, GHC.Generics.UFloat a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__UFloat_foldr c n t)).

#[global]
Program Instance Foldable__UFloat : Foldable GHC.Generics.UFloat :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UFloat_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UFloat_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UFloat_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__UFloat_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__UFloat_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__UFloat_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__UFloat_foldr' ;
           length__ := fun {a : Type} => Foldable__UFloat_length ;
           null__ := fun {a : Type} => Foldable__UFloat_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UFloat_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UFloat_sum ;
           toList__ := fun {a : Type} => Foldable__UFloat_toList |}.

#[local] Definition Foldable__UDouble_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UDouble a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UDouble a1 => GHC.Base.mempty
      end.

#[local] Definition Foldable__UDouble_fold
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, GHC.Generics.UDouble m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UDouble_foldMap GHC.Base.id.

#[local] Definition Foldable__UDouble_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UDouble a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Generics.UDouble a1 => z
      end.

#[local] Definition Foldable__UDouble_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UDouble a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__UDouble_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__UDouble_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UDouble a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__UDouble_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__UDouble_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UDouble a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__UDouble_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__UDouble_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UDouble a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__UDouble_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__UDouble_length
   : forall {a : Type}, GHC.Generics.UDouble a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__UDouble_foldl' (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

#[local] Definition Foldable__UDouble_null
   : forall {a : Type}, GHC.Generics.UDouble a -> bool :=
  fun {a : Type} => fun '(GHC.Generics.UDouble a1) => true.

#[local] Definition Foldable__UDouble_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UDouble a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__UDouble_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__UDouble_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UDouble a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__UDouble_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__UDouble_toList
   : forall {a : Type}, GHC.Generics.UDouble a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__UDouble_foldr c n t)).

#[global]
Program Instance Foldable__UDouble : Foldable GHC.Generics.UDouble :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UDouble_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UDouble_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UDouble_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__UDouble_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__UDouble_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__UDouble_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__UDouble_foldr' ;
           length__ := fun {a : Type} => Foldable__UDouble_length ;
           null__ := fun {a : Type} => Foldable__UDouble_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UDouble_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UDouble_sum ;
           toList__ := fun {a : Type} => Foldable__UDouble_toList |}.

#[local] Definition Foldable__UChar_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UChar a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UChar a1 => GHC.Base.mempty
      end.

#[local] Definition Foldable__UChar_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, GHC.Generics.UChar m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UChar_foldMap GHC.Base.id.

#[local] Definition Foldable__UChar_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UChar a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Generics.UChar a1 => z
      end.

#[local] Definition Foldable__UChar_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UChar a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__UChar_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__UChar_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UChar a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__UChar_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__UChar_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UChar a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__UChar_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                 GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__UChar_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UChar a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__UChar_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__UChar_length
   : forall {a : Type}, GHC.Generics.UChar a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__UChar_foldl' (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

#[local] Definition Foldable__UChar_null
   : forall {a : Type}, GHC.Generics.UChar a -> bool :=
  fun {a : Type} => fun '(GHC.Generics.UChar a1) => true.

#[local] Definition Foldable__UChar_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UChar a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__UChar_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__UChar_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UChar a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__UChar_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__UChar_toList
   : forall {a : Type}, GHC.Generics.UChar a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__UChar_foldr c n t)).

#[global]
Program Instance Foldable__UChar : Foldable GHC.Generics.UChar :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UChar_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UChar_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UChar_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__UChar_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__UChar_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__UChar_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__UChar_foldr' ;
           length__ := fun {a : Type} => Foldable__UChar_length ;
           null__ := fun {a : Type} => Foldable__UChar_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UChar_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UChar_sum ;
           toList__ := fun {a : Type} => Foldable__UChar_toList |}.

#[local] Definition Foldable__UAddr_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UAddr a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Generics.UAddr a1 => GHC.Base.mempty
      end.

#[local] Definition Foldable__UAddr_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, GHC.Generics.UAddr m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UAddr_foldMap GHC.Base.id.

#[local] Definition Foldable__UAddr_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UAddr a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Generics.UAddr a1 => z
      end.

#[local] Definition Foldable__UAddr_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UAddr a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__UAddr_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__UAddr_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Generics.UAddr a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__UAddr_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__UAddr_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Generics.UAddr a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__UAddr_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                 GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__UAddr_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Generics.UAddr a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__UAddr_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__UAddr_length
   : forall {a : Type}, GHC.Generics.UAddr a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__UAddr_foldl' (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

#[local] Definition Foldable__UAddr_null
   : forall {a : Type}, GHC.Generics.UAddr a -> bool :=
  fun {a : Type} => fun '(GHC.Generics.UAddr a1) => true.

#[local] Definition Foldable__UAddr_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UAddr a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__UAddr_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__UAddr_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Generics.UAddr a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__UAddr_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__UAddr_toList
   : forall {a : Type}, GHC.Generics.UAddr a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__UAddr_foldr c n t)).

#[global]
Program Instance Foldable__UAddr : Foldable GHC.Generics.UAddr :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__UAddr_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UAddr_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__UAddr_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__UAddr_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__UAddr_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__UAddr_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__UAddr_foldr' ;
           length__ := fun {a : Type} => Foldable__UAddr_length ;
           null__ := fun {a : Type} => Foldable__UAddr_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UAddr_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__UAddr_sum ;
           toList__ := fun {a : Type} => Foldable__UAddr_toList |}.

(* Skipping instance `Data.Foldable.Foldable__op_ZCziZC__' of class
   `Data.Foldable.Foldable' *)

(* Skipping instance `Data.Foldable.Foldable__op_ZCztZC__' of class
   `Data.Foldable.Foldable' *)

(* Skipping instance `Data.Foldable.Foldable__op_ZCzpZC__' of class
   `Data.Foldable.Foldable' *)

(* Skipping instance `Data.Foldable.Foldable__M1' of class
   `Data.Foldable.Foldable' *)

(* Skipping instance `Data.Foldable.Foldable__K1' of class
   `Data.Foldable.Foldable' *)

(* Skipping instance `Data.Foldable.Foldable__Rec1' of class
   `Data.Foldable.Foldable' *)

(* Skipping instance `Data.Foldable.Foldable__Par1' of class
   `Data.Foldable.Foldable' *)

(* Skipping instance `Data.Foldable.Foldable__V1' of class
   `Data.Foldable.Foldable' *)

#[local] Definition Foldable__option_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> option a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    Data.Maybe.maybe GHC.Base.mempty.

#[local] Definition Foldable__option_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, option m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__option_foldMap GHC.Base.id.

#[local] Definition Foldable__option_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> option a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, None => z
      | f, z, Some x => f x z
      end.

#[local] Definition Foldable__option_foldl'
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> option a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__option_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__option_foldMap'
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> option a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__option_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__option_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> option a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, None => z
      | f, z, Some x => f z x
      end.

#[local] Definition Foldable__option_foldr'
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> option a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__option_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__option_length
   : forall {a : Type}, option a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__option_foldl' (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | c, _ => c GHC.Num.+ #1
                               end) #0.

#[local] Definition Foldable__option_null
   : forall {a : Type}, option a -> bool :=
  fun {a : Type} => Foldable__option_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__option_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, option a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__option_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__option_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, option a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__option_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__option_toList
   : forall {a : Type}, option a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__option_foldr c n t)).

#[global]
Program Instance Foldable__option : Foldable option :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__option_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__option_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__option_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__option_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__option_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__option_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__option_foldr' ;
           length__ := fun {a : Type} => Foldable__option_length ;
           null__ := fun {a : Type} => Foldable__option_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__option_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__option_sum ;
           toList__ := fun {a : Type} => Foldable__option_toList |}.

#[local] Definition Foldable__list_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> list a -> b :=
  fun {a : Type} {b : Type} => GHC.Base.foldr.

#[local] Definition Foldable__list_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> list a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f => Foldable__list_foldr (GHC.Base.mappend GHC.Base.∘ f) GHC.Base.mempty.

#[local] Definition Foldable__list_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, list m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__list_foldMap GHC.Base.id.

#[local] Definition Foldable__list_foldl'
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> list a -> b :=
  fun {b : Type} {a : Type} => GHC.Base.foldl'.

#[local] Definition Foldable__list_foldMap'
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> list a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__list_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__list_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> list a -> b :=
  fun {b : Type} {a : Type} => GHC.Base.foldl.

#[local] Definition Foldable__list_foldr'
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> list a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__list_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__list_length
   : forall {a : Type}, list a -> GHC.Num.Int :=
  fun {a : Type} => GHC.List.length.

#[local] Definition Foldable__list_null : forall {a : Type}, list a -> bool :=
  fun {a : Type} => GHC.List.null.

#[local] Definition Foldable__list_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, list a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => GHC.List.product.

#[local] Definition Foldable__list_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, list a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => GHC.List.sum.

#[local] Definition Foldable__list_toList
   : forall {a : Type}, list a -> list a :=
  fun {a : Type} => GHC.Base.id.

#[global]
Program Instance Foldable__list : Foldable list :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__list_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__list_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__list_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__list_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__list_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__list_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__list_foldr' ;
           length__ := fun {a : Type} => Foldable__list_length ;
           null__ := fun {a : Type} => Foldable__list_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__list_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__list_sum ;
           toList__ := fun {a : Type} => Foldable__list_toList |}.

#[local] Definition Foldable__NonEmpty_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, GHC.Base.NonEmpty m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    fun '(GHC.Base.NEcons m ms) => GHC.Base.mappend m (fold ms).

#[local] Definition Foldable__NonEmpty_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Base.NonEmpty a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Base.NEcons a as_ => GHC.Base.mappend (f a) (foldMap f as_)
      end.

#[local] Definition Foldable__NonEmpty_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Base.NonEmpty a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Base.NEcons a as_ => f a (GHC.Base.foldr f z as_)
      end.

#[local] Definition Foldable__NonEmpty_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Base.NonEmpty a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__NonEmpty_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__NonEmpty_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Base.NonEmpty a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__NonEmpty_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__NonEmpty_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Base.NonEmpty a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Base.NEcons a as_ => GHC.Base.foldl f (f z a) as_
      end.

#[local] Definition Foldable__NonEmpty_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Base.NonEmpty a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__NonEmpty_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__NonEmpty_length
   : forall {a : Type}, GHC.Base.NonEmpty a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__NonEmpty_foldl' (fun arg_0__ arg_1__ =>
                                 match arg_0__, arg_1__ with
                                 | c, _ => c GHC.Num.+ #1
                                 end) #0.

#[local] Definition Foldable__NonEmpty_null
   : forall {a : Type}, GHC.Base.NonEmpty a -> bool :=
  fun {a : Type} => Foldable__NonEmpty_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__NonEmpty_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Base.NonEmpty a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__NonEmpty_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__NonEmpty_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, GHC.Base.NonEmpty a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__NonEmpty_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__NonEmpty_toList
   : forall {a : Type}, GHC.Base.NonEmpty a -> list a :=
  fun {a : Type} => fun '(GHC.Base.NEcons a as_) => cons a as_.

#[global]
Program Instance Foldable__NonEmpty : Foldable GHC.Base.NonEmpty :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__NonEmpty_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__NonEmpty_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__NonEmpty_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__NonEmpty_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__NonEmpty_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__NonEmpty_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__NonEmpty_foldr' ;
           length__ := fun {a : Type} => Foldable__NonEmpty_length ;
           null__ := fun {a : Type} => Foldable__NonEmpty_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__NonEmpty_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__NonEmpty_sum ;
           toList__ := fun {a : Type} => Foldable__NonEmpty_toList |}.

#[local] Definition Foldable__Either_foldMap {inst_a : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Either.Either inst_a a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Data.Either.Left _ => GHC.Base.mempty
      | f, Data.Either.Right y => f y
      end.

#[local] Definition Foldable__Either_fold {inst_a : Type}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Data.Either.Either inst_a m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Either_foldMap GHC.Base.id.

#[local] Definition Foldable__Either_foldr {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.Either.Either inst_a a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, Data.Either.Left _ => z
      | f, z, Data.Either.Right y => f y z
      end.

#[local] Definition Foldable__Either_foldl' {inst_a : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.Either.Either inst_a a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Either_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__Either_foldMap' {inst_a : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Either.Either inst_a a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Either_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Either_foldl {inst_a : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.Either.Either inst_a a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Either_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                 (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                  GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Either_foldr' {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.Either.Either inst_a a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Either_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__Either_length {inst_a : Type}
   : forall {a : Type}, Data.Either.Either inst_a a -> GHC.Num.Int :=
  fun {a : Type} =>
    fun arg_0__ =>
      match arg_0__ with
      | Data.Either.Left _ => #0
      | Data.Either.Right _ => #1
      end.

#[local] Definition Foldable__Either_null {inst_a : Type}
   : forall {a : Type}, Data.Either.Either inst_a a -> bool :=
  fun {a : Type} => Data.Either.isLeft.

#[local] Definition Foldable__Either_product {inst_a : Type}
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.Either.Either inst_a a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Either_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Either_sum {inst_a : Type}
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.Either.Either inst_a a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Either_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Either_toList {inst_a : Type}
   : forall {a : Type}, Data.Either.Either inst_a a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Either_foldr c n t)).

#[global]
Program Instance Foldable__Either {a : Type}
   : Foldable (Data.Either.Either a) :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Either_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Either_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Either_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__Either_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__Either_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__Either_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__Either_foldr' ;
           length__ := fun {a : Type} => Foldable__Either_length ;
           null__ := fun {a : Type} => Foldable__Either_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Either_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Either_sum ;
           toList__ := fun {a : Type} => Foldable__Either_toList |}.

#[local] Definition Foldable__pair_type_foldMap {inst_a : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Tuple.pair_type inst_a a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, pair _ y => f y end.

#[local] Definition Foldable__pair_type_fold {inst_a : Type}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, GHC.Tuple.pair_type inst_a m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__pair_type_foldMap GHC.Base.id.

#[local] Definition Foldable__pair_type_foldr {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Tuple.pair_type inst_a a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, pair _ y => f y z
      end.

#[local] Definition Foldable__pair_type_foldl' {inst_a : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Tuple.pair_type inst_a a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__pair_type_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__pair_type_foldMap' {inst_a : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Tuple.pair_type inst_a a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__pair_type_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__pair_type_foldl {inst_a : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> GHC.Tuple.pair_type inst_a a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__pair_type_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                    (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                     GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__pair_type_foldr' {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Tuple.pair_type inst_a a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__pair_type_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__pair_type_length {inst_a : Type}
   : forall {a : Type}, GHC.Tuple.pair_type inst_a a -> GHC.Num.Int :=
  fun {a : Type} => fun arg_0__ => #1.

#[local] Definition Foldable__pair_type_null {inst_a : Type}
   : forall {a : Type}, GHC.Tuple.pair_type inst_a a -> bool :=
  fun {a : Type} => fun arg_0__ => false.

#[local] Definition Foldable__pair_type_product {inst_a : Type}
   : forall {a : Type},
     forall `{GHC.Num.Num a}, GHC.Tuple.pair_type inst_a a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__pair_type_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__pair_type_sum {inst_a : Type}
   : forall {a : Type},
     forall `{GHC.Num.Num a}, GHC.Tuple.pair_type inst_a a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__pair_type_foldMap Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__pair_type_toList {inst_a : Type}
   : forall {a : Type}, GHC.Tuple.pair_type inst_a a -> list a :=
  fun {a : Type} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__pair_type_foldr c n t)).

#[global]
Program Instance Foldable__pair_type {a : Type}
   : Foldable (GHC.Tuple.pair_type a) :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__pair_type_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__pair_type_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__pair_type_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__pair_type_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__pair_type_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__pair_type_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__pair_type_foldr' ;
           length__ := fun {a : Type} => Foldable__pair_type_length ;
           null__ := fun {a : Type} => Foldable__pair_type_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__pair_type_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__pair_type_sum ;
           toList__ := fun {a : Type} => Foldable__pair_type_toList |}.

(* Skipping instance `Data.Foldable.Foldable__Array' of class
   `Data.Foldable.Foldable' *)

#[local] Definition Foldable__Proxy_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Data.Proxy.Proxy m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => fun arg_0__ => GHC.Base.mempty.

#[local] Definition Foldable__Proxy_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Proxy.Proxy a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => GHC.Base.mempty.

#[local] Definition Foldable__Proxy_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, _ => z
      end.

#[local] Definition Foldable__Proxy_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Proxy_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__Proxy_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Proxy.Proxy a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Proxy_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Proxy_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, _ => z
      end.

#[local] Definition Foldable__Proxy_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Proxy_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__Proxy_length
   : forall {a : Type}, Data.Proxy.Proxy a -> GHC.Num.Int :=
  fun {a : Type} => fun arg_0__ => #0.

#[local] Definition Foldable__Proxy_null
   : forall {a : Type}, Data.Proxy.Proxy a -> bool :=
  fun {a : Type} => fun arg_0__ => true.

#[local] Definition Foldable__Proxy_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Data.Proxy.Proxy a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => fun arg_0__ => #1.

#[local] Definition Foldable__Proxy_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Data.Proxy.Proxy a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => fun arg_0__ => #0.

#[local] Definition Foldable__Proxy_toList
   : forall {a : Type}, Data.Proxy.Proxy a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Proxy_foldr c n t)).

#[global]
Program Instance Foldable__Proxy : Foldable Data.Proxy.Proxy :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Proxy_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Proxy_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Proxy_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__Proxy_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__Proxy_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__Proxy_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__Proxy_foldr' ;
           length__ := fun {a : Type} => Foldable__Proxy_length ;
           null__ := fun {a : Type} => Foldable__Proxy_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Proxy_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Proxy_sum ;
           toList__ := fun {a : Type} => Foldable__Proxy_toList |}.

#[local] Definition Foldable__Dual_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.SemigroupInternal.Dual a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

#[local] Definition Foldable__Dual_fold
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Data.SemigroupInternal.Dual m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Dual_foldMap GHC.Base.id.

#[local] Definition Foldable__Dual_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.SemigroupInternal.Dual a -> b :=
  fun {b : Type} {a : Type} => GHC.Prim.coerce.

#[local] Definition Foldable__Dual_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.SemigroupInternal.Dual a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Dual_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Dual_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.SemigroupInternal.Dual a -> b :=
  fun {b : Type} {a : Type} => GHC.Prim.coerce.

#[local] Definition Foldable__Dual_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.SemigroupInternal.Dual a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Data.SemigroupInternal.Mk_Dual x => f x z
      end.

#[local] Definition Foldable__Dual_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.SemigroupInternal.Dual a -> b :=
  fun {a : Type} {b : Type} => Foldable__Dual_foldr.

#[local] Definition Foldable__Dual_length
   : forall {a : Type}, Data.SemigroupInternal.Dual a -> GHC.Num.Int :=
  fun {a : Type} => fun arg_0__ => #1.

#[local] Definition Foldable__Dual_null
   : forall {a : Type}, Data.SemigroupInternal.Dual a -> bool :=
  fun {a : Type} => fun arg_0__ => false.

#[local] Definition Foldable__Dual_product
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.SemigroupInternal.Dual a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => Data.SemigroupInternal.getDual.

#[local] Definition Foldable__Dual_sum
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.SemigroupInternal.Dual a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => Data.SemigroupInternal.getDual.

#[local] Definition Foldable__Dual_toList
   : forall {a : Type}, Data.SemigroupInternal.Dual a -> list a :=
  fun {a : Type} => fun '(Data.SemigroupInternal.Mk_Dual x) => cons x nil.

#[global]
Program Instance Foldable__Dual : Foldable Data.SemigroupInternal.Dual :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Dual_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Dual_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Dual_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__Dual_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__Dual_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__Dual_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__Dual_foldr' ;
           length__ := fun {a : Type} => Foldable__Dual_length ;
           null__ := fun {a : Type} => Foldable__Dual_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Dual_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Dual_sum ;
           toList__ := fun {a : Type} => Foldable__Dual_toList |}.

#[local] Definition Foldable__Sum_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.SemigroupInternal.Sum a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

#[local] Definition Foldable__Sum_fold
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Data.SemigroupInternal.Sum m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Sum_foldMap GHC.Base.id.

#[local] Definition Foldable__Sum_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.SemigroupInternal.Sum a -> b :=
  fun {b : Type} {a : Type} => GHC.Prim.coerce.

#[local] Definition Foldable__Sum_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.SemigroupInternal.Sum a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Sum_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Sum_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.SemigroupInternal.Sum a -> b :=
  fun {b : Type} {a : Type} => GHC.Prim.coerce.

#[local] Definition Foldable__Sum_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.SemigroupInternal.Sum a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Data.SemigroupInternal.Mk_Sum x => f x z
      end.

#[local] Definition Foldable__Sum_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.SemigroupInternal.Sum a -> b :=
  fun {a : Type} {b : Type} => Foldable__Sum_foldr.

#[local] Definition Foldable__Sum_length
   : forall {a : Type}, Data.SemigroupInternal.Sum a -> GHC.Num.Int :=
  fun {a : Type} => fun arg_0__ => #1.

#[local] Definition Foldable__Sum_null
   : forall {a : Type}, Data.SemigroupInternal.Sum a -> bool :=
  fun {a : Type} => fun arg_0__ => false.

#[local] Definition Foldable__Sum_product
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.SemigroupInternal.Sum a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => Data.SemigroupInternal.getSum.

#[local] Definition Foldable__Sum_sum
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.SemigroupInternal.Sum a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => Data.SemigroupInternal.getSum.

#[local] Definition Foldable__Sum_toList
   : forall {a : Type}, Data.SemigroupInternal.Sum a -> list a :=
  fun {a : Type} => fun '(Data.SemigroupInternal.Mk_Sum x) => cons x nil.

#[global]
Program Instance Foldable__Sum : Foldable Data.SemigroupInternal.Sum :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Sum_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Sum_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Sum_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__Sum_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__Sum_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__Sum_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__Sum_foldr' ;
           length__ := fun {a : Type} => Foldable__Sum_length ;
           null__ := fun {a : Type} => Foldable__Sum_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Sum_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Sum_sum ;
           toList__ := fun {a : Type} => Foldable__Sum_toList |}.

#[local] Definition Foldable__Product_foldMap
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> Data.SemigroupInternal.Product a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

#[local] Definition Foldable__Product_fold
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Data.SemigroupInternal.Product m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Product_foldMap GHC.Base.id.

#[local] Definition Foldable__Product_foldl'
   : forall {b : Type},
     forall {a : Type},
     (b -> a -> b) -> b -> Data.SemigroupInternal.Product a -> b :=
  fun {b : Type} {a : Type} => GHC.Prim.coerce.

#[local] Definition Foldable__Product_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> Data.SemigroupInternal.Product a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Product_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Product_foldl
   : forall {b : Type},
     forall {a : Type},
     (b -> a -> b) -> b -> Data.SemigroupInternal.Product a -> b :=
  fun {b : Type} {a : Type} => GHC.Prim.coerce.

#[local] Definition Foldable__Product_foldr
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> b) -> b -> Data.SemigroupInternal.Product a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Data.SemigroupInternal.Mk_Product x => f x z
      end.

#[local] Definition Foldable__Product_foldr'
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> b) -> b -> Data.SemigroupInternal.Product a -> b :=
  fun {a : Type} {b : Type} => Foldable__Product_foldr.

#[local] Definition Foldable__Product_length
   : forall {a : Type}, Data.SemigroupInternal.Product a -> GHC.Num.Int :=
  fun {a : Type} => fun arg_0__ => #1.

#[local] Definition Foldable__Product_null
   : forall {a : Type}, Data.SemigroupInternal.Product a -> bool :=
  fun {a : Type} => fun arg_0__ => false.

#[local] Definition Foldable__Product_product
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.SemigroupInternal.Product a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => Data.SemigroupInternal.getProduct.

#[local] Definition Foldable__Product_sum
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.SemigroupInternal.Product a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => Data.SemigroupInternal.getProduct.

#[local] Definition Foldable__Product_toList
   : forall {a : Type}, Data.SemigroupInternal.Product a -> list a :=
  fun {a : Type} => fun '(Data.SemigroupInternal.Mk_Product x) => cons x nil.

#[global]
Program Instance Foldable__Product : Foldable Data.SemigroupInternal.Product :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Product_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Product_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Product_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__Product_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__Product_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__Product_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__Product_foldr' ;
           length__ := fun {a : Type} => Foldable__Product_length ;
           null__ := fun {a : Type} => Foldable__Product_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Product_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Product_sum ;
           toList__ := fun {a : Type} => Foldable__Product_toList |}.

(* Skipping instance `Data.Foldable.Foldable__First' of class
   `Data.Foldable.Foldable' *)

(* Skipping instance `Data.Foldable.Foldable__Last' of class
   `Data.Foldable.Foldable' *)

#[local] Definition Foldable__Alt_foldMap {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> Data.SemigroupInternal.Alt inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f => foldMap f GHC.Base.∘ Data.SemigroupInternal.getAlt.

#[local] Definition Foldable__Alt_fold {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Data.SemigroupInternal.Alt inst_f m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Alt_foldMap GHC.Base.id.

#[local] Definition Foldable__Alt_foldr {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> b) -> b -> Data.SemigroupInternal.Alt inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Alt_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Alt_foldl' {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {b : Type},
     forall {a : Type},
     (b -> a -> b) -> b -> Data.SemigroupInternal.Alt inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Alt_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__Alt_foldMap' {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> Data.SemigroupInternal.Alt inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Alt_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Alt_foldl {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {b : Type},
     forall {a : Type},
     (b -> a -> b) -> b -> Data.SemigroupInternal.Alt inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Alt_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Alt_foldr' {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> b) -> b -> Data.SemigroupInternal.Alt inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Alt_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__Alt_length {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type}, Data.SemigroupInternal.Alt inst_f a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Alt_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

#[local] Definition Foldable__Alt_null {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type}, Data.SemigroupInternal.Alt inst_f a -> bool :=
  fun {a : Type} => Foldable__Alt_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Alt_product {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.SemigroupInternal.Alt inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Alt_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Alt_sum {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type},
     forall `{GHC.Num.Num a}, Data.SemigroupInternal.Alt inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Alt_foldMap
                                Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Alt_toList {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type}, Data.SemigroupInternal.Alt inst_f a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Alt_foldr c n t)).

#[global]
Program Instance Foldable__Alt {f : Type -> Type} `{(Foldable f)}
   : Foldable (Data.SemigroupInternal.Alt f) :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Alt_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Alt_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Alt_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__Alt_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__Alt_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__Alt_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__Alt_foldr' ;
           length__ := fun {a : Type} => Foldable__Alt_length ;
           null__ := fun {a : Type} => Foldable__Alt_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Alt_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Alt_sum ;
           toList__ := fun {a : Type} => Foldable__Alt_toList |}.

#[local] Definition Foldable__Ap_foldMap {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Monoid.Ap inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f => foldMap f GHC.Base.∘ Data.Monoid.getAp.

#[local] Definition Foldable__Ap_fold {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Data.Monoid.Ap inst_f m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Ap_foldMap GHC.Base.id.

#[local] Definition Foldable__Ap_foldr {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.Monoid.Ap inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Ap_foldMap (Coq.Program.Basics.compose
                                                            Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Ap_foldl' {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.Monoid.Ap inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Ap_foldr f' GHC.Base.id xs z0.

#[local] Definition Foldable__Ap_foldMap' {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Monoid.Ap inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Ap_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Ap_foldl {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Data.Monoid.Ap inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Ap_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                             (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                              GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Ap_foldr' {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.Monoid.Ap inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Ap_foldl f' GHC.Base.id xs z0.

#[local] Definition Foldable__Ap_length {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type}, Data.Monoid.Ap inst_f a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Ap_foldl' (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | c, _ => c GHC.Num.+ #1
                           end) #0.

#[local] Definition Foldable__Ap_null {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type}, Data.Monoid.Ap inst_f a -> bool :=
  fun {a : Type} => Foldable__Ap_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Ap_product {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Data.Monoid.Ap inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Ap_foldMap Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Ap_sum {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Data.Monoid.Ap inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Ap_foldMap
                                Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Ap_toList {inst_f : Type -> Type} `{(Foldable
   inst_f)}
   : forall {a : Type}, Data.Monoid.Ap inst_f a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Ap_foldr c n t)).

#[global]
Program Instance Foldable__Ap {f : Type -> Type} `{(Foldable f)}
   : Foldable (Data.Monoid.Ap f) :=
  fun _ k__ =>
    k__ {| fold__ := fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Ap_fold ;
           foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Ap_foldMap ;
           foldMap'__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Ap_foldMap' ;
           foldl__ := fun {b : Type} {a : Type} => Foldable__Ap_foldl ;
           foldl'__ := fun {b : Type} {a : Type} => Foldable__Ap_foldl' ;
           foldr__ := fun {a : Type} {b : Type} => Foldable__Ap_foldr ;
           foldr'__ := fun {a : Type} {b : Type} => Foldable__Ap_foldr' ;
           length__ := fun {a : Type} => Foldable__Ap_length ;
           null__ := fun {a : Type} => Foldable__Ap_null ;
           product__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Ap_product ;
           sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Ap_sum ;
           toList__ := fun {a : Type} => Foldable__Ap_toList |}.

(* Skipping instance `Data.Foldable.Foldable__U1' of class
   `Data.Foldable.Foldable' *)

#[global] Definition foldrM {t : Type -> Type} {m : Type -> Type} {a : Type} {b
   : Type} `{Foldable t} `{GHC.Base.Monad m}
   : (a -> b -> m b) -> b -> t a -> m b :=
  fun f z0 xs =>
    let c := fun k x z => f x z GHC.Base.>>= k in foldl c GHC.Base.return_ xs z0.

#[global] Definition foldlM {t : Type -> Type} {m : Type -> Type} {b : Type} {a
   : Type} `{Foldable t} `{GHC.Base.Monad m}
   : (b -> a -> m b) -> b -> t a -> m b :=
  fun f z0 xs =>
    let c := fun x k z => f z x GHC.Base.>>= k in foldr c GHC.Base.return_ xs z0.

#[global] Definition traverse_ {t : Type -> Type} {f : Type -> Type} {a : Type}
  {b : Type} `{Foldable t} `{GHC.Base.Applicative f}
   : (a -> f b) -> t a -> f unit :=
  fun f => let c := fun x k => f x GHC.Base.*> k in foldr c (GHC.Base.pure tt).

#[global] Definition for__ {t : Type -> Type} {f : Type -> Type} {a : Type} {b
   : Type} `{Foldable t} `{GHC.Base.Applicative f}
   : t a -> (a -> f b) -> f unit :=
  GHC.Base.flip traverse_.

#[global] Definition mapM_ {t : Type -> Type} {m : Type -> Type} {a : Type} {b
   : Type} `{Foldable t} `{GHC.Base.Monad m}
   : (a -> m b) -> t a -> m unit :=
  fun f => let c := fun x k => f x GHC.Base.>> k in foldr c (GHC.Base.return_ tt).

#[global] Definition forM_ {t : Type -> Type} {m : Type -> Type} {a : Type} {b
   : Type} `{Foldable t} `{GHC.Base.Monad m}
   : t a -> (a -> m b) -> m unit :=
  GHC.Base.flip mapM_.

#[global] Definition sequenceA_ {t : Type -> Type} {f : Type -> Type} {a : Type}
  `{Foldable t} `{GHC.Base.Applicative f}
   : t (f a) -> f unit :=
  let c := fun m k => m GHC.Base.*> k in foldr c (GHC.Base.pure tt).

#[global] Definition sequence_ {t : Type -> Type} {m : Type -> Type} {a : Type}
  `{Foldable t} `{GHC.Base.Monad m}
   : t (m a) -> m unit :=
  let c := fun m k => m GHC.Base.>> k in foldr c (GHC.Base.return_ tt).

(* Skipping definition `Data.Foldable.asum' *)

(* Skipping definition `Data.Foldable.msum' *)

#[global] Definition concatMap {t : Type -> Type} {a : Type} {b : Type}
  `{Foldable t}
   : (a -> list b) -> t a -> list b :=
  fun f xs =>
    GHC.Base.build' (fun _ => (fun c n => foldr (fun x b => foldr c b (f x)) n xs)).

#[global] Definition concat {t : Type -> Type} {a : Type} `{Foldable t}
   : t (list a) -> list a :=
  fun xs =>
    GHC.Base.build' (fun _ =>
                       fun c n => foldr (fun x y => (@foldr _ Foldable__list _ _ c y x)) n xs).

#[global] Definition and {t : Type -> Type} `{Foldable t} : t bool -> bool :=
  Coq.Program.Basics.compose Data.SemigroupInternal.getAll (foldMap
                              Data.SemigroupInternal.Mk_All).

#[global] Definition or {t : Type -> Type} `{Foldable t} : t bool -> bool :=
  Coq.Program.Basics.compose Data.SemigroupInternal.getAny (foldMap
                              Data.SemigroupInternal.Mk_Any).

#[global] Definition any {t : Type -> Type} {a : Type} `{Foldable t}
   : (a -> bool) -> t a -> bool :=
  fun p =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getAny (foldMap
                                (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Any p)).

#[global] Definition all {t : Type -> Type} {a : Type} `{Foldable t}
   : (a -> bool) -> t a -> bool :=
  fun p =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getAll (foldMap
                                (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_All p)).

(* Skipping definition `Data.Foldable.maximumBy' *)

(* Skipping definition `Data.Foldable.minimumBy' *)

#[global] Definition elem {f} `{Foldable f} {a} `{GHC.Base.Eq_ a}
   : a -> f a -> bool :=
  fun x xs => any (fun y => x GHC.Base.== y) xs.

#[global] Definition notElem {t : Type -> Type} {a : Type} `{Foldable t}
  `{GHC.Base.Eq_ a}
   : a -> t a -> bool :=
  fun x => negb GHC.Base.∘ elem x.

#[global] Definition find {t : Type -> Type} {a : Type} `{Foldable t}
   : (a -> bool) -> t a -> option a :=
  fun p =>
    Data.Monoid.getFirst GHC.Base.∘
    foldMap (fun x => Data.Monoid.Mk_First (if p x : bool then Some x else None)).

(* External variables:
     None Some Type bool cons false list negb nil option pair true tt unit
     Coq.Program.Basics.compose Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Either.isLeft Data.Maybe.maybe Data.Monoid.Ap Data.Monoid.Mk_First
     Data.Monoid.getAp Data.Monoid.getFirst Data.Ord.Down Data.Ord.Mk_Down
     Data.Proxy.Proxy Data.SemigroupInternal.Alt Data.SemigroupInternal.Dual
     Data.SemigroupInternal.Mk_All Data.SemigroupInternal.Mk_Any
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.Product Data.SemigroupInternal.Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getAll
     Data.SemigroupInternal.getAlt Data.SemigroupInternal.getAny
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.NEcons GHC.Base.NonEmpty GHC.Base.build' GHC.Base.flip
     GHC.Base.foldl GHC.Base.foldl' GHC.Base.foldr GHC.Base.id GHC.Base.mappend
     GHC.Base.mempty GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.op_zlzlzgzg__ GHC.Base.op_ztzg__ GHC.Base.pure
     GHC.Base.return_ GHC.Generics.UAddr GHC.Generics.UChar GHC.Generics.UDouble
     GHC.Generics.UFloat GHC.Generics.UInt GHC.Generics.UWord GHC.List.length
     GHC.List.null GHC.List.product GHC.List.sum GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.coerce GHC.Tuple.pair_type
*)
