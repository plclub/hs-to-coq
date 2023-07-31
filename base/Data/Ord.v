(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Prim.
Require HsToCoq.Unpeel.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Down a : Type := | Mk_Down (getDown : a) : Down a.

Arguments Mk_Down {_} _.

Definition getDown {a} (arg_0__ : Down a) :=
  let 'Mk_Down getDown := arg_0__ in
  getDown.

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Ord.Read__Down' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Ord.Show__Down' *)

Local Definition Ord__Down_compare {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => GHC.Base.compare y x
    end.

Local Definition Ord__Down_op_zl__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base.== Lt.

Local Definition Ord__Down_op_zlze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base./= Gt.

Local Definition Ord__Down_op_zg__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base.== Gt.

Local Definition Ord__Down_op_zgze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base./= Lt.

Local Definition Ord__Down_max {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> Down inst_a :=
  fun x y => if Ord__Down_op_zlze__ x y : bool then y else x.

Local Definition Ord__Down_min {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> Down inst_a :=
  fun x y => if Ord__Down_op_zlze__ x y : bool then x else y.

Program Instance Ord__Down {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Down a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Down_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Down_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Down_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Down_op_zgze__ ;
           GHC.Base.compare__ := Ord__Down_compare ;
           GHC.Base.max__ := Ord__Down_max ;
           GHC.Base.min__ := Ord__Down_min |}.

Local Definition Functor__Down_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Down a -> Down b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Functor__Down_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Down b -> Down a :=
  fun {a : Type} {b : Type} => Functor__Down_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Down : GHC.Base.Functor Down :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Down_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Down_op_zlzd__ |}.

Local Definition Applicative__Down_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Down (a -> b) -> Down a -> Down b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Applicative__Down_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Down a -> Down b -> Down c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Down_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Down_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Down a -> Down b -> Down b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Down_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Down_pure : forall {a : Type}, a -> Down a :=
  fun {a : Type} => Mk_Down.

Program Instance Applicative__Down : GHC.Base.Applicative Down :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Down_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Down_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Down_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Down_pure |}.

Local Definition Monad__Down_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Down a -> (a -> Down b) -> Down b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Down a, k => k a end.

Local Definition Monad__Down_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Down a -> Down b -> Down b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Down_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Down_return_ : forall {a : Type}, a -> Down a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__Down : GHC.Base.Monad Down :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__Down_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} => Monad__Down_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__Down_return_ |}.

Definition comparing {a : Type} {b : Type} `{GHC.Base.Ord a}
   : (b -> a) -> b -> b -> comparison :=
  fun p x y => GHC.Base.compare (p x) (p y).

Instance Unpeel_Down a : HsToCoq.Unpeel.Unpeel (Down a) a :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun '(Mk_Down x) => x) Mk_Down.

(* External variables:
     Gt Lt Type bool comparison GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Ord GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____ GHC.Base.op_zl____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Base.return___ GHC.Prim.coerce HsToCoq.Unpeel.Build_Unpeel
     HsToCoq.Unpeel.Unpeel
*)
