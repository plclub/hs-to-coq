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
Require HsToCoq.Unpeel.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Last a : Type := | Mk_Last (getLast : option a) : Last a.

Inductive First a : Type := | Mk_First (getFirst : option a) : First a.

Inductive Ap (f : Type -> Type) (a : Type) : Type :=
  | Mk_Ap (getAp : f a) : Ap f a.

Arguments Mk_Last {_} _.

Arguments Mk_First {_} _.

Arguments Mk_Ap {_} {_} _.

#[global] Definition getLast {a} (arg_0__ : Last a) :=
  let 'Mk_Last getLast := arg_0__ in
  getLast.

#[global] Definition getFirst {a} (arg_0__ : First a) :=
  let 'Mk_First getFirst := arg_0__ in
  getFirst.

#[global] Definition getAp {f : Type -> Type} {a : Type} (arg_0__ : Ap f a) :=
  let 'Mk_Ap getAp := arg_0__ in
  getAp.

(* Converted value declarations: *)

#[local] Definition Semigroup__First_op_zlzlzgzg__ {inst_a : Type}
   : First inst_a -> First inst_a -> First inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_First None, b => b
    | a, _ => a
    end.

#[global]
Program Instance Semigroup__First {a : Type} : GHC.Base.Semigroup (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__First_op_zlzlzgzg__ |}.

#[local] Definition Monoid__First_mappend {inst_a : Type}
   : First inst_a -> First inst_a -> First inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__First_mempty {inst_a : Type} : First inst_a :=
  Mk_First None.

#[local] Definition Monoid__First_mconcat {inst_a : Type}
   : list (First inst_a) -> First inst_a :=
  GHC.Base.foldr Monoid__First_mappend Monoid__First_mempty.

#[global]
Program Instance Monoid__First {a : Type} : GHC.Base.Monoid (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__First_mappend ;
           GHC.Base.mconcat__ := Monoid__First_mconcat ;
           GHC.Base.mempty__ := Monoid__First_mempty |}.

#[local] Definition Semigroup__Last_op_zlzlzgzg__ {inst_a : Type}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_Last None => a
    | _, b => b
    end.

#[global]
Program Instance Semigroup__Last {a : Type} : GHC.Base.Semigroup (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Last_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Last_mappend {inst_a : Type}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Last_mempty {inst_a : Type} : Last inst_a :=
  Mk_Last None.

#[local] Definition Monoid__Last_mconcat {inst_a : Type}
   : list (Last inst_a) -> Last inst_a :=
  GHC.Base.foldr Monoid__Last_mappend Monoid__Last_mempty.

#[global]
Program Instance Monoid__Last {a : Type} : GHC.Base.Monoid (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Last_mappend ;
           GHC.Base.mconcat__ := Monoid__Last_mconcat ;
           GHC.Base.mempty__ := Monoid__Last_mempty |}.

#[local] Definition Semigroup__Ap_op_zlzlzgzg__ {inst_f : Type -> Type} {inst_a
   : Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Semigroup inst_a}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> Ap inst_f inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Ap x, Mk_Ap y => Mk_Ap (GHC.Base.liftA2 _GHC.Base.<<>>_ x y)
    end.

#[global]
Program Instance Semigroup__Ap {f : Type -> Type} {a : Type}
  `{GHC.Base.Applicative f} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Ap f a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Ap_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Ap_mappend {inst_f : Type -> Type} {inst_a : Type}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monoid inst_a}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> Ap inst_f inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Ap_mempty {inst_f : Type -> Type} {inst_a : Type}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monoid inst_a}
   : Ap inst_f inst_a :=
  Mk_Ap (GHC.Base.pure GHC.Base.mempty).

#[local] Definition Monoid__Ap_mconcat {inst_f : Type -> Type} {inst_a : Type}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monoid inst_a}
   : list (Ap inst_f inst_a) -> Ap inst_f inst_a :=
  GHC.Base.foldr Monoid__Ap_mappend Monoid__Ap_mempty.

#[global]
Program Instance Monoid__Ap {f : Type -> Type} {a : Type} `{GHC.Base.Applicative
  f} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Ap f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Ap_mappend ;
           GHC.Base.mconcat__ := Monoid__Ap_mconcat ;
           GHC.Base.mempty__ := Monoid__Ap_mempty |}.

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Monoid.Bounded__Ap' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.Monoid.Num__Ap' *)

Instance Unpeel_Last a : HsToCoq.Unpeel.Unpeel (Last a) (option a) :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getLast Mk_Last.

Instance Unpeel_First a : HsToCoq.Unpeel.Unpeel (First a) (option a) :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getFirst Mk_First.

(* External variables:
     None Type list option GHC.Base.Applicative GHC.Base.Monoid GHC.Base.Semigroup
     GHC.Base.foldr GHC.Base.liftA2 GHC.Base.mappend__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Base.pure HsToCoq.Unpeel.Build_Unpeel
     HsToCoq.Unpeel.Unpeel
*)
