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
Require GHC.Num.
Require GHC.Prim.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Store i k v : Type :=
  | Mk_Store (info : i) (values : k -> v) : Store i k v.

Inductive Hash a : Type := | Mk_Hash : a -> Hash a.

Record Hashable__Dict (a : Type) := Hashable__Dict_Build {
  hash__ : a -> Hash a }.

Definition Hashable (a : Type) `{GHC.Base.Ord a} :=
  forall r__, (Hashable__Dict a -> r__) -> r__.
Existing Class Hashable.

Definition hash `{g__0__ : Hashable a} : a -> Hash a :=
  g__0__ _ (hash__ a).

Arguments Mk_Store {_} {_} {_} _ _.

Arguments Mk_Hash {_} _.

Definition info {i} {k} {v} (arg_0__ : Store i k v) :=
  let 'Mk_Store info _ := arg_0__ in
  info.

Definition values {i} {k} {v} (arg_0__ : Store i k v) :=
  let 'Mk_Store _ values := arg_0__ in
  values.

(* Converted value declarations: *)

Local Definition Eq___Hash_op_zeze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Hash inst_a -> Hash inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Hash_op_zsze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Hash inst_a -> Hash inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Hash {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Hash a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Hash_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Hash_op_zsze__ |}.

Local Definition Ord__Hash_op_zl__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Hash inst_a -> Hash inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Hash_op_zlze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Hash inst_a -> Hash inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Hash_op_zg__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Hash inst_a -> Hash inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Hash_op_zgze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Hash inst_a -> Hash inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Hash_compare {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Hash inst_a -> Hash inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Hash_max {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Hash inst_a -> Hash inst_a -> Hash inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Hash_min {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Hash inst_a -> Hash inst_a -> Hash inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Hash {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Hash a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Hash_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Hash_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Hash_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Hash_op_zgze__ ;
           GHC.Base.compare__ := Ord__Hash_compare ;
           GHC.Base.max__ := Ord__Hash_max ;
           GHC.Base.min__ := Ord__Hash_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Build.Store.Show__Hash' *)

Local Definition Functor__Hash_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Hash a -> Hash b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Hash a => Mk_Hash (f a)
      end.

Local Definition Functor__Hash_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Hash b -> Hash a :=
  fun {a : Type} {b : Type} => Functor__Hash_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Hash : GHC.Base.Functor Hash :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Hash_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Hash_op_zlzd__ |}.

Local Definition Applicative__Hash_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Hash (a -> b) -> Hash a -> Hash b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Hash f, Mk_Hash a => Mk_Hash (f a)
      end.

Local Definition Applicative__Hash_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Hash a -> Hash b -> Hash c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Hash_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Hash_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Hash a -> Hash b -> Hash b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Hash_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Hash_pure : forall {a : Type}, a -> Hash a :=
  fun {a : Type} => Mk_Hash.

Program Instance Applicative__Hash : GHC.Base.Applicative Hash :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Hash_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Hash_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Hash_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Hash_pure |}.

Local Definition Hashable__Int_hash : GHC.Num.Int -> Hash GHC.Num.Int :=
  Mk_Hash.

Program Instance Hashable__Int : Hashable GHC.Num.Int :=
  fun _ k__ => k__ {| hash__ := Hashable__Int_hash |}.

Local Definition Hashable__Integer_hash
   : GHC.Integer.Type.Integer -> Hash GHC.Integer.Type.Integer :=
  Mk_Hash.

Program Instance Hashable__Integer : Hashable GHC.Integer.Type.Integer :=
  fun _ k__ => k__ {| hash__ := Hashable__Integer_hash |}.

Local Definition Hashable__list_hash {inst_a : Type} `{Hashable inst_a}
   : list inst_a -> Hash (list inst_a) :=
  Mk_Hash.

Program Instance Hashable__list {a : Type} `{Hashable a} : Hashable (list a) :=
  fun _ k__ => k__ {| hash__ := Hashable__list_hash |}.

Local Definition Hashable__Hash_hash {inst_a : Type} `{Hashable inst_a}
   : Hash inst_a -> Hash (Hash inst_a) :=
  Mk_Hash.

Program Instance Hashable__Hash {a : Type} `{Hashable a} : Hashable (Hash a) :=
  fun _ k__ => k__ {| hash__ := Hashable__Hash_hash |}.

Local Definition Hashable__op_zt___hash {inst_a : Type} {inst_b : Type}
  `{Hashable inst_a} `{Hashable inst_b}
   : (inst_a * inst_b)%type -> Hash (inst_a * inst_b)%type :=
  Mk_Hash.

Program Instance Hashable__op_zt__ {a : Type} {b : Type} `{Hashable a}
  `{Hashable b}
   : Hashable (a * b)%type :=
  fun _ k__ => k__ {| hash__ := Hashable__op_zt___hash |}.

Definition getInfo {i : Type} {k : Type} {v : Type} : Store i k v -> i :=
  info.

Definition getValue {k : Type} {i : Type} {v : Type} : k -> Store i k v -> v :=
  GHC.Base.flip values.

Definition getHash {v : Type} {k : Type} {i : Type} `{Hashable v}
   : k -> Store i k v -> Hash v :=
  fun k => hash GHC.Base.∘ getValue k.

Definition putInfo {i : Type} {k : Type} {v : Type}
   : i -> Store i k v -> Store i k v :=
  fun i s => let 'Mk_Store info_0__ values_1__ := s in Mk_Store i values_1__.

Definition mapInfo {i : Type} {j : Type} {k : Type} {v : Type}
   : (i -> j) -> Store i k v -> Store j k v :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_Store i kv => Mk_Store (f i) kv
    end.

Definition putValue {k : Type} {v : Type} {i : Type} `{GHC.Base.Eq_ k}
   : k -> v -> Store i k v -> Store i k v :=
  fun k v s =>
    let 'Mk_Store info_0__ values_1__ := s in
    Mk_Store info_0__ (fun key =>
                if key GHC.Base.== k : bool
                then v
                else values s key).

Definition initialise {i : Type} {k : Type} {v : Type}
   : i -> (k -> v) -> Store i k v :=
  Mk_Store.

(* External variables:
     Type bool comparison list op_zt__ GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Ord GHC.Base.compare GHC.Base.compare__ GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__
     GHC.Base.max GHC.Base.max__ GHC.Base.min GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure__ GHC.Integer.Type.Integer GHC.Num.Int
     GHC.Prim.coerce
*)
