(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require GHC.Base.
Require GHC.Prim.
Import GHC.Base.Notations.
Import GHC.Prim.Notations.

(* Converted type declarations: *)

Record Category__Dict {k : Type} (cat : k -> k -> Type) :=
  Category__Dict_Build {
  id__ : forall {a : k}, cat a a ;
  op_z2218U____ : forall {b : k},
  forall {c : k}, forall {a : k}, cat b c -> cat a b -> cat a c }.

Definition Category {k : Type} (cat : k -> k -> Type) :=
  forall r__, (Category__Dict cat -> r__) -> r__.
Existing Class Category.

Definition id `{g__0__ : Category k cat} : forall {a : k}, cat a a :=
  g__0__ _ (id__ cat).

Definition op_z2218U__ `{g__0__ : Category k cat}
   : forall {b : k},
     forall {c : k}, forall {a : k}, cat b c -> cat a b -> cat a c :=
  g__0__ _ (op_z2218U____ cat).

Notation "'_∘_'" := (op_z2218U__).

Infix "∘" := (_∘_) (left associativity, at level 40).

(* Converted value declarations: *)

Local Definition Category__op_zmzg___id
   : forall {a : Type}, _GHC.Prim.->_ a a :=
  fun {a : Type} => GHC.Base.id.

Local Definition Category__op_zmzg___op_z2218U__
   : forall {b : Type},
     forall {c : Type},
     forall {a : Type},
     _GHC.Prim.->_ b c -> _GHC.Prim.->_ a b -> _GHC.Prim.->_ a c :=
  fun {b : Type} {c : Type} {a : Type} => _GHC.Base.∘_.

Program Instance Category__op_zmzg__ : Category _GHC.Prim.->_ :=
  fun _ k__ =>
    k__ {| id__ := fun {a : Type} => Category__op_zmzg___id ;
           op_z2218U____ := fun {b : Type} {c : Type} {a : Type} =>
             Category__op_zmzg___op_z2218U__ |}.

(* Skipping instance `Control.Category.Category__op_ZCz7eUZC__' of class
   `Control.Category.Category' *)

(* Skipping instance `Control.Category.Category__op_ZCz7eUz7eUZC__' of class
   `Control.Category.Category' *)

(* Skipping instance `Control.Category.Category__Coercion' of class
   `Control.Category.Category' *)

Definition op_zlzlzl__ {k : Type} {cat : k -> k -> Type} {b : k} {c : k} {a : k}
  `{Category k cat}
   : cat b c -> cat a b -> cat a c :=
  _∘_.

Notation "'_<<<_'" := (op_zlzlzl__).

Infix "<<<" := (_<<<_) (at level 99).

Definition op_zgzgzg__ {k : Type} {cat : k -> k -> Type} {a : k} {b : k} {c : k}
  `{Category k cat}
   : cat a b -> cat b c -> cat a c :=
  fun f g => g ∘ f.

Notation "'_>>>_'" := (op_zgzgzg__).

Infix ">>>" := (_>>>_) (at level 99).

Module Notations.
Notation "'_Control.Category.∘_'" := (op_z2218U__).
Infix "Control.Category.∘" := (_∘_) (left associativity, at level 40).
Notation "'_Control.Category.<<<_'" := (op_zlzlzl__).
Infix "Control.Category.<<<" := (_<<<_) (at level 99).
Notation "'_Control.Category.>>>_'" := (op_zgzgzg__).
Infix "Control.Category.>>>" := (_>>>_) (at level 99).
End Notations.

(* External variables:
     Type GHC.Base.id GHC.Base.op_z2218U__ GHC.Prim.op_zmzg__
*)
