Require Import Prelude.

(* An abstract datatype for a key/value store with build information of type @i@. *)
Record Store (I K V : Type) :=
  mkStore { info : I
          ; values : K -> V
          }.

(* Read the build information. *)
Definition getInfo {I K V : Type} (store : Store I K V) : I :=
  info _ _ _ store.

(* Read the value of a key. *)
Definition getValue {I K V : Type} (key : K) (store : Store I K V) : V :=
  values _ _ _ store key.

(* Read the value of a key. *)
Definition putValue {I K V : Type} (eqb : K -> K -> bool )
           (key : K) (value : V) (store : Store I K V) : Store I K V :=
  mkStore _ _ _ (info _ _ _ store)
                (fun k => if eqb k key then value else values _ _ _ store k).

