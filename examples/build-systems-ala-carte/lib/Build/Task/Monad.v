(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Build.Store.
Require Build.Task.
Require Data.Either.
Require Data.Maybe.
Require GHC.Base.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom trackPure : forall {k : Type},
                  forall {v : Type},
                  Build.Task.Task GHC.Base.Monad__Dict k v -> (k -> v) -> (v * list k)%type.

Axiom track : forall {m : Type -> Type},
              forall {k : Type},
              forall {v : Type},
              forall `{GHC.Base.Monad__Dict m},
              Build.Task.Task GHC.Base.Monad__Dict k v ->
              (k -> m v) -> m (v * list (k * v)%type)%type.

Definition isInput {k : Type} {v : Type}
   : Build.Task.Tasks GHC.Base.Monad__Dict k v -> k -> bool :=
  fun tasks => Data.Maybe.isNothing GHC.Base.∘ tasks.

Axiom computePure : forall {k : Type},
                    forall {v : Type}, Build.Task.Task GHC.Base.Monad__Dict k v -> (k -> v) -> v.

Axiom compute : forall {k : Type},
                forall {v : Type},
                forall {i : Type},
                Build.Task.Task GHC.Base.Monad__Dict k v -> Build.Store.Store i k v -> v.

Axiom liftMaybe : forall {k : Type},
                  forall {v : Type},
                  Build.Task.Task GHC.Base.Monad__Dict k v ->
                  Build.Task.Task GHC.Base.Monad__Dict k (option v).

Axiom liftEither : forall {k : Type},
                   forall {v : Type},
                   forall {e : Type},
                   Build.Task.Task GHC.Base.Monad__Dict k v ->
                   Build.Task.Task GHC.Base.Monad__Dict k (Data.Either.Either e v).

(* External variables:
     Type bool list op_zt__ option Build.Store.Store Build.Task.Task Build.Task.Tasks
     Data.Either.Either Data.Maybe.isNothing GHC.Base.Monad__Dict
     GHC.Base.op_z2218U__
*)
