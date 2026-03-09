(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require Data.Traversable.
Require GHC.Base.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom zipWith3M : forall {m : Type -> Type},
                  forall {a : Type},
                  forall {b : Type},
                  forall {c : Type},
                  forall {d : Type},
                  forall `{GHC.Base.Monad m},
                  (a -> b -> c -> m d) -> list a -> list b -> list c -> m (list d).

Axiom zipWith3M_ : forall {m : Type -> Type},
                   forall {a : Type},
                   forall {b : Type},
                   forall {c : Type},
                   forall {d : Type},
                   forall `{GHC.Base.Monad m},
                   (a -> b -> c -> m d) -> list a -> list b -> list c -> m unit.

Axiom zipWith4M : forall {m : Type -> Type},
                  forall {a : Type},
                  forall {b : Type},
                  forall {c : Type},
                  forall {d : Type},
                  forall {e : Type},
                  forall `{GHC.Base.Monad m},
                  (a -> b -> c -> d -> m e) -> list a -> list b -> list c -> list d -> m (list e).

Axiom zipWithAndUnzipM : forall {m : Type -> Type},
                         forall {a : Type},
                         forall {b : Type},
                         forall {c : Type},
                         forall {d : Type},
                         forall `{GHC.Base.Monad m},
                         (a -> b -> m (c * d)%type) -> list a -> list b -> m (list c * list d)%type.

Axiom zipWith3MNE : forall {m : Type -> Type},
                    forall {a : Type},
                    forall {b : Type},
                    forall {c : Type},
                    forall {d : Type},
                    forall `{GHC.Base.Monad m},
                    (a -> b -> c -> m d) ->
                    GHC.Base.NonEmpty a ->
                    GHC.Base.NonEmpty b -> GHC.Base.NonEmpty c -> m (GHC.Base.NonEmpty d).

Axiom mapAndUnzip3M : forall {m : Type -> Type},
                      forall {a : Type},
                      forall {b : Type},
                      forall {c : Type},
                      forall {d : Type},
                      forall `{GHC.Base.Monad m},
                      (a -> m (b * c * d)%type) -> list a -> m (list b * list c * list d)%type.

Axiom mapAndUnzip4M : forall {m : Type -> Type},
                      forall {a : Type},
                      forall {b : Type},
                      forall {c : Type},
                      forall {d : Type},
                      forall {e : Type},
                      forall `{GHC.Base.Monad m},
                      (a -> m (b * c * d * e)%type) ->
                      list a -> m (list b * list c * list d * list e)%type.

Axiom mapAndUnzip5M : forall {m : Type -> Type},
                      forall {a : Type},
                      forall {b : Type},
                      forall {c : Type},
                      forall {d : Type},
                      forall {e : Type},
                      forall {f : Type},
                      forall `{GHC.Base.Monad m},
                      (a -> m (b * c * d * e * f)%type) ->
                      list a -> m (list b * list c * list d * list e * list f)%type.

Axiom mapAccumLM : forall {m : Type -> Type},
                   forall {t : Type -> Type},
                   forall {acc : Type},
                   forall {x : Type},
                   forall {y : Type},
                   forall `{GHC.Base.Monad m},
                   forall `{Data.Traversable.Traversable t},
                   (acc -> x -> m (acc * y)%type) -> acc -> t x -> m (acc * t y)%type.

Axiom mapAccumLM_List : forall {m} {acc} {x} {y},
                        forall `{GHC.Base.Monad m},
                        (acc -> x -> m (acc * y)%type) -> acc -> list x -> m (acc * list y)%type.

Axiom mapAccumLM_NonEmpty : forall {m} {acc} {x} {y},
                            forall `{GHC.Base.Monad m},
                            (acc -> x -> m (acc * y)%type) ->
                            acc -> GHC.Base.NonEmpty x -> m (acc * GHC.Base.NonEmpty y)%type.

Axiom mapSndM : forall {m : Type -> Type},
                forall {f : Type -> Type},
                forall {b : Type},
                forall {c : Type},
                forall {a : Type},
                forall `{GHC.Base.Applicative m},
                forall `{Data.Traversable.Traversable f},
                (b -> m c) -> f (a * b)%type -> m (f (a * c)%type).

Axiom concatMapM : forall {m : Type -> Type},
                   forall {f : Type -> Type},
                   forall {a : Type},
                   forall {b : Type},
                   forall `{GHC.Base.Monad m},
                   forall `{Data.Traversable.Traversable f},
                   (a -> m (list b)) -> f a -> m (list b).

Axiom mapMaybeM : forall {m : Type -> Type},
                  forall {a : Type},
                  forall {b : Type},
                  forall `{GHC.Base.Applicative m}, (a -> m (option b)) -> list a -> m (list b).

Axiom anyM : forall {m : Type -> Type},
             forall {f : Type -> Type},
             forall {a : Type},
             forall `{GHC.Base.Monad m},
             forall `{Data.Foldable.Foldable f}, (a -> m bool) -> f a -> m bool.

Axiom allM : forall {m : Type -> Type},
             forall {f : Type -> Type},
             forall {a : Type},
             forall `{GHC.Base.Monad m},
             forall `{Data.Foldable.Foldable f}, (a -> m bool) -> f a -> m bool.

Axiom orM : forall {m : Type -> Type},
            forall `{GHC.Base.Monad m}, m bool -> m bool -> m bool.

Axiom andM : forall {m}, forall `{GHC.Base.Monad m}, m bool -> m bool -> m bool.

Axiom foldlM_ : forall {m : Type -> Type},
                forall {t : Type -> Type},
                forall {a : Type},
                forall {b : Type},
                forall `{GHC.Base.Monad m},
                forall `{Data.Foldable.Foldable t}, (a -> b -> m a) -> a -> t b -> m unit.

Axiom whenM : forall {m : Type -> Type},
              forall `{GHC.Base.Monad m}, m bool -> m unit -> m unit.

(* Skipping definition `MonadUtils.unlessM' *)

Axiom filterOutM : forall {m : Type -> Type},
                   forall {a : Type},
                   forall `{GHC.Base.Applicative m}, (a -> m bool) -> list a -> m (list a).

Axiom partitionM : forall {m : Type -> Type},
                   forall {a : Type},
                   forall `{GHC.Base.Monad m}, (a -> m bool) -> list a -> m (list a * list a)%type.

(* External variables:
     Type bool list op_zt__ option unit Data.Foldable.Foldable
     Data.Traversable.Traversable GHC.Base.Applicative GHC.Base.Monad
     GHC.Base.NonEmpty
*)
