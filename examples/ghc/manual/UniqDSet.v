(* Stub module for UniqDSet — deterministic UniqSet *)
(* In our translation, DVarSet = VarSet = UniqSet, so we just delegate *)

Require UniqSet.
Require Unique.

Definition nonDetStrictFoldUniqDSet {a : Type} {b : Type} `{Unique.Uniquable a}
   : (a -> b -> b) -> b -> UniqSet.UniqSet a -> b :=
  UniqSet.nonDetStrictFoldUniqSet.

Definition mapUniqDSet {b : Type} {a : Type} `{Unique.Uniquable b}
   : (a -> b) -> UniqSet.UniqSet a -> UniqSet.UniqSet b :=
  UniqSet.mapUniqSet.
