(* Stub module for UniqDFM — deterministic UniqFM *)
(* In our translation, DVarEnv = VarEnv = UniqFM, so we just delegate *)

Require UniqFM.
Require Unique.

Definition nonDetStrictFoldUDFM {key : Type} {elt : Type} {a : Type}
   : (elt -> a -> a) -> a -> UniqFM.UniqFM key elt -> a :=
  UniqFM.nonDetStrictFoldUFM.

Definition adjustUDFM {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (elt -> elt) -> UniqFM.UniqFM key elt -> key -> UniqFM.UniqFM key elt :=
  UniqFM.adjustUFM.
