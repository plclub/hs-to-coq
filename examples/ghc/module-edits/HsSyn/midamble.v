Require FastString.

(* FieldLabelString is a newtype around FastString in GHC 9.10 *)
Definition FieldLabelString : Type := FastString.FastString.
