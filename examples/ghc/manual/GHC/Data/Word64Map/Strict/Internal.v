(* Stub: GHC.Data.Word64Map.Strict.Internal aliases to Data.IntMap.Internal
   for the Coq translation. Strict maps behave the same as lazy ones in Coq. *)

Require Export Data.IntMap.Internal.

Definition map {a b} := @Data.IntMap.Internal.map a b.
Definition mergeWithKey {a b c} := @Data.IntMap.Internal.mergeWithKey a b c.
