(* Stub: GHC.Data.Word64Set.Internal is equivalent to Data.IntSet.Internal
   in the Coq translation, since Word64 is mapped to N (same as Word/Key). *)

Require Export Data.IntSet.Internal.

Definition Word64Set := IntSet.

(* Re-export IntSet functions so qualified GHC.Data.Word64Set.Internal.X works *)
Definition empty := Data.IntSet.Internal.empty.
Definition member := Data.IntSet.Internal.member.
Definition null := Data.IntSet.Internal.null.
Definition delete := Data.IntSet.Internal.delete.
Definition difference := Data.IntSet.Internal.difference.
Definition fromList := Data.IntSet.Internal.fromList.
Definition size := Data.IntSet.Internal.size.
Definition insert := Data.IntSet.Internal.insert.
Definition union := Data.IntSet.Internal.union.
