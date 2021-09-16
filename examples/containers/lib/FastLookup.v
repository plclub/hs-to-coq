(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.IntMap.Internal.
Require Data.IntSet.Internal.
Require GHC.Base.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition fastLookup {a : Type}
   : Data.IntSet.Internal.Key -> Data.IntMap.Internal.IntMap a -> option a :=
  fun k =>
    let fix go arg_0__
      := match arg_0__ with
         | Data.IntMap.Internal.Bin _p m l r =>
             if Data.IntSet.Internal.zero k m : bool then go l else
             go r
         | Data.IntMap.Internal.Tip kx x =>
             if k GHC.Base.== kx : bool then Some x else
             None
         | Data.IntMap.Internal.Nil => None
         end in
    go.

(* External variables:
     None Some Type bool option Data.IntMap.Internal.Bin Data.IntMap.Internal.IntMap
     Data.IntMap.Internal.Nil Data.IntMap.Internal.Tip Data.IntSet.Internal.Key
     Data.IntSet.Internal.zero GHC.Base.op_zeze__
*)
