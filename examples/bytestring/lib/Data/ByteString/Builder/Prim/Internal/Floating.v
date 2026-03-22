(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.ByteString.Builder.Prim.Internal.
Require GHC.Base.
Require GHC.Err.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition encodeFloatViaWord32F
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word32 ->
     Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Float :=
  fun w32fe =>
    if Data.ByteString.Builder.Prim.Internal.size w32fe GHC.Base.<
       Foreign.Storable.sizeOf (GHC.Err.undefined : GHC.Types.Float) : bool
    then GHC.Err.error (GHC.Base.hs_string__
                        "encodeFloatViaWord32F: encoding not wide enough") else
    Data.ByteString.Builder.Prim.Internal.fixedPrim
    (Data.ByteString.Builder.Prim.Internal.size w32fe) (fun x op =>
                                                          Foreign.Storable.poke (GHC.Ptr.castPtr op) x GHC.Base.>>
                                                          (Foreign.Storable.peek (GHC.Ptr.castPtr op) GHC.Base.>>=
                                                           (fun x' =>
                                                              Data.ByteString.Builder.Prim.Internal.runF w32fe x' op))).

Definition encodeDoubleViaWord64F
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word64 ->
     Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Double :=
  fun w64fe =>
    if Data.ByteString.Builder.Prim.Internal.size w64fe GHC.Base.<
       Foreign.Storable.sizeOf (GHC.Err.undefined : GHC.Types.Float) : bool
    then GHC.Err.error (GHC.Base.hs_string__
                        "encodeDoubleViaWord64F: encoding not wide enough") else
    Data.ByteString.Builder.Prim.Internal.fixedPrim
    (Data.ByteString.Builder.Prim.Internal.size w64fe) (fun x op =>
                                                          Foreign.Storable.poke (GHC.Ptr.castPtr op) x GHC.Base.>>
                                                          (Foreign.Storable.peek (GHC.Ptr.castPtr op) GHC.Base.>>=
                                                           (fun x' =>
                                                              Data.ByteString.Builder.Prim.Internal.runF w64fe x' op))).

(* External variables:
     bool Data.ByteString.Builder.Prim.Internal.FixedPrim
     Data.ByteString.Builder.Prim.Internal.fixedPrim
     Data.ByteString.Builder.Prim.Internal.runF
     Data.ByteString.Builder.Prim.Internal.size Foreign.Storable.peek
     Foreign.Storable.poke Foreign.Storable.sizeOf GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Err.error GHC.Err.undefined
     GHC.Ptr.castPtr GHC.Types.Double GHC.Types.Float GHC.Word.Word32 GHC.Word.Word64
*)
