(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.ByteString.Builder.Internal.
Require Data.ByteString.Lazy.Internal.
Require GHC.Base.
Require GHC.Char.

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.ByteString.Builder.Show__Builder' *)

Axiom toLazyByteString : Data.ByteString.Builder.Internal.Builder ->
                         Data.ByteString.Lazy.Internal.ByteString.

Axiom hPutBuilder : GHC.IO.Handle.Types.Handle ->
                    Data.ByteString.Builder.Internal.Builder -> GHC.Types.IO unit.

Axiom modifyFile : GHC.IO.IOMode.IOMode ->
                   GHC.Base.String ->
                   Data.ByteString.Builder.Internal.Builder -> GHC.Types.IO unit.

Axiom writeFile : GHC.Base.String ->
                  Data.ByteString.Builder.Internal.Builder -> GHC.Types.IO unit.

Axiom int8 : GHC.Int.Int8 -> Data.ByteString.Builder.Internal.Builder.

Axiom word8 : GHC.Word.Word8 -> Data.ByteString.Builder.Internal.Builder.

Axiom int16LE : GHC.Int.Int16 -> Data.ByteString.Builder.Internal.Builder.

Axiom int32LE : GHC.Int.Int32 -> Data.ByteString.Builder.Internal.Builder.

Axiom int64LE : GHC.Int.Int64 -> Data.ByteString.Builder.Internal.Builder.

Axiom word16LE : GHC.Word.Word16 -> Data.ByteString.Builder.Internal.Builder.

Axiom word32LE : GHC.Word.Word32 -> Data.ByteString.Builder.Internal.Builder.

Axiom word64LE : GHC.Word.Word64 -> Data.ByteString.Builder.Internal.Builder.

Axiom floatLE : GHC.Types.Float -> Data.ByteString.Builder.Internal.Builder.

Axiom doubleLE : GHC.Types.Double -> Data.ByteString.Builder.Internal.Builder.

Axiom int16BE : GHC.Int.Int16 -> Data.ByteString.Builder.Internal.Builder.

Axiom int32BE : GHC.Int.Int32 -> Data.ByteString.Builder.Internal.Builder.

Axiom int64BE : GHC.Int.Int64 -> Data.ByteString.Builder.Internal.Builder.

Axiom word16BE : GHC.Word.Word16 -> Data.ByteString.Builder.Internal.Builder.

Axiom word32BE : GHC.Word.Word32 -> Data.ByteString.Builder.Internal.Builder.

Axiom word64BE : GHC.Word.Word64 -> Data.ByteString.Builder.Internal.Builder.

Axiom floatBE : GHC.Types.Float -> Data.ByteString.Builder.Internal.Builder.

Axiom doubleBE : GHC.Types.Double -> Data.ByteString.Builder.Internal.Builder.

Axiom char7 : GHC.Char.Char -> Data.ByteString.Builder.Internal.Builder.

Axiom string7 : GHC.Base.String -> Data.ByteString.Builder.Internal.Builder.

Axiom char8 : GHC.Char.Char -> Data.ByteString.Builder.Internal.Builder.

Axiom string8 : GHC.Base.String -> Data.ByteString.Builder.Internal.Builder.

Axiom charUtf8 : GHC.Char.Char -> Data.ByteString.Builder.Internal.Builder.

Axiom stringUtf8 : GHC.Base.String -> Data.ByteString.Builder.Internal.Builder.

(* External variables:
     unit Data.ByteString.Builder.Internal.Builder
     Data.ByteString.Lazy.Internal.ByteString GHC.Base.String GHC.Char.Char
     GHC.IO.Handle.Types.Handle GHC.IO.IOMode.IOMode GHC.Int.Int16 GHC.Int.Int32
     GHC.Int.Int64 GHC.Int.Int8 GHC.Types.Double GHC.Types.Float GHC.Types.IO
     GHC.Word.Word16 GHC.Word.Word32 GHC.Word.Word64 GHC.Word.Word8
*)
