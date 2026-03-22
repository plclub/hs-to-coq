(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Char.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Import GHC.Prim.Notations.

(* Converted type declarations: *)

Inductive ByteString : Type :=
  | BS : (GHC.ForeignPtr.ForeignPtr GHC.Word.Word8) -> GHC.Num.Int -> ByteString.

Definition StrictByteString :=
  ByteString%type.

(* Converted value declarations: *)

Instance Eq___ByteString : GHC.Base.Eq_ ByteString.
Proof.
Admitted.

Instance Ord__ByteString : GHC.Base.Ord ByteString.
Proof.
Admitted.

Instance Semigroup__ByteString : GHC.Base.Semigroup ByteString.
Proof.
Admitted.

Instance Monoid__ByteString : GHC.Base.Monoid ByteString.
Proof.
Admitted.

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Data.ByteString.Internal.NFData__ByteString' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.ByteString.Internal.Show__ByteString' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.ByteString.Internal.Read__ByteString' *)

(* Skipping all instances of class `GHC.Exts.IsList', including
   `Data.ByteString.Internal.IsList__ByteString' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.ByteString.Internal.Data__ByteString' *)

Axiom unsafeWithForeignPtr : forall {a : Type},
                             forall {b : Type},
                             GHC.ForeignPtr.ForeignPtr a ->
                             (GHC.Ptr.Ptr a -> GHC.Types.IO b) -> GHC.Types.IO b.

Axiom findIndexOrLength : (GHC.Word.Word8 -> bool) -> ByteString -> GHC.Num.Int.

Axiom packBytes : list GHC.Word.Word8 -> ByteString.

Axiom packChars : list GHC.Char.Char -> ByteString.

Axiom unsafePackLenBytes : GHC.Num.Int -> list GHC.Word.Word8 -> ByteString.

Axiom unsafePackLenChars : GHC.Num.Int -> list GHC.Char.Char -> ByteString.

Axiom unsafePackAddress : _GHC.Prim.Addr#_ -> GHC.Types.IO ByteString.

Axiom unsafePackLenAddress : GHC.Num.Int ->
                             _GHC.Prim.Addr#_ -> GHC.Types.IO ByteString.

Axiom unsafePackLiteral : _GHC.Prim.Addr#_ -> ByteString.

Axiom unsafePackLenLiteral : GHC.Num.Int -> _GHC.Prim.Addr#_ -> ByteString.

Axiom packUptoLenBytes : GHC.Num.Int ->
                         list GHC.Word.Word8 -> (ByteString * list GHC.Word.Word8)%type.

Axiom packUptoLenChars : GHC.Num.Int ->
                         list GHC.Char.Char -> (ByteString * list GHC.Char.Char)%type.

Axiom unpackBytes : ByteString -> list GHC.Word.Word8.

Axiom unpackChars : ByteString -> list GHC.Char.Char.

Axiom unpackAppendBytesLazy : ByteString ->
                              list GHC.Word.Word8 -> list GHC.Word.Word8.

Axiom unpackAppendCharsLazy : ByteString ->
                              list GHC.Char.Char -> list GHC.Char.Char.

Axiom unpackAppendBytesStrict : ByteString ->
                                list GHC.Word.Word8 -> list GHC.Word.Word8.

Axiom unpackAppendCharsStrict : ByteString ->
                                list GHC.Char.Char -> list GHC.Char.Char.

Axiom nullForeignPtr : GHC.ForeignPtr.ForeignPtr GHC.Word.Word8.

Axiom fromForeignPtr : GHC.ForeignPtr.ForeignPtr GHC.Word.Word8 ->
                       GHC.Num.Int -> GHC.Num.Int -> ByteString.

Axiom fromForeignPtr0 : GHC.ForeignPtr.ForeignPtr GHC.Word.Word8 ->
                        GHC.Num.Int -> ByteString.

Axiom toForeignPtr : ByteString ->
                     (GHC.ForeignPtr.ForeignPtr GHC.Word.Word8 * GHC.Num.Int * GHC.Num.Int)%type.

Axiom toForeignPtr0 : ByteString ->
                      (GHC.ForeignPtr.ForeignPtr GHC.Word.Word8 * GHC.Num.Int)%type.

Axiom unsafeCreate : GHC.Num.Int ->
                     (GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO unit) -> ByteString.

Axiom unsafeCreateUptoN : GHC.Num.Int ->
                          (GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO GHC.Num.Int) -> ByteString.

Axiom unsafeCreateUptoN' : forall {a : Type},
                           GHC.Num.Int ->
                           (GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO (GHC.Num.Int * a)%type) ->
                           (ByteString * a)%type.

Axiom create : GHC.Num.Int ->
               (GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO unit) -> GHC.Types.IO ByteString.

Axiom createUptoN : GHC.Num.Int ->
                    (GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO GHC.Num.Int) ->
                    GHC.Types.IO ByteString.

Axiom createUptoN' : forall {a : Type},
                     GHC.Num.Int ->
                     (GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO (GHC.Num.Int * a)%type) ->
                     GHC.Types.IO (ByteString * a)%type.

Axiom createAndTrim : GHC.Num.Int ->
                      (GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO GHC.Num.Int) ->
                      GHC.Types.IO ByteString.

Axiom createAndTrim' : forall {a : Type},
                       GHC.Num.Int ->
                       (GHC.Ptr.Ptr GHC.Word.Word8 ->
                        GHC.Types.IO (GHC.Num.Int * GHC.Num.Int * a)%type) ->
                       GHC.Types.IO (ByteString * a)%type.

Axiom mallocByteString : forall {a : Type},
                         GHC.Num.Int -> GHC.Types.IO (GHC.ForeignPtr.ForeignPtr a).

Axiom eq : ByteString -> ByteString -> bool.

Axiom compareBytes : ByteString -> ByteString -> comparison.

Axiom append : ByteString -> ByteString -> ByteString.

Axiom concat : list ByteString -> ByteString.

Axiom times : forall {a},
              forall `{GHC.Real.Integral a}, a -> ByteString -> ByteString.

Axiom checkedAdd : GHC.Base.String -> GHC.Num.Int -> GHC.Num.Int -> GHC.Num.Int.

Axiom w2c : GHC.Word.Word8 -> GHC.Char.Char.

Axiom c2w : GHC.Char.Char -> GHC.Word.Word8.

Axiom isSpaceWord8 : GHC.Word.Word8 -> bool.

Axiom isSpaceChar8 : GHC.Char.Char -> bool.

Axiom overflowError : forall {a}, GHC.Base.String -> a.

Axiom intmaxWord : GHC.Num.Word.

Axiom intminWord : GHC.Num.Word.

Axiom intmaxQuot10 : GHC.Num.Word.

Axiom intmaxRem10 : GHC.Num.Word.

Axiom intminQuot10 : GHC.Num.Word.

Axiom intminRem10 : GHC.Num.Word.

Axiom accursedUnutterablePerformIO : forall {a : Type}, GHC.Types.IO a -> a.

Axiom memchr : GHC.Ptr.Ptr GHC.Word.Word8 ->
               GHC.Word.Word8 ->
               Foreign.C.Types.CSize -> GHC.Types.IO (GHC.Ptr.Ptr GHC.Word.Word8).

Axiom memcmp : GHC.Ptr.Ptr GHC.Word.Word8 ->
               GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Num.Int -> GHC.Types.IO Foreign.C.Types.CInt.

Axiom memcpy : GHC.Ptr.Ptr GHC.Word.Word8 ->
               GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Num.Int -> GHC.Types.IO unit.

Axiom memset : GHC.Ptr.Ptr GHC.Word.Word8 ->
               GHC.Word.Word8 ->
               Foreign.C.Types.CSize -> GHC.Types.IO (GHC.Ptr.Ptr GHC.Word.Word8).

(* External variables:
     Type bool comparison list op_zt__ unit Foreign.C.Types.CInt
     Foreign.C.Types.CSize GHC.Base.Eq_ GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.Semigroup GHC.Base.String GHC.Char.Char GHC.ForeignPtr.ForeignPtr
     GHC.Num.Int GHC.Num.Word GHC.Prim.op_Addrzh__ GHC.Ptr.Ptr GHC.Real.Integral
     GHC.Types.IO GHC.Word.Word8
*)
