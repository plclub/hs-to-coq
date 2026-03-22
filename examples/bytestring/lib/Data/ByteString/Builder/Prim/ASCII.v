(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Bits.
Require Data.ByteString.Builder.Prim.Binary.
Require Data.ByteString.Builder.Prim.Internal.
Require Data.ByteString.Builder.Prim.Internal.Base16.
Require Data.ByteString.Builder.Prim.Internal.Floating.
Require GHC.Base.
Require GHC.Char.
Require GHC.Err.
Require GHC.Num.
Require GHC.Real.
Import Data.Bits.Notations.
Import Data.ByteString.Builder.Prim.Internal.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition char7
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Char.Char :=
  (fun c => GHC.Real.fromIntegral (GHC.Base.ord c Data.Bits..&.(**) #127))
  Data.ByteString.Builder.Prim.Internal.>$<
  Data.ByteString.Builder.Prim.Binary.word8.

Definition encodeIntDecimal {a} `{GHC.Real.Integral a}
   : GHC.Num.Int -> Data.ByteString.Builder.Prim.Internal.BoundedPrim a :=
  fun bound =>
    Data.ByteString.Builder.Prim.Internal.boundedPrim bound (c_int_dec GHC.Base.∘
                                                             GHC.Real.fromIntegral).

Definition int8Dec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Int.Int8 :=
  encodeIntDecimal #4.

Definition int16Dec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Int.Int16 :=
  encodeIntDecimal #6.

Definition int32Dec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Int.Int32 :=
  encodeIntDecimal #11.

Definition int64Dec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Int.Int64 :=
  Data.ByteString.Builder.Prim.Internal.boundedPrim #20 (c_long_long_int_dec
                                                         GHC.Base.∘
                                                         GHC.Real.fromIntegral).

Definition intDec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Num.Int :=
  Data.ByteString.Builder.Prim.Internal.caseWordSize_32_64 (GHC.Real.fromIntegral
                                                            Data.ByteString.Builder.Prim.Internal.>$<
                                                            int32Dec) (GHC.Real.fromIntegral
                                                                       Data.ByteString.Builder.Prim.Internal.>$<
                                                                       int64Dec).

Definition encodeWordDecimal {a} `{GHC.Real.Integral a}
   : GHC.Num.Int -> Data.ByteString.Builder.Prim.Internal.BoundedPrim a :=
  fun bound =>
    Data.ByteString.Builder.Prim.Internal.boundedPrim bound (c_uint_dec GHC.Base.∘
                                                             GHC.Real.fromIntegral).

Definition word8Dec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word8 :=
  encodeWordDecimal #3.

Definition word16Dec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word16 :=
  encodeWordDecimal #5.

Definition word32Dec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word32 :=
  encodeWordDecimal #10.

Definition word64Dec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word64 :=
  Data.ByteString.Builder.Prim.Internal.boundedPrim #20 (c_long_long_uint_dec
                                                         GHC.Base.∘
                                                         GHC.Real.fromIntegral).

Definition wordDec
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Num.Word :=
  Data.ByteString.Builder.Prim.Internal.caseWordSize_32_64 (GHC.Real.fromIntegral
                                                            Data.ByteString.Builder.Prim.Internal.>$<
                                                            word32Dec) (GHC.Real.fromIntegral
                                                                        Data.ByteString.Builder.Prim.Internal.>$<
                                                                        word64Dec).

Definition encodeWordHex {a} `{Foreign.Storable.Storable a} `{GHC.Real.Integral
  a}
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim a :=
  Data.ByteString.Builder.Prim.Internal.boundedPrim (#2 GHC.Num.*
                                                     Foreign.Storable.sizeOf (GHC.Err.undefined : a)) (c_uint_hex
                                                                                                       GHC.Base.∘
                                                                                                       GHC.Real.fromIntegral).

Definition word8Hex
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word8 :=
  encodeWordHex.

Definition word16Hex
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word16 :=
  encodeWordHex.

Definition word32Hex
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word32 :=
  encodeWordHex.

Definition word64Hex
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word64 :=
  Data.ByteString.Builder.Prim.Internal.boundedPrim #16 (c_long_long_uint_hex
                                                         GHC.Base.∘
                                                         GHC.Real.fromIntegral).

Definition wordHex
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Num.Word :=
  Data.ByteString.Builder.Prim.Internal.caseWordSize_32_64 (GHC.Real.fromIntegral
                                                            Data.ByteString.Builder.Prim.Internal.>$<
                                                            word32Hex) (GHC.Real.fromIntegral
                                                                        Data.ByteString.Builder.Prim.Internal.>$<
                                                                        word64Hex).

Definition word8HexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word8 :=
  Data.ByteString.Builder.Prim.Internal.fixedPrim #2 (fun x op =>
                                                        Foreign.Storable.poke (GHC.Ptr.castPtr op) GHC.Base.=<<
                                                        Data.ByteString.Builder.Prim.Internal.Base16.encode8_as_16h
                                                        Data.ByteString.Builder.Prim.Internal.Base16.lowerTable x).

Definition word16HexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word16 :=
  (fun x =>
     pair (GHC.Real.fromIntegral (Data.Bits.shiftR x #8)) (GHC.Real.fromIntegral x))
  Data.ByteString.Builder.Prim.Internal.>$<
  Data.ByteString.Builder.Prim.Internal.pairF word8HexFixed word8HexFixed.

Definition word32HexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word32 :=
  (fun x =>
     pair (GHC.Real.fromIntegral (Data.Bits.shiftR x #16)) (GHC.Real.fromIntegral x))
  Data.ByteString.Builder.Prim.Internal.>$<
  Data.ByteString.Builder.Prim.Internal.pairF word16HexFixed word16HexFixed.

Definition word64HexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word64 :=
  (fun x =>
     pair (GHC.Real.fromIntegral (Data.Bits.shiftR x #32)) (GHC.Real.fromIntegral x))
  Data.ByteString.Builder.Prim.Internal.>$<
  Data.ByteString.Builder.Prim.Internal.pairF word32HexFixed word32HexFixed.

Definition int8HexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int8 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word8HexFixed.

Definition int16HexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int16 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word16HexFixed.

Definition int32HexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int32 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word32HexFixed.

Definition int64HexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int64 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word64HexFixed.

Definition floatHexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Float :=
  Data.ByteString.Builder.Prim.Internal.Floating.encodeFloatViaWord32F
  word32HexFixed.

Definition doubleHexFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Double :=
  Data.ByteString.Builder.Prim.Internal.Floating.encodeDoubleViaWord64F
  word64HexFixed.

(* External variables:
     c_int_dec c_long_long_int_dec c_long_long_uint_dec c_long_long_uint_hex
     c_uint_dec c_uint_hex pair Data.Bits.op_zizazi__ Data.Bits.shiftR
     Data.ByteString.Builder.Prim.Binary.word8
     Data.ByteString.Builder.Prim.Internal.BoundedPrim
     Data.ByteString.Builder.Prim.Internal.FixedPrim
     Data.ByteString.Builder.Prim.Internal.boundedPrim
     Data.ByteString.Builder.Prim.Internal.caseWordSize_32_64
     Data.ByteString.Builder.Prim.Internal.fixedPrim
     Data.ByteString.Builder.Prim.Internal.op_zgzdzl__
     Data.ByteString.Builder.Prim.Internal.pairF
     Data.ByteString.Builder.Prim.Internal.Base16.encode8_as_16h
     Data.ByteString.Builder.Prim.Internal.Base16.lowerTable
     Data.ByteString.Builder.Prim.Internal.Floating.encodeDoubleViaWord64F
     Data.ByteString.Builder.Prim.Internal.Floating.encodeFloatViaWord32F
     Foreign.Storable.Storable Foreign.Storable.poke Foreign.Storable.sizeOf
     GHC.Base.op_z2218U__ GHC.Base.op_zezlzl__ GHC.Base.ord GHC.Char.Char
     GHC.Err.undefined GHC.Int.Int16 GHC.Int.Int32 GHC.Int.Int64 GHC.Int.Int8
     GHC.Num.Int GHC.Num.Word GHC.Num.fromInteger GHC.Num.op_zt__ GHC.Ptr.castPtr
     GHC.Real.Integral GHC.Real.fromIntegral GHC.Types.Double GHC.Types.Float
     GHC.Word.Word16 GHC.Word.Word32 GHC.Word.Word64 GHC.Word.Word8
*)
