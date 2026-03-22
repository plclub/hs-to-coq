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
Require Data.ByteString.Builder.Prim.Internal.
Require Data.ByteString.Builder.Prim.Internal.Floating.
Require GHC.Base.
Require GHC.Num.
Require GHC.Real.
Import Data.ByteString.Builder.Prim.Internal.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition word8
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word8 :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition word16BE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word16 :=
  Data.ByteString.Builder.Prim.Internal.fixedPrim #2 (fun w p =>
                                                        Foreign.Storable.poke p (GHC.Real.fromIntegral (Data.Bits.shiftR
                                                                                                        w
                                                                                                        #8) : GHC.Word.Word8)
                                                        GHC.Base.>>
                                                        Foreign.Storable.poke (GHC.Ptr.plusPtr p #1)
                                                        (GHC.Real.fromIntegral w : GHC.Word.Word8)).

Definition word16Host
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word16 :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition word16LE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word16 :=
  word16Host.

Definition word32BE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word32 :=
  Data.ByteString.Builder.Prim.Internal.fixedPrim #4 (fun w p =>
                                                        Foreign.Storable.poke p (GHC.Real.fromIntegral (Data.Bits.shiftR
                                                                                                        w
                                                                                                        #24) : GHC.Word.Word8)
                                                        GHC.Base.>>
                                                        (Foreign.Storable.poke (GHC.Ptr.plusPtr p #1)
                                                         (GHC.Real.fromIntegral (Data.Bits.shiftR w
                                                                                 #16) : GHC.Word.Word8) GHC.Base.>>
                                                         (Foreign.Storable.poke (GHC.Ptr.plusPtr p #2)
                                                          (GHC.Real.fromIntegral (Data.Bits.shiftR w
                                                                                  #8) : GHC.Word.Word8) GHC.Base.>>
                                                          Foreign.Storable.poke (GHC.Ptr.plusPtr p #3)
                                                          (GHC.Real.fromIntegral w : GHC.Word.Word8)))).

Definition word32Host
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word32 :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition word32LE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word32 :=
  word32Host.

Definition word64BE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word64 :=
  Data.ByteString.Builder.Prim.Internal.fixedPrim #8 (fun w p =>
                                                        Foreign.Storable.poke p (GHC.Real.fromIntegral (Data.Bits.shiftR
                                                                                                        w
                                                                                                        #56) : GHC.Word.Word8)
                                                        GHC.Base.>>
                                                        (Foreign.Storable.poke (GHC.Ptr.plusPtr p #1)
                                                         (GHC.Real.fromIntegral (Data.Bits.shiftR w
                                                                                 #48) : GHC.Word.Word8) GHC.Base.>>
                                                         (Foreign.Storable.poke (GHC.Ptr.plusPtr p #2)
                                                          (GHC.Real.fromIntegral (Data.Bits.shiftR w
                                                                                  #40) : GHC.Word.Word8) GHC.Base.>>
                                                          (Foreign.Storable.poke (GHC.Ptr.plusPtr p #3)
                                                           (GHC.Real.fromIntegral (Data.Bits.shiftR w
                                                                                   #32) : GHC.Word.Word8) GHC.Base.>>
                                                           (Foreign.Storable.poke (GHC.Ptr.plusPtr p #4)
                                                            (GHC.Real.fromIntegral (Data.Bits.shiftR w
                                                                                    #24) : GHC.Word.Word8) GHC.Base.>>
                                                            (Foreign.Storable.poke (GHC.Ptr.plusPtr p #5)
                                                             (GHC.Real.fromIntegral (Data.Bits.shiftR w
                                                                                     #16) : GHC.Word.Word8) GHC.Base.>>
                                                             (Foreign.Storable.poke (GHC.Ptr.plusPtr p #6)
                                                              (GHC.Real.fromIntegral (Data.Bits.shiftR w
                                                                                      #8) : GHC.Word.Word8) GHC.Base.>>
                                                              Foreign.Storable.poke (GHC.Ptr.plusPtr p #7)
                                                              (GHC.Real.fromIntegral w : GHC.Word.Word8)))))))).

Definition word64Host
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word64 :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition word64LE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word64 :=
  word64Host.

Definition wordHost
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Num.Word :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition int8
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int8 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word8.

Definition int16BE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int16 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word16BE.

Definition int16LE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int16 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word16LE.

Definition int32BE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int32 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word32BE.

Definition int32LE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int32 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word32LE.

Definition int64BE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int64 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word64BE.

Definition int64LE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int64 :=
  GHC.Real.fromIntegral Data.ByteString.Builder.Prim.Internal.>$< word64LE.

Definition intHost
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Num.Int :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition int16Host
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int16 :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition int32Host
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int32 :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition int64Host
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Int.Int64 :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition floatBE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Float :=
  Data.ByteString.Builder.Prim.Internal.Floating.encodeFloatViaWord32F word32BE.

Definition floatLE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Float :=
  Data.ByteString.Builder.Prim.Internal.Floating.encodeFloatViaWord32F word32LE.

Definition doubleBE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Double :=
  Data.ByteString.Builder.Prim.Internal.Floating.encodeDoubleViaWord64F word64BE.

Definition doubleLE
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Double :=
  Data.ByteString.Builder.Prim.Internal.Floating.encodeDoubleViaWord64F word64LE.

Definition floatHost
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Float :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

Definition doubleHost
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Types.Double :=
  Data.ByteString.Builder.Prim.Internal.storableToF.

(* External variables:
     Data.Bits.shiftR Data.ByteString.Builder.Prim.Internal.FixedPrim
     Data.ByteString.Builder.Prim.Internal.fixedPrim
     Data.ByteString.Builder.Prim.Internal.op_zgzdzl__
     Data.ByteString.Builder.Prim.Internal.storableToF
     Data.ByteString.Builder.Prim.Internal.Floating.encodeDoubleViaWord64F
     Data.ByteString.Builder.Prim.Internal.Floating.encodeFloatViaWord32F
     Foreign.Storable.poke GHC.Base.op_zgzg__ GHC.Int.Int16 GHC.Int.Int32
     GHC.Int.Int64 GHC.Int.Int8 GHC.Num.Int GHC.Num.Word GHC.Num.fromInteger
     GHC.Ptr.plusPtr GHC.Real.fromIntegral GHC.Types.Double GHC.Types.Float
     GHC.Word.Word16 GHC.Word.Word32 GHC.Word.Word64 GHC.Word.Word8
*)
