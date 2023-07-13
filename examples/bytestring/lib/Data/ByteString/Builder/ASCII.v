(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Data.ByteString.Builder.Internal.
Require Data.ByteString.Builder.Prim.
Require Data.ByteString.Builder.Prim.ASCII.
Require Data.ByteString.Builder.Prim.Internal.
Require Data.ByteString.Internal.
Require Data.ByteString.Lazy.Internal.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Real.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Real.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition string7
   : GHC.Base.String -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primMapListFixed
  Data.ByteString.Builder.Prim.ASCII.char7.

Definition int8Dec : GHC.Int.Int8 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.int8Dec.

Definition int16Dec
   : GHC.Int.Int16 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.int16Dec.

Definition int32Dec
   : GHC.Int.Int32 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.int32Dec.

Definition int64Dec
   : GHC.Int.Int64 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.int64Dec.

Definition intDec : GHC.Num.Int -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.intDec.

Definition word8Dec
   : GHC.Word.Word8 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.word8Dec.

Definition word16Dec
   : GHC.Word.Word16 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.word16Dec.

Definition word32Dec
   : GHC.Word.Word32 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.word32Dec.

Definition word64Dec
   : GHC.Word.Word64 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.word64Dec.

Definition wordDec : GHC.Num.Word -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.wordDec.

Definition floatDec
   : GHC.Types.Float -> Data.ByteString.Builder.Internal.Builder :=
  string7 GHC.Base.∘ GHC.Show.show.

Definition doubleDec
   : GHC.Types.Double -> Data.ByteString.Builder.Internal.Builder :=
  string7 GHC.Base.∘ GHC.Show.show.

Definition word8Hex
   : GHC.Word.Word8 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.word8Hex.

Definition word16Hex
   : GHC.Word.Word16 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.word16Hex.

Definition word32Hex
   : GHC.Word.Word32 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.word32Hex.

Definition word64Hex
   : GHC.Word.Word64 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.word64Hex.

Definition wordHex : GHC.Num.Word -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primBounded
  Data.ByteString.Builder.Prim.ASCII.wordHex.

Definition int8HexFixed
   : GHC.Int.Int8 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.int8HexFixed.

Definition int16HexFixed
   : GHC.Int.Int16 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.int16HexFixed.

Definition int32HexFixed
   : GHC.Int.Int32 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.int32HexFixed.

Definition int64HexFixed
   : GHC.Int.Int64 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.int64HexFixed.

Definition word8HexFixed
   : GHC.Word.Word8 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.word8HexFixed.

Definition word16HexFixed
   : GHC.Word.Word16 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.word16HexFixed.

Definition word32HexFixed
   : GHC.Word.Word32 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.word32HexFixed.

Definition word64HexFixed
   : GHC.Word.Word64 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.word64HexFixed.

Definition floatHexFixed
   : GHC.Types.Float -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.floatHexFixed.

Definition doubleHexFixed
   : GHC.Types.Double -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.ASCII.doubleHexFixed.

Definition byteStringHex
   : Data.ByteString.Internal.ByteString ->
     Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primMapByteStringFixed
  Data.ByteString.Builder.Prim.ASCII.word8HexFixed.

Definition lazyByteStringHex
   : Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primMapLazyByteStringFixed
  Data.ByteString.Builder.Prim.ASCII.word8HexFixed.

Definition maxPow10 : GHC.Integer.Type.Integer :=
  GHC.Real.toInteger ((#10 : GHC.Num.Int) GHC.Real.^
                      Data.ByteString.Builder.Prim.Internal.caseWordSize_32_64 (#9 : GHC.Num.Int)
                      #18).

Definition intDecPadded
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Num.Int :=
  Data.ByteString.Builder.Prim.Internal.liftFixedToBounded
  (Data.ByteString.Builder.Prim.Internal.caseWordSize_32_64
   (Data.ByteString.Builder.Prim.Internal.fixedPrim #9 (c_int_dec_padded9
                                                        GHC.Base.∘
                                                        GHC.Real.fromIntegral))
   (Data.ByteString.Builder.Prim.Internal.fixedPrim #18
    (c_long_long_int_dec_padded18 GHC.Base.∘ GHC.Real.fromIntegral))).

Definition integerDec
   : GHC.Integer.Type.Integer -> Data.ByteString.Builder.Internal.Builder :=
  fun i =>
    let putB : list GHC.Integer.Type.Integer -> list GHC.Num.Int :=
      fix putB (arg_0__ : list GHC.Integer.Type.Integer) : list GHC.Num.Int
        := match arg_0__ with
           | nil => nil
           | cons n ns =>
               let 'pair q r := GHC.Real.quotRem n maxPow10 in
               cons (GHC.Num.fromInteger q) (cons (GHC.Num.fromInteger r) (putB ns))
           end in
    let errImpossible :=
      fun fun_ =>
        GHC.Err.error (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "integerDec: ")
                                              (Coq.Init.Datatypes.app fun_ (GHC.Base.hs_string__
                                                                       ": the impossible happened."))) in
    let splitf
     : GHC.Integer.Type.Integer ->
       GHC.Integer.Type.Integer -> list GHC.Integer.Type.Integer :=
      fix splitf (pow10 n0 : GHC.Integer.Type.Integer) : list GHC.Integer.Type.Integer
        := let fix splitb arg_7__
             := match arg_7__ with
                | nil => nil
                | cons n ns =>
                    let 'pair q r := GHC.Real.quotRem n pow10 in
                    cons q (cons r (splitb ns))
                end in
           let splith :=
             fun arg_13__ =>
               match arg_13__ with
               | nil => errImpossible (GHC.Base.hs_string__ "splith")
               | cons n ns =>
                   let 'pair q r := GHC.Real.quotRem n pow10 in
                   if q GHC.Base.> #0 : bool then cons q (cons r (splitb ns)) else
                   cons r (splitb ns)
               end in
           if pow10 GHC.Base.> n0 : bool then cons n0 nil else
           splith (splitf (pow10 GHC.Num.* pow10) n0) in
    let putH : list GHC.Integer.Type.Integer -> list GHC.Num.Int :=
      fun arg_23__ =>
        match arg_23__ with
        | nil => errImpossible (GHC.Base.hs_string__ "putH")
        | cons n ns =>
            let 'pair x y := GHC.Real.quotRem n maxPow10 in
            let r := GHC.Num.fromInteger y in
            let q := GHC.Num.fromInteger x in
            if q GHC.Base.> #0 : bool then cons q (cons r (putB ns)) else
            cons r (putB ns)
        end in
    let go : GHC.Integer.Type.Integer -> Data.ByteString.Builder.Internal.Builder :=
      fun n =>
        if n GHC.Base.< maxPow10 : bool then intDec (GHC.Num.fromInteger n) else
        match putH (splitf (maxPow10 GHC.Num.* maxPow10) n) with
        | cons x xs =>
            GHC.Base.mappend (intDec x) (Data.ByteString.Builder.Prim.primMapListBounded
                              intDecPadded xs)
        | nil => errImpossible (GHC.Base.hs_string__ "integerDec: go")
        end in
    let 'i' := GHC.Num.fromInteger i in
    if GHC.Real.toInteger i' GHC.Base.== i : bool then intDec i' else
    if i GHC.Base.< #0 : bool
    then GHC.Base.mappend (Data.ByteString.Builder.Prim.primFixed
                           Data.ByteString.Builder.Prim.char8 (GHC.Char.hs_char__ "-")) (go (GHC.Num.negate
                                                                                             i)) else
    go i.

(* External variables:
     bool c_int_dec_padded9 c_long_long_int_dec_padded18 cons list nil pair
     Coq.Init.Datatypes.app Data.ByteString.Builder.Internal.Builder
     Data.ByteString.Builder.Prim.char8 Data.ByteString.Builder.Prim.primBounded
     Data.ByteString.Builder.Prim.primFixed
     Data.ByteString.Builder.Prim.primMapByteStringFixed
     Data.ByteString.Builder.Prim.primMapLazyByteStringFixed
     Data.ByteString.Builder.Prim.primMapListBounded
     Data.ByteString.Builder.Prim.primMapListFixed
     Data.ByteString.Builder.Prim.ASCII.char7
     Data.ByteString.Builder.Prim.ASCII.doubleHexFixed
     Data.ByteString.Builder.Prim.ASCII.floatHexFixed
     Data.ByteString.Builder.Prim.ASCII.int16Dec
     Data.ByteString.Builder.Prim.ASCII.int16HexFixed
     Data.ByteString.Builder.Prim.ASCII.int32Dec
     Data.ByteString.Builder.Prim.ASCII.int32HexFixed
     Data.ByteString.Builder.Prim.ASCII.int64Dec
     Data.ByteString.Builder.Prim.ASCII.int64HexFixed
     Data.ByteString.Builder.Prim.ASCII.int8Dec
     Data.ByteString.Builder.Prim.ASCII.int8HexFixed
     Data.ByteString.Builder.Prim.ASCII.intDec
     Data.ByteString.Builder.Prim.ASCII.word16Dec
     Data.ByteString.Builder.Prim.ASCII.word16Hex
     Data.ByteString.Builder.Prim.ASCII.word16HexFixed
     Data.ByteString.Builder.Prim.ASCII.word32Dec
     Data.ByteString.Builder.Prim.ASCII.word32Hex
     Data.ByteString.Builder.Prim.ASCII.word32HexFixed
     Data.ByteString.Builder.Prim.ASCII.word64Dec
     Data.ByteString.Builder.Prim.ASCII.word64Hex
     Data.ByteString.Builder.Prim.ASCII.word64HexFixed
     Data.ByteString.Builder.Prim.ASCII.word8Dec
     Data.ByteString.Builder.Prim.ASCII.word8Hex
     Data.ByteString.Builder.Prim.ASCII.word8HexFixed
     Data.ByteString.Builder.Prim.ASCII.wordDec
     Data.ByteString.Builder.Prim.ASCII.wordHex
     Data.ByteString.Builder.Prim.Internal.BoundedPrim
     Data.ByteString.Builder.Prim.Internal.caseWordSize_32_64
     Data.ByteString.Builder.Prim.Internal.fixedPrim
     Data.ByteString.Builder.Prim.Internal.liftFixedToBounded
     Data.ByteString.Internal.ByteString Data.ByteString.Lazy.Internal.ByteString
     GHC.Base.String GHC.Base.mappend GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zg__ GHC.Base.op_zl__ GHC.Err.error GHC.Int.Int16 GHC.Int.Int32
     GHC.Int.Int64 GHC.Int.Int8 GHC.Integer.Type.Integer GHC.Num.Int GHC.Num.Word
     GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zt__ GHC.Real.fromIntegral
     GHC.Real.op_zc__ GHC.Real.quotRem GHC.Real.toInteger GHC.Show.show
     GHC.Types.Double GHC.Types.Float GHC.Word.Word16 GHC.Word.Word32 GHC.Word.Word64
     GHC.Word.Word8
*)
