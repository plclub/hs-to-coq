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
Require Data.ByteString.Builder.Internal.
Require Data.ByteString.Builder.Prim.Binary.
Require Data.ByteString.Builder.Prim.Internal.
Require Data.ByteString.Internal.
Require Data.ByteString.Lazy.Internal.
Require GHC.Base.
Require GHC.Char.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Import Data.Bits.Notations.
Import Data.ByteString.Builder.Prim.Internal.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Prim.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition primBounded {a : Type}
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim a ->
     a -> Data.ByteString.Builder.Internal.Builder :=
  fun w x =>
    let step :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | k, Data.ByteString.Builder.Internal.BufferRange op ope =>
            Data.ByteString.Builder.Prim.Internal.runB w x op GHC.Base.>>=
            (fun op' =>
               let br' := Data.ByteString.Builder.Internal.BufferRange op' ope in k br')
        end in
    GHC.Base.mappend (Data.ByteString.Builder.Internal.ensureFree
                      (Data.ByteString.Builder.Prim.Internal.sizeBound w))
                     (Data.ByteString.Builder.Internal.builder step).

Definition primFixed {a : Type}
   : Data.ByteString.Builder.Prim.Internal.FixedPrim a ->
     a -> Data.ByteString.Builder.Internal.Builder :=
  primBounded GHC.Base.∘ Data.ByteString.Builder.Prim.Internal.toB.

Definition primMapListBounded {a : Type}
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim a ->
     list a -> Data.ByteString.Builder.Internal.Builder :=
  fun w xs0 =>
    let bound := Data.ByteString.Builder.Prim.Internal.sizeBound w in
    let fix step arg_1__ arg_2__ arg_3__
      := match arg_1__, arg_2__, arg_3__ with
         | xs1, k, Data.ByteString.Builder.Internal.BufferRange op0 ope0 =>
             let fix go arg_4__ arg_5__
               := match arg_4__, arg_5__ with
                  | nil, op => k (Data.ByteString.Builder.Internal.BufferRange op ope0)
                  | (cons x' xs' as xs), op =>
                      if GHC.Ptr.plusPtr op bound GHC.Base.<= ope0 : bool
                      then Data.ByteString.Builder.Prim.Internal.runB w x' op GHC.Base.>>= go xs' else
                      GHC.Base.return_ (Data.ByteString.Builder.Internal.bufferFull bound op (step xs
                                                                                     k))
                  end in
             go xs1 op0
         end in
    Data.ByteString.Builder.Internal.builder (step xs0).

Definition primMapListFixed {a : Type}
   : Data.ByteString.Builder.Prim.Internal.FixedPrim a ->
     list a -> Data.ByteString.Builder.Internal.Builder :=
  primMapListBounded GHC.Base.∘ Data.ByteString.Builder.Prim.Internal.toB.

Definition primUnfoldrBounded {b : Type} {a : Type}
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim b ->
     (a -> option (b * a)%type) -> a -> Data.ByteString.Builder.Internal.Builder :=
  fun w f x0 =>
    let bound := Data.ByteString.Builder.Prim.Internal.sizeBound w in
    let fix fillWith arg_1__ arg_2__ arg_3__
      := match arg_1__, arg_2__, arg_3__ with
         | x, k, Data.ByteString.Builder.Internal.BufferRange op0 ope0 =>
             let fix go arg_4__ arg_5__
               := match arg_4__, arg_5__ with
                  | None, op => k (Data.ByteString.Builder.Internal.BufferRange op ope0)
                  | Some (pair y x'), op =>
                      if GHC.Ptr.plusPtr op bound GHC.Base.<= ope0 : bool
                      then Data.ByteString.Builder.Prim.Internal.runB w y op GHC.Base.>>=
                           go (f x') else
                      GHC.Base.return_ (Data.ByteString.Builder.Internal.bufferFull bound op
                                                                                    (fun '(Data.ByteString.Builder.Internal.BufferRange
                                                                                     opNew opeNew) =>
                                                                                       Data.ByteString.Builder.Prim.Internal.runB
                                                                                       w y opNew GHC.Base.>>=
                                                                                       (fun opNew' =>
                                                                                          fillWith x' k
                                                                                          (Data.ByteString.Builder.Internal.BufferRange
                                                                                           opNew' opeNew))))
                  end in
             go (f x) op0
         end in
    Data.ByteString.Builder.Internal.builder (fillWith x0).

Definition primUnfoldrFixed {b : Type} {a : Type}
   : Data.ByteString.Builder.Prim.Internal.FixedPrim b ->
     (a -> option (b * a)%type) -> a -> Data.ByteString.Builder.Internal.Builder :=
  primUnfoldrBounded GHC.Base.∘ Data.ByteString.Builder.Prim.Internal.toB.

Definition primMapByteStringBounded
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString ->
     Data.ByteString.Builder.Internal.Builder :=
  fun w =>
    let bound := Data.ByteString.Builder.Prim.Internal.sizeBound w in
    let step :=
      fun arg_1__ arg_2__ =>
        match arg_1__, arg_2__ with
        | Data.ByteString.Internal.BS ifp isize, k =>
            let ipe := GHC.Ptr.plusPtr (GHC.ForeignPtr.unsafeForeignPtrToPtr ifp) isize in
            let fix goBS arg_4__ arg_5__
              := match arg_4__, arg_5__ with
                 | ip0, (Data.ByteString.Builder.Internal.BufferRange op0 ope as br) =>
                     let goPartial :=
                       fun ipeTmp =>
                         let fix go ip op
                           := if ip GHC.Base.< ipeTmp : bool
                              then Foreign.Storable.peek ip GHC.Base.>>=
                                   (fun x =>
                                      Data.ByteString.Builder.Prim.Internal.runB w x op GHC.Base.>>=
                                      (fun op' => go (GHC.Ptr.plusPtr ip #1) op')) else
                              goBS ip (Data.ByteString.Builder.Internal.BufferRange op ope) in
                         go ip0 op0 in
                     let inpRemaining := GHC.Ptr.minusPtr ipe ip0 in
                     let outRemaining := GHC.Real.div (GHC.Ptr.minusPtr ope op0) bound in
                     if ip0 GHC.Base.>= ipe : bool
                     then GHC.ForeignPtr.touchForeignPtr ifp GHC.Base.>> k br else
                     if GHC.Ptr.plusPtr op0 bound GHC.Base.<= ope : bool
                     then goPartial (GHC.Ptr.plusPtr ip0 (GHC.Base.min outRemaining
                                                      inpRemaining)) else
                     GHC.Base.return_ (Data.ByteString.Builder.Internal.bufferFull bound op0 (goBS
                                                                                    ip0))
                 end in
            goBS (GHC.ForeignPtr.unsafeForeignPtrToPtr ifp)
        end in
    fun bs => Data.ByteString.Builder.Internal.builder (step bs).

Definition primMapByteStringFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString ->
     Data.ByteString.Builder.Internal.Builder :=
  primMapByteStringBounded GHC.Base.∘ Data.ByteString.Builder.Prim.Internal.toB.

Definition primMapLazyByteStringBounded
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Builder.Internal.Builder :=
  fun w =>
    Data.ByteString.Lazy.Internal.foldrChunks (fun x b =>
                                                 GHC.Base.mappend (primMapByteStringBounded w x) b) GHC.Base.mempty.

Definition primMapLazyByteStringFixed
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Builder.Internal.Builder :=
  primMapLazyByteStringBounded GHC.Base.∘
  Data.ByteString.Builder.Prim.Internal.toB.

Definition cstring
   : _GHC.Prim.Addr#_ -> Data.ByteString.Builder.Internal.Builder :=
  let step {r}
   : _GHC.Prim.Addr#_ ->
     Data.ByteString.Builder.Internal.BuildStep r ->
     Data.ByteString.Builder.Internal.BuildStep r :=
    fix step arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | addr
         , k
         , (Data.ByteString.Builder.Internal.BufferRange (GHC.Ptr.Ptr lop_op0zh__ as op0)
          ope as br) =>
             let ch := _GHC.Prim.indexWord8OffAddr#_ addr 0 in
             if _GHC.Word.W8#_ ch GHC.Base.== #0 : bool then k br else
             if op0 GHC.Base.== ope : bool
             then GHC.Base.return_ (Data.ByteString.Builder.Internal.bufferFull
                                    Data.ByteString.Lazy.Internal.defaultChunkSize op0 (step addr k)) else
             GHC.Types.IO (fun s =>
                             let 's' := _GHC.Prim.writeWord8OffAddr#_ lop_op0zh__ 0 ch s in
                             pair s' tt) GHC.Base.>>
             (let br' :=
                Data.ByteString.Builder.Internal.BufferRange (GHC.Ptr.plusPtr op0 #1) ope in
              step (addr GHC.Prim.plusAddr# 1) k br')
         end in
  fun addr0 => Data.ByteString.Builder.Internal.builder (step addr0).

Definition cstringUtf8
   : _GHC.Prim.Addr#_ -> Data.ByteString.Builder.Internal.Builder :=
  let step {r}
   : _GHC.Prim.Addr#_ ->
     Data.ByteString.Builder.Internal.BuildStep r ->
     Data.ByteString.Builder.Internal.BuildStep r :=
    fix step arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | addr
         , k
         , (Data.ByteString.Builder.Internal.BufferRange (GHC.Ptr.Ptr lop_op0zh__ as op0)
          ope as br) =>
             let ch := _GHC.Prim.indexWord8OffAddr#_ addr 0 in
             if _GHC.Word.W8#_ ch GHC.Base.== #0 : bool then k br else
             if op0 GHC.Base.== ope : bool
             then GHC.Base.return_ (Data.ByteString.Builder.Internal.bufferFull
                                    Data.ByteString.Lazy.Internal.defaultChunkSize op0 (step addr k)) else
             if andb (_GHC.Word.W8#_ ch GHC.Base.== #192) (_GHC.Word.W8#_
                      (_GHC.Prim.indexWord8OffAddr#_ addr 1) GHC.Base.==
                      #128) : bool
             then let 'GHC.Word.op_W8zh__ lop_nullBytezh__ := #0 in
                  GHC.Types.IO (fun s =>
                                  let 's' := _GHC.Prim.writeWord8OffAddr#_ lop_op0zh__ 0 lop_nullBytezh__ s in
                                  pair s' tt) GHC.Base.>>
                  (let br' :=
                     Data.ByteString.Builder.Internal.BufferRange (GHC.Ptr.plusPtr op0 #1) ope in
                   step (addr GHC.Prim.plusAddr# 2) k br') else
             GHC.Types.IO (fun s =>
                             let 's' := _GHC.Prim.writeWord8OffAddr#_ lop_op0zh__ 0 ch s in
                             pair s' tt) GHC.Base.>>
             (let br' :=
                Data.ByteString.Builder.Internal.BufferRange (GHC.Ptr.plusPtr op0 #1) ope in
              step (addr GHC.Prim.plusAddr# 1) k br')
         end in
  fun addr0 => Data.ByteString.Builder.Internal.builder (step addr0).

Definition char8
   : Data.ByteString.Builder.Prim.Internal.FixedPrim GHC.Char.Char :=
  (GHC.Real.fromIntegral GHC.Base.∘ GHC.Base.ord)
  Data.ByteString.Builder.Prim.Internal.>$<
  Data.ByteString.Builder.Prim.Binary.word8.

Definition encodeCharUtf8 {a}
   : (GHC.Word.Word8 -> a) ->
     (GHC.Word.Word8 -> GHC.Word.Word8 -> a) ->
     (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8 -> a) ->
     (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8 -> a) ->
     GHC.Char.Char -> a :=
  fun f1 f2 f3 f4 c =>
    let 'x := GHC.Base.ord c in
    if x GHC.Base.<= #127 : bool then f1 (GHC.Real.fromIntegral x) else
    if x GHC.Base.<= #2047 : bool
    then let x2 :=
           GHC.Real.fromIntegral ((x Data.Bits..&.(**) #63) GHC.Num.+ #128) in
         let x1 := GHC.Real.fromIntegral ((Data.Bits.shiftR x #6) GHC.Num.+ #192) in
         f2 x1 x2 else
    if x GHC.Base.<= #65535 : bool
    then let x3 :=
           GHC.Real.fromIntegral ((x Data.Bits..&.(**) #63) GHC.Num.+ #128) in
         let x2 :=
           GHC.Real.fromIntegral (((Data.Bits.shiftR x #6) Data.Bits..&.(**) #63) GHC.Num.+
                                  #128) in
         let x1 := GHC.Real.fromIntegral ((Data.Bits.shiftR x #12) GHC.Num.+ #224) in
         f3 x1 x2 x3 else
    let x4 := GHC.Real.fromIntegral ((x Data.Bits..&.(**) #63) GHC.Num.+ #128) in
    let x3 :=
      GHC.Real.fromIntegral (((Data.Bits.shiftR x #6) Data.Bits..&.(**) #63) GHC.Num.+
                             #128) in
    let x2 :=
      GHC.Real.fromIntegral (((Data.Bits.shiftR x #12) Data.Bits..&.(**) #63)
                             GHC.Num.+
                             #128) in
    let x1 := GHC.Real.fromIntegral ((Data.Bits.shiftR x #18) GHC.Num.+ #240) in
    f4 x1 x2 x3 x4.

Definition charUtf8
   : Data.ByteString.Builder.Prim.Internal.BoundedPrim GHC.Char.Char :=
  let pokeN :=
    fun n io op => io op GHC.Base.>> GHC.Base.return_ (GHC.Ptr.plusPtr op n) in
  let f1 :=
    fun x1 => pokeN #1 (fun op => Foreign.Storable.pokeByteOff op #0 x1) in
  let f2 :=
    fun x1 x2 =>
      pokeN #2 (fun op =>
                  Foreign.Storable.pokeByteOff op #0 x1 GHC.Base.>>
                  Foreign.Storable.pokeByteOff op #1 x2) in
  let f3 :=
    fun x1 x2 x3 =>
      pokeN #3 (fun op =>
                  Foreign.Storable.pokeByteOff op #0 x1 GHC.Base.>>
                  (Foreign.Storable.pokeByteOff op #1 x2 GHC.Base.>>
                   Foreign.Storable.pokeByteOff op #2 x3)) in
  let f4 :=
    fun x1 x2 x3 x4 =>
      pokeN #4 (fun op =>
                  Foreign.Storable.pokeByteOff op #0 x1 GHC.Base.>>
                  (Foreign.Storable.pokeByteOff op #1 x2 GHC.Base.>>
                   (Foreign.Storable.pokeByteOff op #2 x3 GHC.Base.>>
                    Foreign.Storable.pokeByteOff op #3 x4))) in
  Data.ByteString.Builder.Prim.Internal.boundedPrim #4 (encodeCharUtf8 f1 f2 f3
                                                        f4).

(* External variables:
     None Some Type andb bool cons list nil op_zt__ option pair tt
     Data.Bits.op_zizazi__ Data.Bits.shiftR
     Data.ByteString.Builder.Internal.BufferRange
     Data.ByteString.Builder.Internal.BuildStep
     Data.ByteString.Builder.Internal.Builder
     Data.ByteString.Builder.Internal.bufferFull
     Data.ByteString.Builder.Internal.builder
     Data.ByteString.Builder.Internal.ensureFree
     Data.ByteString.Builder.Prim.Binary.word8
     Data.ByteString.Builder.Prim.Internal.BoundedPrim
     Data.ByteString.Builder.Prim.Internal.FixedPrim
     Data.ByteString.Builder.Prim.Internal.boundedPrim
     Data.ByteString.Builder.Prim.Internal.op_zgzdzl__
     Data.ByteString.Builder.Prim.Internal.runB
     Data.ByteString.Builder.Prim.Internal.sizeBound
     Data.ByteString.Builder.Prim.Internal.toB Data.ByteString.Internal.BS
     Data.ByteString.Internal.ByteString Data.ByteString.Lazy.Internal.ByteString
     Data.ByteString.Lazy.Internal.defaultChunkSize
     Data.ByteString.Lazy.Internal.foldrChunks Foreign.Storable.peek
     Foreign.Storable.pokeByteOff GHC.Base.mappend GHC.Base.mempty GHC.Base.min
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zgze__ GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.ord
     GHC.Base.return_ GHC.Char.Char GHC.ForeignPtr.touchForeignPtr
     GHC.ForeignPtr.unsafeForeignPtrToPtr GHC.Num.fromInteger GHC.Num.op_zp__
     GHC.Prim.op_Addrzh__ GHC.Prim.op_indexWord8OffAddrzh__ GHC.Prim.op_plusAddrzh__
     GHC.Prim.op_writeWord8OffAddrzh__ GHC.Ptr.Ptr GHC.Ptr.minusPtr GHC.Ptr.plusPtr
     GHC.Real.div GHC.Real.fromIntegral GHC.Types.IO GHC.Word.Word8
     GHC.Word.op_W8zh__
*)
