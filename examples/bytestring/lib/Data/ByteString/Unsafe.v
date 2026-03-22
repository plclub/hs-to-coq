(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.ByteString.Internal.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Prim.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition unsafeHead : Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun '(Data.ByteString.Internal.BS x l) =>
    GHC.Base.assert (l GHC.Base.> #0)
    (Data.ByteString.Internal.accursedUnutterablePerformIO
     (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                       Foreign.Storable.peek p))).

Definition unsafeTail
   : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun '(Data.ByteString.Internal.BS ps l) =>
    GHC.Base.assert (l GHC.Base.> #0) (Data.ByteString.Internal.BS
                                       (GHC.ForeignPtr.plusForeignPtr ps #1) (l GHC.Num.- #1)).

Definition unsafeInit
   : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun '(Data.ByteString.Internal.BS ps l) =>
    GHC.Base.assert (l GHC.Base.> #0) (Data.ByteString.Internal.BS ps (l GHC.Num.-
                                                                    #1)).

Definition unsafeLast : Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun '(Data.ByteString.Internal.BS x l) =>
    GHC.Base.assert (l GHC.Base.> #0)
    (Data.ByteString.Internal.accursedUnutterablePerformIO
     (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                       Foreign.Storable.peekByteOff p (l GHC.Num.- #1)))).

Definition unsafeIndex
   : Data.ByteString.Internal.ByteString -> GHC.Num.Int -> GHC.Word.Word8 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.ByteString.Internal.BS x l, i =>
        GHC.Base.assert (andb (i GHC.Base.>= #0) (i GHC.Base.< l))
        (Data.ByteString.Internal.accursedUnutterablePerformIO
         (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                           Foreign.Storable.peekByteOff p i)))
    end.

Definition unsafeTake
   : GHC.Num.Int ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, Data.ByteString.Internal.BS x l =>
        GHC.Base.assert (andb (#0 GHC.Base.<= n) (n GHC.Base.<= l))
        (Data.ByteString.Internal.BS x n)
    end.

Definition unsafeDrop
   : GHC.Num.Int ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, Data.ByteString.Internal.BS x l =>
        GHC.Base.assert (andb (#0 GHC.Base.<= n) (n GHC.Base.<= l))
        (Data.ByteString.Internal.BS (GHC.ForeignPtr.plusForeignPtr x n) (l GHC.Num.-
                                      n))
    end.

Definition unsafePackAddressLen
   : GHC.Num.Int ->
     _GHC.Prim.Addr#_ -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun len lop_addrzh__ =>
    GHC.ForeignPtr.newForeignPtr_ (GHC.Ptr.Ptr lop_addrzh__) GHC.Base.>>=
    (fun p => GHC.Base.return_ (Data.ByteString.Internal.BS p len)).

Definition unsafePackCStringFinalizer
   : GHC.Ptr.Ptr GHC.Word.Word8 ->
     GHC.Num.Int ->
     GHC.Types.IO unit -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun p l f =>
    Foreign.Concurrent.newForeignPtr p f GHC.Base.>>=
    (fun fp => GHC.Base.return_ (Data.ByteString.Internal.BS fp l)).

Definition unsafeFinalize
   : Data.ByteString.Internal.ByteString -> GHC.Types.IO unit :=
  fun '(Data.ByteString.Internal.BS p _) => GHC.ForeignPtr.finalizeForeignPtr p.

Definition unsafePackCString
   : Foreign.C.String.CString ->
     GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun cstr =>
    GHC.ForeignPtr.newForeignPtr_ (GHC.Ptr.castPtr cstr) GHC.Base.>>=
    (fun fp =>
       Data.ByteString.Internal.c_strlen cstr GHC.Base.>>=
       (fun l =>
          GHC.Base.return_ (Data.ByteString.Internal.BS fp (GHC.Real.fromIntegral l)))).

Definition unsafePackCStringLen
   : Foreign.C.String.CStringLen ->
     GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun '(pair ptr len) =>
    GHC.ForeignPtr.newForeignPtr_ (GHC.Ptr.castPtr ptr) GHC.Base.>>=
    (fun fp =>
       GHC.Base.return_ (Data.ByteString.Internal.BS fp (GHC.Real.fromIntegral len))).

Definition unsafePackMallocCString
   : Foreign.C.String.CString ->
     GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun cstr =>
    Foreign.ForeignPtr.Imp.newForeignPtr Data.ByteString.Internal.c_free_finalizer
    (GHC.Ptr.castPtr cstr) GHC.Base.>>=
    (fun fp =>
       Data.ByteString.Internal.c_strlen cstr GHC.Base.>>=
       (fun len =>
          GHC.Base.return_ (Data.ByteString.Internal.BS fp (GHC.Real.fromIntegral len)))).

Definition unsafePackMallocCStringLen
   : Foreign.C.String.CStringLen ->
     GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun '(pair cstr len) =>
    Foreign.ForeignPtr.Imp.newForeignPtr Data.ByteString.Internal.c_free_finalizer
    (GHC.Ptr.castPtr cstr) GHC.Base.>>=
    (fun fp => GHC.Base.return_ (Data.ByteString.Internal.BS fp len)).

Definition unsafeUseAsCString {a : Type}
   : Data.ByteString.Internal.ByteString ->
     (Foreign.C.String.CString -> GHC.Types.IO a) -> GHC.Types.IO a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.ByteString.Internal.BS ps _, action =>
        Foreign.ForeignPtr.Imp.withForeignPtr ps (fun p => action (GHC.Ptr.castPtr p))
    end.

Definition unsafeUseAsCStringLen {a : Type}
   : Data.ByteString.Internal.ByteString ->
     (Foreign.C.String.CStringLen -> GHC.Types.IO a) -> GHC.Types.IO a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.ByteString.Internal.BS ps l, action =>
        Foreign.ForeignPtr.Imp.withForeignPtr ps (fun p =>
                                                    action (pair (GHC.Ptr.castPtr p) l))
    end.

(* External variables:
     Type andb pair unit Data.ByteString.Internal.BS
     Data.ByteString.Internal.ByteString
     Data.ByteString.Internal.accursedUnutterablePerformIO
     Data.ByteString.Internal.c_free_finalizer Data.ByteString.Internal.c_strlen
     Data.ByteString.Internal.unsafeWithForeignPtr Foreign.C.String.CString
     Foreign.C.String.CStringLen Foreign.Concurrent.newForeignPtr
     Foreign.ForeignPtr.Imp.newForeignPtr Foreign.ForeignPtr.Imp.withForeignPtr
     Foreign.Storable.peek Foreign.Storable.peekByteOff GHC.Base.assert
     GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Base.return_ GHC.ForeignPtr.finalizeForeignPtr
     GHC.ForeignPtr.newForeignPtr_ GHC.ForeignPtr.plusForeignPtr GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Prim.op_Addrzh__ GHC.Ptr.Ptr
     GHC.Ptr.castPtr GHC.Real.fromIntegral GHC.Types.IO GHC.Word.Word8
*)
