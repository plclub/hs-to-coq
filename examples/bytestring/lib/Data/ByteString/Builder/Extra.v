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
Require Data.ByteString.Builder.Prim.
Require Data.ByteString.Builder.Prim.Binary.
Require Data.ByteString.Internal.
Require GHC.Base.
Require GHC.Num.
Require HsToCoq.Err.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Next : Type :=
  | Done : Next
  | More
   : GHC.Num.Int ->
     (GHC.Ptr.Ptr GHC.Word.Word8 ->
      GHC.Num.Int -> GHC.Types.IO (GHC.Num.Int * Next)%type)%type ->
     Next
  | Chunk
   : Data.ByteString.Internal.ByteString ->
     (GHC.Ptr.Ptr GHC.Word.Word8 ->
      GHC.Num.Int -> GHC.Types.IO (GHC.Num.Int * Next)%type)%type ->
     Next.

Definition BufferWriter :=
  (GHC.Ptr.Ptr GHC.Word.Word8 ->
   GHC.Num.Int -> GHC.Types.IO (GHC.Num.Int * Next)%type)%type.

Instance Default__Next : HsToCoq.Err.Default Next :=
  HsToCoq.Err.Build_Default _ Done.

(* Converted value declarations: *)

Definition runBuilder
   : Data.ByteString.Builder.Internal.Builder -> BufferWriter :=
  let bytesWritten := fun startPtr endPtr => GHC.Ptr.minusPtr endPtr startPtr in
  let run : Data.ByteString.Builder.Internal.BuildStep unit -> BufferWriter :=
    fix run (step : Data.ByteString.Builder.Internal.BuildStep unit) : BufferWriter
      := fun buf len =>
           let br :=
             Data.ByteString.Builder.Internal.BufferRange buf (GHC.Ptr.plusPtr buf len) in
           let insertChunkH :=
             fun endPtr bs step' =>
               let next := Chunk bs (run step') in
               let wc := bytesWritten buf endPtr in GHC.Base.return_ (pair wc next) in
           let bufferFullH :=
             fun endPtr minReq step' =>
               let next := More minReq (run step') in
               let wc := bytesWritten buf endPtr in GHC.Base.return_ (pair wc next) in
           let doneH :=
             fun arg_8__ arg_9__ =>
               match arg_8__, arg_9__ with
               | endPtr, tt =>
                   let next := Done in
                   let wc := bytesWritten buf endPtr in GHC.Base.return_ (pair wc next)
               end in
           Data.ByteString.Builder.Internal.fillWithBuildStep step doneH bufferFullH
           insertChunkH br in
  run GHC.Base.∘ Data.ByteString.Builder.Internal.runBuilder.

Definition intHost : GHC.Num.Int -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.intHost.

Definition int16Host
   : GHC.Int.Int16 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.int16Host.

Definition int32Host
   : GHC.Int.Int32 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.int32Host.

Definition int64Host
   : GHC.Int.Int64 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.int64Host.

Definition wordHost
   : GHC.Num.Word -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.wordHost.

Definition word16Host
   : GHC.Word.Word16 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.word16Host.

Definition word32Host
   : GHC.Word.Word32 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.word32Host.

Definition word64Host
   : GHC.Word.Word64 -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.word64Host.

Definition floatHost
   : GHC.Types.Float -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.floatHost.

Definition doubleHost
   : GHC.Types.Double -> Data.ByteString.Builder.Internal.Builder :=
  Data.ByteString.Builder.Prim.primFixed
  Data.ByteString.Builder.Prim.Binary.doubleHost.

(* External variables:
     op_zt__ pair tt unit Data.ByteString.Builder.Internal.BufferRange
     Data.ByteString.Builder.Internal.BuildStep
     Data.ByteString.Builder.Internal.Builder
     Data.ByteString.Builder.Internal.fillWithBuildStep
     Data.ByteString.Builder.Internal.runBuilder
     Data.ByteString.Builder.Prim.primFixed
     Data.ByteString.Builder.Prim.Binary.doubleHost
     Data.ByteString.Builder.Prim.Binary.floatHost
     Data.ByteString.Builder.Prim.Binary.int16Host
     Data.ByteString.Builder.Prim.Binary.int32Host
     Data.ByteString.Builder.Prim.Binary.int64Host
     Data.ByteString.Builder.Prim.Binary.intHost
     Data.ByteString.Builder.Prim.Binary.word16Host
     Data.ByteString.Builder.Prim.Binary.word32Host
     Data.ByteString.Builder.Prim.Binary.word64Host
     Data.ByteString.Builder.Prim.Binary.wordHost Data.ByteString.Internal.ByteString
     GHC.Base.op_z2218U__ GHC.Base.return_ GHC.Int.Int16 GHC.Int.Int32 GHC.Int.Int64
     GHC.Num.Int GHC.Num.Word GHC.Ptr.Ptr GHC.Ptr.minusPtr GHC.Ptr.plusPtr
     GHC.Types.Double GHC.Types.Float GHC.Types.IO GHC.Word.Word16 GHC.Word.Word32
     GHC.Word.Word64 GHC.Word.Word8 HsToCoq.Err.Build_Default HsToCoq.Err.Default
*)
