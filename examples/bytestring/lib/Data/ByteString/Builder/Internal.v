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
Require Data.ByteString.Lazy.Internal.
Require Data.ByteString.Short.Internal.
Require GHC.Base.
Require GHC.Num.

(* Converted type declarations: *)

Inductive BufferRange : Type :=
  | BufferRange
   : (GHC.Ptr.Ptr GHC.Word.Word8) -> (GHC.Ptr.Ptr GHC.Word.Word8) -> BufferRange.

Inductive BuildSignal a : Type :=
  | Done : (GHC.Ptr.Ptr GHC.Word.Word8) -> a -> BuildSignal a
  | BufferFull
   : GHC.Num.Int ->
     (GHC.Ptr.Ptr GHC.Word.Word8) ->
     ((fun a_ => (BufferRange -> GHC.Types.IO (BuildSignal a_))%type) a) ->
     BuildSignal a
  | InsertChunk
   : (GHC.Ptr.Ptr GHC.Word.Word8) ->
     Data.ByteString.Internal.ByteString ->
     ((fun a_ => (BufferRange -> GHC.Types.IO (BuildSignal a_))%type) a) ->
     BuildSignal a.

Definition BuildStep :=
  fun a_ => (BufferRange -> GHC.Types.IO (BuildSignal a_))%type.

Inductive Builder : Type :=
  | Builder : (forall {r}, BuildStep r -> BuildStep r) -> Builder.

Inductive Put a : Type :=
  | Put (unPut : forall {r}, (a -> BuildStep r) -> BuildStep r) : Put a.

Inductive Buffer : Type :=
  | Buffer : (GHC.ForeignPtr.ForeignPtr GHC.Word.Word8) -> BufferRange -> Buffer.

Inductive ChunkIOStream a : Type :=
  | Finished : Buffer -> a -> ChunkIOStream a
  | Yield1
   : Data.ByteString.Internal.ByteString ->
     (GHC.Types.IO (ChunkIOStream a)) -> ChunkIOStream a.

Inductive AllocationStrategy : Type :=
  | AllocationStrategy
   : (option (Buffer * GHC.Num.Int)%type -> GHC.Types.IO Buffer) ->
     GHC.Num.Int -> (GHC.Num.Int -> GHC.Num.Int -> bool) -> AllocationStrategy.

Arguments Done {_} _ _.

Arguments BufferFull {_} _ _ _.

Arguments InsertChunk {_} _ _ _.

Arguments Put {_} _.

Arguments Finished {_} _ _.

Arguments Yield1 {_} _ _.

Definition unPut {a} (arg_0__ : Put a) :=
  let 'Put unPut := arg_0__ in
  unPut.

(* Converted value declarations: *)

Instance Semigroup__Builder : GHC.Base.Semigroup Builder.
Proof.
Admitted.

Instance Monoid__Builder : GHC.Base.Monoid Builder.
Proof.
Admitted.

Instance Functor__Put : GHC.Base.Functor Put.
Proof.
Admitted.

Instance Applicative__Put : GHC.Base.Applicative Put.
Proof.
Admitted.

Instance Monad__Put : GHC.Base.Monad Put.
Proof.
Admitted.

Axiom bufferSize : Buffer -> GHC.Num.Int.

Axiom newBuffer : GHC.Num.Int -> GHC.Types.IO Buffer.

Axiom byteStringFromBuffer : Buffer -> Data.ByteString.Internal.ByteString.

Axiom trimmedChunkFromBuffer : AllocationStrategy ->
                               Buffer ->
                               Data.ByteString.Lazy.Internal.ByteString ->
                               Data.ByteString.Lazy.Internal.ByteString.

Axiom yield1 : forall {a},
               Data.ByteString.Internal.ByteString ->
               GHC.Types.IO (ChunkIOStream a) -> GHC.Types.IO (ChunkIOStream a).

Axiom ciosUnitToLazyByteString : AllocationStrategy ->
                                 Data.ByteString.Lazy.Internal.ByteString ->
                                 ChunkIOStream unit -> Data.ByteString.Lazy.Internal.ByteString.

Axiom ciosToLazyByteString : forall {a : Type},
                             forall {b : Type},
                             AllocationStrategy ->
                             (a -> (b * Data.ByteString.Lazy.Internal.ByteString)%type) ->
                             ChunkIOStream a -> (b * Data.ByteString.Lazy.Internal.ByteString)%type.

Axiom done : forall {a : Type},
             GHC.Ptr.Ptr GHC.Word.Word8 -> a -> BuildSignal a.

Axiom bufferFull : forall {a : Type},
                   GHC.Num.Int -> GHC.Ptr.Ptr GHC.Word.Word8 -> BuildStep a -> BuildSignal a.

Axiom insertChunk : forall {a : Type},
                    GHC.Ptr.Ptr GHC.Word.Word8 ->
                    Data.ByteString.Internal.ByteString -> BuildStep a -> BuildSignal a.

Axiom fillWithBuildStep : forall {a : Type},
                          forall {b : Type},
                          BuildStep a ->
                          (GHC.Ptr.Ptr GHC.Word.Word8 -> a -> GHC.Types.IO b) ->
                          (GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Num.Int -> BuildStep a -> GHC.Types.IO b) ->
                          (GHC.Ptr.Ptr GHC.Word.Word8 ->
                           Data.ByteString.Internal.ByteString -> BuildStep a -> GHC.Types.IO b) ->
                          BufferRange -> GHC.Types.IO b.

Axiom builder : (forall {r : Type}, BuildStep r -> BuildStep r) -> Builder.

Axiom finalBuildStep : BuildStep unit.

Axiom runBuilder : Builder -> BuildStep unit.

Axiom runBuilderWith : forall {a : Type}, Builder -> BuildStep a -> BuildStep a.

Axiom empty : Builder.

Axiom append : Builder -> Builder -> Builder.

Axiom flush : Builder.

Axiom put : forall {a : Type},
            (forall {r : Type}, (a -> BuildStep r) -> BuildStep r) -> Put a.

Axiom runPut : forall {a : Type}, Put a -> BuildStep a.

Axiom ap_l : forall {a} {b}, Put a -> Put b -> Put a.

Axiom ap_r : forall {a} {b}, Put a -> Put b -> Put b.

Axiom putBuilder : Builder -> Put unit.

Axiom fromPut : Put unit -> Builder.

Axiom hPut : forall {a : Type},
             GHC.IO.Handle.Types.Handle -> Put a -> GHC.Types.IO a.

Axiom putToLazyByteString : forall {a : Type},
                            Put a -> (a * Data.ByteString.Lazy.Internal.ByteString)%type.

Axiom putToLazyByteStringWith : forall {a : Type},
                                forall {b : Type},
                                AllocationStrategy ->
                                (a -> (b * Data.ByteString.Lazy.Internal.ByteString)%type) ->
                                Put a -> (b * Data.ByteString.Lazy.Internal.ByteString)%type.

Axiom ensureFree : GHC.Num.Int -> Builder.

Axiom wrappedBytesCopyStep : forall {a},
                             BufferRange -> BuildStep a -> BuildStep a.

Axiom byteStringThreshold : GHC.Num.Int ->
                            Data.ByteString.Internal.ByteString -> Builder.

Axiom byteStringCopy : Data.ByteString.Internal.ByteString -> Builder.

Axiom byteStringCopyStep : forall {a},
                           Data.ByteString.Internal.ByteString -> BuildStep a -> BuildStep a.

Axiom byteStringInsert : Data.ByteString.Internal.ByteString -> Builder.

Axiom shortByteString : Data.ByteString.Short.Internal.ShortByteString ->
                        Builder.

Axiom shortByteStringCopyStep : forall {a},
                                Data.ByteString.Short.Internal.ShortByteString -> BuildStep a -> BuildStep a.

Axiom lazyByteStringThreshold : GHC.Num.Int ->
                                Data.ByteString.Lazy.Internal.ByteString -> Builder.

Axiom lazyByteStringCopy : Data.ByteString.Lazy.Internal.ByteString -> Builder.

Axiom lazyByteStringInsert : Data.ByteString.Lazy.Internal.ByteString ->
                             Builder.

Axiom byteString : Data.ByteString.Internal.ByteString -> Builder.

Axiom lazyByteString : Data.ByteString.Lazy.Internal.ByteString -> Builder.

Axiom maximalCopySize : GHC.Num.Int.

Axiom customStrategy : (option (Buffer * GHC.Num.Int)%type ->
                        GHC.Types.IO Buffer) ->
                       GHC.Num.Int -> (GHC.Num.Int -> GHC.Num.Int -> bool) -> AllocationStrategy.

Axiom sanitize : GHC.Num.Int -> GHC.Num.Int.

Axiom untrimmedStrategy : GHC.Num.Int -> GHC.Num.Int -> AllocationStrategy.

Axiom safeStrategy : GHC.Num.Int -> GHC.Num.Int -> AllocationStrategy.

Axiom toLazyByteStringWith : AllocationStrategy ->
                             Data.ByteString.Lazy.Internal.ByteString ->
                             Builder -> Data.ByteString.Lazy.Internal.ByteString.

Axiom buildStepToCIOS : forall {a : Type},
                        AllocationStrategy -> BuildStep a -> GHC.Types.IO (ChunkIOStream a).

(* External variables:
     Type bool op_zt__ option unit Data.ByteString.Internal.ByteString
     Data.ByteString.Lazy.Internal.ByteString
     Data.ByteString.Short.Internal.ShortByteString GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Semigroup
     GHC.ForeignPtr.ForeignPtr GHC.IO.Handle.Types.Handle GHC.Num.Int GHC.Ptr.Ptr
     GHC.Types.IO GHC.Word.Word8
*)
