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
Require GHC.Char.
Require GHC.Num.
Require GHC.Real.
Require HsToCoq.Err.

(* Converted type declarations: *)

Inductive ByteString : Type :=
  | Empty : ByteString
  | Chunk : Data.ByteString.Internal.ByteString -> ByteString -> ByteString.

Definition LazyByteString :=
  ByteString%type.

Instance Default__ByteString : HsToCoq.Err.Default ByteString :=
  HsToCoq.Err.Build_Default _ Empty.

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
   `Data.ByteString.Lazy.Internal.NFData__ByteString' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.ByteString.Lazy.Internal.Show__ByteString' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.ByteString.Lazy.Internal.Read__ByteString' *)

(* Skipping all instances of class `GHC.Exts.IsList', including
   `Data.ByteString.Lazy.Internal.IsList__ByteString' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.ByteString.Lazy.Internal.Data__ByteString' *)

Axiom packBytes : list GHC.Word.Word8 -> ByteString.

Axiom packChars : list GHC.Char.Char -> ByteString.

Axiom unpackBytes : ByteString -> list GHC.Word.Word8.

Axiom unpackChars : ByteString -> list GHC.Char.Char.

Axiom invariant : ByteString -> bool.

Axiom checkInvariant : ByteString -> ByteString.

Axiom chunk : Data.ByteString.Internal.ByteString -> ByteString -> ByteString.

Axiom foldrChunks : forall {a : Type},
                    (Data.ByteString.Internal.ByteString -> a -> a) -> a -> ByteString -> a.

Axiom foldlChunks : forall {a : Type},
                    (a -> Data.ByteString.Internal.ByteString -> a) -> a -> ByteString -> a.

Axiom defaultChunkSize : GHC.Num.Int.

Axiom smallChunkSize : GHC.Num.Int.

Axiom chunkOverhead : GHC.Num.Int.

Axiom eq : ByteString -> ByteString -> bool.

Axiom cmp : ByteString -> ByteString -> comparison.

Axiom append : ByteString -> ByteString -> ByteString.

Axiom concat : list ByteString -> ByteString.

Axiom times : forall {a},
              forall `{GHC.Real.Integral a}, a -> ByteString -> ByteString.

Axiom fromStrict : Data.ByteString.Internal.ByteString -> ByteString.

Axiom toStrict : ByteString -> Data.ByteString.Internal.ByteString.

(* External variables:
     Type bool comparison list Data.ByteString.Internal.ByteString GHC.Base.Eq_
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Char.Char GHC.Num.Int
     GHC.Real.Integral GHC.Word.Word8 HsToCoq.Err.Build_Default HsToCoq.Err.Default
*)
