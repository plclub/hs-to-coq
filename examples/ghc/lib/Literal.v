(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require HsToRocq.Nat.
Require Platform.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Data.ByteString.Internal.Type.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Enum.
Require GHC.Num.
Require GHC.Real.
Require HsToRocq.Err.

(* Converted type declarations: *)

Inductive LitNumType : Type :=
  | LitNumBigNat : LitNumType
  | LitNumInt : LitNumType
  | LitNumInt8 : LitNumType
  | LitNumInt16 : LitNumType
  | LitNumInt32 : LitNumType
  | LitNumInt64 : LitNumType
  | LitNumWord : LitNumType
  | LitNumWord8 : LitNumType
  | LitNumWord16 : LitNumType
  | LitNumWord32 : LitNumType
  | LitNumWord64 : LitNumType.

Inductive Literal : Type :=
  | LitChar : GHC.Char.Char -> Literal
  | LitNumber : LitNumType -> GHC.Num.Integer -> Literal
  | LitString : Data.ByteString.Internal.Type.ByteString -> Literal
  | LitNullAddr : Literal
  | LitRubbish
   : BasicTypes.TypeOrConstraint -> AxiomatizedTypes.RuntimeRepType -> Literal
  | LitFloat : GHC.Real.Rational -> Literal
  | LitDouble : GHC.Real.Rational -> Literal
  | LitLabel
   : FastString.FastString ->
     (option nat) -> BasicTypes.FunctionOrData -> Literal.

#[global] Instance Default__LitNumType : HsToRocq.Err.Default LitNumType :=
  HsToRocq.Err.Build_Default _ LitNumBigNat.

#[global] Instance Default__Literal : HsToRocq.Err.Default Literal :=
  HsToRocq.Err.Build_Default _ LitNullAddr.

(* Converted value declarations: *)

(* Skipping all instances of class `Binary.Binary', including
   `Literal.Binary__LitNumType' *)

(* Skipping all instances of class `Binary.Binary', including
   `Literal.Binary__Literal' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Literal.Outputable__Literal' *)

Instance Eq___Literal : GHC.Base.Eq_ Literal.
Proof.
Admitted.

Instance Ord__Literal : GHC.Base.Ord Literal.
Proof.
Admitted.

Axiom litNumIsSigned : LitNumType -> bool.

Axiom litNumBitSize : Platform.Platform -> LitNumType -> option GHC.Num.Word.

Axiom mkLitNumberWrap : Platform.Platform ->
                        LitNumType -> GHC.Num.Integer -> Literal.

Axiom litNumWrap : Platform.Platform -> Literal -> Literal.

Axiom litNumCoerce : LitNumType -> Platform.Platform -> Literal -> Literal.

Axiom litNumNarrow : LitNumType -> Platform.Platform -> Literal -> Literal.

Axiom litNumCheckRange : Platform.Platform ->
                         LitNumType -> GHC.Num.Integer -> bool.

Axiom litNumRange : Platform.Platform ->
                    LitNumType -> (option GHC.Num.Integer * option GHC.Num.Integer)%type.

Axiom mkLitNumber : Platform.Platform ->
                    LitNumType -> GHC.Num.Integer -> Literal.

Axiom mkLitNumberMaybe : Platform.Platform ->
                         LitNumType -> GHC.Num.Integer -> option Literal.

Axiom mkLitInt : Platform.Platform -> GHC.Num.Integer -> Literal.

Axiom mkLitIntWrap : Platform.Platform -> GHC.Num.Integer -> Literal.

Axiom mkLitIntUnchecked : GHC.Num.Integer -> Literal.

Axiom mkLitIntWrapC : Platform.Platform ->
                      GHC.Num.Integer -> (Literal * bool)%type.

Axiom mkLitWord : Platform.Platform -> GHC.Num.Integer -> Literal.

Axiom mkLitWordWrap : Platform.Platform -> GHC.Num.Integer -> Literal.

Axiom mkLitWordUnchecked : GHC.Num.Integer -> Literal.

Axiom mkLitWordWrapC : Platform.Platform ->
                       GHC.Num.Integer -> (Literal * bool)%type.

Axiom mkLitInt8 : GHC.Num.Integer -> Literal.

Axiom mkLitInt8Wrap : GHC.Num.Integer -> Literal.

Axiom mkLitInt8Unchecked : GHC.Num.Integer -> Literal.

Axiom mkLitWord8 : GHC.Num.Integer -> Literal.

Axiom mkLitWord8Wrap : GHC.Num.Integer -> Literal.

Axiom mkLitWord8Unchecked : GHC.Num.Integer -> Literal.

Axiom mkLitInt16 : GHC.Num.Integer -> Literal.

Axiom mkLitInt16Wrap : GHC.Num.Integer -> Literal.

Axiom mkLitInt16Unchecked : GHC.Num.Integer -> Literal.

Axiom mkLitWord16 : GHC.Num.Integer -> Literal.

Axiom mkLitWord16Wrap : GHC.Num.Integer -> Literal.

Axiom mkLitWord16Unchecked : GHC.Num.Integer -> Literal.

Axiom mkLitInt32 : GHC.Num.Integer -> Literal.

Axiom mkLitInt32Wrap : GHC.Num.Integer -> Literal.

Axiom mkLitInt32Unchecked : GHC.Num.Integer -> Literal.

Axiom mkLitWord32 : GHC.Num.Integer -> Literal.

Axiom mkLitWord32Wrap : GHC.Num.Integer -> Literal.

Axiom mkLitWord32Unchecked : GHC.Num.Integer -> Literal.

Axiom mkLitInt64 : GHC.Num.Integer -> Literal.

Axiom mkLitInt64Wrap : GHC.Num.Integer -> Literal.

Axiom mkLitInt64Unchecked : GHC.Num.Integer -> Literal.

Axiom mkLitWord64 : GHC.Num.Integer -> Literal.

Axiom mkLitWord64Wrap : GHC.Num.Integer -> Literal.

Axiom mkLitWord64Unchecked : GHC.Num.Integer -> Literal.

Axiom mkLitFloat : GHC.Real.Rational -> Literal.

Axiom mkLitDouble : GHC.Real.Rational -> Literal.

Axiom mkLitChar : GHC.Char.Char -> Literal.

Axiom mkLitString : GHC.Base.String -> Literal.

Axiom mkLitBigNat : GHC.Num.Integer -> Literal.

Axiom isLitRubbish : Literal -> bool.

Axiom inBoundedRange : forall {a},
                       forall `{GHC.Enum.Bounded a} `{GHC.Real.Integral a}, GHC.Num.Integer -> bool.

Axiom boundedRange : forall {a},
                     forall `{GHC.Enum.Bounded a} `{GHC.Real.Integral a},
                     (GHC.Num.Integer * GHC.Num.Integer)%type.

Axiom isMinBound : Platform.Platform -> Literal -> bool.

Axiom isMaxBound : Platform.Platform -> Literal -> bool.

Axiom inCharRange : GHC.Char.Char -> bool.

Axiom isZeroLit : Literal -> bool.

Axiom isOneLit : Literal -> bool.

Axiom litValue : Literal -> GHC.Num.Integer.

Axiom isLitValue_maybe : Literal -> option GHC.Num.Integer.

(* Skipping definition `Literal.mapLitValue' *)

Axiom narrowLit' : forall {a},
                   forall `{GHC.Real.Integral a}, LitNumType -> Literal -> Literal.

Axiom narrowInt8Lit : Literal -> Literal.

Axiom narrowInt16Lit : Literal -> Literal.

Axiom narrowInt32Lit : Literal -> Literal.

Axiom narrowInt64Lit : Literal -> Literal.

Axiom narrowWord8Lit : Literal -> Literal.

Axiom narrowWord16Lit : Literal -> Literal.

Axiom narrowWord32Lit : Literal -> Literal.

Axiom narrowWord64Lit : Literal -> Literal.

Axiom convertToWordLit : Platform.Platform -> Literal -> Literal.

Axiom convertToIntLit : Platform.Platform -> Literal -> Literal.

Axiom charToIntLit : Literal -> Literal.

Axiom intToCharLit : Literal -> Literal.

Axiom floatToIntLit : Literal -> Literal.

Axiom intToFloatLit : Literal -> Literal.

Axiom doubleToIntLit : Literal -> Literal.

Axiom intToDoubleLit : Literal -> Literal.

Axiom floatToDoubleLit : Literal -> Literal.

Axiom doubleToFloatLit : Literal -> Literal.

Axiom nullAddrLit : Literal.

Axiom litIsTrivial : Literal -> bool.

Axiom litIsDupable : Platform.Platform -> Literal -> bool.

Axiom litFitsInChar : Literal -> bool.

Axiom litIsLifted : Literal -> bool.

Axiom literalType : Literal -> AxiomatizedTypes.Type_.

Axiom cmpLit : Literal -> Literal -> comparison.

(* Skipping definition `Literal.pprLiteral' *)

(* External variables:
     bool comparison nat op_zt__ option AxiomatizedTypes.RuntimeRepType
     AxiomatizedTypes.Type_ BasicTypes.FunctionOrData BasicTypes.TypeOrConstraint
     Data.ByteString.Internal.Type.ByteString FastString.FastString GHC.Base.Eq_
     GHC.Base.Ord GHC.Base.String GHC.Char.Char GHC.Enum.Bounded GHC.Num.Integer
     GHC.Num.Word GHC.Real.Integral GHC.Real.Rational HsToRocq.Err.Build_Default
     HsToRocq.Err.Default Platform.Platform
*)
