(* Types that were in BasicTypes in GHC 8.4 but moved to separate modules in GHC 9.10.
   GHC.Types.SourceText, GHC.Types.Fixity, GHC.Unit.Module.Warnings *)

Require FastString.
Require SrcLoc.

(* From GHC.Types.SourceText *)
Inductive SourceText : Type :=
  | Mk_SourceText : GHC.Base.String -> SourceText
  | NoSourceText : SourceText.

Inductive StringLiteral : Type :=
  | Mk_StringLiteral (sl_st : SourceText) (sl_fs : FastString.FastString)
   : StringLiteral.

(* From GHC.Types.Fixity *)
Inductive FixityDirection : Type :=
  | InfixL : FixityDirection
  | InfixR : FixityDirection
  | InfixN : FixityDirection.

Inductive Fixity : Type :=
  | Mk_Fixity : SourceText -> GHC.Num.Int -> FixityDirection -> Fixity.

Inductive LexicalFixity : Type :=
  | Prefix : LexicalFixity
  | Infix : LexicalFixity.

(* From GHC.Unit.Module.Warnings *)
Inductive WarningTxt : Type :=
  | Mk_WarningTxt
   : (SrcLoc.Located SourceText) ->
     list (SrcLoc.Located StringLiteral) -> WarningTxt
  | DeprecatedTxt
   : (SrcLoc.Located SourceText) ->
     list (SrcLoc.Located StringLiteral) -> WarningTxt.
