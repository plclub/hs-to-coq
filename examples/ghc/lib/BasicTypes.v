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
Require Data.Maybe.
Require Datatypes.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require HsSyn.
Require HsToCoq.Err.
Require Panic.
Import Data.Bits.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

#[global] Definition VisArity :=
  GHC.Num.Int%type.

Inductive UnfoldingSource : Type :=
  | VanillaSrc : UnfoldingSource
  | StableUserSrc : UnfoldingSource
  | StableSystemSrc : UnfoldingSource
  | CompulsorySrc : UnfoldingSource.

Inductive UnboxedTupleOrSum : Type :=
  | UnboxedTupleType : UnboxedTupleOrSum
  | UnboxedSumType : UnboxedTupleOrSum.

Inductive TypeOrKind : Type :=
  | TypeLevel : TypeOrKind
  | KindLevel : TypeOrKind.

Inductive TypeOrData : Type := | IAmData : TypeOrData | IAmType : TypeOrData.

Inductive TypeOrConstraint : Type :=
  | TypeLike : TypeOrConstraint
  | ConstraintLike : TypeOrConstraint.

Inductive TyConFlavour tc : Type :=
  | ClassFlavour : TyConFlavour tc
  | TupleFlavour : HsSyn.Boxity -> TyConFlavour tc
  | SumFlavour : TyConFlavour tc
  | DataTypeFlavour : TyConFlavour tc
  | NewtypeFlavour : TyConFlavour tc
  | AbstractTypeFlavour : TyConFlavour tc
  | OpenFamilyFlavour : TypeOrData -> (option tc) -> TyConFlavour tc
  | ClosedTypeFamilyFlavour : TyConFlavour tc
  | TypeSynonymFlavour : TyConFlavour tc
  | BuiltInTypeFlavour : TyConFlavour tc
  | PromotedDataConFlavour : TyConFlavour tc.

Inductive TupleSort : Type :=
  | BoxedTuple : TupleSort
  | UnboxedTuple : TupleSort
  | ConstraintTuple : TupleSort.

Inductive TopLevelFlag : Type :=
  | TopLevel : TopLevelFlag
  | NotTopLevel : TopLevelFlag.

Inductive SwapFlag : Type := | NotSwapped : SwapFlag | IsSwapped : SwapFlag.

Inductive SuccessFlag : Type :=
  | Succeeded : SuccessFlag
  | Failed : SuccessFlag.

#[global] Definition RulesOnly :=
  bool%type.

#[global] Definition RuleName :=
  GHC.Data.FastString.FastString%type.

Inductive RuleMatchInfo : Type :=
  | ConLike : RuleMatchInfo
  | FunLike : RuleMatchInfo.

#[global] Definition RepArity :=
  nat.

Inductive RecFlag : Type := | Recursive : RecFlag | NonRecursive : RecFlag.

Inductive PprPrec : Type := | PprPrec : GHC.Num.Int -> PprPrec.

#[global] Definition PhaseNum :=
  nat.

Inductive OverlapMode : Type :=
  | NoOverlap : SourceText -> OverlapMode
  | Overlappable : SourceText -> OverlapMode
  | Overlapping : SourceText -> OverlapMode
  | Overlaps : SourceText -> OverlapMode
  | Incoherent : SourceText -> OverlapMode
  | NonCanonical : SourceText -> OverlapMode.

Inductive OverlapFlag : Type :=
  | Mk_OverlapFlag (overlapMode : OverlapMode) (isSafeOverlap : bool)
   : OverlapFlag.

Inductive OneShotInfo : Type :=
  | NoOneShotInfo : OneShotInfo
  | OneShotLam : OneShotInfo.

Inductive NonStandardDefaultingStrategy : Type :=
  | DefaultNonStandardTyVars : NonStandardDefaultingStrategy
  | TryNotToDefaultNonStandardTyVars : NonStandardDefaultingStrategy.

Inductive Levity : Type := | Lifted : Levity | Unlifted : Levity.

Inductive LeftOrRight : Type := | CLeft : LeftOrRight | CRight : LeftOrRight.

#[global] Definition JoinArity :=
  nat.

Inductive TailCallInfo : Type :=
  | AlwaysTailCalled : JoinArity -> TailCallInfo
  | NoTailCallInfo : TailCallInfo.

Inductive InterestingCxt : Type :=
  | IsInteresting : InterestingCxt
  | NotInteresting : InterestingCxt.

Inductive IntWithInf : Type :=
  | Int : GHC.Num.Int -> IntWithInf
  | Infinity : IntWithInf.

Inductive InsideLam : Type :=
  | IsInsideLam : InsideLam
  | NotInsideLam : InsideLam.

Inductive InlineSpec : Type :=
  | Inline : SourceText -> InlineSpec
  | Inlinable : SourceText -> InlineSpec
  | NoInline : SourceText -> InlineSpec
  | Opaque : SourceText -> InlineSpec
  | NoUserInlinePrag : InlineSpec.

Inductive GenReason : Type :=
  | DoExpansion : Language.Haskell.Syntax.Expr.HsDoFlavour -> GenReason
  | OtherExpansion : GenReason.

Inductive FunctionOrData : Type :=
  | IsFunction : FunctionOrData
  | IsData : FunctionOrData.

#[global] Definition FullArgCount :=
  GHC.Num.Int%type.

Inductive EP a : Type := | Mk_EP (fromEP : a) (toEP : a) : EP a.

Inductive DoPmc : Type := | SkipPmc : DoPmc | DoPmc : DoPmc.

Inductive Origin : Type :=
  | FromSource : Origin
  | Generated : GenReason -> DoPmc -> Origin.

Inductive DefaultingStrategy : Type :=
  | DefaultKindVars : DefaultingStrategy
  | NonStandardDefaulting : NonStandardDefaultingStrategy -> DefaultingStrategy.

Inductive DefMethSpec ty : Type :=
  | VanillaDM : DefMethSpec ty
  | GenericDM : ty -> DefMethSpec ty.

#[global] Definition ConTagZ :=
  GHC.Num.Int%type.

Inductive CompilerPhase : Type :=
  | InitialPhase : CompilerPhase
  | Phase : PhaseNum -> CompilerPhase
  | FinalPhase : CompilerPhase.

Inductive CbvMark : Type := | MarkedCbv : CbvMark | NotMarkedCbv : CbvMark.

#[global] Definition BranchCount :=
  GHC.Num.Int%type.

Inductive OccInfo : Type :=
  | ManyOccs (occ_tail : TailCallInfo) : OccInfo
  | IAmDead : OccInfo
  | OneOcc (occ_in_lam : InsideLam) (occ_n_br : BranchCount) (occ_int_cxt
    : InterestingCxt) (occ_tail : TailCallInfo)
   : OccInfo
  | IAmALoopBreaker (occ_rules_only : RulesOnly) (occ_tail : TailCallInfo)
   : OccInfo.

#[global] Definition Arity :=
  nat.

Inductive Alignment : Type :=
  | Alignment (alignmentBytes : GHC.Num.Int) : Alignment.

Inductive Activation : Type :=
  | AlwaysActive : Activation
  | ActiveBefore : SourceText -> PhaseNum -> Activation
  | ActiveAfter : SourceText -> PhaseNum -> Activation
  | FinalActive : Activation
  | NeverActive : Activation.

Inductive InlinePragma : Type :=
  | Mk_InlinePragma (inl_src : SourceText) (inl_inline : InlineSpec) (inl_sat
    : option Arity) (inl_act : Activation) (inl_rule : RuleMatchInfo)
   : InlinePragma.

Arguments ClassFlavour {_}.

Arguments TupleFlavour {_} _.

Arguments SumFlavour {_}.

Arguments DataTypeFlavour {_}.

Arguments NewtypeFlavour {_}.

Arguments AbstractTypeFlavour {_}.

Arguments OpenFamilyFlavour {_} _ _.

Arguments ClosedTypeFamilyFlavour {_}.

Arguments TypeSynonymFlavour {_}.

Arguments BuiltInTypeFlavour {_}.

Arguments PromotedDataConFlavour {_}.

Arguments Mk_EP {_} _ _.

Arguments VanillaDM {_}.

Arguments GenericDM {_} _.

Instance Default__UnfoldingSource : HsToCoq.Err.Default UnfoldingSource :=
  HsToCoq.Err.Build_Default _ VanillaSrc.

Instance Default__UnboxedTupleOrSum : HsToCoq.Err.Default UnboxedTupleOrSum :=
  HsToCoq.Err.Build_Default _ UnboxedTupleType.

Instance Default__TypeOrKind : HsToCoq.Err.Default TypeOrKind :=
  HsToCoq.Err.Build_Default _ TypeLevel.

Instance Default__TypeOrData : HsToCoq.Err.Default TypeOrData :=
  HsToCoq.Err.Build_Default _ IAmData.

Instance Default__TypeOrConstraint : HsToCoq.Err.Default TypeOrConstraint :=
  HsToCoq.Err.Build_Default _ TypeLike.

Instance Default__TupleSort : HsToCoq.Err.Default TupleSort :=
  HsToCoq.Err.Build_Default _ BoxedTuple.

Instance Default__TopLevelFlag : HsToCoq.Err.Default TopLevelFlag :=
  HsToCoq.Err.Build_Default _ TopLevel.

Instance Default__SwapFlag : HsToCoq.Err.Default SwapFlag :=
  HsToCoq.Err.Build_Default _ NotSwapped.

Instance Default__SuccessFlag : HsToCoq.Err.Default SuccessFlag :=
  HsToCoq.Err.Build_Default _ Succeeded.

Instance Default__RuleMatchInfo : HsToCoq.Err.Default RuleMatchInfo :=
  HsToCoq.Err.Build_Default _ ConLike.

Instance Default__RecFlag : HsToCoq.Err.Default RecFlag :=
  HsToCoq.Err.Build_Default _ Recursive.

Instance Default__OneShotInfo : HsToCoq.Err.Default OneShotInfo :=
  HsToCoq.Err.Build_Default _ NoOneShotInfo.

Instance Default__NonStandardDefaultingStrategy
   : HsToCoq.Err.Default NonStandardDefaultingStrategy :=
  HsToCoq.Err.Build_Default _ DefaultNonStandardTyVars.

Instance Default__Levity : HsToCoq.Err.Default Levity :=
  HsToCoq.Err.Build_Default _ Lifted.

Instance Default__LeftOrRight : HsToCoq.Err.Default LeftOrRight :=
  HsToCoq.Err.Build_Default _ CLeft.

Instance Default__TailCallInfo : HsToCoq.Err.Default TailCallInfo :=
  HsToCoq.Err.Build_Default _ NoTailCallInfo.

Instance Default__InterestingCxt : HsToCoq.Err.Default InterestingCxt :=
  HsToCoq.Err.Build_Default _ IsInteresting.

Instance Default__IntWithInf : HsToCoq.Err.Default IntWithInf :=
  HsToCoq.Err.Build_Default _ Infinity.

Instance Default__InsideLam : HsToCoq.Err.Default InsideLam :=
  HsToCoq.Err.Build_Default _ IsInsideLam.

Instance Default__InlineSpec : HsToCoq.Err.Default InlineSpec :=
  HsToCoq.Err.Build_Default _ NoUserInlinePrag.

Instance Default__GenReason : HsToCoq.Err.Default GenReason :=
  HsToCoq.Err.Build_Default _ OtherExpansion.

Instance Default__FunctionOrData : HsToCoq.Err.Default FunctionOrData :=
  HsToCoq.Err.Build_Default _ IsFunction.

Instance Default__DoPmc : HsToCoq.Err.Default DoPmc :=
  HsToCoq.Err.Build_Default _ SkipPmc.

Instance Default__Origin : HsToCoq.Err.Default Origin :=
  HsToCoq.Err.Build_Default _ FromSource.

Instance Default__DefaultingStrategy : HsToCoq.Err.Default DefaultingStrategy :=
  HsToCoq.Err.Build_Default _ DefaultKindVars.

Instance Default__CompilerPhase : HsToCoq.Err.Default CompilerPhase :=
  HsToCoq.Err.Build_Default _ InitialPhase.

Instance Default__CbvMark : HsToCoq.Err.Default CbvMark :=
  HsToCoq.Err.Build_Default _ MarkedCbv.

Instance Default__OccInfo : HsToCoq.Err.Default OccInfo :=
  HsToCoq.Err.Build_Default _ (ManyOccs HsToCoq.Err.default).

Instance Default__Alignment : HsToCoq.Err.Default Alignment :=
  HsToCoq.Err.Build_Default _ (Alignment HsToCoq.Err.default).

Instance Default__Activation : HsToCoq.Err.Default Activation :=
  HsToCoq.Err.Build_Default _ AlwaysActive.

#[global] Definition isSafeOverlap (arg_0__ : OverlapFlag) :=
  let 'Mk_OverlapFlag _ isSafeOverlap := arg_0__ in
  isSafeOverlap.

#[global] Definition overlapMode (arg_0__ : OverlapFlag) :=
  let 'Mk_OverlapFlag overlapMode _ := arg_0__ in
  overlapMode.

#[global] Definition fromEP {a} (arg_0__ : EP a) :=
  let 'Mk_EP fromEP _ := arg_0__ in
  fromEP.

#[global] Definition toEP {a} (arg_0__ : EP a) :=
  let 'Mk_EP _ toEP := arg_0__ in
  toEP.

#[global] Definition occ_in_lam (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_in_lam' has no match in constructor `ManyOccs' of type `OccInfo'")
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_in_lam' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc occ_in_lam _ _ _ => occ_in_lam
  | IAmALoopBreaker _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_in_lam' has no match in constructor `IAmALoopBreaker' of type `OccInfo'")
  end.

#[global] Definition occ_int_cxt (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_int_cxt' has no match in constructor `ManyOccs' of type `OccInfo'")
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_int_cxt' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc _ _ occ_int_cxt _ => occ_int_cxt
  | IAmALoopBreaker _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_int_cxt' has no match in constructor `IAmALoopBreaker' of type `OccInfo'")
  end.

#[global] Definition occ_n_br (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_n_br' has no match in constructor `ManyOccs' of type `OccInfo'")
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_n_br' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc _ occ_n_br _ _ => occ_n_br
  | IAmALoopBreaker _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_n_br' has no match in constructor `IAmALoopBreaker' of type `OccInfo'")
  end.

#[global] Definition occ_rules_only (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_rules_only' has no match in constructor `ManyOccs' of type `OccInfo'")
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_rules_only' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_rules_only' has no match in constructor `OneOcc' of type `OccInfo'")
  | IAmALoopBreaker occ_rules_only _ => occ_rules_only
  end.

#[global] Definition occ_tail (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs occ_tail => occ_tail
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_tail' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc _ _ _ occ_tail => occ_tail
  | IAmALoopBreaker _ occ_tail => occ_tail
  end.

#[global] Definition alignmentBytes (arg_0__ : Alignment) :=
  let 'Alignment alignmentBytes := arg_0__ in
  alignmentBytes.

#[global] Definition inl_act (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma _ _ _ inl_act _ := arg_0__ in
  inl_act.

#[global] Definition inl_inline (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma _ inl_inline _ _ _ := arg_0__ in
  inl_inline.

#[global] Definition inl_rule (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma _ _ _ _ inl_rule := arg_0__ in
  inl_rule.

#[global] Definition inl_sat (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma _ _ inl_sat _ _ := arg_0__ in
  inl_sat.

#[global] Definition inl_src (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma inl_src _ _ _ _ := arg_0__ in
  inl_src.

(* Midamble *)

Require HsToCoq.Err.

Instance Default__OverlapMode : HsToCoq.Err.Default OverlapMode :=
  HsToCoq.Err.Build_Default _ (NoOverlap HsToCoq.Err.default).
Instance Default__OverlapFlag : HsToCoq.Err.Default OverlapFlag :=
  HsToCoq.Err.Build_Default _ (Mk_OverlapFlag HsToCoq.Err.default HsToCoq.Err.default).
Instance Default__Fixity : HsToCoq.Err.Default Fixity :=
  HsToCoq.Err.Build_Default _ (Mk_Fixity HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
Instance Default__InlinePragma : HsToCoq.Err.Default InlinePragma :=
  HsToCoq.Err.Build_Default _ (Mk_InlinePragma HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

(* Converted value declarations: *)

#[local] Definition Functor__TyConFlavour_fmap
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> TyConFlavour a -> TyConFlavour b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, ClassFlavour => ClassFlavour
      | f, TupleFlavour a1 => TupleFlavour a1
      | f, SumFlavour => SumFlavour
      | f, DataTypeFlavour => DataTypeFlavour
      | f, NewtypeFlavour => NewtypeFlavour
      | f, AbstractTypeFlavour => AbstractTypeFlavour
      | f, OpenFamilyFlavour a1 a2 => OpenFamilyFlavour a1 (GHC.Base.fmap f a2)
      | f, ClosedTypeFamilyFlavour => ClosedTypeFamilyFlavour
      | f, TypeSynonymFlavour => TypeSynonymFlavour
      | f, BuiltInTypeFlavour => BuiltInTypeFlavour
      | f, PromotedDataConFlavour => PromotedDataConFlavour
      end.

#[local] Definition Functor__TyConFlavour_op_zlzd__
   : forall {a : Type},
     forall {b : Type}, a -> TyConFlavour b -> TyConFlavour a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | z, ClassFlavour => ClassFlavour
      | z, TupleFlavour a1 => TupleFlavour a1
      | z, SumFlavour => SumFlavour
      | z, DataTypeFlavour => DataTypeFlavour
      | z, NewtypeFlavour => NewtypeFlavour
      | z, AbstractTypeFlavour => AbstractTypeFlavour
      | z, OpenFamilyFlavour a1 a2 => OpenFamilyFlavour a1 (GHC.Base.op_zlzd__ z a2)
      | z, ClosedTypeFamilyFlavour => ClosedTypeFamilyFlavour
      | z, TypeSynonymFlavour => TypeSynonymFlavour
      | z, BuiltInTypeFlavour => BuiltInTypeFlavour
      | z, PromotedDataConFlavour => PromotedDataConFlavour
      end.

#[global]
Program Instance Functor__TyConFlavour : GHC.Base.Functor TyConFlavour :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} =>
             Functor__TyConFlavour_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__TyConFlavour_op_zlzd__ |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__LeftOrRight' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__LeftOrRight' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__Alignment' *)

(* Skipping all instances of class `Outputable.OutputableP', including
   `BasicTypes.OutputableP__Alignment__5' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__OneShotInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__SwapFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__PromotionFlag' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__PromotionFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__FunctionOrData' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__FunctionOrData' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__TopLevelFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__Boxity' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__Boxity' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__CbvMark' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__CbvMark' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__RecFlag' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__RecFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__GenReason' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__Origin' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__DoPmc' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__OverlapFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__OverlapMode' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__OverlapMode' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__OverlapFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__TupleSort' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__TupleSort' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__UnboxedTupleOrSum' *)

#[local] Definition Semigroup__InterestingCxt_op_zlzlzgzg__
   : InterestingCxt -> InterestingCxt -> InterestingCxt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NotInteresting, x => x
    | IsInteresting, _ => IsInteresting
    end.

#[global]
Program Instance Semigroup__InterestingCxt
   : GHC.Base.Semigroup InterestingCxt :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__InterestingCxt_op_zlzlzgzg__ |}.

#[local] Definition Monoid__InterestingCxt_mappend
   : InterestingCxt -> InterestingCxt -> InterestingCxt :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__InterestingCxt_mempty : InterestingCxt :=
  NotInteresting.

#[local] Definition Monoid__InterestingCxt_mconcat
   : list InterestingCxt -> InterestingCxt :=
  GHC.Base.foldr Monoid__InterestingCxt_mappend Monoid__InterestingCxt_mempty.

#[global]
Program Instance Monoid__InterestingCxt : GHC.Base.Monoid InterestingCxt :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__InterestingCxt_mappend ;
           GHC.Base.mconcat__ := Monoid__InterestingCxt_mconcat ;
           GHC.Base.mempty__ := Monoid__InterestingCxt_mempty |}.

#[local] Definition Semigroup__InsideLam_op_zlzlzgzg__
   : InsideLam -> InsideLam -> InsideLam :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NotInsideLam, x => x
    | IsInsideLam, _ => IsInsideLam
    end.

#[global]
Program Instance Semigroup__InsideLam : GHC.Base.Semigroup InsideLam :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__InsideLam_op_zlzlzgzg__ |}.

#[local] Definition Monoid__InsideLam_mappend
   : InsideLam -> InsideLam -> InsideLam :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__InsideLam_mempty : InsideLam :=
  NotInsideLam.

#[local] Definition Monoid__InsideLam_mconcat : list InsideLam -> InsideLam :=
  GHC.Base.foldr Monoid__InsideLam_mappend Monoid__InsideLam_mempty.

#[global]
Program Instance Monoid__InsideLam : GHC.Base.Monoid InsideLam :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__InsideLam_mappend ;
           GHC.Base.mconcat__ := Monoid__InsideLam_mconcat ;
           GHC.Base.mempty__ := Monoid__InsideLam_mempty |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__TailCallInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__OccInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__DefMethSpec' *)

#[local] Definition Semigroup__SuccessFlag_op_zlzlzgzg__
   : SuccessFlag -> SuccessFlag -> SuccessFlag :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Failed, _ => Failed
    | _, Failed => Failed
    | _, _ => Succeeded
    end.

#[global]
Program Instance Semigroup__SuccessFlag : GHC.Base.Semigroup SuccessFlag :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__SuccessFlag_op_zlzlzgzg__ |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__SuccessFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__CompilerPhase' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__Activation' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__Activation' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__RuleMatchInfo' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__RuleMatchInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__InlineSpec' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__InlineSpec' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__InlinePragma' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__InlinePragma' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__UnfoldingSource' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__UnfoldingSource' *)

#[local] Definition Ord__IntWithInf_compare
   : IntWithInf -> IntWithInf -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, Infinity => Eq
    | Int _, Infinity => Lt
    | Infinity, Int _ => Gt
    | Int a, Int b => GHC.Base.compare a b
    end.

#[local] Definition Ord__IntWithInf_op_zl__
   : IntWithInf -> IntWithInf -> bool :=
  fun x y => Ord__IntWithInf_compare x y GHC.Base.== Lt.

#[local] Definition Ord__IntWithInf_op_zlze__
   : IntWithInf -> IntWithInf -> bool :=
  fun x y => Ord__IntWithInf_compare x y GHC.Base./= Gt.

#[local] Definition Ord__IntWithInf_op_zg__
   : IntWithInf -> IntWithInf -> bool :=
  fun x y => Ord__IntWithInf_compare x y GHC.Base.== Gt.

#[local] Definition Ord__IntWithInf_op_zgze__
   : IntWithInf -> IntWithInf -> bool :=
  fun x y => Ord__IntWithInf_compare x y GHC.Base./= Lt.

#[local] Definition Ord__IntWithInf_max
   : IntWithInf -> IntWithInf -> IntWithInf :=
  fun x y => if Ord__IntWithInf_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__IntWithInf_min
   : IntWithInf -> IntWithInf -> IntWithInf :=
  fun x y => if Ord__IntWithInf_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__IntWithInf : GHC.Base.Ord IntWithInf :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__IntWithInf_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__IntWithInf_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__IntWithInf_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__IntWithInf_op_zgze__ ;
           GHC.Base.compare__ := Ord__IntWithInf_compare ;
           GHC.Base.max__ := Ord__IntWithInf_max ;
           GHC.Base.min__ := Ord__IntWithInf_min |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__IntWithInf' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `BasicTypes.Num__IntWithInf' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__TypeOrKind' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__Levity' *)

(* Skipping all instances of class `Binary.Binary', including
   `BasicTypes.Binary__Levity' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__TyConFlavour' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `BasicTypes.NFData__TyConFlavour' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__TypeOrData' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__NonStandardDefaultingStrategy' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__DefaultingStrategy' *)

#[global] Definition pickLR {a : Type} : LeftOrRight -> (a * a)%type -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CLeft, pair l _ => l
    | CRight, pair _ r => r
    end.

#[global] Definition fIRST_TAG : HsSyn.ConTag :=
  #1.

#[global] Definition mkAlignment : GHC.Num.Int -> Alignment :=
  fun n =>
    if n GHC.Base.== #1 : bool then Alignment #1 else
    if n GHC.Base.== #2 : bool then Alignment #2 else
    if n GHC.Base.== #4 : bool then Alignment #4 else
    if n GHC.Base.== #8 : bool then Alignment #8 else
    if n GHC.Base.== #16 : bool then Alignment #16 else
    if n GHC.Base.== #32 : bool then Alignment #32 else
    if n GHC.Base.== #64 : bool then Alignment #64 else
    if n GHC.Base.== #128 : bool then Alignment #128 else
    if n GHC.Base.== #256 : bool then Alignment #256 else
    if n GHC.Base.== #512 : bool then Alignment #512 else
    Panic.panic (GHC.Base.hs_string__
                 "mkAlignment: received either a non power of 2 argument or > 512").

#[global] Definition alignmentOf : GHC.Num.Int -> Alignment :=
  fun x =>
    let scrut_0__ := Data.Bits.op_zizazi__ x #7 in
    let 'num_1__ := scrut_0__ in
    if num_1__ GHC.Base.== #0 : bool then Alignment #8 else
    let 'num_2__ := scrut_0__ in
    if num_2__ GHC.Base.== #4 : bool then Alignment #4 else
    let 'num_3__ := scrut_0__ in
    if num_3__ GHC.Base.== #2 : bool then Alignment #2 else
    Alignment #1.

#[global] Definition noOneShotInfo : OneShotInfo :=
  NoOneShotInfo.

#[global] Definition isOneShotInfo : OneShotInfo -> bool :=
  fun arg_0__ => match arg_0__ with | OneShotLam => true | _ => false end.

#[global] Definition hasNoOneShotInfo : OneShotInfo -> bool :=
  fun arg_0__ => match arg_0__ with | NoOneShotInfo => true | _ => false end.

#[global] Definition worstOneShot : OneShotInfo -> OneShotInfo -> OneShotInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOneShotInfo, _ => NoOneShotInfo
    | OneShotLam, os => os
    end.

#[global] Definition bestOneShot : OneShotInfo -> OneShotInfo -> OneShotInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOneShotInfo, os => os
    | OneShotLam, _ => OneShotLam
    end.

(* Skipping definition `BasicTypes.pprOneShotInfo' *)

#[global] Definition flipSwap : SwapFlag -> SwapFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | IsSwapped => NotSwapped
    | NotSwapped => IsSwapped
    end.

#[global] Definition isSwapped : SwapFlag -> bool :=
  fun arg_0__ => match arg_0__ with | IsSwapped => true | NotSwapped => false end.

#[global] Definition unSwap {a : Type} {b : Type}
   : SwapFlag -> (a -> a -> b) -> a -> a -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | NotSwapped, f, a, b => f a b
    | IsSwapped, f, a, b => f b a
    end.

(* Skipping definition `BasicTypes.pprRuleName' *)

#[global] Definition isNotTopLevel : TopLevelFlag -> bool :=
  fun arg_0__ => match arg_0__ with | NotTopLevel => true | TopLevel => false end.

#[global] Definition isTopLevel : TopLevelFlag -> bool :=
  fun arg_0__ => match arg_0__ with | TopLevel => true | NotTopLevel => false end.

#[global] Definition isMarkedCbv : CbvMark -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | MarkedCbv => true
    | NotMarkedCbv => false
    end.

#[global] Definition isRec : RecFlag -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Recursive => true
    | NonRecursive => false
    end.

#[global] Definition isNonRec : RecFlag -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Recursive => false
    | NonRecursive => true
    end.

#[global] Definition boolToRecFlag : bool -> RecFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | true => Recursive
    | false => NonRecursive
    end.

#[global] Definition isGenerated : Origin -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Generated _ _ => true
    | FromSource => false
    end.

#[global] Definition doExpansionFlavour
   : Origin -> option Language.Haskell.Syntax.Expr.HsDoFlavour :=
  fun arg_0__ =>
    match arg_0__ with
    | Generated (DoExpansion f) _ => Some f
    | _ => None
    end.

#[global] Definition isDoExpansionGenerated : Origin -> bool :=
  Data.Maybe.isJust GHC.Base.∘ doExpansionFlavour.

#[global] Definition doExpansionOrigin
   : Language.Haskell.Syntax.Expr.HsDoFlavour -> Origin :=
  fun f => Generated (DoExpansion f) DoPmc.

#[global] Definition requiresPMC : Origin -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Generated _ SkipPmc => false
    | _ => true
    end.

#[global] Definition setOverlapModeMaybe
   : OverlapFlag -> option OverlapMode -> OverlapFlag :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, None => f
    | f, Some m =>
        let 'Mk_OverlapFlag overlapMode_2__ isSafeOverlap_3__ := f in
        Mk_OverlapFlag m isSafeOverlap_3__
    end.

#[global] Definition hasIncoherentFlag : OverlapMode -> bool :=
  fun mode =>
    match mode with
    | Incoherent _ => true
    | NonCanonical _ => true
    | _ => false
    end.

#[global] Definition hasOverlappableFlag : OverlapMode -> bool :=
  fun mode =>
    match mode with
    | Overlappable _ => true
    | Overlaps _ => true
    | Incoherent _ => true
    | NonCanonical _ => true
    | _ => false
    end.

#[global] Definition hasOverlappingFlag : OverlapMode -> bool :=
  fun mode =>
    match mode with
    | Overlapping _ => true
    | Overlaps _ => true
    | Incoherent _ => true
    | NonCanonical _ => true
    | _ => false
    end.

#[global] Definition hasNonCanonicalFlag : OverlapMode -> bool :=
  fun arg_0__ => match arg_0__ with | NonCanonical _ => true | _ => false end.

(* Skipping definition `BasicTypes.pprSafeOverlap' *)

#[global] Definition topPrec : PprPrec :=
  PprPrec #0.

#[global] Definition sigPrec : PprPrec :=
  PprPrec #1.

#[global] Definition funPrec : PprPrec :=
  PprPrec #2.

#[global] Definition opPrec : PprPrec :=
  PprPrec #2.

#[global] Definition starPrec : PprPrec :=
  PprPrec #3.

#[global] Definition appPrec : PprPrec :=
  PprPrec #4.

#[global] Definition maxPrec : PprPrec :=
  appPrec.

(* Skipping definition `BasicTypes.maybeParen' *)

#[global] Definition tupleSortBoxity : TupleSort -> HsSyn.Boxity :=
  fun arg_0__ =>
    match arg_0__ with
    | BoxedTuple => HsSyn.Boxed
    | UnboxedTuple => HsSyn.Unboxed
    | ConstraintTuple => HsSyn.Boxed
    end.

#[global] Definition boxityTupleSort : HsSyn.Boxity -> TupleSort :=
  fun arg_0__ =>
    match arg_0__ with
    | HsSyn.Boxed => BoxedTuple
    | HsSyn.Unboxed => UnboxedTuple
    end.

(* Skipping definition `BasicTypes.tupleParens' *)

#[global] Definition sumParens : GHC.Base.String -> GHC.Base.String :=
  fun p =>
    GHC.Base.mappend (GHC.Base.mappend (Datatypes.id (GHC.Base.hs_string__ "(#")) p)
                     (Datatypes.id (GHC.Base.hs_string__ "#)")).

(* Skipping definition `BasicTypes.pprAlternative' *)

#[global] Definition unboxedTupleOrSumExtension
   : UnboxedTupleOrSum -> GHC.LanguageExtensions.Type.Extension :=
  fun arg_0__ =>
    match arg_0__ with
    | UnboxedTupleType => GHC.LanguageExtensions.Type.UnboxedTuples
    | UnboxedSumType => GHC.LanguageExtensions.Type.UnboxedSums
    end.

#[global] Definition oneBranch : BranchCount :=
  #1.

#[global] Definition noOccInfo : OccInfo :=
  ManyOccs NoTailCallInfo.

#[global] Definition isNoOccInfo : OccInfo -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | ManyOccs NoTailCallInfo => true
    | _ => false
    end.

#[global] Definition isManyOccs : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | ManyOccs _ => true | _ => false end.

#[global] Definition seqOccInfo : OccInfo -> unit :=
  fun occ => GHC.Prim.seq occ tt.

#[global] Definition tailCallInfo : OccInfo -> TailCallInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | IAmDead => NoTailCallInfo
    | other => occ_tail other
    end.

#[global] Definition zapOccTailCallInfo : OccInfo -> OccInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | IAmDead => IAmDead
    | occ =>
        match occ with
        | ManyOccs occ_tail_1__ => ManyOccs NoTailCallInfo
        | IAmDead => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | OneOcc occ_in_lam_2__ occ_n_br_3__ occ_int_cxt_4__ occ_tail_5__ =>
            OneOcc occ_in_lam_2__ occ_n_br_3__ occ_int_cxt_4__ NoTailCallInfo
        | IAmALoopBreaker occ_rules_only_6__ occ_tail_7__ =>
            IAmALoopBreaker occ_rules_only_6__ NoTailCallInfo
        end
    end.

#[global] Definition isAlwaysTailCalled : OccInfo -> bool :=
  fun occ =>
    match tailCallInfo occ with
    | AlwaysTailCalled _ => true
    | NoTailCallInfo => false
    end.

#[global] Definition strongLoopBreaker : OccInfo :=
  IAmALoopBreaker false NoTailCallInfo.

#[global] Definition weakLoopBreaker : OccInfo :=
  IAmALoopBreaker true NoTailCallInfo.

#[global] Definition isWeakLoopBreaker : OccInfo -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | IAmALoopBreaker _ _ => true
    | _ => false
    end.

#[global] Definition isStrongLoopBreaker : OccInfo -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | IAmALoopBreaker false _ => true
    | _ => false
    end.

#[global] Definition isDeadOcc : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | IAmDead => true | _ => false end.

#[global] Definition isOneOcc : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | OneOcc _ _ _ _ => true | _ => false end.

#[global] Definition zapFragileOcc : OccInfo -> OccInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | OneOcc _ _ _ _ => noOccInfo
    | occ => zapOccTailCallInfo occ
    end.

#[global] Definition pprShortTailCallInfo : TailCallInfo -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | AlwaysTailCalled ar => GHC.Base.mappend Panic.someSDoc Panic.someSDoc
    | NoTailCallInfo => Panic.someSDoc
    end.

#[global] Definition successIf : bool -> SuccessFlag :=
  fun arg_0__ => match arg_0__ with | true => Succeeded | false => Failed end.

#[global] Definition succeeded : SuccessFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Succeeded => true | Failed => false end.

#[global] Definition failed : SuccessFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Succeeded => false | Failed => true end.

#[global] Definition beginPhase : Activation -> CompilerPhase :=
  fun arg_0__ =>
    match arg_0__ with
    | AlwaysActive => InitialPhase
    | ActiveBefore _ _ => InitialPhase
    | ActiveAfter _ n => Phase n
    | FinalActive => FinalPhase
    | NeverActive => FinalPhase
    end.

#[global] Definition activeAfter : CompilerPhase -> Activation :=
  fun arg_0__ =>
    match arg_0__ with
    | InitialPhase => AlwaysActive
    | Phase n => ActiveAfter NoSourceText n
    | FinalPhase => FinalActive
    end.

#[global] Definition nextPhase : CompilerPhase -> CompilerPhase :=
  fun arg_0__ =>
    let j_3__ :=
      match arg_0__ with
      | Phase n => Phase (n GHC.Num.- #1)
      | FinalPhase => FinalPhase
      | _ => GHC.Err.patternFailure
      end in
    match arg_0__ with
    | InitialPhase => Phase #2
    | Phase num_1__ => if num_1__ GHC.Base.== #0 : bool then FinalPhase else j_3__
    | _ => j_3__
    end.

#[global] Definition laterPhase
   : CompilerPhase -> CompilerPhase -> CompilerPhase :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Phase n1, Phase n2 => Phase (GHC.Base.min n1 n2)
    | InitialPhase, p2 => p2
    | FinalPhase, _ => FinalPhase
    | p1, InitialPhase => p1
    | _, FinalPhase => FinalPhase
    end.

#[global] Definition activateAfterInitial : Activation :=
  activeAfter (nextPhase InitialPhase).

#[global] Definition activateDuringFinal : Activation :=
  FinalActive.

#[global] Definition activeInFinalPhase : Activation -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlwaysActive => true
    | FinalActive => true
    | ActiveAfter _ _ => true
    | _ => false
    end.

#[global] Definition activeInInitialPhase : Activation -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlwaysActive => true
    | ActiveBefore _ _ => true
    | _ => false
    end.

#[global] Definition activeInPhase : PhaseNum -> Activation -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, AlwaysActive => true
    | _, NeverActive => false
    | _, FinalActive => false
    | p, ActiveAfter _ n => p GHC.Base.<= n
    | p, ActiveBefore _ n => p GHC.Base.> n
    end.

#[global] Definition isActive : CompilerPhase -> Activation -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InitialPhase, act => activeInInitialPhase act
    | Phase p, act => activeInPhase p act
    | FinalPhase, act => activeInFinalPhase act
    end.

#[global] Definition isNeverActive : Activation -> bool :=
  fun arg_0__ => match arg_0__ with | NeverActive => true | _ => false end.

#[global] Definition isAlwaysActive : Activation -> bool :=
  fun arg_0__ => match arg_0__ with | AlwaysActive => true | _ => false end.

#[global] Definition competesWith : Activation -> Activation -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | AlwaysActive, _ => true
    | NeverActive, _ => false
    | _, NeverActive => false
    | FinalActive, FinalActive => true
    | FinalActive, _ => false
    | ActiveBefore _ _, AlwaysActive => true
    | ActiveBefore _ _, FinalActive => false
    | ActiveBefore _ _, ActiveBefore _ _ => true
    | ActiveBefore _ a, ActiveAfter _ b => a GHC.Base.< b
    | ActiveAfter _ _, AlwaysActive => false
    | ActiveAfter _ _, FinalActive => true
    | ActiveAfter _ _, ActiveBefore _ _ => false
    | ActiveAfter _ a, ActiveAfter _ b => a GHC.Base.>= b
    end.

#[global] Definition isConLike : RuleMatchInfo -> bool :=
  fun arg_0__ => match arg_0__ with | ConLike => true | _ => false end.

#[global] Definition isFunLike : RuleMatchInfo -> bool :=
  fun arg_0__ => match arg_0__ with | FunLike => true | _ => false end.

#[global] Definition noUserInlineSpec : InlineSpec -> bool :=
  fun arg_0__ => match arg_0__ with | NoUserInlinePrag => true | _ => false end.

#[global] Definition defaultInlinePragma : InlinePragma :=
  Mk_InlinePragma (Mk_SourceText (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                             "{-# INLINE"))) NoUserInlinePrag None AlwaysActive FunLike.

#[global] Definition inlinePragmaSource : InlinePragma -> SourceText :=
  fun prag =>
    match inl_inline prag with
    | Inline x => x
    | Inlinable y => y
    | NoInline z => z
    | Opaque q => q
    | NoUserInlinePrag => NoSourceText
    end.

#[global] Definition alwaysInlinePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := defaultInlinePragma in
  Mk_InlinePragma inl_src_0__ (Inline (inlinePragmaSource defaultInlinePragma))
                  inl_sat_2__ inl_act_3__ inl_rule_4__.

#[global] Definition neverInlinePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := defaultInlinePragma in
  Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ NeverActive inl_rule_4__.

#[global] Definition alwaysInlineConLikePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := alwaysInlinePragma in
  Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__ ConLike.

#[global] Definition inlinePragmaSpec : InlinePragma -> InlineSpec :=
  inl_inline.

#[global] Definition inlineSpecSource : InlineSpec -> SourceText :=
  fun spec =>
    match spec with
    | Inline x => x
    | Inlinable y => y
    | NoInline z => z
    | Opaque q => q
    | NoUserInlinePrag => NoSourceText
    end.

#[global] Definition dfunInlinePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := defaultInlinePragma in
  Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ AlwaysActive ConLike.

#[global] Definition isDefaultInlinePragma : InlinePragma -> bool :=
  fun '(Mk_InlinePragma _ inline _ activation match_info) =>
    andb (noUserInlineSpec inline) (andb (isAlwaysActive activation) (isFunLike
                                          match_info)).

#[global] Definition isInlinePragma : InlinePragma -> bool :=
  fun prag => match inl_inline prag with | Inline _ => true | _ => false end.

#[global] Definition isInlinablePragma : InlinePragma -> bool :=
  fun prag => match inl_inline prag with | Inlinable _ => true | _ => false end.

#[global] Definition isNoInlinePragma : InlinePragma -> bool :=
  fun prag => match inl_inline prag with | NoInline _ => true | _ => false end.

#[global] Definition isAnyInlinePragma : InlinePragma -> bool :=
  fun prag =>
    match inl_inline prag with
    | Inline _ => true
    | Inlinable _ => true
    | _ => false
    end.

#[global] Definition isOpaquePragma : InlinePragma -> bool :=
  fun prag => match inl_inline prag with | Opaque _ => true | _ => false end.

#[global] Definition inlinePragmaSat : InlinePragma -> option Arity :=
  inl_sat.

#[global] Definition inlinePragmaActivation : InlinePragma -> Activation :=
  fun '(Mk_InlinePragma _ _ _ activation _) => activation.

#[global] Definition inlinePragmaRuleMatchInfo
   : InlinePragma -> RuleMatchInfo :=
  fun '(Mk_InlinePragma _ _ _ _ info) => info.

#[global] Definition setInlinePragmaActivation
   : InlinePragma -> Activation -> InlinePragma :=
  fun prag activation =>
    let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
       inl_rule_4__ := prag in
    Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ activation inl_rule_4__.

#[global] Definition setInlinePragmaRuleMatchInfo
   : InlinePragma -> RuleMatchInfo -> InlinePragma :=
  fun prag info =>
    let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
       inl_rule_4__ := prag in
    Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__ info.

#[global] Definition inlinePragmaName : InlineSpec -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | Inline _ => Datatypes.id (GHC.Base.hs_string__ "INLINE")
    | Inlinable _ => Datatypes.id (GHC.Base.hs_string__ "INLINABLE")
    | NoInline _ => Datatypes.id (GHC.Base.hs_string__ "NOINLINE")
    | Opaque _ => Datatypes.id (GHC.Base.hs_string__ "OPAQUE")
    | NoUserInlinePrag => Panic.someSDoc
    end.

#[global] Definition pprInline' : bool -> InlinePragma -> GHC.Base.String :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | emptyInline, Mk_InlinePragma _ inline mb_arity activation info =>
        let pp_info :=
          if isFunLike info : bool then Panic.someSDoc else
          Panic.someSDoc in
        let pp_sat :=
          match mb_arity with
          | Some ar =>
              GHC.Base.mappend (Datatypes.id (GHC.Base.hs_string__ "sat-args="))
                               Panic.someSDoc
          | _ => Panic.someSDoc
          end in
        let pp_act :=
          fun arg_4__ arg_5__ =>
            match arg_4__, arg_5__ with
            | Inline _, AlwaysActive => Panic.someSDoc
            | NoInline _, NeverActive => Panic.someSDoc
            | Opaque _, NeverActive => Panic.someSDoc
            | _, act => Panic.someSDoc
            end in
        let pp_inl :=
          fun x => if emptyInline : bool then Panic.someSDoc else inlinePragmaName x in
        GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend (pp_inl inline) (pp_act
                                                              inline activation)) pp_sat) pp_info
    end.

#[global] Definition pprInline : InlinePragma -> GHC.Base.String :=
  pprInline' true.

#[global] Definition pprInlineDebug : InlinePragma -> GHC.Base.String :=
  pprInline' false.

#[global] Definition isStableUserSource : UnfoldingSource -> bool :=
  fun arg_0__ => match arg_0__ with | StableUserSrc => true | _ => false end.

#[global] Definition isStableSystemSource : UnfoldingSource -> bool :=
  fun arg_0__ => match arg_0__ with | StableSystemSrc => true | _ => false end.

#[global] Definition isCompulsorySource : UnfoldingSource -> bool :=
  fun arg_0__ => match arg_0__ with | CompulsorySrc => true | _ => false end.

#[global] Definition isStableSource : UnfoldingSource -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CompulsorySrc => true
    | StableSystemSrc => true
    | StableUserSrc => true
    | VanillaSrc => false
    end.

#[global] Definition infinity : IntWithInf :=
  Infinity.

#[global] Definition intGtLimit : GHC.Num.Int -> IntWithInf -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Infinity => false
    | n, Int m => n GHC.Base.> m
    end.

#[global] Definition plusWithInf : IntWithInf -> IntWithInf -> IntWithInf :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, _ => Infinity
    | _, Infinity => Infinity
    | Int a, Int b => Int (a GHC.Num.+ b)
    end.

#[global] Definition mulWithInf : IntWithInf -> IntWithInf -> IntWithInf :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, _ => Infinity
    | _, Infinity => Infinity
    | Int a, Int b => Int (a GHC.Num.* b)
    end.

#[global] Definition subWithInf : IntWithInf -> GHC.Num.Int -> IntWithInf :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, _ => Infinity
    | Int a, b => Int (a GHC.Num.- b)
    end.

#[global] Definition treatZeroAsInf : GHC.Num.Int -> IntWithInf :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #0 : bool then Infinity else
    let 'n := arg_0__ in
    Int n.

#[global] Definition mkIntWithInf : GHC.Num.Int -> IntWithInf :=
  Int.

#[global] Definition isTypeLevel : TypeOrKind -> bool :=
  fun arg_0__ => match arg_0__ with | TypeLevel => true | KindLevel => false end.

#[global] Definition isKindLevel : TypeOrKind -> bool :=
  fun arg_0__ => match arg_0__ with | TypeLevel => false | KindLevel => true end.

#[global] Definition mightBeLifted : option Levity -> bool :=
  fun arg_0__ => match arg_0__ with | Some Unlifted => false | _ => true end.

#[global] Definition mightBeUnlifted : option Levity -> bool :=
  fun arg_0__ => match arg_0__ with | Some Lifted => false | _ => true end.

#[global] Definition tyConFlavourAssoc_maybe {tc : Type}
   : TyConFlavour tc -> option tc :=
  fun arg_0__ =>
    match arg_0__ with
    | OpenFamilyFlavour _ mb_parent => mb_parent
    | _ => None
    end.

#[global] Definition defaultNonStandardTyVars : DefaultingStrategy -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | DefaultKindVars => true
    | NonStandardDefaulting DefaultNonStandardTyVars => true
    | NonStandardDefaulting TryNotToDefaultNonStandardTyVars => false
    end.

(* External variables:
     Eq Gt Lt Mk_SourceText NoSourceText None Some SourceText Type andb bool
     comparison false list nat op_zt__ option pair true tt unit Data.Bits.op_zizazi__
     Data.Maybe.isJust Datatypes.id GHC.Base.Functor GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.Semigroup GHC.Base.String GHC.Base.compare GHC.Base.compare__
     GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr GHC.Base.mappend GHC.Base.mappend__
     GHC.Base.max__ GHC.Base.mconcat__ GHC.Base.mempty__ GHC.Base.min GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zsze__
     GHC.Data.FastString.FastString GHC.Data.FastString.fsLit GHC.Err.error
     GHC.Err.patternFailure GHC.LanguageExtensions.Type.Extension
     GHC.LanguageExtensions.Type.UnboxedSums
     GHC.LanguageExtensions.Type.UnboxedTuples GHC.Num.Int GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq HsSyn.Boxed
     HsSyn.Boxity HsSyn.ConTag HsSyn.Unboxed HsToCoq.Err.Build_Default
     HsToCoq.Err.Default HsToCoq.Err.default Language.Haskell.Syntax.Expr.HsDoFlavour
     Panic.panic Panic.someSDoc
*)
