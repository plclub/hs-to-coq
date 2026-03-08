(*  IdInfo: midamble *)

Require HsToCoq.Err.

(* --------------------- *)


(*****)

#[global] Instance Default__RuleInfo : HsToCoq.Err.Default RuleInfo :=
  HsToCoq.Err.Build_Default _ EmptyRuleInfo.

#[global] Instance Default__TickBoxOp : HsToCoq.Err.Default TickBoxOp :=
  HsToCoq.Err.Build_Default _ (TickBox HsToCoq.Err.default HsToCoq.Err.default).

(* Default__DmdType, Default__IdInfo, Default__Var, Default__DataCon
   are injected via sed in Makefile before record accessors need them.
   Default__RecSelParent is needed by record accessors for IdDetails. *)
#[global] Instance Default__RecSelParent : HsToCoq.Err.Default RecSelParent :=
  HsToCoq.Err.Build_Default _ (RecSelData HsToCoq.Err.default).
