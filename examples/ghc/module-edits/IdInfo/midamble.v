(*  IdInfo: midamble *)

Require HsToRocq.Err.

(* --------------------- *)


(*****)

#[global] Instance Default__RuleInfo : HsToRocq.Err.Default RuleInfo :=
  HsToRocq.Err.Build_Default _ EmptyRuleInfo.

#[global] Instance Default__TickBoxOp : HsToRocq.Err.Default TickBoxOp :=
  HsToRocq.Err.Build_Default _ (TickBox HsToRocq.Err.default HsToRocq.Err.default).

(* Default__DmdType, Default__IdInfo, Default__Var, Default__DataCon
   are injected via sed in Makefile before record accessors need them.
   Default__RecSelParent is needed by record accessors for IdDetails. *)
#[global] Instance Default__RecSelParent : HsToRocq.Err.Default RecSelParent :=
  HsToRocq.Err.Build_Default _ (RecSelData HsToRocq.Err.default).
