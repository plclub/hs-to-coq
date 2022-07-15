(*  IdInfo: midamble *)

Require HsToCoq.Err.

(* --------------------- *)


(*****)

Instance Default__RuleInfo : HsToCoq.Err.Default RuleInfo :=
  HsToCoq.Err.Build_Default _ EmptyRuleInfo.

Instance Default__TickBoxOp : HsToCoq.Err.Default TickBoxOp :=
  HsToCoq.Err.Build_Default _ (TickBox HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__Termination {r} : HsToCoq.Err.Default (Termination r) :=
  HsToCoq.Err.Build_Default _ Diverges.

Instance Default__DmdType : HsToCoq.Err.Default DmdType :=
  HsToCoq.Err.Build_Default _ (Mk_DmdType HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__StrictSig : HsToCoq.Err.Default StrictSig :=
  HsToCoq.Err.Build_Default _ (Mk_StrictSig HsToCoq.Err.default).

Instance Default__JointDmd `{HsToCoq.Err.Default a} `{HsToCoq.Err.Default b} : HsToCoq.Err.Default (JointDmd a b) :=
  HsToCoq.Err.Build_Default _ (JD HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__Str {s} : HsToCoq.Err.Default (Str s) :=
  HsToCoq.Err.Build_Default _ Lazy.
Instance Default__Use {s} : HsToCoq.Err.Default (Use s) :=
  HsToCoq.Err.Build_Default _ Abs.

Instance Default__IdInfo : HsToCoq.Err.Default IdInfo :=
  HsToCoq.Err.Build_Default _ (Mk_IdInfo HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default
                         HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default
                         HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__RecSelParent : HsToCoq.Err.Default RecSelParent :=
  HsToCoq.Err.Build_Default _ (RecSelData HsToCoq.Err.default).


Instance Default__Var : HsToCoq.Err.Default Var := HsToCoq.Err.Build_Default _ (Mk_Id HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).


Instance Default__DataCon : HsToCoq.Err.Default DataCon :=
 Err.Build_Default _ (MkData HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default nil nil nil nil HsToCoq.Err.default HsToCoq.Err.default nil HsToCoq.Err.default nil nil HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
