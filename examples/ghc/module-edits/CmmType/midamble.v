Require Import HsToRocq.Nat.

#[global] Instance Default__CmmType : HsToRocq.Err.Default CmmType :=
	 { default := Mk_CmmType HsToRocq.Err.default HsToRocq.Err.default }.
