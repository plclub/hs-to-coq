Require Import HsToCoq.Nat.

Instance Default__CmmType : HsToCoq.Err.Default CmmType :=
	 { default := Mk_CmmType HsToCoq.Err.default HsToCoq.Err.default }.
