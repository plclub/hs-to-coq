(* Stub module for GHC.Types.Cpr *)
Require HsToCoq.Err.

Axiom CprSig : Type.
Axiom topCprSig : CprSig.

Axiom prependArgsCprSig : nat -> CprSig -> CprSig.

Axiom CprType : Type.
Axiom botCpr : CprType.
Axiom mkCprSig : nat -> CprType -> CprSig.

#[global] Instance Default__CprSig : HsToCoq.Err.Default CprSig. Admitted.
