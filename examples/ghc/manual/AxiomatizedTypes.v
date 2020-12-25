Require GHC.Base.
Require HsToCoq.Err.

Axiom Coercion           : Type.
Axiom Type_              : Type.
Axiom ThetaType          : Type.
Axiom TyBinder           : Type.
Axiom TyThing            : Type.

Definition Kind          : Type := Type_.
Definition PredType      : Type := Type_.

Axiom BranchFlag         : Type.
Axiom CoAxiom            : BranchFlag -> Type.
Axiom Branched           : BranchFlag.
Axiom Unbranched         : BranchFlag.
Axiom BuiltInSynFamily   : Type.
Axiom BranchIndex        : Type.
Axiom CoAxiomRule        : Type.
Axiom CoAxBranch         : Type.
Inductive Role           : Type := Representational | Nominal | Phantom.

Axiom TcTyVarDetails     : Type.
Axiom liftedTypeKind     : Kind.
Axiom constraintKind     : Kind.

Axiom PrimOp             : Type.
Axiom ForeignCall        : Type.
Axiom CType              : Type.
Axiom CostCentre         : Type.
Axiom DataConBoxer       : Type.


(* -------------------- assumed default instances ------------------- *)

Instance Default__Coercion
   : HsToCoq.Err.Default Coercion.
Admitted.

Instance Default__Type_
   : HsToCoq.Err.Default Type_.
Admitted.

Instance Default__ThetaType
   : HsToCoq.Err.Default ThetaType.
Admitted.


Instance Default__TyBinder
   : HsToCoq.Err.Default TyBinder.
Admitted.

Instance Default__TyThing
   : HsToCoq.Err.Default TyThing.
Admitted.

Instance Default__CoAxiom
   : forall {a}, HsToCoq.Err.Default (CoAxiom a).
Admitted.


Instance Default__BuiltInSynFamily
   : HsToCoq.Err.Default BuiltInSynFamily.
Admitted.


Instance Default__TcTyVarDetails
   : HsToCoq.Err.Default TcTyVarDetails.
Admitted.

Instance Default__Role
   : HsToCoq.Err.Default Role.
Admitted.


Instance Default__BranchIndex
   : HsToCoq.Err.Default BranchIndex.
Admitted.

Instance Default__CoAxiomRule
   : HsToCoq.Err.Default CoAxiomRule.
Admitted.

Instance Default__CoAxiomBranch
   : HsToCoq.Err.Default CoAxBranch.
Admitted.


Instance Default__CostCentre
   : HsToCoq.Err.Default CostCentre.
Admitted.

Instance Default__DataConBoxer
   : HsToCoq.Err.Default DataConBoxer.
Admitted.


Instance Default__PrimOp
   : HsToCoq.Err.Default PrimOp.
Admitted.
Instance Default__ForeignCall
   : HsToCoq.Err.Default ForeignCall.
Admitted.
Instance Default__CType
   : HsToCoq.Err.Default CType.
Admitted.


(* ---------------- Eq -------------- *)

Instance Eq___CoAxiomRule
   : GHC.Base.Eq_ CoAxiomRule.
Admitted.

Instance Eq___Role
   : GHC.Base.Eq_ Role.
Admitted.

Instance Eq___CostCentre
   : GHC.Base.Eq_ CostCentre.
Admitted.

Instance Ord___CostCentre
   : GHC.Base.Ord CostCentre.
Admitted.
