Require GHC.Base.
Require HsToCoq.Err.

Axiom Coercion           : Type.
Axiom Type_              : Type.
Axiom ThetaType          : Type.
Axiom TyBinder           : Type.
Axiom TyThing            : Type.

Definition Kind          : Type := Type_.
Definition PredType      : Type := Type_.
Definition RuntimeRepType : Type := Type_.

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

#[global] Instance Default__Coercion
   : HsToCoq.Err.Default Coercion.
Admitted.

#[global] Instance Default__Type_
   : HsToCoq.Err.Default Type_.
Admitted.

#[global] Instance Default__ThetaType
   : HsToCoq.Err.Default ThetaType.
Admitted.


#[global] Instance Default__TyBinder
   : HsToCoq.Err.Default TyBinder.
Admitted.

#[global] Instance Default__TyThing
   : HsToCoq.Err.Default TyThing.
Admitted.

#[global] Instance Default__CoAxiom
   : forall {a}, HsToCoq.Err.Default (CoAxiom a).
Admitted.


#[global] Instance Default__BuiltInSynFamily
   : HsToCoq.Err.Default BuiltInSynFamily.
Admitted.


#[global] Instance Default__TcTyVarDetails
   : HsToCoq.Err.Default TcTyVarDetails.
Admitted.

#[global] Instance Default__Role
   : HsToCoq.Err.Default Role.
Admitted.


#[global] Instance Default__BranchIndex
   : HsToCoq.Err.Default BranchIndex.
Admitted.

#[global] Instance Default__CoAxiomRule
   : HsToCoq.Err.Default CoAxiomRule.
Admitted.

#[global] Instance Default__CoAxiomBranch
   : HsToCoq.Err.Default CoAxBranch.
Admitted.


#[global] Instance Default__CostCentre
   : HsToCoq.Err.Default CostCentre.
Admitted.

#[global] Instance Default__DataConBoxer
   : HsToCoq.Err.Default DataConBoxer.
Admitted.


#[global] Instance Default__PrimOp
   : HsToCoq.Err.Default PrimOp.
Admitted.
#[global] Instance Default__ForeignCall
   : HsToCoq.Err.Default ForeignCall.
Admitted.
#[global] Instance Default__CType
   : HsToCoq.Err.Default CType.
Admitted.


(* ---------------- Eq -------------- *)

#[global] Instance Eq___CoAxiomRule
   : GHC.Base.Eq_ CoAxiomRule.
Admitted.

#[global] Instance Eq___Role
   : GHC.Base.Eq_ Role.
Admitted.

#[global] Instance Eq___CostCentre
   : GHC.Base.Eq_ CostCentre.
Admitted.

#[global] Instance Ord___CostCentre
   : GHC.Base.Ord CostCentre.
Admitted.
