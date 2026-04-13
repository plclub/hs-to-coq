Require GHC.Base.
Require HsToRocq.Err.

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
   : HsToRocq.Err.Default Coercion.
Admitted.

#[global] Instance Default__Type_
   : HsToRocq.Err.Default Type_.
Admitted.

#[global] Instance Default__ThetaType
   : HsToRocq.Err.Default ThetaType.
Admitted.


#[global] Instance Default__TyBinder
   : HsToRocq.Err.Default TyBinder.
Admitted.

#[global] Instance Default__TyThing
   : HsToRocq.Err.Default TyThing.
Admitted.

#[global] Instance Default__CoAxiom
   : forall {a}, HsToRocq.Err.Default (CoAxiom a).
Admitted.


#[global] Instance Default__BuiltInSynFamily
   : HsToRocq.Err.Default BuiltInSynFamily.
Admitted.


#[global] Instance Default__TcTyVarDetails
   : HsToRocq.Err.Default TcTyVarDetails.
Admitted.

#[global] Instance Default__Role
   : HsToRocq.Err.Default Role.
Admitted.


#[global] Instance Default__BranchIndex
   : HsToRocq.Err.Default BranchIndex.
Admitted.

#[global] Instance Default__CoAxiomRule
   : HsToRocq.Err.Default CoAxiomRule.
Admitted.

#[global] Instance Default__CoAxiomBranch
   : HsToRocq.Err.Default CoAxBranch.
Admitted.


#[global] Instance Default__CostCentre
   : HsToRocq.Err.Default CostCentre.
Admitted.

#[global] Instance Default__DataConBoxer
   : HsToRocq.Err.Default DataConBoxer.
Admitted.


#[global] Instance Default__PrimOp
   : HsToRocq.Err.Default PrimOp.
Admitted.
#[global] Instance Default__ForeignCall
   : HsToRocq.Err.Default ForeignCall.
Admitted.
#[global] Instance Default__CType
   : HsToRocq.Err.Default CType.
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
