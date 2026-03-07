(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require FastStringEnv.
Require HsSyn.
Require HsToCoq.Err.
Require Name.
Require OccName.
Require Unique.

(* Converted type declarations: *)

Inductive FieldSelectors : Type :=
  | Mk_FieldSelectors : FieldSelectors
  | NoFieldSelectors : FieldSelectors.

Inductive DuplicateRecordFields : Type :=
  | Mk_DuplicateRecordFields : DuplicateRecordFields
  | NoDuplicateRecordFields : DuplicateRecordFields.

Inductive FieldLabel : Type :=
  | Mk_FieldLabel (flHasDuplicateRecordFields : DuplicateRecordFields)
  (flHasFieldSelector : FieldSelectors) (flSelector : Name.Name)
   : FieldLabel.

#[global] Definition FieldLabelEnv :=
  (FastStringEnv.DFastStringEnv FieldLabel)%type.

Instance Default__FieldSelectors : HsToCoq.Err.Default FieldSelectors :=
  HsToCoq.Err.Build_Default _ Mk_FieldSelectors.

Instance Default__DuplicateRecordFields
   : HsToCoq.Err.Default DuplicateRecordFields :=
  HsToCoq.Err.Build_Default _ Mk_DuplicateRecordFields.

Instance Default__FieldLabel : HsToCoq.Err.Default FieldLabel :=
  HsToCoq.Err.Build_Default _ (Mk_FieldLabel HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default).

#[global] Definition flHasDuplicateRecordFields (arg_0__ : FieldLabel) :=
  let 'Mk_FieldLabel flHasDuplicateRecordFields _ _ := arg_0__ in
  flHasDuplicateRecordFields.

#[global] Definition flHasFieldSelector (arg_0__ : FieldLabel) :=
  let 'Mk_FieldLabel _ flHasFieldSelector _ := arg_0__ in
  flHasFieldSelector.

#[global] Definition flSelector (arg_0__ : FieldLabel) :=
  let 'Mk_FieldLabel _ _ flSelector := arg_0__ in
  flSelector.

(* Converted value declarations: *)

Instance HasOccName__FieldLabel : OccName.HasOccName FieldLabel.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `FieldLabel.Outputable__FieldLabel' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `FieldLabel.Outputable__FieldLabelString' *)

Instance Uniquable__FieldLabelString : Unique.Uniquable HsSyn.FieldLabelString.
Proof.
Admitted.

(* Skipping all instances of class `Binary.Binary', including
   `FieldLabel.Binary__DuplicateRecordFields' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `FieldLabel.Outputable__DuplicateRecordFields' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `FieldLabel.NFData__DuplicateRecordFields' *)

(* Skipping all instances of class `Binary.Binary', including
   `FieldLabel.Binary__FieldSelectors' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `FieldLabel.Outputable__FieldSelectors' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `FieldLabel.NFData__FieldSelectors' *)

(* Skipping all instances of class `Binary.Binary', including
   `FieldLabel.Binary__FieldLabel' *)

Axiom flLabel : FieldLabel -> HsSyn.FieldLabelString.

Axiom flIsOverloaded : FieldLabel -> bool.

(* External variables:
     bool FastStringEnv.DFastStringEnv HsSyn.FieldLabelString
     HsToCoq.Err.Build_Default HsToCoq.Err.Default HsToCoq.Err.default Name.Name
     OccName.HasOccName Unique.Uniquable
*)
