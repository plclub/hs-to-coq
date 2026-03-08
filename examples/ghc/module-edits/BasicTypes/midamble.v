Require HsToCoq.Err.

#[global] Instance Default__SourceText : HsToCoq.Err.Default SourceText :=
  HsToCoq.Err.Build_Default _ NoSourceText.

#[global] Instance Default__TyConFlavour {tc} : HsToCoq.Err.Default (TyConFlavour tc) :=
  HsToCoq.Err.Build_Default _ ClassFlavour.

(* GHC 9.10: hs-to-coq does not generate derived Eq instances.
   Add the ones needed by downstream code. *)

Definition Eq__IntWithInf_op_zeze : IntWithInf -> IntWithInf -> bool :=
  fun a b => match a, b with
             | Int x, Int y => (x GHC.Base.== y)
             | Infinity, Infinity => true
             | _, _ => false
             end.

#[global]
Instance Eq__IntWithInf : GHC.Base.Eq_ IntWithInf :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq__IntWithInf_op_zeze ;
           GHC.Base.op_zsze____ := fun a b => negb (Eq__IntWithInf_op_zeze a b) |}.

#[global] Instance Eq___OccInfo : GHC.Base.Eq_ OccInfo. Admitted.

