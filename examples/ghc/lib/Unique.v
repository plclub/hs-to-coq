(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BinNums.
Require Coq.ZArith.BinInt.
Require Data.Bits.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Num.
Require Module.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Unique : Type := | MkUnique : BinNums.N -> Unique.

Record Uniquable__Dict (a : Type) := Uniquable__Dict_Build {
  getUnique__ : a -> Unique }.

#[global] Definition Uniquable (a : Type) :=
  forall r__, (Uniquable__Dict a -> r__) -> r__.
Existing Class Uniquable.

#[global] Definition getUnique `{g__0__ : Uniquable a} : a -> Unique :=
  g__0__ _ (getUnique__ a).

(* Midamble *)

Instance Default__Name : HsToCoq.Err.Default Unique
  := HsToCoq.Err.Build_Default _ (MkUnique HsToCoq.Err.default).

Program Instance Uniquable__Word : Uniquable GHC.Num.Word :=
  fun _ k => k {| getUnique__ x := MkUnique x |}.


(* Converted value declarations: *)

#[global] Definition mkUniqueIntGrimily : BinNums.N -> Unique :=
  MkUnique GHC.Base.∘ GHC.Base.id.

#[local] Definition Uniquable__FastString_getUnique
   : FastString.FastString -> Unique :=
  fun fs => mkUniqueIntGrimily (FastString.uniqueOfFS fs).

#[global]
Program Instance Uniquable__FastString : Uniquable FastString.FastString :=
  fun _ k__ => k__ {| getUnique__ := Uniquable__FastString_getUnique |}.

#[local] Definition Uniquable__N_getUnique : BinNums.N -> Unique :=
  fun i => mkUniqueIntGrimily i.

#[global]
Program Instance Uniquable__N : Uniquable BinNums.N :=
  fun _ k__ => k__ {| getUnique__ := Uniquable__N_getUnique |}.

#[local] Definition Uniquable__ModuleName_getUnique
   : Module.ModuleName -> Unique :=
  fun '(Module.Mk_ModuleName nm) => getUnique nm.

#[global]
Program Instance Uniquable__ModuleName : Uniquable Module.ModuleName :=
  fun _ k__ => k__ {| getUnique__ := Uniquable__ModuleName_getUnique |}.

#[global] Definition eqUnique : Unique -> Unique -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique u1, MkUnique u2 => u1 GHC.Base.== u2
    end.

#[local] Definition Eq___Unique_op_zeze__ : Unique -> Unique -> bool :=
  fun a b => eqUnique a b.

#[local] Definition Eq___Unique_op_zsze__ : Unique -> Unique -> bool :=
  fun a b => negb (eqUnique a b).

#[global]
Program Instance Eq___Unique : GHC.Base.Eq_ Unique :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Unique_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Unique_op_zsze__ |}.

#[local] Definition Uniquable__Unique_getUnique : Unique -> Unique :=
  fun u => u.

#[global]
Program Instance Uniquable__Unique : Uniquable Unique :=
  fun _ k__ => k__ {| getUnique__ := Uniquable__Unique_getUnique |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Unique.Outputable__Unique' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Unique.Show__Unique' *)

#[global] Definition uNIQUE_BITS : GHC.Num.Int :=
  #56.

#[global] Definition mkUniqueGrimily : BinNums.N -> Unique :=
  MkUnique.

#[global] Definition getKey : Unique -> BinNums.N :=
  fun '(MkUnique x) => x.

#[global] Definition incrUnique : Unique -> Unique :=
  fun '(MkUnique i) => MkUnique (i GHC.Num.+ #1).

#[global] Definition stepUnique : Unique -> BinNums.N -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique i, n => MkUnique (i GHC.Num.+ n)
    end.

#[global] Definition uniqueMask : GHC.Num.Int :=
  Data.Bits.shiftL #1 uNIQUE_BITS GHC.Num.- #1.

#[global] Definition mkUnique : GHC.Char.Char -> GHC.Num.Word -> Unique :=
  fun c i =>
    let bits := Coq.ZArith.BinInt.Z.land (Coq.ZArith.BinInt.Z.of_N i) uniqueMask in
    let tag := Data.Bits.shiftL (GHC.Base.ord c) uNIQUE_BITS in
    MkUnique (Coq.ZArith.BinInt.Z.to_N (Coq.ZArith.BinInt.Z.lor tag bits)).

#[global] Definition mkLocalUnique : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "X") i.

#[global] Definition minLocalUnique : Unique :=
  mkLocalUnique #0.

#[global] Definition maxLocalUnique : Unique :=
  mkLocalUnique (Coq.ZArith.BinInt.Z.to_N uniqueMask).

(* Skipping definition `Unique.newTagUnique' *)

(* Skipping definition `Unique.mkTag' *)

#[global] Definition mkUniqueInt : GHC.Char.Char -> BinNums.N -> Unique :=
  fun c i => mkUnique c (GHC.Base.id i).

#[global] Definition unpkUnique : Unique -> GHC.Char.Char * GHC.Num.Int :=
  fun '(MkUnique u) =>
    let i := Coq.ZArith.BinInt.Z.land (Coq.ZArith.BinInt.Z.of_N u) uniqueMask in
    let tag :=
      GHC.Char.chr (Data.Bits.shiftR (Coq.ZArith.BinInt.Z.of_N u) uNIQUE_BITS) in
    pair tag i.

(* Skipping definition `Unique.isValidKnownKeyUnique' *)

#[global] Definition hasKey {a : Type} `{Uniquable a} : a -> Unique -> bool :=
  fun x k => getUnique x GHC.Base.== k.

#[global] Definition ltUnique : Unique -> Unique -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique u1, MkUnique u2 => u1 GHC.Base.< u2
    end.

#[global] Definition nonDetCmpUnique : Unique -> Unique -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique u1, MkUnique u2 =>
        if u1 GHC.Base.== u2 : bool
        then Eq
        else if u1 GHC.Base.< u2 : bool
             then Lt
             else Gt
    end.

(* Skipping definition `Unique.showUnique' *)

(* Skipping definition `Unique.pprUniqueAlways' *)

(* Skipping definition `Unique.w64ToBase62' *)

#[global] Definition getWordKey : Unique -> GHC.Num.Word :=
  getKey.

Axiom isLocalUnique : Unique -> bool.

(* External variables:
     Eq Gt Lt Type bool comparison negb op_zt__ pair BinNums.N
     Coq.ZArith.BinInt.Z.land Coq.ZArith.BinInt.Z.lor Coq.ZArith.BinInt.Z.of_N
     Coq.ZArith.BinInt.Z.to_N Data.Bits.shiftL Data.Bits.shiftR FastString.FastString
     FastString.uniqueOfFS GHC.Base.Eq_ GHC.Base.id GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zl__ GHC.Base.op_zsze____
     GHC.Base.ord GHC.Char.Char GHC.Char.chr GHC.Num.Int GHC.Num.Word
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ Module.Mk_ModuleName
     Module.ModuleName
*)
