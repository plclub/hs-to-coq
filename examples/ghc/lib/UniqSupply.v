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
Require GHC.Base.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UniqSupply : Type :=
  | MkSplitUniqSupply : BinNums.N -> UniqSupply -> UniqSupply -> UniqSupply.

#[global] Definition UniqResult result :=
  (result * UniqSupply)%type%type.

Inductive UniqSM result : Type :=
  | USM (unUSM : UniqSupply -> UniqResult result) : UniqSM result.

Record MonadUnique__Dict (m : Type -> Type) := MonadUnique__Dict_Build {
  getUniqueM__ : m Unique.Unique ;
  getUniqueSupplyM__ : m UniqSupply ;
  getUniquesM__ : m (list Unique.Unique) }.

#[global] Definition MonadUnique (m : Type -> Type) `{GHC.Base.Monad m} :=
  forall r__, (MonadUnique__Dict m -> r__) -> r__.
Existing Class MonadUnique.

#[global] Definition getUniqueM `{g__0__ : MonadUnique m} : m Unique.Unique :=
  g__0__ _ (getUniqueM__ m).

#[global] Definition getUniqueSupplyM `{g__0__ : MonadUnique m}
   : m UniqSupply :=
  g__0__ _ (getUniqueSupplyM__ m).

#[global] Definition getUniquesM `{g__0__ : MonadUnique m}
   : m (list Unique.Unique) :=
  g__0__ _ (getUniquesM__ m).

Arguments USM {_} _.

#[global] Definition unUSM {result} (arg_0__ : UniqSM result) :=
  let 'USM unUSM := arg_0__ in
  unUSM.

(* Midamble *)

Instance Default__UniqSupply
   : HsToCoq.Err.Default UniqSupply.
Admitted.

(* Converted value declarations: *)

#[global] Definition mkUniqSM {a} : (UniqSupply -> UniqResult a) -> UniqSM a :=
  fun f => USM (f).

#[local] Definition Functor__UniqSM_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> UniqSM a -> UniqSM b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, USM m => mkUniqSM (fun us => let 'pair r us' := m us in pair (f r) us')
      end.

#[local] Definition Functor__UniqSM_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> UniqSM b -> UniqSM a :=
  fun {a : Type} {b : Type} => Functor__UniqSM_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__UniqSM : GHC.Base.Functor UniqSM :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__UniqSM_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__UniqSM_op_zlzd__ |}.

#[local] Definition Applicative__UniqSM_op_zlztzg__
   : forall {a : Type},
     forall {b : Type}, UniqSM (a -> b) -> UniqSM a -> UniqSM b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | USM f, USM x =>
          mkUniqSM (fun us0 =>
                      let 'pair ff us1 := f us0 in
                      let 'pair xx us2 := x us1 in
                      pair (ff xx) us2)
      end.

#[local] Definition Applicative__UniqSM_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> UniqSM a -> UniqSM b -> UniqSM c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__UniqSM_op_zlztzg__ (GHC.Base.fmap f x).

#[global] Definition thenUs_ {a} {b} : UniqSM a -> UniqSM b -> UniqSM b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | USM expr, USM cont =>
        mkUniqSM (fun us0 => let 'pair _ us1 := (expr us0) in cont us1)
    end.

#[local] Definition Applicative__UniqSM_op_ztzg__
   : forall {a : Type}, forall {b : Type}, UniqSM a -> UniqSM b -> UniqSM b :=
  fun {a : Type} {b : Type} => thenUs_.

#[global] Definition returnUs {a} : a -> UniqSM a :=
  fun result => mkUniqSM (fun us => pair result us).

#[local] Definition Applicative__UniqSM_pure
   : forall {a : Type}, a -> UniqSM a :=
  fun {a : Type} => returnUs.

#[global]
Program Instance Applicative__UniqSM : GHC.Base.Applicative UniqSM :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__UniqSM_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__UniqSM_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__UniqSM_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__UniqSM_pure |}.

#[local] Definition Monad__UniqSM_op_zgzg__
   : forall {a : Type}, forall {b : Type}, UniqSM a -> UniqSM b -> UniqSM b :=
  fun {a : Type} {b : Type} => _GHC.Base.*>_.

#[global] Definition thenUs {a} {b} : UniqSM a -> (a -> UniqSM b) -> UniqSM b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | USM expr, cont =>
        mkUniqSM (fun us0 =>
                    let 'pair result us1 := (expr us0) in
                    unUSM (cont result) us1)
    end.

#[local] Definition Monad__UniqSM_op_zgzgze__
   : forall {a : Type},
     forall {b : Type}, UniqSM a -> (a -> UniqSM b) -> UniqSM b :=
  fun {a : Type} {b : Type} => thenUs.

#[local] Definition Monad__UniqSM_return_ : forall {a : Type}, a -> UniqSM a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__UniqSM : GHC.Base.Monad UniqSM :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__UniqSM_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__UniqSM_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__UniqSM_return_ |}.

(* Skipping instance `UniqSupply.MonadFail__UniqSM' of class
   `Control.Monad.Fail.MonadFail' *)

(* Skipping all instances of class `GHC.Internal.Control.Monad.Fix.MonadFix',
   including `UniqSupply.MonadFix__UniqSM' *)

#[global] Definition takeUniqFromSupply
   : UniqSupply -> (Unique.Unique * UniqSupply)%type :=
  fun '(MkSplitUniqSupply n s1 _) => pair (Unique.mkUniqueGrimily n) s1.

#[global] Definition getUniqueUs : UniqSM Unique.Unique :=
  mkUniqSM (fun us0 => let 'pair u us1 := takeUniqFromSupply us0 in pair u us1).

#[local] Definition MonadUnique__UniqSM_getUniqueM : UniqSM Unique.Unique :=
  getUniqueUs.

#[global] Definition splitUniqSupply
   : UniqSupply -> (UniqSupply * UniqSupply)%type :=
  fun '(MkSplitUniqSupply _ s1 s2) => pair s1 s2.

#[global] Definition getUs : UniqSM UniqSupply :=
  mkUniqSM (fun us0 => let 'pair us1 us2 := splitUniqSupply us0 in pair us1 us2).

#[local] Definition MonadUnique__UniqSM_getUniqueSupplyM : UniqSM UniqSupply :=
  getUs.

Fixpoint uniqsFromSupply (arg_0__ : UniqSupply) : list Unique.Unique
  := let 'MkSplitUniqSupply n _ s2 := arg_0__ in
     cons (Unique.mkUniqueGrimily n) (uniqsFromSupply s2).

#[global] Definition getUniquesUs : UniqSM (list Unique.Unique) :=
  mkUniqSM (fun us0 =>
              let 'pair us1 us2 := splitUniqSupply us0 in
              pair (uniqsFromSupply us1) us2).

#[local] Definition MonadUnique__UniqSM_getUniquesM
   : UniqSM (list Unique.Unique) :=
  getUniquesUs.

#[global]
Program Instance MonadUnique__UniqSM : MonadUnique UniqSM :=
  fun _ k__ =>
    k__ {| getUniqueM__ := MonadUnique__UniqSM_getUniqueM ;
           getUniqueSupplyM__ := MonadUnique__UniqSM_getUniqueSupplyM ;
           getUniquesM__ := MonadUnique__UniqSM_getUniquesM |}.

(* Skipping definition `UniqSupply.mkSplitUniqSupply' *)

(* Skipping definition `UniqSupply.op_fetchAddWord64Addrzh__' *)

(* Skipping definition `UniqSupply.genSym' *)

(* Skipping definition `UniqSupply.initUniqSupply' *)

(* Skipping definition `UniqSupply.uniqFromTag' *)

Fixpoint listSplitUniqSupply (arg_0__ : UniqSupply) : list UniqSupply
  := let 'MkSplitUniqSupply _ s1 s2 := arg_0__ in
     cons s1 (listSplitUniqSupply s2).

#[global] Definition uniqFromSupply : UniqSupply -> Unique.Unique :=
  fun '(MkSplitUniqSupply n _ _) => Unique.mkUniqueGrimily n.

#[global] Definition initUs {a : Type}
   : UniqSupply -> UniqSM a -> (a * UniqSupply)%type :=
  fun init_us m => let 'pair r us := unUSM m init_us in pair r us.

#[global] Definition initUs_ {a : Type} : UniqSupply -> UniqSM a -> a :=
  fun init_us m => let 'pair r _ := unUSM m init_us in r.

#[global] Definition liftUSM {a}
   : UniqSM a -> UniqSupply -> (a * UniqSupply)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | USM m, us0 => let 'pair a us1 := m us0 in pair a us1
    end.

(* External variables:
     Type cons list op_zt__ pair BinNums.N GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.liftA2__
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____
     GHC.Base.op_zlzd____ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg__
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return___
     Unique.Unique Unique.mkUniqueGrimily
*)
