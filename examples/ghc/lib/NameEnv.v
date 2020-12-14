(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require Name.
Require UniqFM.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition NameEnv :=
  UniqFM.UniqFM%type.

Definition DNameEnv :=
  UniqFM.UniqFM%type.

(* Converted value declarations: *)

(* Skipping definition `NameEnv.depAnal' *)

Definition nameEnvElts {a : Type} : NameEnv a -> list a :=
  fun x => UniqFM.eltsUFM x.

Definition emptyNameEnv {a : Type} : NameEnv a :=
  UniqFM.emptyUFM.

Definition isEmptyNameEnv {a : Type} : NameEnv a -> bool :=
  UniqFM.isNullUFM.

Definition unitNameEnv {a : Type} : Name.Name -> a -> NameEnv a :=
  fun x y => UniqFM.unitUFM x y.

Definition extendNameEnv {a : Type}
   : NameEnv a -> Name.Name -> a -> NameEnv a :=
  fun x y z => UniqFM.addToUFM x y z.

Definition extendNameEnvList {a : Type}
   : NameEnv a -> list (Name.Name * a)%type -> NameEnv a :=
  fun x l => UniqFM.addListToUFM x l.

Definition lookupNameEnv {a : Type} : NameEnv a -> Name.Name -> option a :=
  fun x y => UniqFM.lookupUFM x y.

Definition alterNameEnv {a : Type}
   : (option a -> option a) -> NameEnv a -> Name.Name -> NameEnv a :=
  UniqFM.alterUFM.

Definition mkNameEnv {a : Type} : list (Name.Name * a)%type -> NameEnv a :=
  fun l => UniqFM.listToUFM l.

Definition elemNameEnv {a : Type} : Name.Name -> NameEnv a -> bool :=
  fun x y => UniqFM.elemUFM x y.

Definition plusNameEnv {a : Type} : NameEnv a -> NameEnv a -> NameEnv a :=
  fun x y => UniqFM.plusUFM x y.

Definition plusNameEnv_C {a : Type}
   : (a -> a -> a) -> NameEnv a -> NameEnv a -> NameEnv a :=
  fun f x y => UniqFM.plusUFM_C f x y.

Definition extendNameEnv_C {a : Type}
   : (a -> a -> a) -> NameEnv a -> Name.Name -> a -> NameEnv a :=
  fun f x y z => UniqFM.addToUFM_C f x y z.

Definition mapNameEnv {elt1 : Type} {elt2 : Type}
   : (elt1 -> elt2) -> NameEnv elt1 -> NameEnv elt2 :=
  fun f x => UniqFM.mapUFM f x.

Definition extendNameEnv_Acc {a : Type} {b : Type}
   : (a -> b -> b) -> (a -> b) -> NameEnv b -> Name.Name -> a -> NameEnv b :=
  fun x y z a b => UniqFM.addToUFM_Acc x y z a b.

Definition extendNameEnvList_C {a : Type}
   : (a -> a -> a) -> NameEnv a -> list (Name.Name * a)%type -> NameEnv a :=
  fun x y z => UniqFM.addListToUFM_C x y z.

Definition delFromNameEnv {a : Type} : NameEnv a -> Name.Name -> NameEnv a :=
  fun x y => UniqFM.delFromUFM x y.

Definition delListFromNameEnv {a : Type}
   : NameEnv a -> list Name.Name -> NameEnv a :=
  fun x y => UniqFM.delListFromUFM x y.

Definition filterNameEnv {elt : Type}
   : (elt -> bool) -> NameEnv elt -> NameEnv elt :=
  fun x y => UniqFM.filterUFM x y.

Definition anyNameEnv {elt : Type} : (elt -> bool) -> NameEnv elt -> bool :=
  fun f x => UniqFM.foldUFM (orb GHC.Base.∘ f) false x.

Definition disjointNameEnv {a : Type} : NameEnv a -> NameEnv a -> bool :=
  fun x y => UniqFM.isNullUFM (UniqFM.intersectUFM x y).

(* Skipping definition `NameEnv.lookupNameEnv_NF' *)

Definition emptyDNameEnv {a : Type} : DNameEnv a :=
  UniqFM.emptyUFM.

Definition lookupDNameEnv {a : Type} : DNameEnv a -> Name.Name -> option a :=
  UniqFM.lookupUFM.

Definition mapDNameEnv {a : Type} {b : Type}
   : (a -> b) -> DNameEnv a -> DNameEnv b :=
  UniqFM.mapUFM.

Definition alterDNameEnv {a : Type}
   : (option a -> option a) -> DNameEnv a -> Name.Name -> DNameEnv a :=
  UniqFM.alterUFM.

(* External variables:
     Type bool false list op_zt__ option orb GHC.Base.op_z2218U__ Name.Name
     UniqFM.UniqFM UniqFM.addListToUFM UniqFM.addListToUFM_C UniqFM.addToUFM
     UniqFM.addToUFM_Acc UniqFM.addToUFM_C UniqFM.alterUFM UniqFM.delFromUFM
     UniqFM.delListFromUFM UniqFM.elemUFM UniqFM.eltsUFM UniqFM.emptyUFM
     UniqFM.filterUFM UniqFM.foldUFM UniqFM.intersectUFM UniqFM.isNullUFM
     UniqFM.listToUFM UniqFM.lookupUFM UniqFM.mapUFM UniqFM.plusUFM UniqFM.plusUFM_C
     UniqFM.unitUFM
*)
