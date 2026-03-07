(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Tuple.
Require GHC.Base.
Require GHC.Types.Unique.Map.
Require Name.
Require UniqDFM.
Require UniqFM.
Import GHC.Base.Notations.

(* Converted type declarations: *)

#[global] Definition NameEnv :=
  (UniqFM.UniqFM Name.Name)%type.

#[global] Definition DNameEnv :=
  (UniqFM.UniqFM Name.Name)%type.

(* Converted value declarations: *)

(* Skipping definition `NameEnv.depAnal' *)

#[global] Definition nonDetNameEnvElts {a : Type} : NameEnv a -> list a :=
  fun x => UniqFM.nonDetEltsUFM x.

#[global] Definition emptyNameEnv {a : Type} : NameEnv a :=
  UniqFM.emptyUFM.

#[global] Definition isEmptyNameEnv {a : Type} : NameEnv a -> bool :=
  UniqFM.isNullUFM.

#[global] Definition unitNameEnv {a : Type} : Name.Name -> a -> NameEnv a :=
  fun x y => UniqFM.unitUFM x y.

#[global] Definition extendNameEnv {a : Type}
   : NameEnv a -> Name.Name -> a -> NameEnv a :=
  fun x y z => UniqFM.addToUFM x y z.

#[global] Definition extendNameEnvList {a : Type}
   : NameEnv a -> list (Name.Name * a)%type -> NameEnv a :=
  fun x l => UniqFM.addListToUFM x l.

#[global] Definition extendNameEnvListWith {a : Type}
   : (a -> Name.Name) -> NameEnv a -> list a -> NameEnv a :=
  fun f x l => UniqFM.addListToUFM x (GHC.Base.map (fun a => pair (f a) a) l).

#[global] Definition lookupNameEnv {a : Type}
   : NameEnv a -> Name.Name -> option a :=
  fun x y => UniqFM.lookupUFM x y.

#[global] Definition alterNameEnv {a : Type}
   : (option a -> option a) -> NameEnv a -> Name.Name -> NameEnv a :=
  UniqFM.alterUFM.

#[global] Definition mkNameEnv {a : Type}
   : list (Name.Name * a)%type -> NameEnv a :=
  fun l => UniqFM.listToUFM l.

#[global] Definition mkNameEnvWith {a : Type}
   : (a -> Name.Name) -> list a -> NameEnv a :=
  fun f => mkNameEnv GHC.Base.∘ GHC.Base.map (fun a => pair (f a) a).

#[global] Definition fromUniqMap {a : Type}
   : GHC.Types.Unique.Map.UniqMap Name.Name a -> NameEnv a :=
  UniqFM.mapUFM Data.Tuple.snd GHC.Base.∘ GHC.Types.Unique.Map.getUniqMap.

#[global] Definition elemNameEnv {a : Type} : Name.Name -> NameEnv a -> bool :=
  fun x y => UniqFM.elemUFM x y.

#[global] Definition plusNameEnv {a : Type}
   : NameEnv a -> NameEnv a -> NameEnv a :=
  fun x y => UniqFM.plusUFM x y.

#[global] Definition plusNameEnv_C {a : Type}
   : (a -> a -> a) -> NameEnv a -> NameEnv a -> NameEnv a :=
  fun f x y => UniqFM.plusUFM_C f x y.

#[global] Definition plusNameEnv_CD {a : Type}
   : (a -> a -> a) -> NameEnv a -> a -> NameEnv a -> a -> NameEnv a :=
  fun f x d y b => UniqFM.plusUFM_CD f x d y b.

#[global] Definition plusNameEnv_CD2 {a : Type}
   : (option a -> option a -> a) -> NameEnv a -> NameEnv a -> NameEnv a :=
  fun f x y => UniqFM.plusUFM_CD2 f x y.

#[global] Definition plusNameEnvList {a : Type}
   : list (NameEnv a) -> NameEnv a :=
  fun xs => UniqFM.plusUFMList xs.

#[global] Definition plusNameEnvListWith {a : Type}
   : (a -> a -> a) -> list (NameEnv a) -> NameEnv a :=
  fun f xs => UniqFM.plusUFMListWith f xs.

#[global] Definition extendNameEnv_C {a : Type}
   : (a -> a -> a) -> NameEnv a -> Name.Name -> a -> NameEnv a :=
  fun f x y z => UniqFM.addToUFM_C f x y z.

#[global] Definition mapNameEnv {elt1 : Type} {elt2 : Type}
   : (elt1 -> elt2) -> NameEnv elt1 -> NameEnv elt2 :=
  fun f x => UniqFM.mapUFM f x.

#[global] Definition extendNameEnv_Acc {a : Type} {b : Type}
   : (a -> b -> b) -> (a -> b) -> NameEnv b -> Name.Name -> a -> NameEnv b :=
  fun x y z a b => UniqFM.addToUFM_Acc x y z a b.

#[global] Definition extendNameEnvList_C {a : Type}
   : (a -> a -> a) -> NameEnv a -> list (Name.Name * a)%type -> NameEnv a :=
  fun x y z => UniqFM.addListToUFM_C x y z.

#[global] Definition delFromNameEnv {a : Type}
   : NameEnv a -> Name.Name -> NameEnv a :=
  fun x y => UniqFM.delFromUFM x y.

#[global] Definition delListFromNameEnv {a : Type}
   : NameEnv a -> list Name.Name -> NameEnv a :=
  fun x y => UniqFM.delListFromUFM x y.

#[global] Definition filterNameEnv {elt : Type}
   : (elt -> bool) -> NameEnv elt -> NameEnv elt :=
  fun x y => UniqFM.filterUFM x y.

#[global] Definition mapMaybeNameEnv {a : Type} {b : Type}
   : (a -> option b) -> NameEnv a -> NameEnv b :=
  fun x y => UniqFM.mapMaybeUFM x y.

#[global] Definition anyNameEnv {elt : Type}
   : (elt -> bool) -> NameEnv elt -> bool :=
  fun f x => UniqFM.nonDetFoldUFM (orb GHC.Base.∘ f) false x.

#[global] Definition disjointNameEnv {a : Type}
   : NameEnv a -> NameEnv a -> bool :=
  fun x y => UniqFM.disjointUFM x y.

#[global] Definition seqEltsNameEnv {elt : Type}
   : (elt -> unit) -> NameEnv elt -> unit :=
  fun seqElt x => UniqFM.seqEltsUFM seqElt x.

(* Skipping definition `NameEnv.lookupNameEnv_NF' *)

#[global] Definition emptyDNameEnv {a : Type} : DNameEnv a :=
  UniqFM.emptyUFM.

#[global] Definition isEmptyDNameEnv {a : Type} : DNameEnv a -> bool :=
  UniqFM.isNullUFM.

#[global] Definition lookupDNameEnv {a : Type}
   : DNameEnv a -> Name.Name -> option a :=
  UniqFM.lookupUFM.

#[global] Definition delFromDNameEnv {a : Type}
   : DNameEnv a -> Name.Name -> DNameEnv a :=
  UniqFM.delFromUFM.

#[global] Definition filterDNameEnv {a : Type}
   : (a -> bool) -> DNameEnv a -> DNameEnv a :=
  UniqFM.filterUFM.

#[global] Definition mapDNameEnv {a : Type} {b : Type}
   : (a -> b) -> DNameEnv a -> DNameEnv b :=
  UniqFM.mapUFM.

#[global] Definition adjustDNameEnv {a : Type}
   : (a -> a) -> DNameEnv a -> Name.Name -> DNameEnv a :=
  UniqDFM.adjustUDFM.

#[global] Definition alterDNameEnv {a : Type}
   : (option a -> option a) -> DNameEnv a -> Name.Name -> DNameEnv a :=
  UniqFM.alterUFM.

#[global] Definition extendDNameEnv {a : Type}
   : DNameEnv a -> Name.Name -> a -> DNameEnv a :=
  UniqFM.addToUFM.

#[global] Definition extendDNameEnv_C {a : Type}
   : (a -> a -> a) -> DNameEnv a -> Name.Name -> a -> DNameEnv a :=
  UniqFM.addToUFM_C.

#[global] Definition eltsDNameEnv {a : Type} : DNameEnv a -> list a :=
  UniqFM.eltsUFM.

#[global] Definition foldDNameEnv {a : Type} {b : Type}
   : (a -> b -> b) -> b -> DNameEnv a -> b :=
  UniqFM.nonDetFoldUFM.

#[global] Definition plusDNameEnv_C {elt : Type}
   : (elt -> elt -> elt) -> DNameEnv elt -> DNameEnv elt -> DNameEnv elt :=
  UniqFM.plusUFM_C.

#[global] Definition nonDetStrictFoldDNameEnv {a : Type} {b : Type}
   : (a -> b -> b) -> b -> DNameEnv a -> b :=
  UniqDFM.nonDetStrictFoldUDFM.

(* External variables:
     Type bool false list op_zt__ option orb pair unit Data.Tuple.snd GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Types.Unique.Map.UniqMap
     GHC.Types.Unique.Map.getUniqMap Name.Name UniqDFM.adjustUDFM
     UniqDFM.nonDetStrictFoldUDFM UniqFM.UniqFM UniqFM.addListToUFM
     UniqFM.addListToUFM_C UniqFM.addToUFM UniqFM.addToUFM_Acc UniqFM.addToUFM_C
     UniqFM.alterUFM UniqFM.delFromUFM UniqFM.delListFromUFM UniqFM.disjointUFM
     UniqFM.elemUFM UniqFM.eltsUFM UniqFM.emptyUFM UniqFM.filterUFM UniqFM.isNullUFM
     UniqFM.listToUFM UniqFM.lookupUFM UniqFM.mapMaybeUFM UniqFM.mapUFM
     UniqFM.nonDetEltsUFM UniqFM.nonDetFoldUFM UniqFM.plusUFM UniqFM.plusUFMList
     UniqFM.plusUFMListWith UniqFM.plusUFM_C UniqFM.plusUFM_CD UniqFM.plusUFM_CD2
     UniqFM.seqEltsUFM UniqFM.unitUFM
*)
