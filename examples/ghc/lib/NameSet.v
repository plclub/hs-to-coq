(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Lists.List.
Require Data.Foldable.
Require GHC.Base.
Require HsToCoq.Err.
Require Name.
Require OccName.
Require OrdList.
Require UniqSet.
Import GHC.Base.Notations.

(* Converted type declarations: *)

#[global] Definition NameSet :=
  (UniqSet.UniqSet Name.Name)%type.

Inductive NonCaffySet : Type :=
  | Mk_NonCaffySet (ncs_nameSet : NameSet) : NonCaffySet.

#[global] Definition Uses :=
  NameSet%type.

#[global] Definition FreeVars :=
  NameSet%type.

#[global] Definition Defs :=
  NameSet%type.

#[global] Definition DefUse :=
  (option Defs * Uses)%type%type.

#[global] Definition DefUses :=
  (OrdList.OrdList DefUse)%type.

Instance Default__NonCaffySet : HsToCoq.Err.Default NonCaffySet :=
  HsToCoq.Err.Build_Default _ (Mk_NonCaffySet HsToCoq.Err.default).

(* Converted value declarations: *)

(* Skipping instance `NameSet.Semigroup__NonCaffySet' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `NameSet.Monoid__NonCaffySet' of class `GHC.Base.Monoid' *)

#[global] Definition isEmptyNameSet : NameSet -> bool :=
  UniqSet.isEmptyUniqSet.

#[global] Definition emptyNameSet : NameSet :=
  UniqSet.emptyUniqSet.

#[global] Definition unitNameSet : Name.Name -> NameSet :=
  UniqSet.unitUniqSet.

#[global] Definition mkNameSet : list Name.Name -> NameSet :=
  UniqSet.mkUniqSet.

#[global] Definition extendNameSetList : NameSet -> list Name.Name -> NameSet :=
  UniqSet.addListToUniqSet.

#[global] Definition extendNameSet : NameSet -> Name.Name -> NameSet :=
  UniqSet.addOneToUniqSet.

#[global] Definition unionNameSet : NameSet -> NameSet -> NameSet :=
  UniqSet.unionUniqSets.

#[global] Definition unionNameSets : list NameSet -> NameSet :=
  UniqSet.unionManyUniqSets.

#[global] Definition minusNameSet : NameSet -> NameSet -> NameSet :=
  UniqSet.minusUniqSet.

#[global] Definition elemNameSet : Name.Name -> NameSet -> bool :=
  UniqSet.elementOfUniqSet.

#[global] Definition delFromNameSet : NameSet -> Name.Name -> NameSet :=
  UniqSet.delOneFromUniqSet.

#[global] Definition filterNameSet
   : (Name.Name -> bool) -> NameSet -> NameSet :=
  UniqSet.filterUniqSet.

#[global] Definition intersectNameSet : NameSet -> NameSet -> NameSet :=
  UniqSet.intersectUniqSets.

#[global] Definition disjointNameSet : NameSet -> NameSet -> bool :=
  UniqSet.disjointUniqSets.

#[global] Definition delListFromNameSet
   : NameSet -> list Name.Name -> NameSet :=
  fun set ns => Data.Foldable.foldl' delFromNameSet set ns.

#[global] Definition intersectsNameSet : NameSet -> NameSet -> bool :=
  fun s1 s2 => negb (disjointNameSet s1 s2).

#[global] Definition nameSetAny : (Name.Name -> bool) -> NameSet -> bool :=
  UniqSet.uniqSetAny.

#[global] Definition nameSetAll : (Name.Name -> bool) -> NameSet -> bool :=
  UniqSet.uniqSetAll.

(* Skipping definition `NameSet.nameSetElemsStable' *)

#[global] Definition isEmptyFVs : NameSet -> bool :=
  isEmptyNameSet.

#[global] Definition emptyFVs : FreeVars :=
  emptyNameSet.

#[global] Definition plusFVs : list FreeVars -> FreeVars :=
  unionNameSets.

#[global] Definition plusFV : FreeVars -> FreeVars -> FreeVars :=
  unionNameSet.

#[global] Definition mkFVs : list Name.Name -> FreeVars :=
  mkNameSet.

#[global] Definition addOneFV : FreeVars -> Name.Name -> FreeVars :=
  extendNameSet.

#[global] Definition unitFV : Name.Name -> FreeVars :=
  unitNameSet.

#[global] Definition delFV : Name.Name -> FreeVars -> FreeVars :=
  fun n s => delFromNameSet s n.

#[global] Definition delFVs : list Name.Name -> FreeVars -> FreeVars :=
  fun ns s => delListFromNameSet s ns.

#[global] Definition intersectFVs : FreeVars -> FreeVars -> FreeVars :=
  intersectNameSet.

#[global] Definition intersectsFVs : FreeVars -> FreeVars -> bool :=
  intersectsNameSet.

#[global] Definition emptyDUs : DefUses :=
  OrdList.nilOL.

#[global] Definition usesOnly : Uses -> DefUses :=
  fun uses => OrdList.unitOL (pair None uses).

#[global] Definition mkDUs : list (Defs * Uses)%type -> DefUses :=
  fun pairs =>
    OrdList.toOL (let cont_0__ arg_1__ :=
                    let 'pair defs uses := arg_1__ in
                    cons (pair (Some defs) uses) nil in
                  Coq.Lists.List.flat_map cont_0__ pairs).

#[global] Definition plusDU : DefUses -> DefUses -> DefUses :=
  OrdList.appOL.

#[global] Definition duDefs : DefUses -> Defs :=
  fun dus =>
    let get :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair None _u1, d2 => d2
        | pair (Some d1) _u1, d2 => unionNameSet d1 d2
        end in
    Data.Foldable.foldr get emptyNameSet dus.

#[global] Definition allUses : DefUses -> Uses :=
  fun dus =>
    let get :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair _d1 u1, u2 => unionNameSet u1 u2
        end in
    Data.Foldable.foldr get emptyNameSet dus.

#[global] Definition duUses : DefUses -> Uses :=
  fun dus =>
    let get :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair None rhs_uses, uses => unionNameSet rhs_uses uses
        | pair (Some defs) rhs_uses, uses =>
            minusNameSet (unionNameSet rhs_uses uses) defs
        end in
    Data.Foldable.foldr get emptyNameSet dus.

#[global] Definition findUses : DefUses -> Uses -> Uses :=
  fun dus uses =>
    let get :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair None rhs_uses, uses => unionNameSet rhs_uses uses
        | pair (Some defs) rhs_uses, uses =>
            if orb (intersectsNameSet defs uses) (nameSetAny (OccName.startsWithUnderscore
                                                              GHC.Base.∘
                                                              Name.nameOccName) defs) : bool
            then unionNameSet rhs_uses uses else
            uses
        end in
    Data.Foldable.foldr get uses dus.

(* External variables:
     None Some bool cons list negb nil op_zt__ option orb pair
     Coq.Lists.List.flat_map Data.Foldable.foldl' Data.Foldable.foldr
     GHC.Base.op_z2218U__ HsToCoq.Err.Build_Default HsToCoq.Err.Default
     HsToCoq.Err.default Name.Name Name.nameOccName OccName.startsWithUnderscore
     OrdList.OrdList OrdList.appOL OrdList.nilOL OrdList.toOL OrdList.unitOL
     UniqSet.UniqSet UniqSet.addListToUniqSet UniqSet.addOneToUniqSet
     UniqSet.delOneFromUniqSet UniqSet.disjointUniqSets UniqSet.elementOfUniqSet
     UniqSet.emptyUniqSet UniqSet.filterUniqSet UniqSet.intersectUniqSets
     UniqSet.isEmptyUniqSet UniqSet.minusUniqSet UniqSet.mkUniqSet
     UniqSet.unionManyUniqSets UniqSet.unionUniqSets UniqSet.uniqSetAll
     UniqSet.uniqSetAny UniqSet.unitUniqSet
*)
