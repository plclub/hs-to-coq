(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Bag.
Require Coq.Init.Datatypes.
Require Core.
Require Data.Foldable.
Require Data.IntSet.Internal.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require UniqFM.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UnVarSet : Type :=
  | Mk_UnVarSet : (Data.IntSet.Internal.IntSet) -> UnVarSet.

Inductive Gen : Type :=
  | CBPG : UnVarSet -> UnVarSet -> Gen
  | CG : UnVarSet -> Gen.

Inductive UnVarGraph : Type := | Mk_UnVarGraph : (Bag.Bag Gen) -> UnVarGraph.

(* Midamble *)

Instance Default_UnVarSet : HsToCoq.Err.Default UnVarSet :=
  HsToCoq.Err.Build_Default _ (Mk_UnVarSet HsToCoq.Err.default).
Instance Default_UnVarGraph : HsToCoq.Err.Default UnVarGraph :=
  HsToCoq.Err.Build_Default _ (Mk_UnVarGraph HsToCoq.Err.default).


Instance Unpeel_UnVarSet : Prim.Unpeel UnVarSet Data.IntSet.Internal.IntSet :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarSet y => y end) Mk_UnVarSet.
Instance Unpeel_UnVarGraph : Prim.Unpeel UnVarGraph (Bag.Bag Gen) :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarGraph y => y end) Mk_UnVarGraph.

(* Converted value declarations: *)

Local Definition Eq___UnVarSet_op_zeze__ : UnVarSet -> UnVarSet -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___UnVarSet_op_zsze__ : UnVarSet -> UnVarSet -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___UnVarSet : GHC.Base.Eq_ UnVarSet :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___UnVarSet_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___UnVarSet_op_zsze__ |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `UnVarGraph.Outputable__UnVarSet' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `UnVarGraph.Outputable__Gen' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `UnVarGraph.Outputable__UnVarGraph' *)

Definition k : Core.Var -> GHC.Num.Word :=
  fun v => Unique.getWordKey (Unique.getUnique v).

Definition emptyUnVarSet : UnVarSet :=
  Mk_UnVarSet Data.IntSet.Internal.empty.

Definition elemUnVarSet : Core.Var -> UnVarSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, Mk_UnVarSet s => Data.IntSet.Internal.member (k v) s
    end.

Definition isEmptyUnVarSet : UnVarSet -> bool :=
  fun '(Mk_UnVarSet s) => Data.IntSet.Internal.null s.

Definition delUnVarSet : UnVarSet -> Core.Var -> UnVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UnVarSet s, v => Mk_UnVarSet (Data.IntSet.Internal.delete (k v) s)
    end.

Definition mkUnVarSet : list Core.Var -> UnVarSet :=
  fun vs => Mk_UnVarSet (Data.IntSet.Internal.fromList (GHC.Base.map k vs)).

Definition varEnvDom {a : Type} : Core.VarEnv a -> UnVarSet :=
  fun ae => Mk_UnVarSet (UniqFM.ufmToSet_Directly ae).

Definition unionUnVarSet : UnVarSet -> UnVarSet -> UnVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UnVarSet set1, Mk_UnVarSet set2 =>
        Mk_UnVarSet (Data.IntSet.Internal.union set1 set2)
    end.

Definition unionUnVarSets : list UnVarSet -> UnVarSet :=
  Data.Foldable.foldr unionUnVarSet emptyUnVarSet.

Definition emptyUnVarGraph : UnVarGraph :=
  Mk_UnVarGraph Bag.emptyBag.

Definition unionUnVarGraph : UnVarGraph -> UnVarGraph -> UnVarGraph :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UnVarGraph g1, Mk_UnVarGraph g2 => Mk_UnVarGraph (Bag.unionBags g1 g2)
    end.

Definition unionUnVarGraphs : list UnVarGraph -> UnVarGraph :=
  Data.Foldable.foldl' unionUnVarGraph emptyUnVarGraph.

Definition prune : UnVarGraph -> UnVarGraph :=
  fun '(Mk_UnVarGraph g) =>
    let go :=
      fun arg_1__ =>
        match arg_1__ with
        | CG s => negb (isEmptyUnVarSet s)
        | CBPG s1 s2 => andb (negb (isEmptyUnVarSet s1)) (negb (isEmptyUnVarSet s2))
        end in
    Mk_UnVarGraph (Bag.filterBag go g).

Definition completeBipartiteGraph : UnVarSet -> UnVarSet -> UnVarGraph :=
  fun s1 s2 => prune (Mk_UnVarGraph (Bag.unitBag (CBPG s1 s2))).

Definition completeGraph : UnVarSet -> UnVarGraph :=
  fun s => prune (Mk_UnVarGraph (Bag.unitBag (CG s))).

Definition neighbors : UnVarGraph -> Core.Var -> UnVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UnVarGraph g, v =>
        let go :=
          fun arg_2__ =>
            match arg_2__ with
            | CG s => (if elemUnVarSet v s : bool then cons s nil else nil)
            | CBPG s1 s2 =>
                Coq.Init.Datatypes.app (if elemUnVarSet v s1 : bool
                                        then cons s2 nil
                                        else nil) (if elemUnVarSet v s2 : bool
                                        then cons s1 nil
                                        else nil)
            end in
        unionUnVarSets (Data.Foldable.concatMap go (Bag.bagToList g))
    end.

Definition delNode : UnVarGraph -> Core.Var -> UnVarGraph :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UnVarGraph g, v =>
        let go :=
          fun arg_2__ =>
            match arg_2__ with
            | CG s => CG (delUnVarSet s v)
            | CBPG s1 s2 => CBPG (delUnVarSet s1 v) (delUnVarSet s2 v)
            end in
        prune (Mk_UnVarGraph (Bag.mapBag go g))
    end.

(* External variables:
     Type andb bool cons list negb nil Bag.Bag Bag.bagToList Bag.emptyBag
     Bag.filterBag Bag.mapBag Bag.unionBags Bag.unitBag Coq.Init.Datatypes.app
     Core.Var Core.VarEnv Data.Foldable.concatMap Data.Foldable.foldl'
     Data.Foldable.foldr Data.IntSet.Internal.IntSet Data.IntSet.Internal.delete
     Data.IntSet.Internal.empty Data.IntSet.Internal.fromList
     Data.IntSet.Internal.member Data.IntSet.Internal.null Data.IntSet.Internal.union
     GHC.Base.Eq_ GHC.Base.map GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Num.Word GHC.Prim.coerce
     UniqFM.ufmToSet_Directly Unique.getUnique Unique.getWordKey
*)
