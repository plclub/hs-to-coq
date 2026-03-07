(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Core.
Require Data.Foldable.
Require GHC.Base.
Require GHC.Data.Word64Set.Internal.
Require GHC.Num.
Require UniqFM.
Require Unique.

(* Converted type declarations: *)

Inductive UnVarSet : Type :=
  | Mk_UnVarSet : GHC.Data.Word64Set.Internal.Word64Set -> UnVarSet.

Inductive UnVarGraph : Type :=
  | CBPG : UnVarSet -> UnVarSet -> UnVarGraph
  | CG : UnVarSet -> UnVarGraph
  | Union : UnVarGraph -> UnVarGraph -> UnVarGraph
  | Del : UnVarSet -> UnVarGraph -> UnVarGraph.

(* Midamble *)

#[global] Instance Default_UnVarSet : HsToCoq.Err.Default UnVarSet :=
  HsToCoq.Err.Build_Default _ (Mk_UnVarSet HsToCoq.Err.default).
#[global] Instance Default_UnVarGraph : HsToCoq.Err.Default UnVarGraph :=
  HsToCoq.Err.Build_Default _ (CG HsToCoq.Err.default).


#[global] Instance Unpeel_UnVarSet : HsToCoq.Unpeel.Unpeel UnVarSet Data.IntSet.Internal.IntSet :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarSet y => y end) Mk_UnVarSet.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `UnVarGraph.Outputable__UnVarSet' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `UnVarGraph.Outputable__UnVarGraph' *)

#[global] Definition k : Core.Var -> GHC.Num.Word :=
  fun v => Unique.getWordKey (Unique.getUnique v).

#[global] Definition domUFMUnVarSet {key : Type} {elt : Type}
   : UniqFM.UniqFM key elt -> UnVarSet :=
  fun ae => Mk_UnVarSet (UniqFM.ufmToSet_Directly ae).

#[global] Definition emptyUnVarSet : UnVarSet :=
  Mk_UnVarSet GHC.Data.Word64Set.Internal.empty.

#[global] Definition elemUnVarSet : Core.Var -> UnVarSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, Mk_UnVarSet s => GHC.Data.Word64Set.Internal.member (k v) s
    end.

#[global] Definition isEmptyUnVarSet : UnVarSet -> bool :=
  fun '(Mk_UnVarSet s) => GHC.Data.Word64Set.Internal.null s.

#[global] Definition delUnVarSet : UnVarSet -> Core.Var -> UnVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UnVarSet s, v => Mk_UnVarSet (GHC.Data.Word64Set.Internal.delete (k v) s)
    end.

#[global] Definition minusUnVarSet : UnVarSet -> UnVarSet -> UnVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UnVarSet s, Mk_UnVarSet s' =>
        Mk_UnVarSet (GHC.Data.Word64Set.Internal.difference s s')
    end.

#[global] Definition mkUnVarSet : list Core.Var -> UnVarSet :=
  fun vs =>
    Mk_UnVarSet (GHC.Data.Word64Set.Internal.fromList (GHC.Base.map k vs)).

#[global] Definition delUnVarSetList : UnVarSet -> list Core.Var -> UnVarSet :=
  fun s vs => minusUnVarSet s (mkUnVarSet vs).

#[global] Definition sizeUnVarSet : UnVarSet -> nat :=
  fun '(Mk_UnVarSet s) => BinNat.N.to_nat (GHC.Data.Word64Set.Internal.size s).

#[global] Definition extendUnVarSet : Core.Var -> UnVarSet -> UnVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, Mk_UnVarSet s => Mk_UnVarSet (GHC.Data.Word64Set.Internal.insert (k v) s)
    end.

#[global] Definition unionUnVarSet : UnVarSet -> UnVarSet -> UnVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UnVarSet set1, Mk_UnVarSet set2 =>
        Mk_UnVarSet (GHC.Data.Word64Set.Internal.union set1 set2)
    end.

#[global] Definition extendUnVarSetList
   : list Core.Var -> UnVarSet -> UnVarSet :=
  fun vs s => unionUnVarSet s (mkUnVarSet vs).

#[global] Definition unionUnVarSets : list UnVarSet -> UnVarSet :=
  Data.Foldable.foldl' (GHC.Base.flip unionUnVarSet) emptyUnVarSet.

#[global] Definition emptyUnVarGraph : UnVarGraph :=
  CG emptyUnVarSet.

#[global] Definition is_null : UnVarGraph -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CBPG s1 s2 => orb (isEmptyUnVarSet s1) (isEmptyUnVarSet s2)
    | CG s => isEmptyUnVarSet s
    | _ => false
    end.

#[global] Definition unionUnVarGraph : UnVarGraph -> UnVarGraph -> UnVarGraph :=
  fun a b =>
    if is_null a : bool then b else
    if is_null b : bool then a else
    Union a b.

#[global] Definition unionUnVarGraphs : list UnVarGraph -> UnVarGraph :=
  Data.Foldable.foldl' unionUnVarGraph emptyUnVarGraph.

#[global] Definition prune : UnVarGraph -> UnVarGraph :=
  let go : UnVarSet -> UnVarGraph -> UnVarGraph :=
    fix go (arg_0__ : UnVarSet) (arg_1__ : UnVarGraph) : UnVarGraph
      := match arg_0__, arg_1__ with
         | dels, Del dels' g => go (unionUnVarSet dels dels') g
         | dels, Union g1 g2 =>
             let g2' := go dels g2 in
             let g1' := go dels g1 in
             if is_null g1' : bool then g2' else
             if is_null g2' : bool then g1' else
             Union g1' g2'
         | dels, CG s => CG (minusUnVarSet s dels)
         | dels, CBPG s1 s2 => CBPG (minusUnVarSet s1 dels) (minusUnVarSet s2 dels)
         end in
  go emptyUnVarSet.

#[global] Definition completeBipartiteGraph
   : UnVarSet -> UnVarSet -> UnVarGraph :=
  fun s1 s2 => prune (CBPG s1 s2).

#[global] Definition completeGraph : UnVarSet -> UnVarGraph :=
  fun s => prune (CG s).

#[global] Definition neighbors : UnVarGraph -> Core.Var -> UnVarSet :=
  let fix go arg_0__ arg_1__
    := match arg_0__, arg_1__ with
       | Del d g, v =>
           if elemUnVarSet v d : bool then emptyUnVarSet else
           minusUnVarSet (go g v) d
       | Union g1 g2, v => unionUnVarSet (go g1 v) (go g2 v)
       | CG s, v => if elemUnVarSet v s : bool then s else emptyUnVarSet
       | CBPG s1 s2, v =>
           unionUnVarSet (if elemUnVarSet v s1 : bool
                          then s2
                          else emptyUnVarSet) (if elemUnVarSet v s2 : bool
                          then s1
                          else emptyUnVarSet)
       end in
  go.

#[global] Definition hasLoopAt : UnVarGraph -> Core.Var -> bool :=
  let fix go arg_0__ arg_1__
    := match arg_0__, arg_1__ with
       | Del d g, v => if elemUnVarSet v d : bool then false else go g v
       | Union g1 g2, v => orb (go g1 v) (go g2 v)
       | CG s, v => elemUnVarSet v s
       | CBPG s1 s2, v => andb (elemUnVarSet v s1) (elemUnVarSet v s2)
       end in
  go.

#[global] Definition delNode : UnVarGraph -> Core.Var -> UnVarGraph :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Del d g, v => Del (extendUnVarSet v d) g
    | g, v =>
        if is_null g : bool then emptyUnVarGraph else
        Del (mkUnVarSet (cons v nil)) g
    end.

(* External variables:
     Type andb bool cons false list nat nil orb Core.Var Data.Foldable.foldl'
     GHC.Base.flip GHC.Base.map GHC.Data.Word64Set.Internal.Word64Set
     GHC.Data.Word64Set.Internal.delete GHC.Data.Word64Set.Internal.difference
     GHC.Data.Word64Set.Internal.empty GHC.Data.Word64Set.Internal.fromList
     GHC.Data.Word64Set.Internal.insert GHC.Data.Word64Set.Internal.member
     GHC.Data.Word64Set.Internal.null GHC.Data.Word64Set.Internal.size
     GHC.Data.Word64Set.Internal.union GHC.Num.Word UniqFM.UniqFM
     UniqFM.ufmToSet_Directly Unique.getUnique Unique.getWordKey
*)
