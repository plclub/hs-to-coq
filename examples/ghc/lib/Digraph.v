(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.IntSet.Internal.
Require Data.Map.Internal.
Require Data.Set.Internal.
Require GHC.Base.
Require HsToCoq.Err.
Require IntMap.
Require Unique.

(* Converted type declarations: *)

Inductive Time : Type := | Mk_Time : nat -> Time.

Axiom ReduceFn : Type -> Type -> Type.

Inductive Node key payload : Type :=
  | DigraphNode (node_payload : payload) (node_key : key) (node_dependencies
    : list key)
   : Node key payload.

#[global] Definition WorkItem key payload :=
  (Node key payload * list payload)%type%type.

Axiom IntGraph : Type.

Axiom Graph : Type -> Type.

Inductive EdgeType : Type :=
  | Forward : EdgeType
  | Cross : EdgeType
  | Backward : EdgeType
  | SelfLoop : EdgeType.

Inductive Edge node : Type := | Mk_Edge : node -> node -> Edge node.

Arguments DigraphNode {_} {_} _ _ _.

Arguments Mk_Edge {_} _ _.

Instance Default__EdgeType : HsToCoq.Err.Default EdgeType :=
  HsToCoq.Err.Build_Default _ Forward.

#[global] Definition node_dependencies {key} {payload} (arg_0__
    : Node key payload) :=
  let 'DigraphNode _ _ node_dependencies := arg_0__ in
  node_dependencies.

#[global] Definition node_key {key} {payload} (arg_0__ : Node key payload) :=
  let 'DigraphNode _ node_key _ := arg_0__ in
  node_key.

#[global] Definition node_payload {key} {payload} (arg_0__
    : Node key payload) :=
  let 'DigraphNode node_payload _ _ := arg_0__ in
  node_payload.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Time' *)

Instance Functor__Node : forall {key}, GHC.Base.Functor (Node key).
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Node' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Graph' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Edge' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__EdgeType' *)

Axiom emptyGraph : forall {a}, Graph a.

Axiom graphFromEdgedVertices : forall {key} {payload},
                               ReduceFn key payload -> list (Node key payload) -> Graph (Node key payload).

Axiom graphFromEdgedVerticesOrd : forall {key : Type},
                                  forall {payload : Type},
                                  forall `{GHC.Base.Ord key}, list (Node key payload) -> Graph (Node key payload).

Axiom graphFromEdgedVerticesUniq : forall {key : Type},
                                   forall {payload : Type},
                                   forall `{Unique.Uniquable key},
                                   list (Node key payload) -> Graph (Node key payload).

(* Skipping definition `Digraph.reduceNodesIntoVertices' *)

Axiom reduceNodesIntoVerticesOrd : forall {key} {payload},
                                   forall `{GHC.Base.Ord key}, ReduceFn key payload.

Axiom reduceNodesIntoVerticesUniq : forall {key} {payload},
                                    forall `{Unique.Uniquable key}, ReduceFn key payload.

Axiom findCycle : forall {payload : Type},
                  forall {key : Type},
                  forall `{GHC.Base.Ord key}, list (Node key payload) -> option (list payload).

(* Skipping definition `Digraph.stronglyConnCompG' *)

(* Skipping definition `Digraph.decodeSccs' *)

(* Skipping definition `Digraph.stronglyConnCompFromEdgedVerticesOrd' *)

(* Skipping definition `Digraph.stronglyConnCompFromEdgedVerticesUniq' *)

(* Skipping definition `Digraph.stronglyConnCompFromEdgedVerticesOrdR' *)

(* Skipping definition `Digraph.stronglyConnCompFromEdgedVerticesUniqR' *)

Axiom topologicalSortG : forall {node : Type}, Graph node -> list node.

Axiom reachableG : forall {node : Type}, Graph node -> node -> list node.

Axiom outgoingG : forall {node : Type}, Graph node -> node -> list node.

Axiom reachablesG : forall {node : Type}, Graph node -> list node -> list node.

Axiom allReachable : forall {key : Type},
                     forall {node : Type},
                     forall `{GHC.Base.Ord key},
                     Graph node ->
                     (node -> key) -> Data.Map.Internal.Map key (Data.Set.Internal.Set_ key).

Axiom allReachableCyclic : forall {key : Type},
                           forall {node : Type},
                           forall `{GHC.Base.Ord key},
                           Graph node ->
                           (node -> key) -> Data.Map.Internal.Map key (Data.Set.Internal.Set_ key).

Axiom all_reachable : forall {key} {node},
                      forall `{GHC.Base.Ord key},
                      (IntGraph -> IntMap.IntMap Data.IntSet.Internal.IntSet) ->
                      Graph node ->
                      (node -> key) -> Data.Map.Internal.Map key (Data.Set.Internal.Set_ key).

Axiom hasVertexG : forall {node : Type}, Graph node -> node -> bool.

Axiom verticesG : forall {node : Type}, Graph node -> list node.

Axiom edgesG : forall {node : Type}, Graph node -> list (Edge node).

Axiom transposeG : forall {node : Type}, Graph node -> Graph node.

Axiom emptyG : forall {node : Type}, Graph node -> bool.

(* Skipping definition `Digraph.graphEmpty' *)

(* Skipping definition `Digraph.preorderF' *)

(* Skipping definition `Digraph.reachable' *)

Axiom reachableGraph : IntGraph -> IntMap.IntMap Data.IntSet.Internal.IntSet.

(* Skipping definition `Digraph.scc' *)

Axiom reachableGraphCyclic : IntGraph ->
                             IntMap.IntMap Data.IntSet.Internal.IntSet.

Axiom classifyEdges : forall {key : Type},
                      forall `{Unique.Uniquable key},
                      key ->
                      (key -> list key) ->
                      list (key * key)%type -> list ((key * key)%type * EdgeType)%type.

Axiom graphFromVerticesAndAdjacency : forall {key : Type},
                                      forall {payload : Type},
                                      forall `{GHC.Base.Ord key},
                                      list (Node key payload) -> list (key * key)%type -> Graph (Node key payload).

(* External variables:
     Type bool list nat op_zt__ option Data.IntSet.Internal.IntSet
     Data.Map.Internal.Map Data.Set.Internal.Set_ GHC.Base.Functor GHC.Base.Ord
     HsToCoq.Err.Build_Default HsToCoq.Err.Default IntMap.IntMap Unique.Uniquable
*)
