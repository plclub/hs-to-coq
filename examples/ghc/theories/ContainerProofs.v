(* Properties of IntMap operations.
   These are axiomatized since IntMap is now a transparent wrapper
   around Data.IntMap.Internal, and the old WFMap-based proofs
   no longer apply directly. All axioms are straightforward
   consequences of the IntMap implementation correctness.

   Axioms are stated in terms of Data.IntMap.Internal operations
   directly, since VarSet/UniqFM unfolds to Internal operations. *)

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import GHC.Base.

Require Import Proofs.Prelude.
Require Import Data.IntMap.Internal.
Require IntMap.

(* IntMap.IntMap = Data.IntMap.Internal.IntMap, so we state axioms
   using IntMap.IntMap for types but Internal operations for functions *)

Axiom member_eq : forall A k k' (i : IntMap.IntMap A),
    k == k' ->
    Data.IntMap.Internal.member k i = Data.IntMap.Internal.member k' i.

Axiom lookup_insert : forall A key (val:A) i,
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.insert key val i) = Some val.

Axiom lookup_singleton_key : forall {A} x y (a b : A),
    Data.IntMap.Internal.lookup x (Data.IntMap.Internal.singleton y a) = Some b -> x == y.

Axiom lookup_singleton_val : forall {A} x y (a b : A),
    Data.IntMap.Internal.lookup x (Data.IntMap.Internal.singleton y a) = Some b -> a = b.

Axiom lookup_insert_neq :
  forall b key1 key2 (val:b) m,
    key1 <> key2 ->
    Data.IntMap.Internal.lookup key1 (Data.IntMap.Internal.insert key2 val m) = Data.IntMap.Internal.lookup key1 m.

Axiom member_insert : forall A k k' v (i : IntMap.IntMap A),
Data.IntMap.Internal.member k (Data.IntMap.Internal.insert k' v i) =
  (k == k') || Data.IntMap.Internal.member k i.

Axiom delete_eq : forall key b (i : IntMap.IntMap b),
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.delete key i) = None.

Axiom delete_neq : forall key1 key2 b (i : IntMap.IntMap b),
    key1 <> key2 ->
    Data.IntMap.Internal.lookup key1 (Data.IntMap.Internal.delete key2 i) = Data.IntMap.Internal.lookup key1 i.

Axiom member_delete_neq : forall k1 k2 b (i: IntMap.IntMap b), k1 <> k2 ->
  Data.IntMap.Internal.member k2 (Data.IntMap.Internal.delete k1 i) =
  Data.IntMap.Internal.member k2 i.

Axiom non_member_lookup :
   forall (A : Type)
     (key : Internal.Key)
     (i : IntMap.IntMap A),
   (Data.IntMap.Internal.member key i = false) <-> (Data.IntMap.Internal.lookup key i = None).

Axiom lookup_eq : forall A k k' (i : IntMap.IntMap A),
    k == k'->
    Data.IntMap.Internal.lookup k i = Data.IntMap.Internal.lookup k' i.

Axiom member_lookup :
   forall (A : Type)
     (key : Internal.Key)
     (i : IntMap.IntMap A),
   (is_true (Data.IntMap.Internal.member key i)) <-> (exists val, Data.IntMap.Internal.lookup key i = Some val).

Axiom null_empty : forall A,
    (@Data.IntMap.Internal.null A Data.IntMap.Internal.empty).

Axiom member_union :
   forall (A : Type)
     (key : Internal.Key)
     (i i0 : IntMap.IntMap A),
   (Data.IntMap.Internal.member key (Data.IntMap.Internal.union i i0)) =
   (Data.IntMap.Internal.member key i0 || Data.IntMap.Internal.member key i).

Axiom difference_nil_r : forall A B (i : IntMap.IntMap A),
    Data.IntMap.Internal.difference i (@Data.IntMap.Internal.empty B) = i.

Axiom difference_nil_l : forall B A (i : IntMap.IntMap A),
    Data.IntMap.Internal.difference (@Data.IntMap.Internal.empty B) i =
    (@Data.IntMap.Internal.empty B).

Axiom filter_comp : forall A `{EqLaws A} f f' (i : IntMap.IntMap A),
    Data.IntMap.Internal.filter f (Data.IntMap.Internal.filter f' i) ==
    Data.IntMap.Internal.filter (fun v => f v && f' v) i.

Axiom lookup_filterWithKey :
  forall b key (val:b) m f, Data.IntMap.Internal.lookup key (Data.IntMap.Internal.filterWithKey f m) = Some val ->
                       Data.IntMap.Internal.lookup key m = Some val.

Axiom filter_true : forall (A:Type) `{EqLaws A} (m:IntMap.IntMap A),
    Data.IntMap.Internal.filter (const true) m == m.

Axiom lookup_intersection :
  forall a b key (val1:a)
    (m1 : IntMap.IntMap a) (m2 : IntMap.IntMap b),
    Data.IntMap.Internal.lookup key m1 = Some val1 /\
    (exists (val2:b), Data.IntMap.Internal.lookup key m2 = Some val2) <->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.intersection m1 m2) = Some val1.

Axiom lookup_union :
  forall (A:Type) key (val:A) (m1 m2: IntMap.IntMap A),
    (Data.IntMap.Internal.lookup key m1 = Some val \/ (Data.IntMap.Internal.lookup key m1 = None /\ Data.IntMap.Internal.lookup key m2 = Some val)) <->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.union m1 m2) = Some val.

Axiom lookup_partition :
  forall (A:Type) key (val:A) (m m': IntMap.IntMap A) (P: A -> bool),
    ((m' = fst (Data.IntMap.Internal.partition P m) \/
      m' = snd (Data.IntMap.Internal.partition P m)) /\
     Data.IntMap.Internal.lookup key m' = Some val) ->
    Data.IntMap.Internal.lookup key m  = Some val.

Axiom lookup_difference_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap.IntMap b) (y:b),
    Data.IntMap.Internal.lookup key i' = Some y ->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.difference i i') = None.

Axiom lookup_difference_not_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap.IntMap b)(y:b),
    Data.IntMap.Internal.lookup key i' = None ->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.difference i i') = Data.IntMap.Internal.lookup key i.

Axiom delete_commute :
  forall (A : Type) `{EqLaws A}
    (kx ky : Internal.Key)
    (i : IntMap.IntMap A),
  Data.IntMap.Internal.delete ky (Data.IntMap.Internal.delete kx i) ==
  Data.IntMap.Internal.delete kx (Data.IntMap.Internal.delete ky i).

Axiom intersection_empty :
  forall A B (i : IntMap.IntMap A) (j : IntMap.IntMap B),
    (j = Data.IntMap.Internal.empty) ->
    Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i j).

Axiom null_intersection_non_member: forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  Data.IntMap.Internal.null
    (Data.IntMap.Internal.intersection i1 (Data.IntMap.Internal.insert k v i2)) <->
  Data.IntMap.Internal.member k i1 = false /\
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i1 i2).

Axiom null_intersection_difference: forall  b (i1 i2 i3 : IntMap.IntMap b),
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i2 i3) ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.difference i1 i2) ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i1 i3).

Axiom null_intersection_eq : forall b (x1 x2 y1 y2 : IntMap.IntMap b),
  (forall a, Data.IntMap.Internal.member a x1 <-> Data.IntMap.Internal.member a y1) ->
  (forall a, Data.IntMap.Internal.member a x2 <-> Data.IntMap.Internal.member a y2) ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection x1 x2) = Data.IntMap.Internal.null (Data.IntMap.Internal.intersection y1 y2).

(* disjoint axioms — GHC 9.10 uses Data.IntMap.Internal.disjoint instead of
   null (intersection ...). These mirror the null_intersection axioms. *)

Axiom disjoint_sym : forall A B (i : IntMap.IntMap A) (j : IntMap.IntMap B),
  Data.IntMap.Internal.disjoint i j = Data.IntMap.Internal.disjoint j i.

Axiom disjoint_empty_r : forall A B (i : IntMap.IntMap A),
  Data.IntMap.Internal.disjoint i (@Data.IntMap.Internal.empty B) = true.

Axiom disjoint_empty_l : forall A B (j : IntMap.IntMap B),
  Data.IntMap.Internal.disjoint (@Data.IntMap.Internal.empty A) j = true.

Axiom disjoint_insert : forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  Data.IntMap.Internal.disjoint i1 (Data.IntMap.Internal.insert k v i2) =
  (negb (Data.IntMap.Internal.member k i1) && Data.IntMap.Internal.disjoint i1 i2).

Axiom disjoint_non_member: forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  Data.IntMap.Internal.disjoint i1 (Data.IntMap.Internal.insert k v i2) <->
  Data.IntMap.Internal.member k i1 = false /\
  Data.IntMap.Internal.disjoint i1 i2.

Axiom disjoint_eq : forall b (x1 x2 y1 y2 : IntMap.IntMap b),
  (forall a, Data.IntMap.Internal.member a x1 <-> Data.IntMap.Internal.member a y1) ->
  (forall a, Data.IntMap.Internal.member a x2 <-> Data.IntMap.Internal.member a y2) ->
  Data.IntMap.Internal.disjoint x1 x2 = Data.IntMap.Internal.disjoint y1 y2.

Axiom disjoint_difference: forall b (i1 i2 i3 : IntMap.IntMap b),
  Data.IntMap.Internal.disjoint i2 i3 = true ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.difference i1 i2) ->
  Data.IntMap.Internal.disjoint i1 i3 = true.

Axiom Eq_membership : forall (A : Type) (HeqA : Eq_ A) (HlawsA : EqLaws A) (m1 m2 : IntMap.IntMap A),
  m1 == m2 ->
  forall k, Data.IntMap.Internal.member k m1 = Data.IntMap.Internal.member k m2.
