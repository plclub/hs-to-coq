Require Import GHC.Base.     Import GHC.Base.Notations.
Require Import Data.Functor. Import Data.Functor.Notations.

Require Import TrieMap.

Require UniqFM.

From Coq Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Class TrieMapLaws (m : Type -> Type) `{TM : TrieMap m} : Prop :=
  { tml_empty {a} k :
      lookupTM k emptyTM = None :> option a
  
  ; tml_alter_here {a} k (f : XT a) tm :
      lookupTM k (alterTM k f tm) = f (lookupTM k tm)
  
  ; tml_alter_there {a} k (f : XT a) tm k' :
      k <> k' -> lookupTM k' (alterTM k f tm) = lookupTM k' tm
  
  ; tml_fold_in {a} (tm : m a) v :
      In v (foldTM cons tm nil) <-> exists k, lookupTM k tm = Some v
  
  ; tml_fold_via_list {a b} (f : a -> b -> b) tm z :
      foldTM f tm z = foldr f z (foldTM cons tm nil) }.

Theorem tml_insert_here `{TML : TrieMapLaws m} {a} k v (tm : m a) :
  lookupTM k (insertTM k v tm) = Some v.
Proof. by rewrite /insertTM tml_alter_here. Qed.

Theorem tml_insert_there `{TML : TrieMapLaws m} {a} k v (tm : m a) k' :
  k <> k' ->
  lookupTM k' (insertTM k v tm) = lookupTM k' tm.
Proof. by move=> NEQ; rewrite /insertTM tml_alter_there. Qed.

Theorem tml_delete_here `{TML : TrieMapLaws m} {a} k (tm : m a) :
  lookupTM k (deleteTM k tm) = None.
Proof. by rewrite /deleteTM tml_alter_here. Qed.

Theorem tml_delete_there `{TML : TrieMapLaws m} {a} k (tm : m a) k' :
  k <> k' ->
  lookupTM k' (deleteTM k tm) = lookupTM k' tm.
Proof. by move=> NEQ; rewrite /deleteTM tml_alter_there. Qed.

(* BLOCKER (TrieMapLaws__Map): Map operations (lookup, alter, empty, foldr)
   are concrete, but proving the 5 laws requires:
   - tml_empty: lookup k empty = None. Needs Map.lookup_empty lemma.
   - tml_alter_here/there: lookup k (alter k f m) = f (lookup k m) and
     lookup k' (alter k f m) = lookup k' m for k<>k'. Needs alter_Desc
     from containers/theories/MapProofs but in a lookup-oriented form.
   - tml_fold_in/fold_via_list: Properties of Map.foldr. Needs foldr_spec
     from MapProofs/ToListProofs.v adapted to the TrieMap formulation.
   FEASIBLE but requires ~200 lines of glue lemmas connecting containers
   proof infrastructure to the TrieMap interface. *)
Instance TrieMapLaws__Map          {k} `{GHC.Base.Ord k}                        : TrieMapLaws (Data.Map.Internal.Map k).   Admitted.

(* BLOCKER (TrieMapLaws__IntMap): IntMap operations are concrete.
   - tml_empty: IntMap.lookup k IntMap.empty = None. Straightforward.
   - tml_alter_here/there: IntMap.lookup k (IntMap.alter f k m) = f (IntMap.lookup k m).
     Needs IntMap alter/lookup interaction lemmas (not yet in IntSetProofs
     or IntMapProofs — those focus on member/insert/delete/union).
   - tml_fold_in/fold_via_list: Properties of IntMap.foldr. The same
     foldr unfolding issue as VarSetFSet's bridge lemmas (memory exhaustion).
   PARTIALLY FEASIBLE: empty + alter laws likely provable; fold laws blocked. *)
Instance TrieMapLaws__IntMap                                                    : TrieMapLaws IntMap.IntMap. Admitted.

Instance TrieMapLaws__MaybeMap     {m} `{TrieMapLaws m}                         : TrieMapLaws (MaybeMap m).
Proof.
  constructor.
  - (* tml_empty *)
    intros a [k|]; simpl; unfold lkMaybe, op_zgzizg__, mm_just.
    + apply tml_empty.
    + reflexivity.
  - (* tml_alter_here *)
    intros a [k|] f [mn mj]; simpl; unfold lkMaybe, xtMaybe, op_zgzizg__, mm_just, mm_nothing, op_zbzg__.
    + apply tml_alter_here.
    + reflexivity.
  - (* tml_alter_there *)
    intros a [k|] f [mn mj] [k'|] NEQ; simpl;
      unfold lkMaybe, xtMaybe, op_zgzizg__, mm_just, mm_nothing, op_zbzg__.
    + apply tml_alter_there. congruence.
    + reflexivity.
    + reflexivity.
    + exfalso. apply NEQ. reflexivity.
  - (* tml_fold_in *)
    intros a [mn mj] v.
    simpl. unfold fdMaybe, foldMaybe, GHC.Base.op_z2218U__, mm_nothing, mm_just.
    split.
    + intro HIn. destruct mn as [a0|].
      * simpl in HIn. destruct HIn as [->|HIn].
        -- exists None. reflexivity.
        -- apply tml_fold_in in HIn. destruct HIn as [k Hk].
           exists (Some k). simpl. unfold lkMaybe, op_zgzizg__, mm_just. exact Hk.
      * apply tml_fold_in in HIn. destruct HIn as [k Hk].
        exists (Some k). simpl. unfold lkMaybe, op_zgzizg__, mm_just. exact Hk.
    + intros [[k|] Hk]; simpl in Hk.
      * unfold lkMaybe, op_zgzizg__, mm_just in Hk.
        destruct mn as [a0|]; simpl.
        -- right. apply tml_fold_in. eauto.
        -- apply tml_fold_in. eauto.
      * destruct mn as [a0|]; simpl.
        -- left. congruence.
        -- congruence.
  - (* tml_fold_via_list *)
    intros a b f [mn mj] z.
    (* MaybeMap foldTM unfolds to fdMaybe = foldMaybe f mn ∘ foldTM f mj *)
    change (fdMaybe f (MM mn mj) z = foldr f z (fdMaybe cons (MM mn mj) nil)).
    unfold fdMaybe, foldMaybe, GHC.Base.op_z2218U__, mm_nothing, mm_just.
    destruct mn as [a0|].
    + simpl. f_equal. apply tml_fold_via_list.
    + apply tml_fold_via_list.
Qed.
(* BLOCKER (TrieMapLaws__ListMap): ListMap is axiomatized (Axiom in TrieMap.v),
   so its internal structure is opaque. All TrieMap operations on ListMap
   (lookupTM, alterTM, emptyTM, foldTM) are axiomatized too. No proofs are
   possible without either de-axiomatizing ListMap or adding axioms about
   the operation interactions. UNFIXABLE without changes to lib/TrieMap.v. *)
Instance TrieMapLaws__ListMap      {m} `{TrieMapLaws m}                         : TrieMapLaws (ListMap m).                 Admitted.

(* BLOCKER (TrieMapLaws__UniqFM): UniqFM wraps IntMap, and its operations
   (lookupUFM, alterUFM, emptyUFM, nonDetFoldUFM) delegate to IntMap.
   The key type goes through Uniquable (getUnique). Proving the laws requires:
   - IntMap alter/lookup interaction lemmas (same as IntMap instance above)
   - Uniquable injectivity or at least consistency axiom
   - nonDetFoldUFM fold properties (blocked by foldr unfolding issues)
   PARTIALLY FEASIBLE but depends on IntMap instance being proved first. *)
Instance TrieMapLaws__UniqFM {key} `{Unique.Uniquable key}                       : TrieMapLaws (UniqFM.UniqFM key).        Admitted.

(* Many TrieMap types (TypeMapX, CoreMapX, etc.) were axiomatized or removed
   in GHC 9.10. Only declare instances for types that exist. *)
(* BLOCKER (TrieMapLaws__GenMap): GenMap is axiomatized (Axiom in TrieMap.v),
   so its structure is completely opaque. All operations are axiomatized.
   UNFIXABLE without de-axiomatizing GenMap. *)
Instance TrieMapLaws__GenMap       {m} `{TrieMapLaws m} `{GHC.Base.Eq_ (Key m)} : TrieMapLaws (GenMap m).                  Admitted.

