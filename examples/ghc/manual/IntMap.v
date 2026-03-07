(* IntMap — thin wrapper around Data.IntMap.Internal for examples/ghc

   We define IntMap a := Data.IntMap.Internal.IntMap a (a plain type alias)
   and delegate each operation transparently. *)

Require Import GHC.Base.
Require Data.IntSet.Internal.
Require Data.IntMap.Internal.

Definition IntMap (a : Type) : Type := Data.IntMap.Internal.IntMap a.

Definition empty {a : Type} : IntMap a :=
  Data.IntMap.Internal.empty.

Definition singleton {a : Type} : Word -> a -> IntMap a :=
  Data.IntMap.Internal.singleton.

Definition null {a : Type} : IntMap a -> bool :=
  Data.IntMap.Internal.null.

Definition keys {a : Type} : IntMap a -> list Word :=
  Data.IntMap.Internal.keys.

Definition keysSet {a : Type} (m : IntMap a) : Data.IntSet.Internal.IntSet :=
  Data.IntSet.Internal.fromList (keys m).

Definition elems {a : Type} : IntMap a -> list a :=
  Data.IntMap.Internal.elems.

Definition member {a : Type} : Word -> IntMap a -> bool :=
  Data.IntMap.Internal.member.

Definition size {a : Type} (m : IntMap a) : nat :=
  N.to_nat (Data.IntMap.Internal.size m).

Definition insert {a : Type} : Word -> a -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.insert.

Definition insertWith {a : Type} : (a -> a -> a) -> Word -> a -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.insertWith.

Definition delete {a : Type} : Word -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.delete.

Definition alter {a : Type} : (option a -> option a) -> Word -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.alter.

Definition adjust {a : Type} : (a -> a) -> Word -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.adjust.

Definition map {a b : Type} : (a -> b) -> IntMap a -> IntMap b :=
  Data.IntMap.Internal.map.

Definition mapWithKey {a b : Type} : (Word -> a -> b) -> IntMap a -> IntMap b :=
  Data.IntMap.Internal.mapWithKey.

Definition filter {a : Type} : (a -> bool) -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.filter.

Definition filterWithKey {a : Type} : (Word -> a -> bool) -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.filterWithKey.

Definition union {a : Type} : IntMap a -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.union.

Definition unionWith {a : Type} : (a -> a -> a) -> IntMap a -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.unionWith.

Definition intersection {a b : Type} : IntMap a -> IntMap b -> IntMap a :=
  Data.IntMap.Internal.intersection.

Definition intersectionWith {a b c : Type} : (a -> b -> c) -> IntMap a -> IntMap b -> IntMap c :=
  Data.IntMap.Internal.intersectionWith.

Definition difference {a b : Type} : IntMap a -> IntMap b -> IntMap a :=
  Data.IntMap.Internal.difference.

Definition partition {a : Type} : (a -> bool) -> IntMap a -> IntMap a * IntMap a :=
  Data.IntMap.Internal.partition.

Definition toList {a : Type} : IntMap a -> list (Word * a) :=
  Data.IntMap.Internal.toList.

Definition toAscList {a : Type} : IntMap a -> list (Word * a) :=
  Data.IntMap.Internal.toAscList.

Definition fromList {a : Type} : list (Word * a) -> IntMap a :=
  Data.IntMap.Internal.fromList.

Definition foldr {a b : Type} : (a -> b -> b) -> b -> IntMap a -> b :=
  Data.IntMap.Internal.foldr.

Definition foldlWithKey' {a b : Type} : (b -> Word -> a -> b) -> b -> IntMap a -> b :=
  Data.IntMap.Internal.foldlWithKey'.

Definition foldrWithKey {a b : Type} : (Word -> a -> b -> b) -> b -> IntMap a -> b :=
  Data.IntMap.Internal.foldrWithKey.

Definition findWithDefault {a : Type} : a -> Word -> IntMap a -> a :=
  Data.IntMap.Internal.findWithDefault.

Definition lookup {a : Type} : Word -> IntMap a -> option a :=
  Data.IntMap.Internal.lookup.

Definition mapKeys {a : Type} : (Word -> Word) -> IntMap a -> IntMap a :=
  Data.IntMap.Internal.mapKeys.

Definition isSubmapOfBy {a b : Type} : (a -> b -> bool) -> IntMap a -> IntMap b -> bool :=
  Data.IntMap.Internal.isSubmapOfBy.

Definition unionsWith {a : Type} : (a -> a -> a) -> list (IntMap a) -> IntMap a :=
  Data.IntMap.Internal.unionsWith.

Definition mergeWithKey {a b c : Type}
  : (Word -> a -> b -> option c) -> (IntMap a -> IntMap c) -> (IntMap b -> IntMap c)
    -> IntMap a -> IntMap b -> IntMap c :=
  Data.IntMap.Internal.mergeWithKey.

Definition mapMaybeWithKey {a b : Type}
  : (Word -> a -> option b) -> IntMap a -> IntMap b :=
  Data.IntMap.Internal.mapMaybeWithKey.
