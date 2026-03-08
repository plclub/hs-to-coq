(* GHC 9.10: GenMap is axiomatized — provide Functor instance via Admitted *)
#[global] Instance Functor__GenMap {m : Type -> Type} `{GHC.Base.Functor m}
  : GHC.Base.Functor (GenMap m). Admitted.

(* GHC 9.10: MapX types moved to GHC.Core.Map modules — axiomatize here *)
Axiom TypeMapX     : Type -> Type.
Axiom CoreMapX     : Type -> Type.
Axiom CoercionMapX : Type -> Type.

Definition CoreMapG     : Type -> Type := GenMap CoreMapX.
Definition TypeMapG     : Type -> Type := GenMap TypeMapX.
Definition CoercionMapG : Type -> Type := GenMap CoercionMapX.

(* Functor instances for MapX types (prerequisite for TrieMap) *)
#[global] Instance Functor__CoreMapX : GHC.Base.Functor CoreMapX. Admitted.
#[global] Instance Functor__TypeMapX : GHC.Base.Functor TypeMapX. Admitted.
#[global] Instance Functor__CoercionMapX : GHC.Base.Functor CoercionMapX. Admitted.

(* TrieMap instances for MapX types *)
#[global] Instance TrieMap__CoreMapX : TrieMap CoreMapX. Admitted.
#[global] Instance TrieMap__TypeMapX : TrieMap TypeMapX. Admitted.
#[global] Instance TrieMap__CoercionMapX : TrieMap CoercionMapX. Admitted.

(* Eq instances for Key types *)
#[global] Instance Eq__Key_CoreMapX : GHC.Base.Eq_ (Key CoreMapX). Admitted.
#[global] Instance Eq__Key_TypeMapX : GHC.Base.Eq_ (Key TypeMapX). Admitted.
#[global] Instance Eq__Key_CoercionMapX : GHC.Base.Eq_ (Key CoercionMapX). Admitted.

(* TrieMap instances for GenMap — generic instance for any m with TrieMap + Eq (Key m) *)
#[global] Instance TrieMap__GenMap {m} `{TrieMap m} `{GHC.Base.Eq_ (Key m)}
  : TrieMap (GenMap m). Admitted.
