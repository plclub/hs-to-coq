Arguments UFM {_} {_} _.
Arguments Mk_NonDetUniqFM {_} {_} _.
Arguments Removed {_} _.
Arguments Added {_} _.
Arguments Changed {_} _ _.

Require GHC.Err.
Require Data.IntMap.Internal.

#[global] Instance Default__UniqFM {key} {ele} : Err.Default (UniqFM key ele) :=
  Err.Build_Default _ (UFM Data.IntMap.Internal.empty).

(* Functor/Semigroup/Monoid instances for UniqFM *)
#[global]
Program Instance Functor__UniqFM {key : Type} : GHC.Base.Functor (UniqFM key) :=
  fun _ k__ => k__ {|
    GHC.Base.fmap__ := fun (a : Type) (b : Type) f '(UFM m) => UFM (GHC.Base.fmap f m) ;
    GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) x '(UFM m) => UFM (GHC.Base.op_zlzd__ x m)
  |}.

#[global]
Program Instance Semigroup__UniqFM {key : Type} {a : Type}
  : GHC.Base.Semigroup (UniqFM key a) :=
  fun _ k__ => k__ {|
    GHC.Base.op_zlzlzgzg____ := fun '(UFM m1) '(UFM m2) =>
      UFM (Data.IntMap.Internal.union m1 m2)
  |}.

#[global]
Program Instance Monoid__UniqFM {key : Type} {a : Type}
  : GHC.Base.Monoid (UniqFM key a) :=
  fun _ k__ => k__ {|
    GHC.Base.mappend__ := fun x y => GHC.Base.op_zlzlzgzg__ x y ;
    GHC.Base.mconcat__ := fun xs => Data.Foldable.foldr GHC.Base.op_zlzlzgzg__ (UFM Data.IntMap.Internal.empty) xs ;
    GHC.Base.mempty__ := UFM Data.IntMap.Internal.empty
  |}.

(* Manual definitions for functions that use GHC.Prim.coerce *)
#[global] Definition addToUFM_L {key : Type} {elt : Type} `{Unique.Uniquable key}
   : (key -> elt -> elt -> elt) ->
     key -> elt -> UniqFM key elt -> (option elt * UniqFM key elt)%type :=
  fun f k v '(UFM m) =>
    let '(old, m') :=
      Data.IntMap.Internal.insertLookupWithKey
        (fun _ _n _o => f k _o _n)
        (Unique.getWordKey (Unique.getUnique k)) v m
    in (old, UFM m').

#[global] Definition mergeUFM {elta : Type} {eltb : Type} {eltc : Type} {key : Type}
   : (elta -> eltb -> option eltc) ->
     (UniqFM key elta -> UniqFM key eltc) ->
     (UniqFM key eltb -> UniqFM key eltc) ->
     UniqFM key elta -> UniqFM key eltb -> UniqFM key eltc :=
  fun f g h '(UFM xm) '(UFM ym) =>
    UFM (Data.IntMap.Internal.mergeWithKey
      (fun _ x y => f x y)
      (fun m => match g (UFM m) with | UFM r => r end)
      (fun m => match h (UFM m) with | UFM r => r end)
      xm ym).
