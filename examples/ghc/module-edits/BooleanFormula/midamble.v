Arguments Var {_} _.
Arguments And {_} _.
Arguments Or {_} _.
Arguments Parens {_} _.

Import GHC.Err.
Instance Default_BooleanFormula {a} : Err.Default (BooleanFormula a) :=
  Err.Build_Default _ (And nil).

Local Fixpoint size {a} (bf: BooleanFormula a) : nat :=
  match bf with
    | Var a => 0
    | And xs => Coq.Lists.List.fold_right Nat.add 0 (Coq.Lists.List.map
        (fun lbf => match lbf with SrcLoc.L _ f => S (size f) end) xs)
    | Or xs => Coq.Lists.List.fold_right Nat.add 0 (Coq.Lists.List.map
        (fun lbf => match lbf with SrcLoc.L _ f => S (size f) end) xs)
    | Parens (SrcLoc.L _ bf) => S (size bf)
  end.

Fixpoint BooleanFormula_eq {a} `{GHC.Base.Eq_ a} (bf1 : BooleanFormula a) (bf2 : BooleanFormula a) : bool :=
  let fix lbf_eq (xs ys : list (SrcLoc.GenLocated SrcLoc.SrcSpan (BooleanFormula a))) : bool :=
    match xs, ys with
    | nil, nil => true
    | cons (SrcLoc.L _ x) xs', cons (SrcLoc.L _ y) ys' => andb (BooleanFormula_eq x y) (lbf_eq xs' ys')
    | _, _ => false
    end in
    match bf1 , bf2 with
      | Var a1 , Var b1 => GHC.Base.op_zeze__ a1 b1
      | And a1 , And b1 => lbf_eq a1 b1
      | Or a1 , Or b1 => lbf_eq a1 b1
      | Parens (SrcLoc.L _ a1) , Parens (SrcLoc.L _ b1) => BooleanFormula_eq a1 b1
      | _ , _ => false
    end.

Instance Eq_BooleanFormula {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (BooleanFormula a) :=
  GHC.Base.eq_default BooleanFormula_eq.

(* Helper to map over Located BooleanFormula lists *)
Local Definition map_lbf {a b} (f : BooleanFormula a -> BooleanFormula b)
  (xs : list (SrcLoc.GenLocated SrcLoc.SrcSpan (BooleanFormula a)))
  : list (SrcLoc.GenLocated SrcLoc.SrcSpan (BooleanFormula b)) :=
  Coq.Lists.List.map (fun lbf => match lbf with SrcLoc.L l bf => SrcLoc.L l (f bf) end) xs.

Local Definition BooleanFormula_fmap
   : forall {a} {b}, (a -> b) -> BooleanFormula a -> BooleanFormula b :=
  fun {a} {b} => fix BooleanFormula_fmap f bf :=
      match bf with
        | Var a1 => Var (f a1)
        | And a1 => And (map_lbf (BooleanFormula_fmap f) a1)
        | Or a1 => Or (map_lbf (BooleanFormula_fmap f) a1)
        | Parens (SrcLoc.L l a1) => Parens (SrcLoc.L l (BooleanFormula_fmap f a1))
      end.

Local Definition BooleanFormula_traverse
    : forall {f} {a} {b}, forall `{GHC.Base.Applicative f}, (a -> f b) -> BooleanFormula a -> f (BooleanFormula b) :=
  fun {f0} {a} {b} `{GHC.Base.Applicative f0} => fix BooleanFormula_traverse g bf :=
      match bf with
        | Var a1 => GHC.Base.fmap Var (g a1)
        | And a1 => GHC.Base.fmap And
            (Data.Traversable.traverse
              (fun lbf => match lbf with SrcLoc.L l x =>
                GHC.Base.fmap (SrcLoc.L l) (BooleanFormula_traverse g x) end) a1)
        | Or a1 => GHC.Base.fmap Or
            (@Data.Traversable.traverse _ _ _ _ f0 _ _ _ _
              (fun lbf => match lbf with SrcLoc.L l x =>
                GHC.Base.fmap (SrcLoc.L l) (BooleanFormula_traverse g x) end) a1)
        | Parens (SrcLoc.L l a1) => GHC.Base.fmap (fun x => Parens (SrcLoc.L l x))
            (BooleanFormula_traverse g a1)
      end.

Local Definition BooleanFormula_foldMap
    : forall {m} {a},
        forall `{GHC.Base.Monoid m}, (a -> m) -> BooleanFormula a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => fix foldMap g bf :=
      match bf with
        | Var a1 => g a1
        | And a1 => Data.Foldable.foldMap
            (fun lbf => match lbf with SrcLoc.L _ x => foldMap g x end) a1
        | Or a1 => Data.Foldable.foldMap
            (fun lbf => match lbf with SrcLoc.L _ x => foldMap g x end) a1
        | Parens (SrcLoc.L _ a1) => foldMap g a1
      end.

Local Fixpoint bf_null {a} (arg_0__ : BooleanFormula a) : bool :=
      match arg_0__ with
      | Var _ => false
      | And a1 => Data.Foldable.all (fun lbf => match lbf with SrcLoc.L _ x => bf_null x end) a1
      | Or a1 => Data.Foldable.all (fun lbf => match lbf with SrcLoc.L _ x => bf_null x end) a1
      | Parens (SrcLoc.L _ a1) => bf_null a1
      end.

Local Fixpoint bf_op_zlzd {a} {b} (z : a) (bf : BooleanFormula b) : BooleanFormula a :=
      match bf with
      | Var _ => Var z
      | And a1 => And (Coq.Lists.List.map (fun lbf => match lbf with SrcLoc.L l x => SrcLoc.L l (bf_op_zlzd z x) end) a1)
      | Or a1 => Or (Coq.Lists.List.map (fun lbf => match lbf with SrcLoc.L l x => SrcLoc.L l (bf_op_zlzd z x) end) a1)
      | Parens (SrcLoc.L l a1) => Parens (SrcLoc.L l (bf_op_zlzd z a1))
      end.

Local Definition BooleanFormula_foldr
    : forall {a} {b}, (a -> b -> b) -> b -> BooleanFormula a -> b :=
  fun {a} {b} => fix foldr g z bf :=
      match bf with
        | Var a1 => g a1 z
        | And a1 => Data.Foldable.foldr
            (fun lbf acc => match lbf with SrcLoc.L _ x => foldr g acc x end) z a1
        | Or a1 => Data.Foldable.foldr
            (fun lbf acc => match lbf with SrcLoc.L _ x => foldr g acc x end) z a1
        | Parens (SrcLoc.L _ a1) => foldr g z a1
      end.
