(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require HsToCoq.DeferredFix.
Require SrcLoc.
Require UniqSet.
Require Unique.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive BooleanFormula (a : Type) : Type :=
  | Var : a -> BooleanFormula a
  | And
   : list (SrcLoc.GenLocated SrcLoc.SrcSpan (BooleanFormula a)) ->
     BooleanFormula a
  | Or
   : list (SrcLoc.GenLocated SrcLoc.SrcSpan (BooleanFormula a)) ->
     BooleanFormula a
  | Parens
   : SrcLoc.GenLocated SrcLoc.SrcSpan (BooleanFormula a) -> BooleanFormula a.

#[global] Definition LBooleanFormula :=
  fun a_ => SrcLoc.GenLocated SrcLoc.SrcSpan (BooleanFormula a_).

Inductive Clause a : Type :=
  | Mk_Clause (clauseAtoms : UniqSet.UniqSet a) (clauseExprs
    : list (BooleanFormula a))
   : Clause a.

Arguments Mk_Clause {_} _ _.

#[global] Definition clauseAtoms {a} (arg_0__ : Clause a) :=
  let 'Mk_Clause clauseAtoms _ := arg_0__ in
  clauseAtoms.

#[global] Definition clauseExprs {a} (arg_0__ : Clause a) :=
  let 'Mk_Clause _ clauseExprs := arg_0__ in
  clauseExprs.

(* Midamble *)

Arguments Var {_} _.
Arguments And {_} _.
Arguments Or {_} _.
Arguments Parens {_} _.

Import GHC.Err.
#[global] Instance Default_BooleanFormula {a} : Err.Default (BooleanFormula a) :=
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

(* Converted value declarations: *)

#[local] Definition Functor__BooleanFormula_fmap {a} {b}
   : (a -> b) -> BooleanFormula a -> BooleanFormula b :=
  BooleanFormula_fmap.

#[local] Definition Functor__BooleanFormula_op_zlzd__ {a} {b}
   : a -> BooleanFormula b -> BooleanFormula a :=
  bf_op_zlzd.

#[global]
Program Instance Functor__BooleanFormula : GHC.Base.Functor BooleanFormula :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) =>
             Functor__BooleanFormula_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__BooleanFormula_op_zlzd__ |}.

#[local] Definition Foldable__BooleanFormula_foldMap {m} {a} `{_
   : GHC.Base.Monoid m}
   : (a -> m) -> BooleanFormula a -> m :=
  BooleanFormula_foldMap.

#[local] Definition Foldable__BooleanFormula_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, BooleanFormula m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Foldable__BooleanFormula_foldMap GHC.Base.id.

#[local] Definition Foldable__BooleanFormula_foldr {a} {b}
   : (a -> b -> b) -> b -> BooleanFormula a -> b :=
  BooleanFormula_foldr.

#[local] Definition Foldable__BooleanFormula_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> BooleanFormula a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__BooleanFormula_foldr (fun arg_0__ arg_1__ =>
                                          match arg_0__, arg_1__ with
                                          | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                          end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__BooleanFormula_foldMap'
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> BooleanFormula a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__BooleanFormula_foldl' (fun acc a => acc GHC.Base.<<>> f a)
      GHC.Base.mempty.

#[local] Definition Foldable__BooleanFormula_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> BooleanFormula a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__BooleanFormula_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                         (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                          GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__BooleanFormula_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> BooleanFormula a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__BooleanFormula_foldl (fun arg_0__ arg_1__ =>
                                          match arg_0__, arg_1__ with
                                          | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                          end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__BooleanFormula_length
   : forall {a : Type}, BooleanFormula a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__BooleanFormula_foldl' (fun arg_0__ arg_1__ =>
                                       match arg_0__, arg_1__ with
                                       | c, _ => c GHC.Num.+ #1
                                       end) #0.

#[local] Definition Foldable__BooleanFormula_null {a}
   : BooleanFormula a -> bool :=
  bf_null.

#[local] Definition Foldable__BooleanFormula_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, BooleanFormula a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__BooleanFormula_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__BooleanFormula_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, BooleanFormula a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__BooleanFormula_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__BooleanFormula_toList
   : forall {a : Type}, BooleanFormula a -> list a :=
  fun {a : Type} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__BooleanFormula_foldr c n t)).

#[global]
Program Instance Foldable__BooleanFormula
   : Data.Foldable.Foldable BooleanFormula :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__BooleanFormula_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__BooleanFormula_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__BooleanFormula_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) =>
             Foldable__BooleanFormula_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) =>
             Foldable__BooleanFormula_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) =>
             Foldable__BooleanFormula_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) =>
             Foldable__BooleanFormula_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__BooleanFormula_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__BooleanFormula_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__BooleanFormula_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__BooleanFormula_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__BooleanFormula_toList |}.

#[local] Definition Traversable__BooleanFormula_traverse {f} {a} {b} `{_
   : GHC.Base.Applicative f}
   : (a -> f b) -> BooleanFormula a -> f (BooleanFormula b) :=
  BooleanFormula_traverse.

#[local] Definition Traversable__BooleanFormula_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> BooleanFormula a -> m (BooleanFormula b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__BooleanFormula_traverse.

#[local] Definition Traversable__BooleanFormula_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     BooleanFormula (f a) -> f (BooleanFormula a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__BooleanFormula_traverse GHC.Base.id.

#[local] Definition Traversable__BooleanFormula_sequence
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, BooleanFormula (m a) -> m (BooleanFormula a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__BooleanFormula_sequenceA.

#[global]
Program Instance Traversable__BooleanFormula
   : Data.Traversable.Traversable BooleanFormula :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__BooleanFormula_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__BooleanFormula_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__BooleanFormula_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__BooleanFormula_traverse |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `BooleanFormula.Outputable__BooleanFormula' *)

#[global] Definition mkVar {a : Type} : a -> BooleanFormula a :=
  Var.

#[global] Definition mkFalse {a : Type} : BooleanFormula a :=
  Or nil.

#[global] Definition mkTrue {a : Type} : BooleanFormula a :=
  And nil.

#[global] Definition mkBool {a} : bool -> BooleanFormula a :=
  fun arg_0__ => match arg_0__ with | false => mkFalse | true => mkTrue end.

Axiom mkAnd : forall {a : Type},
              forall `{GHC.Base.Eq_ a}, list (LBooleanFormula a) -> BooleanFormula a.

Axiom mkOr : forall {a : Type},
             forall `{GHC.Base.Eq_ a}, list (LBooleanFormula a) -> BooleanFormula a.

#[global] Definition isFalse {a : Type} : BooleanFormula a -> bool :=
  fun arg_0__ => match arg_0__ with | Or nil => true | _ => false end.

#[global] Definition isTrue {a : Type} : BooleanFormula a -> bool :=
  fun arg_0__ => match arg_0__ with | And nil => true | _ => false end.

Fixpoint eval {a : Type} (arg_0__ : a -> bool) (arg_1__ : BooleanFormula a)
  : bool
  := match arg_0__, arg_1__ with
     | f, Var x => f x
     | f, And xs => Data.Foldable.all (eval f GHC.Base.∘ SrcLoc.unLoc) xs
     | f, Or xs => Data.Foldable.any (eval f GHC.Base.∘ SrcLoc.unLoc) xs
     | f, Parens x => eval f (SrcLoc.unLoc x)
     end.

Fixpoint simplify {a : Type} `{GHC.Base.Eq_ a} (arg_0__ : a -> option bool)
                  (arg_1__ : BooleanFormula a) : BooleanFormula a
  := match arg_0__, arg_1__ with
     | f, Var a => match f a with | None => Var a | Some b => mkBool b end
     | f, And xs =>
         mkAnd (GHC.Base.map (fun '(SrcLoc.L l x) => SrcLoc.L l (simplify f x)) xs)
     | f, Or xs =>
         mkOr (GHC.Base.map (fun '(SrcLoc.L l x) => SrcLoc.L l (simplify f x)) xs)
     | f, Parens x => simplify f (SrcLoc.unLoc x)
     end.

#[global] Definition isUnsatisfied {a : Type} `{GHC.Base.Eq_ a}
   : (a -> bool) -> BooleanFormula a -> option (BooleanFormula a) :=
  fun f bf =>
    let f' := fun x => if f x : bool then Some true else None in
    let bf' := simplify f' bf in if isTrue bf' : bool then None else Some bf'.

Fixpoint impliesAtom {a : Type} `{GHC.Base.Eq_ a} (arg_0__ : BooleanFormula a)
                     (arg_1__ : a) : bool
  := match arg_0__, arg_1__ with
     | Var x, y => x GHC.Base.== y
     | And xs, y => Data.Foldable.any (fun x => impliesAtom (SrcLoc.unLoc x) y) xs
     | Or xs, y => Data.Foldable.all (fun x => impliesAtom (SrcLoc.unLoc x) y) xs
     | Parens x, y => impliesAtom (SrcLoc.unLoc x) y
     end.

#[global] Definition extendClauseAtoms {a} `{Unique.Uniquable a}
   : Clause a -> a -> Clause a :=
  fun c x =>
    let 'Mk_Clause clauseAtoms_0__ clauseExprs_1__ := c in
    Mk_Clause (UniqSet.addOneToUniqSet (clauseAtoms c) x) clauseExprs_1__.

#[global] Definition memberClauseAtoms {a} `{Unique.Uniquable a}
   : a -> Clause a -> bool :=
  fun x c => UniqSet.elementOfUniqSet x (clauseAtoms c).

#[global] Definition implies {a : Type} `{Unique.Uniquable a}
   : BooleanFormula a -> BooleanFormula a -> bool :=
  fun e1 e2 =>
    let go {a} `{Unique.Uniquable a} : Clause a -> Clause a -> bool :=
      HsToCoq.DeferredFix.deferredFix1 (fun go (arg_0__ arg_1__ : Clause a) =>
                                          match arg_0__, arg_1__ with
                                          | (Mk_Clause _ (cons hyp hyps) as l), r =>
                                              match hyp with
                                              | Var x =>
                                                  if memberClauseAtoms x r : bool then true else
                                                  go (let 'Mk_Clause clauseAtoms_2__ clauseExprs_3__ :=
                                                        (extendClauseAtoms l x) in
                                                      Mk_Clause clauseAtoms_2__ hyps) r
                                              | Parens hyp' =>
                                                  go (let 'Mk_Clause clauseAtoms_9__ clauseExprs_10__ := l in
                                                      Mk_Clause clauseAtoms_9__ (cons (SrcLoc.unLoc hyp') hyps)) r
                                              | And hyps' =>
                                                  go (let 'Mk_Clause clauseAtoms_14__ clauseExprs_15__ := l in
                                                      Mk_Clause clauseAtoms_14__ (Coq.Init.Datatypes.app (GHC.Base.map
                                                                                                          SrcLoc.unLoc
                                                                                                          hyps') hyps))
                                                  r
                                              | Or hyps' =>
                                                  Data.Foldable.all (fun hyp' =>
                                                                       go (let 'Mk_Clause clauseAtoms_19__
                                                                              clauseExprs_20__ := l in
                                                                           Mk_Clause clauseAtoms_19__ (cons
                                                                                      (SrcLoc.unLoc hyp') hyps)) r)
                                                  hyps'
                                              end
                                          | l, (Mk_Clause _ (cons con cons_) as r) =>
                                              match con with
                                              | Var x =>
                                                  if memberClauseAtoms x l : bool then true else
                                                  go l (let 'Mk_Clause clauseAtoms_27__ clauseExprs_28__ :=
                                                          (extendClauseAtoms r x) in
                                                        Mk_Clause clauseAtoms_27__ cons_)
                                              | Parens con' =>
                                                  go l (let 'Mk_Clause clauseAtoms_34__ clauseExprs_35__ := r in
                                                        Mk_Clause clauseAtoms_34__ (cons (SrcLoc.unLoc con') cons_))
                                              | And cons' =>
                                                  Data.Foldable.all (fun con' =>
                                                                       go l (let 'Mk_Clause clauseAtoms_39__
                                                                                clauseExprs_40__ := r in
                                                                             Mk_Clause clauseAtoms_39__ (cons
                                                                                        (SrcLoc.unLoc con') cons_)))
                                                  cons'
                                              | Or cons' =>
                                                  go l (let 'Mk_Clause clauseAtoms_45__ clauseExprs_46__ := r in
                                                        Mk_Clause clauseAtoms_45__ (Coq.Init.Datatypes.app (GHC.Base.map
                                                                                                            SrcLoc.unLoc
                                                                                                            cons')
                                                                                                           cons_))
                                              end
                                          | _, _ => false
                                          end) in
    go (Mk_Clause UniqSet.emptyUniqSet (cons e1 nil)) (Mk_Clause
                                                       UniqSet.emptyUniqSet (cons e2 nil)).

(* Skipping definition `BooleanFormula.pprBooleanFormula'' *)

(* Skipping definition `BooleanFormula.pprBooleanFormula' *)

(* Skipping definition `BooleanFormula.pprBooleanFormulaNice' *)

(* Skipping definition `BooleanFormula.pprBooleanFormulaNormal' *)

(* External variables:
     BooleanFormula_fmap BooleanFormula_foldMap BooleanFormula_foldr
     BooleanFormula_traverse None Some Type bf_null bf_op_zlzd bool cons false list
     nil option true Coq.Init.Datatypes.app Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.all Data.Foldable.any
     Data.Foldable.foldMap'__ Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.build' GHC.Base.flip GHC.Base.fmap__
     GHC.Base.id GHC.Base.map GHC.Base.mempty GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__ GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.seq
     HsToCoq.DeferredFix.deferredFix1 SrcLoc.GenLocated SrcLoc.L SrcLoc.SrcSpan
     SrcLoc.unLoc UniqSet.UniqSet UniqSet.addOneToUniqSet UniqSet.elementOfUniqSet
     UniqSet.emptyUniqSet Unique.Uniquable
*)
