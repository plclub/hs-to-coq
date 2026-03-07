(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require HsToCoq.Nat.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Bifunctor.
Require Data.Bits.
Require Data.Either.
Require Data.Foldable.
Require Data.Maybe.
Require Data.OldList.
Require Data.Set.Internal.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Char.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Tuple.
Require HsToCoq.DeferredFix.
Require HsToCoq.Err.
Require Panic.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

#[global] Definition Suffix :=
  GHC.Base.String%type.

Inductive Direction : Type := | Forwards : Direction | Backwards : Direction.

Instance Default__Direction : HsToCoq.Err.Default Direction :=
  HsToCoq.Err.Build_Default _ Forwards.

(* Midamble *)

(* HasDebugCallStack is a type alias for HasCallStack in GHC.
   We define it as a trivial typeclass so references in other modules compile. *)
Class HasDebugCallStack := {}.
#[global] Instance hasDebugCallStack : HasDebugCallStack := {}.

(* Converted value declarations: *)

#[global] Definition applyWhen {a : Type} : bool -> (a -> a) -> a -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | true, f, x => f x
    | _, _, x => x
    end.

(* Skipping definition `Util.nTimes' *)

#[global] Definition const2 {a : Type} {b : Type} {c : Type}
   : a -> b -> c -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | x, _, _ => x
    end.

#[global] Definition fstOf3 {a : Type} {b : Type} {c : Type}
   : (a * b * c)%type -> a :=
  fun '(pair (pair a _) _) => a.

#[global] Definition sndOf3 {a : Type} {b : Type} {c : Type}
   : (a * b * c)%type -> b :=
  fun '(pair (pair _ b) _) => b.

#[global] Definition thdOf3 {a : Type} {b : Type} {c : Type}
   : (a * b * c)%type -> c :=
  fun '(pair (pair _ _) c) => c.

#[global] Definition fstOf4 {a : Type} {b : Type} {c : Type} {d : Type}
   : (a * b * c * d)%type -> a :=
  fun '(pair (pair (pair a _) _) _) => a.

#[global] Definition sndOf4 {a : Type} {b : Type} {c : Type} {d : Type}
   : (a * b * c * d)%type -> b :=
  fun '(pair (pair (pair _ b) _) _) => b.

#[global] Definition fst3 {a : Type} {d : Type} {b : Type} {c : Type}
   : (a -> d) -> (a * b * c)%type -> (d * b * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair a b) c => pair (pair (f a) b) c
    end.

#[global] Definition snd3 {b : Type} {d : Type} {a : Type} {c : Type}
   : (b -> d) -> (a * b * c)%type -> (a * d * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair a b) c => pair (pair a (f b)) c
    end.

#[global] Definition third3 {c : Type} {d : Type} {a : Type} {b : Type}
   : (c -> d) -> (a * b * c)%type -> (a * b * d)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair a b) c => pair (pair a b) (f c)
    end.

#[global] Definition uncurry3 {a : Type} {b : Type} {c : Type} {d : Type}
   : (a -> b -> c -> d) -> (a * b * c)%type -> d :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair a b) c => f a b c
    end.

#[global] Definition filterOut {a : Type} : (a -> bool) -> list a -> list a :=
  fun p => GHC.List.filter (negb GHC.Base.∘ p).

Fixpoint partitionWith {a : Type} {b : Type} {c : Type} (arg_0__
                         : a -> Data.Either.Either b c) (arg_1__ : list a) : (list b * list c)%type
  := match arg_0__, arg_1__ with
     | _, nil => pair nil nil
     | f, cons x xs =>
         let 'pair bs cs := partitionWith f xs in
         match f x with
         | Data.Either.Left b => pair (cons b bs) cs
         | Data.Either.Right c => pair bs (cons c cs)
         end
     end.

Fixpoint partitionWithM {m : Type -> Type} {a : Type} {b : Type} {c : Type}
                        `{GHC.Base.Monad m} (arg_0__ : a -> m (Data.Either.Either b c)) (arg_1__
                          : list a) : m (list b * list c)%type
  := match arg_0__, arg_1__ with
     | _, nil => GHC.Base.return_ (pair nil nil)
     | f, cons x xs =>
         f x GHC.Base.>>=
         (fun y =>
            let cont_3__ arg_4__ :=
              let 'pair bs cs := arg_4__ in
              match y with
              | Data.Either.Left b => GHC.Base.return_ (pair (cons b bs) cs)
              | Data.Either.Right c => GHC.Base.return_ (pair bs (cons c cs))
              end in
            partitionWithM f xs GHC.Base.>>= cont_3__)
     end.

#[global] Definition chkAppend {a : Type} : list a -> list a -> list a :=
  fun xs ys =>
    if Data.Foldable.null ys : bool then xs else
    Coq.Init.Datatypes.app xs ys.

#[global] Definition zipEqual {a : Type} {b : Type} `{HasDebugCallStack}
   : GHC.Base.String -> list a -> list b -> list (a * b)%type :=
  fun arg_0__ => GHC.List.zip.

#[global] Definition zipWithEqual {a : Type} {b : Type} {c : Type}
  `{HasDebugCallStack}
   : GHC.Base.String -> (a -> b -> c) -> list a -> list b -> list c :=
  fun arg_0__ => GHC.List.zipWith.

#[global] Definition zipWith3Equal {a : Type} {b : Type} {c : Type} {d : Type}
  `{HasDebugCallStack}
   : GHC.Base.String ->
     (a -> b -> c -> d) -> list a -> list b -> list c -> list d :=
  fun arg_0__ => GHC.List.zipWith3.

#[global] Definition zipWith4Equal {a : Type} {b : Type} {c : Type} {d : Type}
  {e : Type} `{HasDebugCallStack}
   : GHC.Base.String ->
     (a -> b -> c -> d -> e) -> list a -> list b -> list c -> list d -> list e :=
  fun arg_0__ => Data.OldList.zipWith4.

Fixpoint filterByList {a : Type} (arg_0__ : list bool) (arg_1__ : list a) : list
                                                                            a
  := match arg_0__, arg_1__ with
     | cons true bs, cons x xs => cons x (filterByList bs xs)
     | cons false bs, cons _ xs => filterByList bs xs
     | _, _ => nil
     end.

Fixpoint filterByLists {a : Type} (arg_0__ : list bool) (arg_1__ arg_2__
                         : list a) : list a
  := match arg_0__, arg_1__, arg_2__ with
     | cons true bs, cons x xs, cons _ ys => cons x (filterByLists bs xs ys)
     | cons false bs, cons _ xs, cons y ys => cons y (filterByLists bs xs ys)
     | _, _, _ => nil
     end.

#[global] Definition partitionByList {a : Type}
   : list bool -> list a -> (list a * list a)%type :=
  let fix go arg_0__ arg_1__ arg_2__ arg_3__
    := match arg_0__, arg_1__, arg_2__, arg_3__ with
       | trues, falses, cons true bs, cons x xs => go (cons x trues) falses bs xs
       | trues, falses, cons false bs, cons x xs => go trues (cons x falses) bs xs
       | trues, falses, _, _ => pair (GHC.List.reverse trues) (GHC.List.reverse falses)
       end in
  go nil nil.

Fixpoint stretchZipWith {a : Type} {b : Type} {c : Type} (arg_0__ : a -> bool)
                        (arg_1__ : b) (arg_2__ : a -> b -> c) (arg_3__ : list a) (arg_4__ : list b)
  : list c
  := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
     | _, _, _, nil, _ => nil
     | p, z, f, cons x xs, ys =>
         if p x : bool then cons (f x z) (stretchZipWith p z f xs ys) else
         match ys with
         | nil => nil
         | cons y ys => cons (f x y) (stretchZipWith p z f xs ys)
         end
     end.

#[global] Definition mapFst {f : Type -> Type} {a : Type} {c : Type} {b : Type}
  `{GHC.Base.Functor f}
   : (a -> c) -> f (a * b)%type -> f (c * b)%type :=
  GHC.Base.fmap GHC.Base.∘ Data.Bifunctor.first.

#[global] Definition mapSnd {f : Type -> Type} {b : Type} {c : Type} {a : Type}
  `{GHC.Base.Functor f}
   : (b -> c) -> f (a * b)%type -> f (a * c)%type :=
  GHC.Base.fmap GHC.Base.∘ Data.Bifunctor.second.

Fixpoint mapAndUnzip {a : Type} {b : Type} {c : Type} (arg_0__
                       : a -> (b * c)%type) (arg_1__ : list a) : (list b * list c)%type
  := match arg_0__, arg_1__ with
     | _, nil => pair nil nil
     | f, cons x xs =>
         let 'pair rs1 rs2 := mapAndUnzip f xs in
         let 'pair r1 r2 := f x in
         pair (cons r1 rs1) (cons r2 rs2)
     end.

Fixpoint mapAndUnzip3 {a : Type} {b : Type} {c : Type} {d : Type} (arg_0__
                        : a -> (b * c * d)%type) (arg_1__ : list a) : (list b * list c * list d)%type
  := match arg_0__, arg_1__ with
     | _, nil => pair (pair nil nil) nil
     | f, cons x xs =>
         let 'pair (pair rs1 rs2) rs3 := mapAndUnzip3 f xs in
         let 'pair (pair r1 r2) r3 := f x in
         pair (pair (cons r1 rs1) (cons r2 rs2)) (cons r3 rs3)
     end.

Fixpoint mapAndUnzip4 {a : Type} {b : Type} {c : Type} {d : Type} {e : Type}
                      (arg_0__ : a -> (b * c * d * e)%type) (arg_1__ : list a) : (list b * list c *
                                                                                  list d *
                                                                                  list e)%type
  := match arg_0__, arg_1__ with
     | _, nil => pair (pair (pair nil nil) nil) nil
     | f, cons x xs =>
         let 'pair (pair (pair rs1 rs2) rs3) rs4 := mapAndUnzip4 f xs in
         let 'pair (pair (pair r1 r2) r3) r4 := f x in
         pair (pair (pair (cons r1 rs1) (cons r2 rs2)) (cons r3 rs3)) (cons r4 rs4)
     end.

Fixpoint zipWithAndUnzip {a : Type} {b : Type} {c : Type} {d : Type} (arg_0__
                           : a -> b -> (c * d)%type) (arg_1__ : list a) (arg_2__ : list b) : (list c *
                                                                                              list d)%type
  := match arg_0__, arg_1__, arg_2__ with
     | f, cons a as_, cons b bs =>
         let 'pair rs1 rs2 := zipWithAndUnzip f as_ bs in
         let 'pair r1 r2 := f a b in
         pair (cons r1 rs1) (cons r2 rs2)
     | _, _, _ => pair nil nil
     end.

Fixpoint zipAndUnzip {a : Type} {b : Type} (arg_0__ : list a) (arg_1__ : list b)
  : (list a * list b)%type
  := match arg_0__, arg_1__ with
     | cons a as_, cons b bs =>
         let 'pair rs1 rs2 := zipAndUnzip as_ bs in
         pair (cons a rs1) (cons b rs2)
     | _, _ => pair nil nil
     end.

#[global] Definition atLength {a : Type} {b : Type}
   : (list a -> b) -> b -> list a -> nat -> b :=
  fun atLenPred atEnd ls0 n0 =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | num_2__, ls =>
             if num_2__ GHC.Base.== #0 : bool then atLenPred ls else
             match arg_0__, arg_1__ with
             | _, nil => atEnd
             | n, cons _ xs => go (n GHC.Num.- #1) xs
             end
         end in
    if n0 GHC.Base.< #0 : bool then atLenPred ls0 else
    go n0 ls0.

#[global] Definition notNull {f : Type -> Type} {a : Type}
  `{Data.Foldable.Foldable f}
   : f a -> bool :=
  negb GHC.Base.∘ Data.Foldable.null.

#[global] Definition lengthExceeds {a : Type} : list a -> nat -> bool :=
  fun lst n =>
    if n GHC.Base.< #0 : bool then true else
    atLength notNull false lst n.

#[global] Definition lengthAtLeast {a : Type} : list a -> nat -> bool :=
  atLength (GHC.Base.const true) false.

#[global] Definition lengthIs {a : Type} : list a -> nat -> bool :=
  fun lst n =>
    if n GHC.Base.< #0 : bool then false else
    atLength Data.Foldable.null false lst n.

#[global] Definition lengthIsNot {a : Type} : list a -> nat -> bool :=
  fun lst n =>
    if n GHC.Base.< #0 : bool then true else
    atLength notNull true lst n.

#[global] Definition lengthAtMost {a : Type} : list a -> nat -> bool :=
  fun lst n =>
    if n GHC.Base.< #0 : bool then false else
    atLength Data.Foldable.null true lst n.

#[global] Definition lengthLessThan {a : Type} : list a -> nat -> bool :=
  atLength (GHC.Base.const false) true.

#[global] Definition listLengthCmp {a : Type} : list a -> nat -> comparison :=
  let atLen := fun arg_0__ => match arg_0__ with | nil => Eq | _ => Gt end in
  let atEnd := Lt in atLength atLen atEnd.

Fixpoint equalLength {a : Type} {b : Type} (arg_0__ : list a) (arg_1__ : list b)
  : bool
  := match arg_0__, arg_1__ with
     | nil, nil => true
     | cons _ xs, cons _ ys => equalLength xs ys
     | _, _ => false
     end.

Fixpoint compareLength {a : Type} {b : Type} (arg_0__ : list a) (arg_1__
                         : list b) : comparison
  := match arg_0__, arg_1__ with
     | nil, nil => Eq
     | cons _ xs, cons _ ys => compareLength xs ys
     | nil, _ => Lt
     | _, nil => Gt
     end.

#[global] Definition leLength {a : Type} {b : Type}
   : list a -> list b -> bool :=
  fun xs ys =>
    match compareLength xs ys with
    | Lt => true
    | Eq => true
    | Gt => false
    end.

#[global] Definition ltLength {a : Type} {b : Type}
   : list a -> list b -> bool :=
  fun xs ys =>
    match compareLength xs ys with
    | Lt => true
    | Eq => false
    | Gt => false
    end.

#[global] Definition singleton {a : Type} : a -> list a :=
  fun x => cons x nil.

#[global] Definition isSingleton {a : Type} : list a -> bool :=
  fun arg_0__ => match arg_0__ with | cons _ nil => true | _ => false end.

#[global] Definition only {a} `{HsToCoq.Err.Default a} : list a -> a :=
  fun arg_0__ =>
    match arg_0__ with
    | cons a _ => a
    | _ => Panic.panic (GHC.Base.hs_string__ "Util: only")
    end.

#[global] Definition expectOnly {a} `{HsToCoq.Err.Default a}
   : GHC.Base.String -> list a -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, cons a _ => a
    | msg, _ =>
        Panic.panic (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "expectOnly: ") msg)
    end.

Fixpoint holes {a : Type} (arg_0__ : list a) : list (a * list a)%type
  := match arg_0__ with
     | nil => nil
     | cons x xs => cons (pair x xs) (mapSnd (cons x) (holes xs))
     end.

Fixpoint changeLast {a} `{HsToCoq.Err.Default a} (arg_0__ : list a) (arg_1__
                      : a) : list a
  := match arg_0__, arg_1__ with
     | nil, _ => Panic.panic (GHC.Base.hs_string__ "changeLast")
     | cons _ nil, x => cons x nil
     | cons x xs, x' => cons x (changeLast xs x')
     end.

(* Skipping definition `Util.expectNonEmpty' *)

#[global] Definition expectNonEmptyPanic {a} `{HsToCoq.Err.Default a}
   : GHC.Base.String -> a :=
  fun msg =>
    Panic.panic (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "expectNonEmpty: ")
                                        msg).

#[global] Definition whenNonEmpty {m : Type -> Type} {a : Type}
  `{GHC.Base.Applicative m}
   : list a -> (GHC.Base.NonEmpty a -> m unit) -> m unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, _ => GHC.Base.pure tt
    | cons x xs, f => f (GHC.Base.NEcons x xs)
    end.

(* Skipping definition `Util.mergeListsBy' *)

(* Skipping definition `Util.isSortedBy' *)

(* Skipping definition `Util.minWith' *)

(* Skipping definition `Util.nubSort' *)

#[global] Definition ordNubOn {b : Type} {a : Type} `{GHC.Base.Ord b}
   : (a -> b) -> list a -> list a :=
  fun f xs =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | _, nil => nil
         | s, cons x xs =>
             if Data.Set.Internal.member (f x) s : bool then go s xs else
             cons x (go (Data.Set.Internal.insert (f x) s) xs)
         end in
    go Data.Set.Internal.empty xs.

#[global] Definition ordNub {a : Type} `{GHC.Base.Ord a} : list a -> list a :=
  fun xs => ordNubOn GHC.Base.id xs.

#[global] Definition transitiveClosure {a : Type}
   : (a -> list a) -> (a -> a -> bool) -> list a -> list a :=
  fun succ eq xs =>
    let fix is_in arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | _, nil => false
         | x, cons y ys => if eq x y : bool then true else is_in x ys
         end in
    let go :=
      HsToCoq.DeferredFix.deferredFix2 (fun go arg_5__ arg_6__ =>
                                          match arg_5__, arg_6__ with
                                          | done, nil => done
                                          | done, cons x xs =>
                                              if is_in x done : bool then go done xs else
                                              go (cons x done) (Coq.Init.Datatypes.app (succ x) xs)
                                          end) in
    go nil xs.

Fixpoint foldl2 {acc} {a} {b} `{HsToCoq.Err.Default acc} (arg_0__
                  : acc -> a -> b -> acc) (arg_1__ : acc) (arg_2__ : list a) (arg_3__ : list b)
  : acc
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, z, nil, nil => z
     | k, z, cons a as_, cons b bs => foldl2 k (k z a b) as_ bs
     | _, _, _, _ => Panic.panic (GHC.Base.hs_string__ "Util: foldl2")
     end.

Fixpoint all2 {a : Type} {b : Type} (arg_0__ : a -> b -> bool) (arg_1__
                : list a) (arg_2__ : list b) : bool
  := match arg_0__, arg_1__, arg_2__ with
     | _, nil, nil => true
     | p, cons x xs, cons y ys => andb (p x y) (all2 p xs ys)
     | _, _, _ => false
     end.

#[global] Definition count {a : Type} : (a -> bool) -> list a -> nat :=
  fun p =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | n, nil => n
         | n, cons x xs => if p x : bool then go (n GHC.Num.+ #1) xs else go n xs
         end in
    go #0.

#[global] Definition countWhile {a : Type} : (a -> bool) -> list a -> nat :=
  fun p =>
    let fix go arg_0__ arg_1__
      := let j_2__ := match arg_0__, arg_1__ with | n, _ => n end in
         match arg_0__, arg_1__ with
         | n, cons x xs => if p x : bool then go (n GHC.Num.+ #1) xs else j_2__
         | _, _ => j_2__
         end in
    go #0.

Fixpoint takeList {b : Type} {a : Type} (arg_0__ : list b) (arg_1__ : list a)
  : list a
  := match arg_0__, arg_1__ with
     | nil, _ => nil
     | cons _ xs, ls =>
         match ls with
         | nil => nil
         | cons y ys => cons y (takeList xs ys)
         end
     end.

Fixpoint dropList {b : Type} {a : Type} (arg_0__ : list b) (arg_1__ : list a)
  : list a
  := match arg_0__, arg_1__ with
     | nil, xs => xs
     | _, (nil as xs) => xs
     | cons _ xs, cons _ ys => dropList xs ys
     end.

(* Skipping definition `Util.splitAtList' *)

#[global] Definition dropTail {a : Type} : nat -> list a -> list a :=
  fun n xs =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | cons _ ys, cons x xs => cons x (go ys xs)
         | _, _ => nil
         end in
    go (Coq.Lists.List.skipn n xs) xs.

#[global] Definition dropWhileEndLE {a : Type}
   : (a -> bool) -> list a -> list a :=
  fun p =>
    Data.Foldable.foldr (fun x r =>
                           if andb (Data.Foldable.null r) (p x) : bool
                           then nil
                           else cons x r) nil.

#[global] Definition spanEnd {a : Type}
   : (a -> bool) -> list a -> (list a * list a)%type :=
  fun p l =>
    let fix go arg_0__ arg_1__ arg_2__ arg_3__
      := match arg_0__, arg_1__, arg_2__, arg_3__ with
         | yes, _rev_yes, rev_no, nil => pair yes (GHC.List.reverse rev_no)
         | yes, rev_yes, rev_no, cons x xs =>
             if p x : bool then go yes (cons x rev_yes) rev_no xs else
             go xs nil (cons x (Coq.Init.Datatypes.app rev_yes rev_no)) xs
         end in
    go l nil nil l.

#[global] Definition last2 {a : Type} : list a -> option (a * a)%type :=
  Data.Tuple.uncurry (GHC.Base.liftA2 GHC.Tuple.pair2) GHC.Base.∘
  Data.Foldable.foldl' (fun arg_0__ arg_1__ =>
                          match arg_0__, arg_1__ with
                          | pair _ x2, x => pair x2 (Some x)
                          end) (pair None None).

(* Skipping definition `Util.lastMaybe' *)

#[global] Definition onJust {b : Type} {a : Type}
   : b -> option a -> (a -> b) -> b :=
  fun dflt => GHC.Base.flip (Data.Maybe.maybe dflt).

(* Skipping definition `Util.snocView' *)

#[global] Definition split
   : GHC.Char.Char -> GHC.Base.String -> list GHC.Base.String :=
  HsToCoq.DeferredFix.deferredFix2 (fun split
                                    (c : GHC.Char.Char)
                                    (s : GHC.Base.String) =>
                                      let 'pair chunk rest := GHC.List.break (GHC.Prim.rightSection _GHC.Base.==_ c)
                                                                s in
                                      match rest with
                                      | nil => cons chunk nil
                                      | cons _ rest => cons chunk (split c rest)
                                      end).

#[global] Definition capitalise : GHC.Base.String -> GHC.Base.String :=
  fun arg_0__ => match arg_0__ with | nil => nil | cons c cs => cons c cs end.

#[global] Definition isEqual : comparison -> bool :=
  fun arg_0__ => match arg_0__ with | Gt => false | Eq => true | Lt => false end.

(* Skipping definition `Util.removeSpaces' *)

#[global] Definition op_zlzazazg__ {f : Type -> Type} `{GHC.Base.Applicative f}
   : f bool -> f bool -> f bool :=
  GHC.Base.liftA2 andb.

Notation "'_<&&>_'" := (op_zlzazazg__).

Infix "<&&>" := (_<&&>_) (at level 99).

#[global] Definition op_zlzbzbzg__ {f : Type -> Type} `{GHC.Base.Applicative f}
   : f bool -> f bool -> f bool :=
  GHC.Base.liftA2 orb.

Notation "'_<||>_'" := (op_zlzbzbzg__).

Infix "<||>" := (_<||>_) (at level 99).

(* Skipping definition `Util.restrictedDamerauLevenshteinDistance' *)

(* Skipping definition `Util.restrictedDamerauLevenshteinDistanceWithLengths' *)

(* Skipping definition `Util.restrictedDamerauLevenshteinDistance'' *)

(* Skipping definition `Util.restrictedDamerauLevenshteinDistanceWorker' *)

#[global] Definition sizedComplement {bv} `{Data.Bits.Bits bv}
   : bv -> bv -> bv :=
  fun vector_mask vect => Data.Bits.xor vector_mask vect.

(* Skipping definition `Util.matchVectors' *)

(* Skipping definition `Util.fuzzyMatch' *)

(* Skipping definition `Util.fuzzyLookup' *)

#[global] Definition unzipWith {a : Type} {b : Type} {c : Type}
   : (a -> b -> c) -> list (a * b)%type -> list c :=
  GHC.Base.fmap GHC.Base.∘ Data.Tuple.uncurry.

Fixpoint seqList {a : Type} {b : Type} (arg_0__ : list a) (arg_1__ : b) : b
  := match arg_0__, arg_1__ with
     | nil, b => b
     | cons x xs, b => GHC.Prim.seq x (seqList xs b)
     end.

Fixpoint strictMap {a : Type} {b : Type} (arg_0__ : a -> b) (arg_1__ : list a)
  : list b
  := match arg_0__, arg_1__ with
     | _, nil => nil
     | f, cons x xs => let xs' := strictMap f xs in let x' := f x in cons x' xs'
     end.

Fixpoint strictZipWith {a : Type} {b : Type} {c : Type} (arg_0__ : a -> b -> c)
                       (arg_1__ : list a) (arg_2__ : list b) : list c
  := match arg_0__, arg_1__, arg_2__ with
     | _, nil, _ => nil
     | _, _, nil => nil
     | f, cons x xs, cons y ys =>
         let xs' := strictZipWith f xs ys in let x' := f x y in cons x' xs'
     end.

Fixpoint strictZipWith3 {a : Type} {b : Type} {c : Type} {d : Type} (arg_0__
                          : a -> b -> c -> d) (arg_1__ : list a) (arg_2__ : list b) (arg_3__ : list c)
  : list d
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, nil, _, _ => nil
     | _, _, nil, _ => nil
     | _, _, _, nil => nil
     | f, cons x xs, cons y ys, cons z zs =>
         let xs' := strictZipWith3 f xs ys zs in let x' := f x y z in cons x' xs'
     end.

(* Skipping definition `Util.looksLikeModuleName' *)

Axiom looksLikePackageName : GHC.Base.String -> bool.

(* Skipping definition `Util.exactLog2' *)

(* Skipping definition `Util.readRational__' *)

(* Skipping definition `Util.readRational' *)

(* Skipping definition `Util.readSignificandExponentPair__' *)

(* Skipping definition `Util.readSignificandExponentPair' *)

(* Skipping definition `Util.readHexRational' *)

(* Skipping definition `Util.readHexRational__' *)

(* Skipping definition `Util.readHexSignificandExponentPair' *)

(* Skipping definition `Util.readHexSignificandExponentPair__' *)

(* Skipping definition `Util.doesDirNameExist' *)

(* Skipping definition `Util.getModificationUTCTime' *)

(* Skipping definition `Util.modificationTimeIfExists' *)

(* Skipping definition `Util.fileHashIfExists' *)

(* Skipping definition `Util.withAtomicRename' *)

(* Skipping definition `Util.splitLongestPrefix' *)

(* Skipping definition `Util.escapeSpaces' *)

(* Skipping definition `Util.reslash' *)

Axiom makeRelativeTo : GHC.Base.String -> GHC.Base.String -> GHC.Base.String.

(* Skipping definition `Util.abstractConstr' *)

(* Skipping definition `Util.abstractDataType' *)

(* Skipping definition `Util.charToC' *)

(* Skipping definition `Util.hashString' *)

(* Skipping definition `Util.golden' *)

(* Skipping definition `Util.hashInt32' *)

(* Skipping definition `Util.mulHi' *)

#[global] Definition mapMaybe' {f : Type -> Type} {a : Type} {b : Type}
  `{Data.Foldable.Foldable f}
   : (a -> option b) -> f a -> list b :=
  fun f =>
    let g := fun x rest => match f x with | Some y => cons y rest | _ => rest end in
    Data.Foldable.foldr g nil.

Module Notations.
Notation "'_Util.<&&>_'" := (op_zlzazazg__).
Infix "Util.<&&>" := (_<&&>_) (at level 99).
Notation "'_Util.<||>_'" := (op_zlzbzbzg__).
Infix "Util.<||>" := (_<||>_) (at level 99).
End Notations.

(* External variables:
     Eq Gt HasDebugCallStack Lt None Some Type andb bool comparison cons false list
     nat negb nil op_zt__ option orb pair true tt unit Coq.Init.Datatypes.app
     Coq.Lists.List.skipn Data.Bifunctor.first Data.Bifunctor.second Data.Bits.Bits
     Data.Bits.xor Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Foldable.Foldable Data.Foldable.foldl' Data.Foldable.foldr
     Data.Foldable.null Data.Maybe.maybe Data.OldList.zipWith4
     Data.Set.Internal.empty Data.Set.Internal.insert Data.Set.Internal.member
     Data.Tuple.uncurry GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.NEcons GHC.Base.NonEmpty GHC.Base.Ord GHC.Base.String GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.id GHC.Base.liftA2 GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.pure
     GHC.Base.return_ GHC.Char.Char GHC.List.break GHC.List.filter GHC.List.reverse
     GHC.List.zip GHC.List.zipWith GHC.List.zipWith3 GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Prim.rightSection GHC.Prim.seq
     GHC.Tuple.pair2 HsToCoq.DeferredFix.deferredFix2 HsToCoq.Err.Build_Default
     HsToCoq.Err.Default Panic.panic
*)
