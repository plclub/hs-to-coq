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

Require Control.Monad.IO.Class.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Bits.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.OldList.
Require Data.Set.Internal.
Require GHC.Base.
Require GHC.Char.
Require GHC.Enum.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require HsToCoq.DeferredFix.
Require HsToCoq.Err.
Require PlainPanic.
Import Data.Bits.Notations.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

#[global] Definition Suffix :=
  GHC.Base.String%type.

Inductive OverridingBool : Type :=
  | Auto : OverridingBool
  | Always : OverridingBool
  | Never : OverridingBool.

#[global] Definition HasDebugCallStack :=
  unit.

Inductive Direction : Type := | Forwards : Direction | Backwards : Direction.

Instance Default__OverridingBool : HsToCoq.Err.Default OverridingBool :=
  HsToCoq.Err.Build_Default _ Auto.

Instance Default__Direction : HsToCoq.Err.Default Direction :=
  HsToCoq.Err.Build_Default _ Forwards.

(* Midamble *)

Existing Class HasDebugCallStack.
Instance Util_HasDebugCallStack : HasDebugCallStack := tt.

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Util.Show__OverridingBool' *)

#[global] Definition ghciSupported : bool :=
  false.

Axiom debugIsOn : bool.

#[global] Definition ghciTablesNextToCode : bool :=
  false.

#[global] Definition isWindowsHost : bool :=
  false.

(* Skipping definition `Util.isDarwinHost' *)

#[global] Definition applyWhen {a : Type} : bool -> (a -> a) -> a -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | true, f, x => f x
    | _, _, x => x
    end.

(* Skipping definition `Util.nTimes' *)

#[global] Definition fstOf3 {a : Type} {b : Type} {c : Type}
   : (a * b * c)%type -> a :=
  fun '(pair (pair a _) _) => a.

#[global] Definition sndOf3 {a : Type} {b : Type} {c : Type}
   : (a * b * c)%type -> b :=
  fun '(pair (pair _ b) _) => b.

#[global] Definition thdOf3 {a : Type} {b : Type} {c : Type}
   : (a * b * c)%type -> c :=
  fun '(pair (pair _ _) c) => c.

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

#[global] Definition liftFst {a : Type} {b : Type} {c : Type}
   : (a -> b) -> (a * c)%type -> (b * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair a c => pair (f a) c
    end.

#[global] Definition liftSnd {a : Type} {b : Type} {c : Type}
   : (a -> b) -> (c * a)%type -> (c * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair c a => pair c (f a)
    end.

#[global] Definition firstM {m : Type -> Type} {a : Type} {c : Type} {b : Type}
  `{GHC.Base.Monad m}
   : (a -> m c) -> (a * b)%type -> m (c * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair x y => GHC.Base.liftM (fun x' => pair x' y) (f x)
    end.

#[global] Definition first3M {m : Type -> Type} {a : Type} {d : Type} {b : Type}
  {c : Type} `{GHC.Base.Monad m}
   : (a -> m d) -> (a * b * c)%type -> m (d * b * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair x y) z => GHC.Base.liftM (fun x' => pair (pair x' y) z) (f x)
    end.

#[global] Definition secondM {m : Type -> Type} {b : Type} {c : Type} {a : Type}
  `{GHC.Base.Monad m}
   : (b -> m c) -> (a * b)%type -> m (a * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair x y => (fun arg_2__ => pair x arg_2__) Data.Functor.<$> f y
    end.

Fixpoint filterOut {a : Type} (arg_0__ : a -> bool) (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | _, nil => nil
     | p, cons x xs => if p x : bool then filterOut p xs else cons x (filterOut p xs)
     end.

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

#[global] Definition chkAppend {a : Type} : list a -> list a -> list a :=
  fun xs ys =>
    if Data.Foldable.null ys : bool then xs else
    Coq.Init.Datatypes.app xs ys.

#[global] Definition zipEqual {a : Type} {b : Type}
   : GHC.Base.String -> list a -> list b -> list (a * b)%type :=
  fun arg_0__ => GHC.List.zip.

#[global] Definition zipWithEqual {a : Type} {b : Type} {c : Type}
   : GHC.Base.String -> (a -> b -> c) -> list a -> list b -> list c :=
  fun arg_0__ => GHC.List.zipWith.

#[global] Definition zipWith3Equal {a : Type} {b : Type} {c : Type} {d : Type}
   : GHC.Base.String ->
     (a -> b -> c -> d) -> list a -> list b -> list c -> list d :=
  fun arg_0__ => GHC.List.zipWith3.

#[global] Definition zipWith4Equal {a : Type} {b : Type} {c : Type} {d : Type}
  {e : Type}
   : GHC.Base.String ->
     (a -> b -> c -> d -> e) -> list a -> list b -> list c -> list d -> list e :=
  fun arg_0__ => Data.OldList.zipWith4.

Fixpoint zipLazy {a : Type} {b : Type} (arg_0__ : list a) (arg_1__ : list b)
  : list (a * b)%type
  := match arg_0__, arg_1__ with
     | nil, _ => nil
     | cons x xs, cons y ys => cons (pair x y) (zipLazy xs ys)
     | _, _ => GHC.Err.patternFailure
     end.

Fixpoint zipWithLazy {a : Type} {b : Type} {c : Type} (arg_0__ : a -> b -> c)
                     (arg_1__ : list a) (arg_2__ : list b) : list c
  := match arg_0__, arg_1__, arg_2__ with
     | _, nil, _ => nil
     | f, cons a as_, cons b bs => cons (f a b) (zipWithLazy f as_ bs)
     | _, _, _ => GHC.Err.patternFailure
     end.

Fixpoint zipWith3Lazy {a : Type} {b : Type} {c : Type} {d : Type} (arg_0__
                        : a -> b -> c -> d) (arg_1__ : list a) (arg_2__ : list b) (arg_3__ : list c)
  : list d
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, nil, _, _ => nil
     | f, cons a as_, cons b bs, cons c cs =>
         cons (f a b c) (zipWith3Lazy f as_ bs cs)
     | _, _, _, _ => GHC.Err.patternFailure
     end.

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

#[global] Definition mapFst {a : Type} {c : Type} {b : Type}
   : (a -> c) -> list (a * b)%type -> list (c * b)%type :=
  fun f xys =>
    let cont_0__ arg_1__ := let 'pair x y := arg_1__ in cons (pair (f x) y) nil in
    Coq.Lists.List.flat_map cont_0__ xys.

#[global] Definition mapSnd {b : Type} {c : Type} {a : Type}
   : (b -> c) -> list (a * b)%type -> list (a * c)%type :=
  fun f xys =>
    let cont_0__ arg_1__ := let 'pair x y := arg_1__ in cons (pair x (f y)) nil in
    Coq.Lists.List.flat_map cont_0__ xys.

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

(* Skipping definition `Util.mapAccumL2' *)

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

#[global] Definition notNull {a : Type} : list a -> bool :=
  fun arg_0__ => match arg_0__ with | nil => false | _ => true end.

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
    | _ => PlainPanic.panic (GHC.Base.hs_string__ "Util: only")
    end.

#[global] Definition isIn {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.String -> a -> list a -> bool :=
  fun _msg x ys => Data.Foldable.elem x ys.

#[global] Definition isn'tIn {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.String -> a -> list a -> bool :=
  fun _msg x ys => Data.Foldable.notElem x ys.

(* Skipping definition `Util.chunkList' *)

Fixpoint changeLast {a : Type} (arg_0__ : list a) (arg_1__ : a) : list a
  := match arg_0__, arg_1__ with
     | nil, _ => PlainPanic.panic (GHC.Base.hs_string__ "changeLast")
     | cons _ nil, x => cons x nil
     | cons x xs, x' => cons x (changeLast xs x')
     end.

#[global] Definition whenNonEmpty {m : Type -> Type} {a : Type}
  `{GHC.Base.Applicative m}
   : list a -> (GHC.Base.NonEmpty a -> m unit) -> m unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, _ => GHC.Base.pure tt
    | cons x xs, f => f (GHC.Base.NEcons x xs)
    end.

(* Skipping definition `Util.minWith' *)

(* Skipping definition `Util.nubSort' *)

#[global] Definition ordNub {a : Type} `{GHC.Base.Ord a} : list a -> list a :=
  fun xs =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | _, nil => nil
         | s, cons x xs =>
             if Data.Set.Internal.member x s : bool then go s xs else
             cons x (go (Data.Set.Internal.insert x s) xs)
         end in
    go Data.Set.Internal.empty xs.

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
     | _, _, _, _ => PlainPanic.panic (GHC.Base.hs_string__ "Util: foldl2")
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

Fixpoint splitAtList {b : Type} {a : Type} (arg_0__ : list b) (arg_1__ : list a)
  : (list a * list a)%type
  := match arg_0__, arg_1__ with
     | nil, xs => pair nil xs
     | _, (nil as xs) => pair xs xs
     | cons _ xs, cons y ys =>
         let 'pair ys' ys'' := splitAtList xs ys in
         pair (cons y ys') ys''
     end.

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

#[global] Definition last2 {a : Type} : list a -> (a * a)%type :=
  let partialError :=
    PlainPanic.panic (GHC.Base.hs_string__ "last2 - list length less than two") in
  Data.Foldable.foldl' (fun arg_1__ arg_2__ =>
                          match arg_1__, arg_2__ with
                          | pair _ x2, x => pair x2 x
                          end) (pair partialError partialError).

#[global] Definition lastMaybe {a : Type} : list a -> option a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => None
    | xs => Some (GHC.List.last xs)
    end.

#[global] Definition snocView {a : Type} : list a -> option (list a * a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => None
    | xs =>
        let go {a} : list a -> (list a * a)%type :=
          fix go (arg_1__ : list a) : (list a * a)%type
            := match arg_1__ with
               | cons x nil => pair nil x
               | cons x xs => let 'pair xs' x' := go xs in pair (cons x xs') x'
               | nil => GHC.Err.error (GHC.Base.hs_string__ "impossible")
               end in
        let 'pair xs x := go xs in
        Some (pair xs x)
    end.

#[global] Definition split
   : GHC.Char.Char -> GHC.Base.String -> list GHC.Base.String :=
  HsToCoq.DeferredFix.deferredFix2 (fun split
                                    (c : GHC.Char.Char)
                                    (s : GHC.Base.String) =>
                                      let 'pair chunk rest := GHC.List.break (fun arg_0__ => arg_0__ GHC.Base.== c)
                                                                s in
                                      match rest with
                                      | nil => cons chunk nil
                                      | cons _ rest => cons chunk (split c rest)
                                      end).

#[global] Definition capitalise : GHC.Base.String -> GHC.Base.String :=
  fun arg_0__ => match arg_0__ with | nil => nil | cons c cs => cons c cs end.

#[global] Definition isEqual : comparison -> bool :=
  fun arg_0__ => match arg_0__ with | Gt => false | Eq => true | Lt => false end.

#[global] Definition thenCmp : comparison -> comparison -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Eq, ordering => ordering
    | ordering, _ => ordering
    end.

Fixpoint eqListBy {a : Type} (arg_0__ : a -> a -> bool) (arg_1__ arg_2__
                    : list a) : bool
  := match arg_0__, arg_1__, arg_2__ with
     | _, nil, nil => true
     | eq, cons x xs, cons y ys => andb (eq x y) (eqListBy eq xs ys)
     | _, _, _ => false
     end.

#[global] Definition eqMaybeBy {a : Type}
   : (a -> a -> bool) -> option a -> option a -> bool :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, None, None => true
    | eq, Some x, Some y => eq x y
    | _, _, _ => false
    end.

Fixpoint cmpList {a : Type} (arg_0__ : a -> a -> comparison) (arg_1__ arg_2__
                   : list a) : comparison
  := match arg_0__, arg_1__, arg_2__ with
     | _, nil, nil => Eq
     | _, nil, _ => Lt
     | _, _, nil => Gt
     | cmp, cons a as_, cons b bs =>
         match cmp a b with
         | Eq => cmpList cmp as_ bs
         | xxx => xxx
         end
     end.

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
  fun f pairs => GHC.Base.map (fun '(pair a b) => f a b) pairs.

Fixpoint seqList {a : Type} {b : Type} (arg_0__ : list a) (arg_1__ : b) : b
  := match arg_0__, arg_1__ with
     | nil, b => b
     | cons x xs, b => GHC.Prim.seq x (seqList xs b)
     end.

(* Skipping definition `Util.global' *)

(* Skipping definition `Util.consIORef' *)

(* Skipping definition `Util.globalM' *)

(* Skipping definition `Util.sharedGlobal' *)

(* Skipping definition `Util.sharedGlobalM' *)

(* Skipping definition `Util.looksLikeModuleName' *)

Axiom looksLikePackageName : GHC.Base.String -> bool.

(* Skipping definition `Util.getCmd' *)

(* Skipping definition `Util.toCmdArgs' *)

(* Skipping definition `Util.toArgs' *)

#[global] Definition exactLog2 : GHC.Num.Integer -> option GHC.Num.Integer :=
  fun x =>
    let x' := GHC.Real.fromIntegral x : GHC.Int.Int32 in
    let c := Data.Bits.countTrailingZeros x' in
    if x GHC.Base.<= #0 : bool then None else
    if x GHC.Base.> GHC.Real.fromIntegral (GHC.Enum.maxBound : GHC.Int.Int32) : bool
    then None else
    if (x' Data.Bits..&.(**) (GHC.Num.negate x')) GHC.Base./= x' : bool
    then None else
    Some (GHC.Real.fromIntegral c).

(* Skipping definition `Util.readRational__' *)

(* Skipping definition `Util.readRational' *)

(* Skipping definition `Util.readHexRational' *)

(* Skipping definition `Util.readHexRational__' *)

(* Skipping definition `Util.doesDirNameExist' *)

(* Skipping definition `Util.getModificationUTCTime' *)

(* Skipping definition `Util.modificationTimeIfExists' *)

#[global] Definition withAtomicRename {m : Type -> Type} {a : Type}
  `{Control.Monad.IO.Class.MonadIO m}
   : GHC.Base.String -> (GHC.Base.String -> m a) -> m a :=
  fun targetFile f =>
    let enableAtomicRename : bool := true in
    if enableAtomicRename : bool
    then let temp :=
           targetFile System.FilePath.Posix.<.> GHC.Base.hs_string__ "tmp" in
         f temp GHC.Base.>>=
         (fun res =>
            Control.Monad.IO.Class.liftIO (System.Directory.renameFile temp targetFile)
            GHC.Base.>>
            GHC.Base.return_ res) else
    f targetFile.

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

#[global] Definition overrideWith : bool -> OverridingBool -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | b, Auto => b
    | _, Always => true
    | _, Never => false
    end.

Module Notations.
Notation "'_Util.<&&>_'" := (op_zlzazazg__).
Infix "Util.<&&>" := (_<&&>_) (at level 99).
Notation "'_Util.<||>_'" := (op_zlzbzbzg__).
Infix "Util.<||>" := (_<||>_) (at level 99).
End Notations.

(* External variables:
     Eq Gt Lt None Some Type andb bool comparison cons false list nat nil op_zt__
     option orb pair true tt unit Control.Monad.IO.Class.MonadIO
     Control.Monad.IO.Class.liftIO Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Coq.Lists.List.skipn Data.Bits.Bits Data.Bits.countTrailingZeros
     Data.Bits.op_zizazi__ Data.Bits.xor Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Foldable.elem Data.Foldable.foldl' Data.Foldable.foldr
     Data.Foldable.notElem Data.Foldable.null Data.Functor.op_zlzdzg__
     Data.OldList.zipWith4 Data.Set.Internal.empty Data.Set.Internal.insert
     Data.Set.Internal.member GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Monad
     GHC.Base.NEcons GHC.Base.NonEmpty GHC.Base.Ord GHC.Base.String GHC.Base.const
     GHC.Base.liftA2 GHC.Base.liftM GHC.Base.map GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Base.op_zsze__ GHC.Base.pure GHC.Base.return_ GHC.Char.Char
     GHC.Enum.maxBound GHC.Err.error GHC.Err.patternFailure GHC.Int.Int32
     GHC.List.break GHC.List.last GHC.List.reverse GHC.List.zip GHC.List.zipWith
     GHC.List.zipWith3 GHC.Num.Integer GHC.Num.fromInteger GHC.Num.negate
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Prim.seq GHC.Real.fromIntegral
     HsToCoq.DeferredFix.deferredFix2 HsToCoq.Err.Build_Default HsToCoq.Err.Default
     PlainPanic.panic System.Directory.renameFile System.FilePath.Posix.op_zlzizg__
*)
