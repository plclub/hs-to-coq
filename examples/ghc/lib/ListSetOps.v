(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Outputable.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require Data.Ord.
Require Data.Set.Internal.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Prim.
Require HsToRocq.Err.
Require Panic.
Require Util.
Import GHC.Base.Notations.

(* Converted type declarations: *)

#[global] Definition Assoc a b :=
  (list (a * b)%type)%type.

(* Converted value declarations: *)

(* Skipping definition `ListSetOps.getNth' *)

#[global] Definition unionListsOrd {a : Type} `{Util.HasDebugCallStack}
  `{Outputable.Outputable a} `{GHC.Base.Ord a}
   : list a -> list a -> list a :=
  fun xs ys =>
    let set_ys := Data.Set.Internal.fromList ys in
    Coq.Init.Datatypes.app (GHC.List.filter (fun e =>
                                               negb (Data.Set.Internal.member e set_ys)) xs) ys.

#[global] Definition isIn {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.String -> a -> list a -> bool :=
  fun _msg x ys => Data.Foldable.elem x ys.

#[global] Definition isn'tIn {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.String -> a -> list a -> bool :=
  fun _msg x ys => Data.Foldable.notElem x ys.

#[global] Definition unionLists {a} `{GHC.Base.Eq_ a}
   : list a -> list a -> list a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | xs, nil => xs
    | nil, ys => ys
    | cons x nil, ys =>
        if isIn (GHC.Base.hs_string__ "unionLists") x ys : bool then ys else
        cons x ys
    | _, _ =>
        match arg_0__, arg_1__ with
        | xs, cons y nil =>
            if isIn (GHC.Base.hs_string__ "unionLists") y xs : bool then xs else
            cons y xs
        | _, _ =>
            match arg_0__, arg_1__ with
            | xs, ys =>
                Coq.Init.Datatypes.app (Coq.Lists.List.flat_map (fun x =>
                                                                   if isn'tIn (GHC.Base.hs_string__ "unionLists") x
                                                                      ys : bool
                                                                   then cons x nil else
                                                                   nil) xs) ys
            end
        end
    end.

#[global] Definition minusList {a : Type} `{GHC.Base.Ord a}
   : list a -> list a -> list a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, _ => nil
    | (cons x nil as xs), ys => if Data.Foldable.elem x ys : bool then nil else xs
    | _, _ =>
        match arg_0__, arg_1__ with
        | xs, nil => xs
        | xs, cons y nil => GHC.List.filter (GHC.Prim.rightSection _GHC.Base./=_ y) xs
        | xs, ys =>
            let yss := Data.Set.Internal.fromList ys in
            GHC.List.filter (GHC.Prim.rightSection Data.Set.Internal.notMember yss) xs
        end
    end.

Fixpoint assocDefaultUsing {a : Type} {b : Type} (arg_0__ : a -> a -> bool)
                           (arg_1__ : b) (arg_2__ : Assoc a b) (arg_3__ : a) : b
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, deflt, nil, _ => deflt
     | eq, deflt, cons (pair k v) rest, key =>
         if eq k key : bool then v else
         assocDefaultUsing eq deflt rest key
     end.

#[global] Definition assoc {a} {b} `{GHC.Base.Eq_ a} `{HsToRocq.Err.Default b}
   : GHC.Base.String -> Assoc a b -> a -> b :=
  fun crash_msg list key =>
    assocDefaultUsing _GHC.Base.==_ (Panic.panic (Coq.Init.Datatypes.app
                                                  (GHC.Base.hs_string__ "Failed in assoc: ") crash_msg)) list key.

#[global] Definition assocDefault {a : Type} {b : Type} `{GHC.Base.Eq_ a}
   : b -> Assoc a b -> a -> b :=
  fun deflt list key => assocDefaultUsing _GHC.Base.==_ deflt list key.

#[global] Definition assocUsing {a} {b} `{HsToRocq.Err.Default b}
   : (a -> a -> bool) -> GHC.Base.String -> Assoc a b -> a -> b :=
  fun eq crash_msg list key =>
    assocDefaultUsing eq (Panic.panic (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                               "Failed in assoc: ") crash_msg)) list key.

#[global] Definition assocMaybe {a : Type} {b : Type} `{GHC.Base.Eq_ a}
   : Assoc a b -> a -> option b :=
  fun alist key =>
    let fix lookup arg_0__
      := match arg_0__ with
         | nil => None
         | cons (pair tv ty) rest =>
             if key GHC.Base.== tv : bool
             then Some ty
             else lookup rest
         end in
    lookup alist.

#[global] Definition hasNoDups {a : Type} `{GHC.Base.Eq_ a} : list a -> bool :=
  fun xs =>
    let is_elem := isIn (GHC.Base.hs_string__ "hasNoDups") in
    let fix f arg_1__ arg_2__
      := match arg_1__, arg_2__ with
         | _, nil => true
         | seen_so_far, cons x xs =>
             if is_elem x seen_so_far : bool
             then false
             else f (cons x seen_so_far) xs
         end in
    f nil xs.

Axiom equivClasses : forall {a : Type},
                     (a -> a -> comparison) -> list a -> list (GHC.Base.NonEmpty a).

#[global] Definition removeDups {a : Type}
   : (a -> a -> comparison) ->
     list a -> (list a * list (GHC.Base.NonEmpty a))%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, nil => pair nil nil
    | _, cons x nil => pair (cons x nil) nil
    | cmp, xs =>
        let collect_dups {a}
         : list (GHC.Base.NonEmpty a) ->
           GHC.Base.NonEmpty a -> (list (GHC.Base.NonEmpty a) * a)%type :=
          fun arg_4__ arg_5__ =>
            match arg_4__, arg_5__ with
            | dups_so_far, GHC.Base.NEcons x nil => pair dups_so_far x
            | dups_so_far, (GHC.Base.NEcons x _ as dups) => pair (cons dups dups_so_far) x
            end in
        let 'pair dups xs' := Data.Traversable.mapAccumR collect_dups nil (equivClasses
                                                                           cmp xs) in
        pair xs' dups
    end.

#[global] Definition removeDupsOn {b : Type} {a : Type} `{GHC.Base.Ord b}
   : (a -> b) -> list a -> (list a * list (GHC.Base.NonEmpty a))%type :=
  fun f x => removeDups (Data.Ord.comparing f) x.

#[global] Definition nubOrdBy {a : Type}
   : (a -> a -> comparison) -> list a -> list a :=
  fun cmp xs => Data.Tuple.fst (removeDups cmp xs).

(* Skipping definition `ListSetOps.findDupsEq' *)

(* External variables:
     None Some Type bool comparison cons false list negb nil op_zt__ option pair true
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map Data.Foldable.elem
     Data.Foldable.notElem Data.Ord.comparing Data.Set.Internal.fromList
     Data.Set.Internal.member Data.Set.Internal.notMember Data.Traversable.mapAccumR
     Data.Tuple.fst GHC.Base.Eq_ GHC.Base.NEcons GHC.Base.NonEmpty GHC.Base.Ord
     GHC.Base.String GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.List.filter
     GHC.Prim.rightSection HsToRocq.Err.Default Outputable.Outputable Panic.panic
     Util.HasDebugCallStack
*)
