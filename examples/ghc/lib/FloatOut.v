(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Bag.
Require Coq.Init.Datatypes.
Require Core.
Require CoreUtils.
Require Data.Foldable.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Types.Tickish.
Require Id.
Require IntMap.
Require MkCore.
Require Panic.
Require SetLevels.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

#[global] Definition MinorEnv :=
  (IntMap.IntMap (Bag.Bag MkCore.FloatBind))%type.

#[global] Definition MajorEnv :=
  (IntMap.IntMap MinorEnv)%type.

Inductive FloatStats : Type := | FlS : nat -> nat -> nat -> FloatStats.

#[global] Definition FloatLet :=
  Core.CoreBind%type.

Inductive FloatBinds : Type :=
  | FB
   : (Bag.Bag FloatLet) -> (Bag.Bag MkCore.FloatBind) -> MajorEnv -> FloatBinds.

(* Midamble *)

#[global] Instance Default_FloatStats : HsToRocq.Err.Default FloatStats :=
  HsToRocq.Err.Build_Default _ (FlS HsToRocq.Err.default HsToRocq.Err.default HsToRocq.Err.default).


(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `FloatOut.Outputable__FloatBinds' *)

(* Skipping definition `FloatOut.floatOutwards' *)

#[global] Definition addTopFloatPairs
   : Bag.Bag Core.CoreBind ->
     list (Core.Id * Core.CoreExpr)%type -> list (Core.Id * Core.CoreExpr)%type :=
  fun float_bag prs =>
    let add :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | Core.NonRec b r, prs => cons (pair b r) prs
        | Core.Rec prs1, prs2 => Coq.Init.Datatypes.app prs1 prs2
        end in
    Data.Foldable.foldr add prs float_bag.

#[global] Definition flattenMinor : MinorEnv -> Bag.Bag MkCore.FloatBind :=
  IntMap.foldr Bag.unionBags Bag.emptyBag.

#[global] Definition flattenMajor : MajorEnv -> Bag.Bag MkCore.FloatBind :=
  IntMap.foldr (Bag.unionBags GHC.Base.∘ flattenMinor) Bag.emptyBag.

#[global] Definition flattenTopFloats : FloatBinds -> Bag.Bag Core.CoreBind :=
  fun '(FB tops ceils defs) =>
    Panic.assertPpr (Bag.isEmptyBag (flattenMajor defs)) (Panic.someSDoc)
    (Panic.assertPpr (Bag.isEmptyBag ceils) (Panic.someSDoc) tops).

Axiom floatBind : SetLevels.LevelledBind ->
                  (FloatStats * FloatBinds * list Core.CoreBind)%type.

#[global] Definition floatTopBind
   : SetLevels.LevelledBind -> (FloatStats * Bag.Bag Core.CoreBind)%type :=
  fun bind =>
    let 'pair (pair fs floats) bind' := (floatBind bind) in
    let float_bag := flattenTopFloats floats in
    match bind' with
    | cons (Core.Rec prs) nil =>
        pair fs (Bag.unitBag (Core.Rec (addTopFloatPairs float_bag prs)))
    | cons (Core.NonRec b e) nil =>
        pair fs (Bag.snocBag float_bag (Core.NonRec b e))
    | _ => Panic.pprPanic (GHC.Base.hs_string__ "floatTopBind") (Panic.someSDoc)
    end.

#[global] Definition splitRecFloats
   : Bag.Bag MkCore.FloatBind ->
     (list (Core.Id * Core.CoreExpr)%type * list (Core.Id * Core.CoreExpr)%type *
      Bag.Bag MkCore.FloatBind)%type :=
  fun fs =>
    let fix go arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | ul_prs, prs, cons (MkCore.FloatLet (Core.NonRec b r)) fs =>
             if andb (Core.isUnliftedType (Id.idType b)) (negb (Id.isJoinId b)) : bool
             then go (cons (pair b r) ul_prs) prs fs else
             go ul_prs (cons (pair b r) prs) fs
         | _, _, _ =>
             match arg_0__, arg_1__, arg_2__ with
             | ul_prs, prs, cons (MkCore.FloatLet (Core.Rec prs')) fs =>
                 go ul_prs (Coq.Init.Datatypes.app prs' prs) fs
             | ul_prs, prs, fs =>
                 pair (pair (GHC.List.reverse ul_prs) prs) (Bag.listToBag fs)
             end
         end in
    go nil nil (Bag.bagToList fs).

#[global] Definition install
   : Bag.Bag MkCore.FloatBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun defn_groups expr => Data.Foldable.foldr MkCore.wrapFloat expr defn_groups.

#[global] Definition installUnderLambdas
   : Bag.Bag MkCore.FloatBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun floats e =>
    let fix go arg_0__
      := match arg_0__ with
         | Core.Lam b e => Core.Lam b (go e)
         | e => install floats e
         end in
    if Bag.isEmptyBag floats : bool then e else
    go e.

#[global] Definition add_stats : FloatStats -> FloatStats -> FloatStats :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FlS a1 b1 c1, FlS a2 b2 c2 =>
        FlS (a1 GHC.Num.+ a2) (b1 GHC.Num.+ b2) (c1 GHC.Num.+ c2)
    end.

#[global] Definition emptyFloats : FloatBinds :=
  FB Bag.emptyBag Bag.emptyBag IntMap.empty.

#[global] Definition plusMinor : MinorEnv -> MinorEnv -> MinorEnv :=
  IntMap.unionWith Bag.unionBags.

#[global] Definition plusMajor : MajorEnv -> MajorEnv -> MajorEnv :=
  IntMap.unionWith plusMinor.

#[global] Definition plusFloats : FloatBinds -> FloatBinds -> FloatBinds :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FB t1 c1 l1, FB t2 c2 l2 =>
        FB (Bag.unionBags t1 t2) (Bag.unionBags c1 c2) (plusMajor l1 l2)
    end.

#[global] Definition zeroStats : FloatStats :=
  FlS #0 #0 #0.

Fixpoint floatList {a} {b} (arg_0__ : (a -> (FloatStats * FloatBinds * b)%type))
                   (arg_1__ : list a) : (FloatStats * FloatBinds * list b)%type
  := match arg_0__, arg_1__ with
     | _, nil => pair (pair zeroStats emptyFloats) nil
     | f, cons a as_ =>
         let 'pair (pair fs_a binds_a) b := f a in
         let 'pair (pair fs_as binds_as) bs := floatList f as_ in
         pair (pair (add_stats fs_a fs_as) (plusFloats binds_a binds_as)) (cons b bs)
     end.

Axiom floatExpr : SetLevels.LevelledExpr ->
                  (FloatStats * FloatBinds * Core.CoreExpr)%type.

Axiom partitionByLevel : SetLevels.Level ->
                         FloatBinds -> (FloatBinds * Bag.Bag MkCore.FloatBind)%type.

#[global] Definition floatBody
   : SetLevels.Level ->
     SetLevels.LevelledExpr -> (FloatStats * FloatBinds * Core.CoreExpr)%type :=
  fun lvl arg =>
    let 'pair (pair fsa floats) arg' := (floatExpr arg) in
    let 'pair floats' heres := (partitionByLevel lvl floats) in
    pair (pair fsa floats') (install heres arg').

Axiom floatRhs : Core.CoreBndr ->
                 SetLevels.LevelledExpr -> (FloatStats * FloatBinds * Core.CoreExpr)%type.

#[global] Definition get_stats : FloatStats -> (nat * nat * nat)%type :=
  fun '(FlS a b c) => pair (pair a b) c.

#[global] Definition sum_stats : list FloatStats -> FloatStats :=
  fun xs => Data.Foldable.foldr add_stats zeroStats xs.

#[global] Definition add_to_stats : FloatStats -> FloatBinds -> FloatStats :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FlS a b c, FB tops ceils others =>
        FlS (a GHC.Num.+ Bag.lengthBag tops) ((b GHC.Num.+ Bag.lengthBag ceils)
                                              GHC.Num.+
                                              Bag.lengthBag (flattenMajor others)) (c GHC.Num.+ #1)
    end.

#[global] Definition unitCaseFloat
   : SetLevels.Level ->
     Core.CoreExpr -> Core.Id -> Core.AltCon -> list Core.Var -> FloatBinds :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | SetLevels.Mk_Level major minor t, e, b, con, bs =>
        let floats := Bag.unitBag (MkCore.FloatCase e b con bs) in
        if t GHC.Base.== SetLevels.JoinCeilLvl : bool
        then FB Bag.emptyBag floats IntMap.empty else
        FB Bag.emptyBag Bag.emptyBag (IntMap.singleton major (IntMap.singleton minor
                                                              floats))
    end.

#[global] Definition unitLetFloat : SetLevels.Level -> FloatLet -> FloatBinds :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (SetLevels.Mk_Level major minor t as lvl), b =>
        let floats := Bag.unitBag (MkCore.FloatLet b) in
        if SetLevels.isTopLvl lvl : bool
        then FB (Bag.unitBag b) Bag.emptyBag IntMap.empty else
        if t GHC.Base.== SetLevels.JoinCeilLvl : bool
        then FB Bag.emptyBag floats IntMap.empty else
        FB Bag.emptyBag Bag.emptyBag (IntMap.singleton major (IntMap.singleton minor
                                                              floats))
    end.

#[global] Definition partitionAtJoinCeiling
   : FloatBinds -> (FloatBinds * Bag.Bag MkCore.FloatBind)%type :=
  fun '(FB tops ceils defs) => pair (FB tops Bag.emptyBag defs) ceils.

#[global] Definition atJoinCeiling
   : (FloatStats * FloatBinds * Core.CoreExpr)%type ->
     (FloatStats * FloatBinds * Core.CoreExpr)%type :=
  fun '(pair (pair fs floats) expr') =>
    let 'pair floats' ceils := partitionAtJoinCeiling floats in
    pair (pair fs floats') (install ceils expr').

#[global] Definition wrapTick
   : GHC.Types.Tickish.CoreTickish -> FloatBinds -> FloatBinds :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | t, FB tops ceils defns =>
        let maybe_tick := fun e => if CoreUtils.exprIsHNF e : bool then e else e in
        let wrap_bind :=
          fun arg_3__ =>
            match arg_3__ with
            | Core.NonRec binder rhs => Core.NonRec binder (maybe_tick rhs)
            | Core.Rec pairs => Core.Rec (Util.mapSnd maybe_tick pairs)
            end in
        let wrap_one :=
          fun arg_7__ =>
            match arg_7__ with
            | MkCore.FloatLet bind => MkCore.FloatLet (wrap_bind bind)
            | MkCore.FloatCase e b c bs => MkCore.FloatCase (maybe_tick e) b c bs
            end in
        let wrap_defns := Bag.mapBag wrap_one in
        FB (Bag.mapBag wrap_bind tops) (wrap_defns ceils) (IntMap.map (IntMap.map
                                                                       wrap_defns) defns)
    end.

(* External variables:
     andb bool cons list nat negb nil op_zt__ pair Bag.Bag Bag.bagToList Bag.emptyBag
     Bag.isEmptyBag Bag.lengthBag Bag.listToBag Bag.mapBag Bag.snocBag Bag.unionBags
     Bag.unitBag Coq.Init.Datatypes.app Core.AltCon Core.CoreBind Core.CoreBndr
     Core.CoreExpr Core.Id Core.Lam Core.NonRec Core.Rec Core.Var Core.isUnliftedType
     CoreUtils.exprIsHNF Data.Foldable.foldr GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.List.reverse GHC.Num.fromInteger GHC.Num.op_zp__
     GHC.Types.Tickish.CoreTickish Id.idType Id.isJoinId IntMap.IntMap IntMap.empty
     IntMap.foldr IntMap.map IntMap.singleton IntMap.unionWith MkCore.FloatBind
     MkCore.FloatCase MkCore.FloatLet MkCore.wrapFloat Panic.assertPpr Panic.pprPanic
     Panic.someSDoc SetLevels.JoinCeilLvl SetLevels.Level SetLevels.LevelledBind
     SetLevels.LevelledExpr SetLevels.Mk_Level SetLevels.isTopLvl Util.mapSnd
*)
