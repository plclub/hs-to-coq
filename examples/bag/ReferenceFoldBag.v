Require Import Bag.
Require Import Proofs.

Require Import Proofs.Data.Foldable.

Require Import ListUtils.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope program_scope.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Bullet Behavior "Strict Subproofs".

(* From Bag.hs:171-176, in the comments *)
Definition referenceFoldBag {r} {a} : (r -> r -> r) -> (a -> r) -> r -> Bag
                                      a -> r :=
  fix referenceFoldBag arg_27__ arg_28__ arg_29__ arg_30__
        := match arg_27__ , arg_28__ , arg_29__ , arg_30__ with
             | t , u , e , Mk_EmptyBag => e
             | t , u , e , (Mk_UnitBag x) => u x
             | t , u , e , (Mk_TwoBags b1 b2) => t (referenceFoldBag t u e b1)
                                                   (referenceFoldBag t u e b2)
             | t , u , e , (Mk_ListBag xs) => Coq.Lists.List.fold_right
                                              (Coq.Program.Basics.compose t u) e xs
           end.
(* Original:
foldBag t u e EmptyBag        = e
foldBag t u e (UnitBag x)     = u x
foldBag t u e (TwoBags b1 b2) = (foldBag t u e b1) `t` (foldBag t u e b2)
foldBag t u e (ListBag xs)    = foldr (t.u) e xs
*)

(* This equivalence requires that `t` be associative, which is documented, but
   also that `e` be the identity for `t`, which is *not*.  `foldBag` is only
   ever used twice in GHC, and in that case `e` is the identity, but there's a
   documentation/definition disagreement.  The ListBag case will always include
   `e`, so for the real implementation and the reference implementation to
   align, there must be a missing requirement that `e` be associative.  But that
   might be too strong of a requirement in the end! *)

Theorem referenceFoldBag_ok {A R} (f : R -> R -> R) (u : A -> R) (z : R) (b : Bag A) :
  associative f -> right_id z f -> left_id z f ->
  referenceFoldBag f u z b = fold_right f z (map u (bagToList b)).
Proof.
  move=> f_assoc z_right_id z_left_id.
  elim: b => [| x | l IHl r IHr | xs] //=.
  - by rewrite bagToList_TwoBags IHl IHr -fold_right_fold_right // map_app fold_right_app.
  - by rewrite bagToList_ListBag fold_right_map.
Qed.

Corollary foldBag_is_referenceFoldBag_if_id
          {A R} (f : R -> R -> R) (u : A -> R) (z : R) (b : Bag A) :
  associative f -> right_id z f -> left_id z f ->
  foldBag f u z b = referenceFoldBag f u z b.
Proof.
  move=> f_assoc z_right_id z_left_id.
  rewrite foldBag_ok // referenceFoldBag_ok //.
Qed.

Lemma foldBag_unwrap_base_case {A R} (f : R -> R -> R) (u : A -> R) (z z' : R) (b : Bag A) :
  associative f -> right_id z f ->
  well_formed_bag b -> ~~ isEmptyBag b ->
  foldBag f u z' b = f (foldBag f u z b) z'.
Proof.
  move=> f_assoc z_right_id.
  elim: b z' => [| x | l IHl r IHr | xs] //= z' wf _.
  - by rewrite z_right_id.
  - move: wf; rewrite eval_wf_TwoBags => /and4P [nonempty_l nonempty_r wf_l wf_r].
    by rewrite (IHl (foldBag f u z r)) // (IHl (foldBag f u z' r)) // -f_assoc IHr //.
  - rewrite !hs_coq_foldr_list /Basics.compose.
    case: xs wf => [|h xs] //= _.
    elim: xs h => [|x xs IH] //= h.
    + by rewrite z_right_id.
    + by rewrite -!f_assoc IH -f_assoc.
Qed.

Theorem foldBag_is_referenceFoldBag_if_right_id {A R} (f : R -> R -> R) (u : A -> R) (z : R) (b : Bag A) :
  associative f -> right_id z f ->
  well_formed_bag b ->
  foldBag f u z b = referenceFoldBag f u z b.
Proof.
  move=> f_assoc z_right_id.
  elim: b => [| x | l IHl r IHr | xs] //=.
  rewrite eval_wf_TwoBags => /and4P [nonempty_l nonempty_r wf_l wf_r].
  rewrite IHr //.
  by rewrite (foldBag_unwrap_base_case f u z) // IHl //.
Qed.

Module BagNeedsUnit.

  Definition pure {A} (x : A) : list A := [x].

  Lemma same_empty_list' {A} (tail : list A) (b : Bag A) :
    foldBag app pure tail b = referenceFoldBag app pure [] b ++ tail.
  Proof.
    elim: b tail => [| x | l IHl r IHr | xs] //= tail.
    - by rewrite IHr IHl app_assoc.
    - by rewrite
         /Data.Foldable.foldr /Foldable.Foldable__list /Data.Foldable.foldr__
         hs_coq_foldr_list' fold_right_cons fold_right_cons_nil.
  Qed.

  Lemma same_empty_list {A} (b : Bag A) :
    foldBag app pure [] b = referenceFoldBag app pure [] b.
  Proof. by rewrite same_empty_list' app_nil_r. Qed.

  Theorem counterexample {A} (x : A) (xs : list A) :
    exists b,
      well_formed_bag b /\
      foldBag app pure (x :: xs) b <> referenceFoldBag app pure (x :: xs) b.
  Proof. by exists (Mk_UnitBag x). Qed.

End BagNeedsUnit.

From Coq.Strings Require Ascii String.

Module StringUtil.
  Export Coq.Strings.Ascii Coq.Strings.String.
  #[global] Open Scope string_scope.

  Theorem append_assoc : associative append.
  Proof. by elim => [|? ? IH] ? ? //=; rewrite IH. Qed.

  Definition abcdBag : Bag string :=
    Mk_TwoBags (Mk_TwoBags (Mk_UnitBag "a") (Mk_UnitBag "b"))
               (Mk_TwoBags (Mk_UnitBag "c") (Mk_UnitBag "d")).

  Theorem abcd_wf : well_formed_bag abcdBag.
  Proof. done. Qed.

  Theorem append_left_id : left_id "" append.
  Proof. by vm_compute. Qed.

  Theorem append_right_id : right_id "" append.
  Proof. by elim=> [|? ? /= ->]. Qed.

  Lemma append_r_eqb_empty s1 a2 s2 :
    s1 ++ String a2 s2 =? "" = false.
  Proof. by case s1. Qed.

  Lemma length_append s1 s2 :
    length (s1 ++ s2) = (length s1 + length s2)%nat.
  Proof. by elim: s1 => [|? ? /= ->]. Qed.

  Fixpoint strip_dots_l s :=
    match s with
    | String "." s' => strip_dots_l s'
    | _ => s
    end.

  Lemma strip_dots_l_cons a s :
    a <> "."%char ->
    strip_dots_l (String a s) = String a s.
  Proof. by case: a; repeat case=> //. Qed.

  Lemma strip_dots_l_cons_dot s :
    strip_dots_l (String "." s) = strip_dots_l s.
  Proof. reflexivity. Qed.

  Lemma strip_dots_l_append s :
    strip_dots_l ("." ++ s) = strip_dots_l s.
  Proof. reflexivity. Qed.

  Lemma strip_dots_l_idempotent s : strip_dots_l (strip_dots_l s) = strip_dots_l s.
  Proof.
    elim: s => [|a s IH] //.
    - simpl.
      case: a => //; repeat case=> //.
  Qed.

  Fixpoint strip_dots_r s :=
    match s with
    | "" => ""
    | String "." s' => let s'' := strip_dots_r s' in
                       if s'' =? ""
                       then ""
                       else String "." s''
    | String a s' => String a (strip_dots_r s')
    end.

  Lemma strip_dots_r_append s :
    strip_dots_r (s ++ ".") = strip_dots_r s.
  Proof.
    elim: s => [|a s IH] //=.
    by rewrite IH.
  Qed.

  Lemma strip_dots_r_cons a s :
    a <> "."%char ->
    strip_dots_r (String a s) = String a (strip_dots_r s).
  Proof.
    move=> nondot /=.
    by case: a nondot; repeat case=> //.
  Qed.

  Lemma strip_dots_r_idempotent s : strip_dots_r (strip_dots_r s) = strip_dots_r s.
  Proof.
    elim: s => [|a s IH] //.
    - case: (Ascii.ascii_dec a ".") => [-> /= | nondot].
      + case: (strip_dots_r s) IH => [|a' s'] //= ->.
        by rewrite /eqb.
      + by rewrite !strip_dots_r_cons // IH.
  Qed.

  Lemma strip_dots_lr_swap s : strip_dots_l (strip_dots_r s) = strip_dots_r (strip_dots_l s).
  Proof.
    elim: s => [|a s IH] //.
    - case: (Ascii.ascii_dec a ".") => [-> /= | nondot].
      + rewrite -IH.
        by case (strip_dots_r s).
      + rewrite strip_dots_r_cons // !strip_dots_l_cons // strip_dots_r_cons //.
  Qed.

  Definition dot_append s1 s2 := strip_dots_r s1 ++ "." ++ strip_dots_l s2.

  Lemma dot_append_nonempty s1 s2 :
    dot_append s1 s2 =? "" = false.
  Proof.
    by rewrite /dot_append; case (strip_dots_r _).
  Qed.

  Lemma dot_append_nil_l s : dot_append "" s = "." ++ strip_dots_l s.
  Proof. reflexivity. Qed.

  Lemma dot_append_nil_r s : dot_append s "" = strip_dots_r s ++ ".".
  Proof. reflexivity. Qed.

  Lemma dot_append_append_l s1 s2 : dot_append (s1 ++ ".") s2 = dot_append s1 s2.
  Proof. by rewrite /dot_append strip_dots_r_append. Qed.

  Lemma dot_append_append_r s1 s2 : dot_append s1 ("." ++ s2) = dot_append s1 s2.
  Proof. done. Qed.

  Lemma dot_append_strip_l s1 s2 : dot_append (strip_dots_r s1) s2 = dot_append s1 s2.
  Proof. by rewrite /dot_append strip_dots_r_idempotent. Qed.

  Lemma dot_append_strip_r s1 s2 : dot_append s1 (strip_dots_l s2) = dot_append s1 s2.
  Proof. by rewrite /dot_append strip_dots_l_idempotent. Qed.

  Lemma dot_append_cons_nondot_l a s1 s2 :
    a <> "."%char ->
    dot_append (String a s1) s2 = String a (dot_append s1 s2).
  Proof.
    move=> nondot; rewrite /dot_append strip_dots_r_cons //.
  Qed.

  Fixpoint all_dots s := match s with
                         | ""           => true
                         | String "." s => all_dots s
                         | _            => false
                         end.

  Fixpoint all_nondots s := match s with
                            | ""           => true
                            | String "." _ => false
                            | String _   s => all_nondots s
                            end.

  Lemma strip_dots_r_all_dots s :
    all_dots s ->
    strip_dots_r s = "".
  Proof.
    elim: s => [|a s IH] // all_s.
    have ?: a = "."%char by move: all_s; case: a; repeat case => //.
    subst a.
    by rewrite /= IH //.
  Qed.

  Lemma strip_dots_l_all_dots s :
    all_dots s ->
    strip_dots_l s = "".
  Proof.
    elim: s => [|a s IH] //=.
    by case: a; repeat case => //.
  Qed.

  Lemma strip_dots_r_all_nondots s :
    all_nondots s ->
    strip_dots_r s = s.
  Proof.
    elim: s => [|a s IH] //=.
    case: a; do 8 case => //.
    all: by move=> /IH->.
  Qed.

  Lemma strip_dots_l_all_nondots s :
    all_nondots s ->
    strip_dots_l s = s.
  Proof.
    case: s; by repeat case => //.
  Qed.

  Lemma strip_dots_r_not_all_dots s :
    ~~ all_dots s ->
    {s' & {a' : ascii & a' <> "."%char & strip_dots_r s = s' ++ String a' ""}}.
  Proof.
    elim: s => [|a s IH] //.
    case: (Ascii.ascii_dec a ".") => [-> /= | nondot].
    - move=> /IH [s' [a' nondot ->]] /=.
      exists (String "." s'), a' => //.
      by replace (_ =? "") with false by case: s' => //.
    - rewrite strip_dots_r_cons // => _.
      case D: (all_dots s).
      + rewrite strip_dots_r_all_dots //.
        by exists "", a.
      + case: IH => [|s' [a' nondot' ->]]; first by rewrite D.
        by exists (String a s'), a'.
  Qed.

  Lemma strip_dots_r_not_all_dots' s :
    ~~ all_dots s ->
    {a' & {s' & strip_dots_r s = String a' s'}}.
  Proof.
    elim: s => [|a s IH] //.
    case: (Ascii.ascii_dec a ".") => [-> /= | nondot].
    - move=> /IH [a' [s' ->]] /=.
      by eauto.
    - rewrite strip_dots_r_cons // => _.
      by eauto.
  Qed.

  Lemma strip_dots_l_not_all_dots s :
    ~~ all_dots s ->
    {a' : ascii & a' <> "."%char & {s' & strip_dots_l s = String a' s'}}.
  Proof.
    elim: s => [|a s IH] //.
    case: (Ascii.ascii_dec a ".") => [-> /= | nondot].
    - move=> /IH [a' nondot [s' ->]] /=.
      by eauto.
    - rewrite strip_dots_l_cons // => _.
      by eauto.
  Qed.

  Lemma strip_dots_r_all_dots_P s : reflect (strip_dots_r s = "") (all_dots s).
  Proof.
    case B: (all_dots s); constructor.
    - by apply strip_dots_r_all_dots.
    - by case: (strip_dots_r_not_all_dots' s) => [|a' [s' ->]]; first by rewrite B.
  Qed.

  Lemma strip_dots_l_all_dots_P s : reflect (strip_dots_l s = "") (all_dots s).
  Proof.
    case B: (all_dots s); constructor.
    - by apply strip_dots_l_all_dots.
    - by case: (strip_dots_l_not_all_dots s) => [|a' _ [s' ->]]; first by rewrite B.
  Qed.

  Lemma strip_dots_r_append_not_dots s1 s2 :
    ~~ all_dots s2 ->
    strip_dots_r (s1 ++ s2) = s1 ++ strip_dots_r s2.
  Proof.
    elim: s1 => [|a1 s1 IH] //=.
    case: (Ascii.ascii_dec a1 ".") => [-> /= | nondot].
    - move=> not_dots.
      rewrite IH //.
      suff ->: (s1 ++ strip_dots_r s2 =? "") = false by done.
      case: s1 {IH} => //=.
      by move: not_dots => /strip_dots_r_not_all_dots [[|? ?] [? ? ->]].
    - move=> /IH ->.
      by case: a1 nondot; repeat case => //.
  Qed.

  Lemma strip_dots_l_append_not_dots s1 s2 :
    ~~ all_dots s1 ->
    strip_dots_l (s1 ++ s2) = strip_dots_l s1 ++ s2.
  Proof.
    elim: s1 => [|a1 s1 IH] //=.
    case: (Ascii.ascii_dec a1 ".") => [-> //= | nondot].
    by case: a1 nondot; do 8 case=> //.
  Qed.

  Lemma strip_dots_r_preserves_dottiness s :
    all_dots s = all_dots (strip_dots_r s).
  Proof.
    elim: s => [|a s IH] //=.
    case: a; do 8 case=> //=.
    rewrite IH.
    by case: (strip_dots_r s).
  Qed.

  Lemma strip_dots_l_preserves_dottiness s :
    all_dots s = all_dots (strip_dots_l s).
  Proof.
    elim: s => [|a s IH] //=.
    by case: a; do 8 case=> //=.
  Qed.

  Lemma dot_append_assoc : associative dot_append.
  Proof.
    move=> s1 s2 s3.
    rewrite /dot_append.
    case D2: (all_dots s2).
    - by rewrite (strip_dots_r_all_dots s2) // (strip_dots_l_all_dots s2) //
                 append_right_id append_left_id
                 strip_dots_r_append strip_dots_l_append
                 strip_dots_r_idempotent strip_dots_l_idempotent.
    - rewrite strip_dots_l_append_not_dots; first by rewrite -strip_dots_r_preserves_dottiness D2.
      rewrite !append_assoc.
      rewrite strip_dots_r_append_not_dots; first by rewrite -strip_dots_l_preserves_dottiness D2.
      by rewrite strip_dots_lr_swap.
  Qed.
End StringUtil.

Module IdNotAssoc.
  Import StringUtil.

  Definition f s1 s2 :=
    if eqb s1 "" || eqb s2 ""
    then s1 ++ s2
    else "(" ++ s1 ++ "," ++ s2 ++ ")".

  Theorem f_left : left_id "" f.
  Proof. vm_compute; reflexivity. Qed.

  Theorem f_right : right_id "" f.
  Proof.
    by move=> s; rewrite /f; rewrite eqb_refl orbT append_right_id.
  Qed.

  Theorem f_nonassoc : ~ associative f.
  Proof. by move=> /(_ "a" "b" "c"). Qed.

  Theorem need_assoc :
    foldBag          f id "" abcdBag <>
    referenceFoldBag f id "" abcdBag.
  Proof. by vm_compute. Qed.
End IdNotAssoc.

Module AssocLeftIdNotRightId.
  Import StringUtil.

  Definition f s1 s2 :=
    if s1 =? ""
    then s2
    else dot_append s1 s2.

  Theorem f_assoc : associative f.
  Proof.
    move=> [|a1 s1] [|a2 s2] s3 //=; rewrite /f ?eqb_refl !/(eqb (String _ _) "") dot_append_nonempty.
    - by rewrite dot_append_nil_r dot_append_append_l dot_append_strip_l.
    - apply dot_append_assoc.
  Qed.

  Theorem f_left : left_id "" f.
  Proof. done. Qed.

  Theorem f_not_right e : ~ right_id e f.
  Proof.
    move=> /(_ ".x").
    rewrite /f /=.
    discriminate.
  Qed.

  Theorem need_right_id :
    foldBag          f id "" abcdBag <>
    referenceFoldBag f id "" abcdBag.
  Proof. by vm_compute. Qed.
End AssocLeftIdNotRightId.

Module AssocRightIdNotLeftId_NotWF.
  Import StringUtil.

  Definition f s1 s2 :=
    if s2 =? ""
    then s1
    else dot_append s1 s2.

  Theorem f_assoc : associative f.
  Proof.
    move=> s1 [|a2 s2] [|a3 s3] //=; rewrite /f ?eqb_refl !/(eqb (String _ _) "") ?dot_append_nonempty.
    - by rewrite dot_append_nil_l dot_append_append_r dot_append_strip_r.
    - apply dot_append_assoc.
  Qed.

  Theorem f_right : right_id "" f.
  Proof. done. Qed.

  Theorem f_not_left e : ~ left_id e f.
  Proof.
    move=> /(_ "x.").
    rewrite /f /= /dot_append.
    move => /(f_equal length).
    rewrite !length_append /= PeanoNat.Nat.add_comm.
    discriminate.
  Qed.

  Theorem need_left_id :
    foldBag          f id "" (Mk_TwoBags Mk_EmptyBag abcdBag) <>
    referenceFoldBag f id "" (Mk_TwoBags Mk_EmptyBag abcdBag).
  Proof. by vm_compute. Qed.
End AssocRightIdNotLeftId_NotWF.
