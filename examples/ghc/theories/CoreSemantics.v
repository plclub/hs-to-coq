(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import Unicode.Utf8.

From Coq      Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat seq.

Require Import Core CoreSubst Id.
Require Import Proofs.Core Proofs.ScopeInvariant Proofs.CoreSubst Proofs.CoreInduct.
Require Import GHC.Base GHC.List Data.Foldable Data.Bifunctor.
Require Import Proofs.GHC.Base Proofs.GHC.List Proofs.Data.Foldable HSUtil.
Require Import Proofs.Var.
Import Data.Functor.Notations.

Set Bullet Behavior "Strict Subproofs".

Fixpoint nth' {A} (xs : list A) (i : nat) : option A :=
  match xs , i with
  | [::]     , _    => None
  | x :: _   , O    => Some x
  | _ :: xs' , S i' => nth' xs' i'
  end.

Theorem nth'_nth {A} (xs : list A) i :
  nth' xs i = nth i (map Some xs) None.
Proof. elim: xs i => [|x xs IH] [|i] //=. Qed.

Definition subst (e₀ : CoreExpr) (n : Id) (e' : CoreExpr) : CoreExpr :=
  let fix subst e₀' := match e₀' with
        | Mk_Var n'        => if n == n' (* TODO?: not (isLocalVar n') && *)
                              then e'
                              else Mk_Var n'
        | Lit lit          => Lit lit
        | App e₁ e₂        => App (subst e₁) (subst e₂)
        | Lam n' e         => if n == n'
                              then Lam n' e
                              else Lam n' (subst e)
        | Let lb e₂        => match lb with
                              | NonRec n' e₁ => Let (NonRec n' (subst e₁)) (if n == n' then e₂ else subst e₂)
                              | Rec    bs    => if elem n (map fst bs)
                                                then Let (Rec bs) e₂
                                                else Let (Rec (map (fun '(v,rhs) => (v, subst rhs)) bs)) (subst e₂)
                              end
        | Case e n' τ alts => Case (subst e) n' τ
                                   (if n == n'
                                    then alts
                                    else map (λ '(Mk_Alt k ns u), Mk_Alt k ns (if elem n ns then u else subst u)) alts)
        | Cast e γ         => Cast (subst e) γ
(*        | Tick tick e      => Tick tick (subst e) *)
        | Mk_Type τ        => Mk_Type τ
        | Mk_Coercion γ    => Mk_Coercion γ
      end
  in subst e₀.

Definition substs (e₀ : CoreExpr) (ss : list (Id * CoreExpr)) : CoreExpr :=
  let substituting := lookup^~ ss in
  let fix subst e₀' := match e₀' with
        | Mk_Var n        => if substituting n is Some e' (* TODO?: not (isLocalVar n') && *)
                             then e'
                             else Mk_Var n
        | Lit lit         => Lit lit
        | App e₁ e₂       => App (subst e₁) (subst e₂)
        | Lam n e         => if substituting n is Some _
                             then Lam n e
                             else Lam n (subst e)
        | Let lb e₂       => match lb with
                             | NonRec n e₁ => Let (NonRec n (subst e₁))
                                                  (if substituting n is Some _ then e₂ else subst e₂)
                             | Rec    bs    => if has (isSome \o substituting \o fst) bs
                                               then Let (Rec bs) e₂
                                               else Let (Rec (map (fun '(v,rhs) => (v, subst rhs)) bs)) (subst e₂)
                             end
        | Case e n τ alts => Case (subst e) n τ
                                  (if substituting n is Some _
                                   then alts
                                   else map (λ '(Mk_Alt k ns u), Mk_Alt k ns
                                                             (if has (isSome \o substituting) ns
                                                             then u
                                                             else subst u))
                                            alts)
        | Cast e γ        => Cast (subst e) γ
(*        | Tick tick e     => Tick tick (subst e) *)
        | Mk_Type τ         => Mk_Type τ
        | Mk_Coercion γ      => Mk_Coercion γ
      end
  in subst e₀.

Ltac move_let :=
  match goal with
  | |- let x := ?e in _ => set x := e
  end.

Ltac if_equal :=
  match goal with
  | |- match ?b1 with true => ?t1 | false => ?f1 end = match ?b2 with true => ?t2 | false => ?f2 end =>
    suff: and3 (b1 = b2) (t1 = t2) (f1 = f2);
    [ by let bEQ := fresh in
         let tEQ := fresh in
         let fEQ := fresh in
         move=> [bEQ tEQ fEQ];
         rewrite ?bEQ ?tEQ ?fEQ
    | split=> // ]
  end.

Lemma map_cong_in {a b} (f g : a → b) xs :
  (∀ x, In x xs → f x = g x) →
  map f xs = map g xs.
Proof.
  elim: xs => [|x xs IH] //= EQ.
  rewrite EQ; last by left.
  rewrite IH // => x' INx'.
  by apply EQ; right.
Qed.

Theorem subst_substs e₀ n e' :
  subst e₀ n e' = substs e₀ [::(n,e')].
Proof.
  rewrite /subst /substs.
  match goal with |- ?fix_subst e₀ = ?fix_substs e₀ => set subst := fix_subst; set substs := fix_substs end.
  elim/core_induct: e₀ =>
    [ n' | lit | e₁  e₂ IH₁ IH₂ | n' e IH | [n' e₁ | bs] e₂ IH₁ IH₂ | e n' τ alts IH₁ IH₂
     | e γ IH (* | tick e IH *) | τ | γ ]
    //=.
  - by rewrite Eq_sym; case: (_ == _).
  - by rewrite IH₁ IH₂.
  - by rewrite IH Eq_sym; case: (_ == _).
  - by rewrite IH₁ IH₂ Eq_sym; case: (_ == _).
  - rewrite IH₂; if_equal.
    + elim: bs {IH₁} => [|[n' e] bs IHbs] //=.
      by rewrite elemC IHbs Eq_sym; case: (_ == _).
    + do 2 f_equal; apply map_cong_in => - [n' e] IN /=.
      by rewrite (IH₁ _ _ IN).
  - rewrite IH₁ Eq_sym; case: (_ == _); f_equal.
    apply map_cong_in => -[k ns u] IN; f_equal; if_equal.
    + elim: ns {IN} => [|n'' ns IHns] //=.
      by rewrite elemC IHns Eq_sym; case: (_ == _).
    + by rewrite (IH₂ _ _ _ IN).
   - by rewrite IH.
Qed.

(* GHC 9.10: substExpr is now axiomatized and no longer takes a doc string argument.
   The subst_expr' local definition and subst_ok theorem are removed since they
   reference the old substExpr signature. *)


Notation "e @[ n ↦ e' ]" := (subst e n e') (at level 15, no associativity, format "e @[ n  ↦  e' ]").


Fixpoint app_list (e : CoreExpr) : CoreExpr * list CoreExpr :=
  match e with
  | App e₁ e₂ => let '(f, es) := app_list e₁ in (f, es ++ [::e₂])
  | _         => (e, [::])
  end.

Definition case_match (e : CoreExpr) (K : DataCon) (args : list Id) : option (list (Id * CoreExpr)) :=
  if app_list e is (Mk_Var K', args')
  then let: (univs, exts, _eqs, _theta, _origArgs, _origRes) := dataConFullSig K in
       if dcWorkId K == K'
       then let matchArgs' := drop (length univs) args' in
            if length matchArgs' == length args
            then Some (zip args matchArgs') (* TODO: Could check better here *)
            else None
       else None
  else None.

Reserved Notation "e₁ ⟶ e₂" (at level 90, right associativity).
(*
Inductive Step : CoreExpr -> CoreExpr -> Type :=

| S_App {e₁ e₂ e₁'} :
    e₁ ⟶ e₁' →
    App e₁ e₂ ⟶ App e₁' e₂

| S_Beta {n e₁ e₂} :
    App (Lam n e₁) e₂ ⟶ e₁@[n ↦ e₂]

| S_Push {γ n e₁ e₂} :
    let γ₀ := tt (* sym (nth⁰ γ) *) in
    let γ₁ := tt (* nth¹ γ *) in
    ¬ (∃ τ, e₂ = Type_ τ) →
    ¬ (∃ γ, e₂ = Coercion γ) →
    App (Cast (Lam n e₁) γ) e₂ ⟶ App (Lam n (Cast e₁ γ₁)) (Cast e₂ γ₀)

| S_TPush {n e γ τ} :
    App (Cast (Lam n e) γ) (Type_ τ) ⟶ App (Lam n (Cast e tt (* γ n *))) (Type_ τ)

| S_CPush {n e γ γ'} :
    let γ₀ := tt (* nth¹ (nth⁰ γ) *) in
    let γ₁ := tt (* sym (nth² (nth⁰ γ)) *) in
    let γ₂ := tt (* nth¹ γ *) in
    App (Cast (Lam n e) γ) γ' ⟶ App (Lam n (Cast e γ₂)) (Coercion tt (* γ₀ ⨾ γ' ⨾ γ₁  *))

| S_Trans {e γ₁ γ₂} :
    Cast (Cast e γ₁) γ₂ ⟶ Cast e tt (* γ₁ ⨾ γ₂ *)

| S_Cast {e e' γ} :
    e ⟶ e' →
    Cast e γ ⟶ Cast e' γ

| S_Tick {e e' tick} :
    e ⟶ e' →
    Tick tick e ⟶ Tick tick e'

| S_Case {e e' n τ alts} :
    e ⟶ e' →
    Case e n τ alts ⟶ Case e' n τ alts

(* TODO stronger checks? *)
| S_MatchData {e n τ alts K args u j s} :
    nth' alts j = Some (DataAlt K, args, u) →
    case_match e K args = Some s →
    Case e n τ alts ⟶ substs (u@[n ↦ e]) s

| S_MatchLit {n τ alts lit u j} :
    nth' alts j = Some (LitAlt lit, [::], u) →
    Case (Lit lit) n τ alts ⟶ u@[n ↦ Lit lit]

| S_MatchDefault {e n τ alts j u} :
    nth' alts j = Some (DEFAULT, [::], u) →
    (* TODO: no other case matches *)
    Case e n τ alts ⟶ u@[n ↦ e]

(* TODO: any checks at all, real coercion manipulation *)
| S_CasePush {e n τ alts K args γ} :
    (Mk_Var K, args) = app_list e →
    isDataConWorkId K →
    Case (Cast e γ) n τ alts ⟶ Case (foldl App (Mk_Var K) (map (Cast^~ tt) args)) n τ alts

| S_LetNonRec {n e₁ e₂} :
    Let (NonRec n e₁) e₂ ⟶ e₂@[n ↦ e₁]

| S_LetRec {bs u} :
    Let (Rec bs) u ⟶ substs u (map (second (Let (Rec bs))) bs)
  
where "e₁ ⟶ e₂" := (Step e₁ e₂).
*)
