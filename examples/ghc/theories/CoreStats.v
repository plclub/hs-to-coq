Require CoreStats.
Require Import Proofs.CoreInduct.
Require Import Lia.

Lemma strictly_greater_than_zero : forall (e: Core.CoreExpr), CoreStats.exprSize e > 0.
Proof. 
  intro e.
  eapply (core_induct e); intros; simpl; lia.
Qed.  