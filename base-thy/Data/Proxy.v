Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Data.Proxy.

From Coq Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

Instance EqLaws_Proxy {k} {a : k} : EqLaws (Proxy a).
Proof. by split. Qed.

Instance EqExact_Proxy {k} {a : k} : EqExact (Proxy a).
Proof. by split; repeat case; constructor. Qed.
