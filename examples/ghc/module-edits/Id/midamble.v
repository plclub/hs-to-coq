(* GHC 9.10: Panic.panic needs Default instances for IdDetails *)
Import Core.

(* GHC 9.10: some functions use GHC.Utils.Trace for debug tracing *)
Require Import GHC.Utils.Trace.

(* GHC 9.10: idJoinArity is used by Exitify but needs Outputable.JoinPointHood.
   We provide it directly here since JoinArity = nat *)
Definition idJoinArity : Core.JoinId -> BasicTypes.JoinArity :=
  fun id =>
    match Core.idDetails id with
    | Core.Mk_JoinId arity _ => arity
    | _ => Panic.panic (GHC.Base.hs_string__ "idJoinArity")
    end.
