(* GHC 9.10: Panic.panic needs Default instances for IdDetails *)
Import Core.

(* GHC 9.10: some functions use GHC.Utils.Trace for debug tracing *)
Require Import GHC.Utils.Trace.

(* GHC 9.10: These functions are skipped because they use Outputable.JoinPointHood
   from GHC.Types.Basic (a module we don't translate). We define them manually
   using Core.idDetails and the Mk_JoinId constructor. *)

Require Import Outputable.

Definition idJoinPointHood : Core.Var -> Outputable.JoinPointHood :=
  fun id =>
    if Core.isId id then
      match Core.idDetails id with
      | Core.Mk_JoinId arity _ => Outputable.JoinPoint arity
      | _ => Outputable.NotJoinPoint
      end
    else Outputable.NotJoinPoint.

Definition idJoinArity : Core.JoinId -> BasicTypes.JoinArity :=
  fun id =>
    match Core.idDetails id with
    | Core.Mk_JoinId arity _ => arity
    | _ => Panic.panic (GHC.Base.hs_string__ "idJoinArity")
    end.

Definition asJoinId : Core.Id -> BasicTypes.JoinArity -> Core.JoinId :=
  fun id arity => Core.setIdDetails id (Core.Mk_JoinId arity None).
