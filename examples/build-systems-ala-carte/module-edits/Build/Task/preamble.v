
Polymorphic Inductive Task (c : (Type -> Type) -> Type) (k : Type) (v : Type) : Type :=
  | Mk_Task (run : forall {f}, forall `{c f}, (k -> f v) -> f v) : Task c k v.

Polymorphic Definition Tasks c k v :=
  (k -> option (Task c k v))%type.
