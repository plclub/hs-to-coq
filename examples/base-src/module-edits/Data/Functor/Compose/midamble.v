(* Semigroup and Monoid for Compose — generated code has duplicate {k : Type}
   bindings and uses coerce. We define these manually with correct type vars
   and explicit pattern matching. *)

#[local] Definition Semigroup__Compose_op_zlzlzgzg__ {k : Type} {f
   : k -> Type} {k1 : Type} {g : k1 -> k} {a : k1}
  `{GHC.Base.Semigroup (f (g a))}
   : Compose f g a -> Compose f g a -> Compose f g a :=
  fun x y => match x, y with | Mk_Compose p, Mk_Compose q => Mk_Compose (p GHC.Base.<<>> q) end.

#[global]
Program Instance Semigroup__Compose {k : Type} {f : k -> Type} {k1 : Type}
  {g : k1 -> k} {a : k1} `{GHC.Base.Semigroup (f (g a))}
   : GHC.Base.Semigroup (Compose f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Compose_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Compose_mappend {k : Type} {f
   : k -> Type} {k1 : Type} {g : k1 -> k} {a : k1}
  `{GHC.Base.Monoid (f (g a))}
   : Compose f g a -> Compose f g a -> Compose f g a :=
  fun x y => match x, y with | Mk_Compose p, Mk_Compose q => Mk_Compose (GHC.Base.mappend p q) end.

#[local] Definition Monoid__Compose_mconcat {k : Type} {f
   : k -> Type} {k1 : Type} {g : k1 -> k} {a : k1}
  `{GHC.Base.Monoid (f (g a))}
   : list (Compose f g a) -> Compose f g a :=
  fun xs => Mk_Compose (GHC.Base.mconcat (GHC.Base.map (fun x => match x with | Mk_Compose p => p end) xs)).

#[local] Definition Monoid__Compose_mempty {k : Type} {f
   : k -> Type} {k1 : Type} {g : k1 -> k} {a : k1}
  `{GHC.Base.Monoid (f (g a))}
   : Compose f g a :=
  Mk_Compose GHC.Base.mempty.

#[global]
Program Instance Monoid__Compose {k : Type} {f : k -> Type} {k1 : Type}
  {g : k1 -> k} {a : k1} `{GHC.Base.Monoid (f (g a))}
   : GHC.Base.Monoid (Compose f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Compose_mappend ;
           GHC.Base.mconcat__ := Monoid__Compose_mconcat ;
           GHC.Base.mempty__ := Monoid__Compose_mempty |}.
