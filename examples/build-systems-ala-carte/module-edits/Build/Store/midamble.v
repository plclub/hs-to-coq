Instance Unpeel__Hash {A : Type}  : Unpeel (Hash A) A :=
  {| unpeel := fun hashA : Hash A => match hashA with | Mk_Hash a => a end;
     repeel := Mk_Hash |}.
