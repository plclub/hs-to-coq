(* Unpeel class: A directed form of Coercible, where a is the newtype type,
   and b the base type *)
Class Unpeel a b :=
  { unpeel : a -> b
  ; repeel : b -> a }.

Instance Unpeel_refl a : Unpeel a a := Build_Unpeel _ _ (fun x => x) (fun x => x).

Instance Unpeel_arrow
  a b c d
  `{Unpeel b a}
  `{Unpeel c d}
  : Unpeel (b -> c) (a -> d) :=
  { unpeel f x := unpeel (f (repeel x))
  ; repeel f x := repeel (f (unpeel x))
  }.

Instance Unpeel_pair
  a b c d
  `{Unpeel a b}
  `{Unpeel c d}
  : Unpeel (a * c) (b * d) :=
  { unpeel '(x,y) := (unpeel x, unpeel y)
  ; repeel '(x,y) := (repeel x, repeel y)
  }.


Require Coq.Lists.List.
Instance Unpeel_list a b
   `{Unpeel a b} : Unpeel (list a) (list b) :=
  { unpeel x := Coq.Lists.List.map unpeel x
  ; repeel x := Coq.Lists.List.map repeel x
  }.
