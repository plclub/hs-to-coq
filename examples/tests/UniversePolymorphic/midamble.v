(* === Polymorphism tests === *)
(* Polymorphic types accept universe instance annotations; monomorphic ones don't *)

Check @Nil@{Set}.
Check @Cons@{Set}.
Check @Left_@{Set Set}.
Check @Right_@{Set Set}.
Check @Leaf@{Set}.
Check @Just_@{Set}.

Fail Check @MkPair@{Set Set}.

(* === Cumulativity tests === *)
(* Cumulative types allow universe-level subtyping (upcasts); polymorphic-only
   types do not.  The key is using a polymorphic Definition with explicit universe
   constraints — this forces Coq to check cumulativity rather than infer fresh
   instances. *)

#[universes(polymorphic)]
Definition tree_upcast@{u v | u <= v} (A : Type@{u}) (t : Tree@{u} A) : Tree@{v} A := t.

#[universes(polymorphic)]
Definition either_upcast@{u1 u2 v1 v2 | u1 <= v1, u2 <= v2}
  (A : Type@{u1}) (B : Type@{u2}) (e : Either_@{u1 u2} A B) : Either_@{v1 v2} A B := e.

(* Maybe_ uses the three-word syntax: universe polymorphic cumulative *)
#[universes(polymorphic)]
Definition maybe_upcast@{u v | u <= v} (A : Type@{u}) (m : Maybe_@{u} A) : Maybe_@{v} A := m.

(* MyList is polymorphic but NOT cumulative: upcast must fail *)
Fail #[universes(polymorphic)]
Definition mylist_upcast@{u v | u <= v} (A : Type@{u}) (l : MyList@{u} A) : MyList@{v} A := l.
