(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* A hack to make a few kind-polymorpic definitions go through *)
Class unit_class.
Instance unit_class_instance : unit_class := {}.
Implicit Type inst_k: unit_class.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Require HsToCoq.Err.
Require HsToCoq.Unpeel.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Sum a : Type := | Mk_Sum (getSum : a) : Sum a.

Inductive Product a : Type := | Mk_Product (getProduct : a) : Product a.

Inductive Endo a : Type := | Mk_Endo (appEndo : a -> a) : Endo a.

Inductive Dual a : Type := | Mk_Dual (getDual : a) : Dual a.

Inductive Any : Type := | Mk_Any (getAny : bool) : Any.

Inductive Alt {k : Type} (f : k -> Type) (a : k) : Type :=
  | Mk_Alt (getAlt : f a) : Alt f a.

Inductive All : Type := | Mk_All (getAll : bool) : All.

Arguments Mk_Sum {_} _.

Arguments Mk_Product {_} _.

Arguments Mk_Endo {_} _.

Arguments Mk_Dual {_} _.

Arguments Mk_Alt {_} {_} {_} _.

Instance Default__Any : HsToCoq.Err.Default Any :=
  HsToCoq.Err.Build_Default _ (Mk_Any HsToCoq.Err.default).

Instance Default__All : HsToCoq.Err.Default All :=
  HsToCoq.Err.Build_Default _ (Mk_All HsToCoq.Err.default).

Definition getSum {a} (arg_0__ : Sum a) :=
  let 'Mk_Sum getSum := arg_0__ in
  getSum.

Definition getProduct {a} (arg_0__ : Product a) :=
  let 'Mk_Product getProduct := arg_0__ in
  getProduct.

Definition appEndo {a} (arg_0__ : Endo a) :=
  let 'Mk_Endo appEndo := arg_0__ in
  appEndo.

Definition getDual {a} (arg_0__ : Dual a) :=
  let 'Mk_Dual getDual := arg_0__ in
  getDual.

Definition getAny (arg_0__ : Any) :=
  let 'Mk_Any getAny := arg_0__ in
  getAny.

Definition getAlt {k : Type} {f : k -> Type} {a : k} (arg_0__ : Alt f a) :=
  let 'Mk_Alt getAlt := arg_0__ in
  getAlt.

Definition getAll (arg_0__ : All) :=
  let 'Mk_All getAll := arg_0__ in
  getAll.

(* Midamble *)

Instance Unpeel_Alt (k : Type) (f : k -> Type) (a : k) : HsToCoq.Unpeel.Unpeel (Alt f a) (f a) :=
    HsToCoq.Unpeel.Build_Unpeel _ _ getAlt Mk_Alt.

(* Converted value declarations: *)

Local Definition Semigroup__Dual_op_zlzlzgzg__ {inst_a : Type}
  `{GHC.Base.Semigroup inst_a}
   : Dual inst_a -> Dual inst_a -> Dual inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Dual a, Mk_Dual b => Mk_Dual (b GHC.Base.<<>> a)
    end.

Program Instance Semigroup__Dual {a : Type} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Dual a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Dual_op_zlzlzgzg__ |}.

Local Definition Monoid__Dual_mappend {inst_a : Type} `{GHC.Base.Monoid inst_a}
   : Dual inst_a -> Dual inst_a -> Dual inst_a :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Dual_mempty {inst_a : Type} `{GHC.Base.Monoid inst_a}
   : Dual inst_a :=
  Mk_Dual GHC.Base.mempty.

Local Definition Monoid__Dual_mconcat {inst_a : Type} `{GHC.Base.Monoid inst_a}
   : list (Dual inst_a) -> Dual inst_a :=
  GHC.Base.foldr Monoid__Dual_mappend Monoid__Dual_mempty.

Program Instance Monoid__Dual {a : Type} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Dual a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Dual_mappend ;
           GHC.Base.mconcat__ := Monoid__Dual_mconcat ;
           GHC.Base.mempty__ := Monoid__Dual_mempty |}.

Local Definition Functor__Dual_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Dual a -> Dual b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Functor__Dual_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Dual b -> Dual a :=
  fun {a : Type} {b : Type} => Functor__Dual_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Dual : GHC.Base.Functor Dual :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Dual_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Dual_op_zlzd__ |}.

Local Definition Applicative__Dual_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Dual (a -> b) -> Dual a -> Dual b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Applicative__Dual_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Dual a -> Dual b -> Dual c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Dual_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Dual_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Dual a -> Dual b -> Dual b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Dual_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Dual_pure : forall {a : Type}, a -> Dual a :=
  fun {a : Type} => Mk_Dual.

Program Instance Applicative__Dual : GHC.Base.Applicative Dual :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Dual_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Dual_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Dual_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Dual_pure |}.

Local Definition Monad__Dual_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Dual a -> (a -> Dual b) -> Dual b :=
  fun {a : Type} {b : Type} => fun m k => k (getDual m).

Local Definition Monad__Dual_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Dual a -> Dual b -> Dual b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Dual_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Dual_return_ : forall {a : Type}, a -> Dual a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__Dual : GHC.Base.Monad Dual :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__Dual_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} => Monad__Dual_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__Dual_return_ |}.

Instance Unpeel_Endo a : HsToCoq.Unpeel.Unpeel (Endo a) (a -> a) :=
  HsToCoq.Unpeel.Build_Unpeel _ _ appEndo Mk_Endo.

Local Definition Semigroup__Endo_op_zlzlzgzg__ {inst_a : Type}
   : Endo inst_a -> Endo inst_a -> Endo inst_a :=
  GHC.Prim.coerce (_GHC.Base.∘_ : (inst_a -> inst_a) ->
                   (inst_a -> inst_a) -> (inst_a -> inst_a)).

Program Instance Semigroup__Endo {a : Type} : GHC.Base.Semigroup (Endo a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Endo_op_zlzlzgzg__ |}.

Local Definition Monoid__Endo_mappend {inst_a : Type}
   : Endo inst_a -> Endo inst_a -> Endo inst_a :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Endo_mempty {inst_a : Type} : Endo inst_a :=
  Mk_Endo GHC.Base.id.

Local Definition Monoid__Endo_mconcat {inst_a : Type}
   : list (Endo inst_a) -> Endo inst_a :=
  GHC.Base.foldr Monoid__Endo_mappend Monoid__Endo_mempty.

Program Instance Monoid__Endo {a : Type} : GHC.Base.Monoid (Endo a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Endo_mappend ;
           GHC.Base.mconcat__ := Monoid__Endo_mconcat ;
           GHC.Base.mempty__ := Monoid__Endo_mempty |}.

Local Definition Semigroup__All_op_zlzlzgzg__ : All -> All -> All :=
  GHC.Prim.coerce andb.

Program Instance Semigroup__All : GHC.Base.Semigroup All :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__All_op_zlzlzgzg__ |}.

Local Definition Monoid__All_mappend : All -> All -> All :=
  _GHC.Base.<<>>_.

Local Definition Monoid__All_mempty : All :=
  Mk_All true.

Local Definition Monoid__All_mconcat : list All -> All :=
  GHC.Base.foldr Monoid__All_mappend Monoid__All_mempty.

Program Instance Monoid__All : GHC.Base.Monoid All :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__All_mappend ;
           GHC.Base.mconcat__ := Monoid__All_mconcat ;
           GHC.Base.mempty__ := Monoid__All_mempty |}.

Local Definition Semigroup__Any_op_zlzlzgzg__ : Any -> Any -> Any :=
  GHC.Prim.coerce orb.

Program Instance Semigroup__Any : GHC.Base.Semigroup Any :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Any_op_zlzlzgzg__ |}.

Local Definition Monoid__Any_mappend : Any -> Any -> Any :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Any_mempty : Any :=
  Mk_Any false.

Local Definition Monoid__Any_mconcat : list Any -> Any :=
  GHC.Base.foldr Monoid__Any_mappend Monoid__Any_mempty.

Program Instance Monoid__Any : GHC.Base.Monoid Any :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Any_mappend ;
           GHC.Base.mconcat__ := Monoid__Any_mconcat ;
           GHC.Base.mempty__ := Monoid__Any_mempty |}.

Local Definition Semigroup__Sum_op_zlzlzgzg__ {inst_a : Type} `{GHC.Num.Num
  inst_a}
   : Sum inst_a -> Sum inst_a -> Sum inst_a :=
  GHC.Prim.coerce (_GHC.Num.+_ : inst_a -> inst_a -> inst_a).

Program Instance Semigroup__Sum {a : Type} `{GHC.Num.Num a}
   : GHC.Base.Semigroup (Sum a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Sum_op_zlzlzgzg__ |}.

Local Definition Monoid__Sum_mappend {inst_a : Type} `{GHC.Num.Num inst_a}
   : Sum inst_a -> Sum inst_a -> Sum inst_a :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Sum_mempty {inst_a : Type} `{GHC.Num.Num inst_a}
   : Sum inst_a :=
  Mk_Sum #0.

Local Definition Monoid__Sum_mconcat {inst_a : Type} `{GHC.Num.Num inst_a}
   : list (Sum inst_a) -> Sum inst_a :=
  GHC.Base.foldr Monoid__Sum_mappend Monoid__Sum_mempty.

Program Instance Monoid__Sum {a : Type} `{GHC.Num.Num a}
   : GHC.Base.Monoid (Sum a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Sum_mappend ;
           GHC.Base.mconcat__ := Monoid__Sum_mconcat ;
           GHC.Base.mempty__ := Monoid__Sum_mempty |}.

Local Definition Functor__Sum_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Sum a -> Sum b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Functor__Sum_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Sum b -> Sum a :=
  fun {a : Type} {b : Type} => Functor__Sum_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Sum : GHC.Base.Functor Sum :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Sum_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Sum_op_zlzd__ |}.

Local Definition Applicative__Sum_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Sum (a -> b) -> Sum a -> Sum b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Applicative__Sum_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Sum a -> Sum b -> Sum c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Sum_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Sum_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Sum a -> Sum b -> Sum b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Sum_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Sum_pure : forall {a : Type}, a -> Sum a :=
  fun {a : Type} => Mk_Sum.

Program Instance Applicative__Sum : GHC.Base.Applicative Sum :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Sum_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Sum_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Sum_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Sum_pure |}.

Local Definition Monad__Sum_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Sum a -> (a -> Sum b) -> Sum b :=
  fun {a : Type} {b : Type} => fun m k => k (getSum m).

Local Definition Monad__Sum_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Sum a -> Sum b -> Sum b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Sum_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Sum_return_ : forall {a : Type}, a -> Sum a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__Sum : GHC.Base.Monad Sum :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__Sum_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} => Monad__Sum_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__Sum_return_ |}.

Local Definition Semigroup__Product_op_zlzlzgzg__ {inst_a : Type} `{GHC.Num.Num
  inst_a}
   : Product inst_a -> Product inst_a -> Product inst_a :=
  GHC.Prim.coerce (_GHC.Num.*_ : inst_a -> inst_a -> inst_a).

Program Instance Semigroup__Product {a : Type} `{GHC.Num.Num a}
   : GHC.Base.Semigroup (Product a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Product_op_zlzlzgzg__ |}.

Local Definition Monoid__Product_mappend {inst_a : Type} `{GHC.Num.Num inst_a}
   : Product inst_a -> Product inst_a -> Product inst_a :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Product_mempty {inst_a : Type} `{GHC.Num.Num inst_a}
   : Product inst_a :=
  Mk_Product #1.

Local Definition Monoid__Product_mconcat {inst_a : Type} `{GHC.Num.Num inst_a}
   : list (Product inst_a) -> Product inst_a :=
  GHC.Base.foldr Monoid__Product_mappend Monoid__Product_mempty.

Program Instance Monoid__Product {a : Type} `{GHC.Num.Num a}
   : GHC.Base.Monoid (Product a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Product_mappend ;
           GHC.Base.mconcat__ := Monoid__Product_mconcat ;
           GHC.Base.mempty__ := Monoid__Product_mempty |}.

Local Definition Functor__Product_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Product a -> Product b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Functor__Product_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Product b -> Product a :=
  fun {a : Type} {b : Type} => Functor__Product_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Product : GHC.Base.Functor Product :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Product_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__Product_op_zlzd__ |}.

Local Definition Applicative__Product_op_zlztzg__
   : forall {a : Type},
     forall {b : Type}, Product (a -> b) -> Product a -> Product b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce.

Local Definition Applicative__Product_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Product a -> Product b -> Product c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Product_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Product_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Product a -> Product b -> Product b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Product_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Product_pure
   : forall {a : Type}, a -> Product a :=
  fun {a : Type} => Mk_Product.

Program Instance Applicative__Product : GHC.Base.Applicative Product :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Product_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Product_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Product_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Product_pure |}.

Local Definition Monad__Product_op_zgzgze__
   : forall {a : Type},
     forall {b : Type}, Product a -> (a -> Product b) -> Product b :=
  fun {a : Type} {b : Type} => fun m k => k (getProduct m).

Local Definition Monad__Product_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Product a -> Product b -> Product b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Product_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Product_return_ : forall {a : Type}, a -> Product a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__Product : GHC.Base.Monad Product :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__Product_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__Product_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__Product_return_ |}.

(* Skipping instance `Data.SemigroupInternal.Semigroup__Alt' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `Data.SemigroupInternal.Monoid__Alt' of class
   `GHC.Base.Monoid' *)

(* Skipping definition `Data.SemigroupInternal.stimesIdempotent' *)

Definition stimesIdempotentMonoid {b : Type} {a : Type} `{GHC.Real.Integral b}
  `{GHC.Base.Monoid a}
   : b -> a -> a :=
  fun n x =>
    match GHC.Base.compare n #0 with
    | Lt =>
        GHC.Err.errorWithoutStackTrace (GHC.Base.hs_string__
                                        "stimesIdempotentMonoid: negative multiplier")
    | Eq => GHC.Base.mempty
    | Gt => x
    end.

(* Skipping definition `Data.SemigroupInternal.stimesMonoid' *)

(* Skipping definition `Data.SemigroupInternal.stimesDefault' *)

(* Skipping definition `Data.SemigroupInternal.stimesMaybe' *)

(* Skipping definition `Data.SemigroupInternal.stimesList' *)

Instance Unpeel_Sum a : HsToCoq.Unpeel.Unpeel (Sum a) a :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getSum Mk_Sum.

Instance Unpeel_Product a : HsToCoq.Unpeel.Unpeel (Product a) a :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getProduct Mk_Product.

Instance Unpeel_All : HsToCoq.Unpeel.Unpeel All bool :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getAll Mk_All.

Instance Unpeel_Any : HsToCoq.Unpeel.Unpeel Any bool :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getAny Mk_Any.

Instance Unpeel_Dual a : HsToCoq.Unpeel.Unpeel (Dual a) a :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getDual Mk_Dual.

(* External variables:
     Eq Gt Lt Type andb bool false list orb true GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Semigroup
     GHC.Base.compare GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr
     GHC.Base.id GHC.Base.liftA2__ GHC.Base.mappend__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.op_z2218U__ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return___
     GHC.Err.errorWithoutStackTrace GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
     GHC.Num.op_zt__ GHC.Prim.coerce GHC.Real.Integral HsToCoq.Err.Build_Default
     HsToCoq.Err.Default HsToCoq.Err.default HsToCoq.Unpeel.Build_Unpeel
     HsToCoq.Unpeel.Unpeel
*)
