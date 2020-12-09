(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Fail.
Require Control.Monad.Signatures.
Require Control.Monad.Trans.Class.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.Classes.
Require Data.Functor.Identity.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive WriterT w m a : Type :=
  | Mk_WriterT (runWriterT : m (a * w)%type) : WriterT w m a.

Definition Writer w :=
  (WriterT w Data.Functor.Identity.Identity)%type.

Arguments Mk_WriterT {_} {_} {_} _.

Definition runWriterT {w} {m} {a} (arg_0__ : WriterT w m a) :=
  let 'Mk_WriterT runWriterT := arg_0__ in
  runWriterT.

(* Midamble *)

Import Notations.

Local Definition Monad__WriterT_tmp {inst_w} {inst_m} `{GHC.Base.Monoid
  inst_w} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (WriterT inst_w inst_m) a ->
     (a -> (WriterT inst_w inst_m) b) -> (WriterT inst_w inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_WriterT (let cont_0__ arg_1__ :=
                    let 'pair a1 w := arg_1__ in
                    let cont_2__ arg_3__ :=
                      let 'pair b1 w' := arg_3__ in
                      GHC.Base.return_ (pair b1 (GHC.Base.mappend w w')) in
                    runWriterT (k a1) GHC.Base.>>= cont_2__ in
                  runWriterT m GHC.Base.>>= cont_0__). 

(* Converted value declarations: *)

Local Definition Eq1__WriterT_liftEq {inst_w : Type} {inst_m : Type -> Type}
  `{GHC.Base.Eq_ inst_w} `{Data.Functor.Classes.Eq1 inst_m}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> bool) ->
     WriterT inst_w inst_m a -> WriterT inst_w inst_m b -> bool :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_WriterT m1, Mk_WriterT m2 =>
          Data.Functor.Classes.liftEq (Data.Functor.Classes.liftEq2 eq _GHC.Base.==_) m1
          m2
      end.

Program Instance Eq1__WriterT {w : Type} {m : Type -> Type} `{GHC.Base.Eq_ w}
  `{Data.Functor.Classes.Eq1 m}
   : Data.Functor.Classes.Eq1 (WriterT w m) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a : Type} {b : Type} =>
             Eq1__WriterT_liftEq |}.

Local Definition Ord1__WriterT_liftCompare {inst_w : Type} {inst_m
   : Type -> Type} `{GHC.Base.Ord inst_w} `{Data.Functor.Classes.Ord1 inst_m}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) ->
     WriterT inst_w inst_m a -> WriterT inst_w inst_m b -> comparison :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_WriterT m1, Mk_WriterT m2 =>
          Data.Functor.Classes.liftCompare (Data.Functor.Classes.liftCompare2 comp
                                            GHC.Base.compare) m1 m2
      end.

Program Instance Ord1__WriterT {w : Type} {m : Type -> Type} `{GHC.Base.Ord w}
  `{Data.Functor.Classes.Ord1 m}
   : Data.Functor.Classes.Ord1 (WriterT w m) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a : Type} {b : Type} =>
             Ord1__WriterT_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Control.Monad.Trans.Writer.Lazy.Read1__WriterT' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Control.Monad.Trans.Writer.Lazy.Show1__WriterT' *)

Local Definition Eq___WriterT_op_zeze__ {inst_w : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Eq_ inst_w} `{Data.Functor.Classes.Eq1 inst_m}
  `{GHC.Base.Eq_ inst_a}
   : WriterT inst_w inst_m inst_a -> WriterT inst_w inst_m inst_a -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___WriterT_op_zsze__ {inst_w : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Eq_ inst_w} `{Data.Functor.Classes.Eq1 inst_m}
  `{GHC.Base.Eq_ inst_a}
   : WriterT inst_w inst_m inst_a -> WriterT inst_w inst_m inst_a -> bool :=
  fun x y => negb (Eq___WriterT_op_zeze__ x y).

Program Instance Eq___WriterT {w : Type} {m : Type -> Type} {a : Type}
  `{GHC.Base.Eq_ w} `{Data.Functor.Classes.Eq1 m} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (WriterT w m a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___WriterT_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___WriterT_op_zsze__ |}.

Local Definition Ord__WriterT_compare {inst_w : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_w} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : WriterT inst_w inst_m inst_a -> WriterT inst_w inst_m inst_a -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__WriterT_op_zl__ {inst_w : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_w} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : WriterT inst_w inst_m inst_a -> WriterT inst_w inst_m inst_a -> bool :=
  fun x y => Ord__WriterT_compare x y GHC.Base.== Lt.

Local Definition Ord__WriterT_op_zlze__ {inst_w : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_w} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : WriterT inst_w inst_m inst_a -> WriterT inst_w inst_m inst_a -> bool :=
  fun x y => Ord__WriterT_compare x y GHC.Base./= Gt.

Local Definition Ord__WriterT_op_zg__ {inst_w : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_w} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : WriterT inst_w inst_m inst_a -> WriterT inst_w inst_m inst_a -> bool :=
  fun x y => Ord__WriterT_compare x y GHC.Base.== Gt.

Local Definition Ord__WriterT_op_zgze__ {inst_w : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_w} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : WriterT inst_w inst_m inst_a -> WriterT inst_w inst_m inst_a -> bool :=
  fun x y => Ord__WriterT_compare x y GHC.Base./= Lt.

Local Definition Ord__WriterT_max {inst_w : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_w} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : WriterT inst_w inst_m inst_a ->
     WriterT inst_w inst_m inst_a -> WriterT inst_w inst_m inst_a :=
  fun x y => if Ord__WriterT_op_zlze__ x y : bool then y else x.

Local Definition Ord__WriterT_min {inst_w : Type} {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Ord inst_w} `{Data.Functor.Classes.Ord1 inst_m}
  `{GHC.Base.Ord inst_a}
   : WriterT inst_w inst_m inst_a ->
     WriterT inst_w inst_m inst_a -> WriterT inst_w inst_m inst_a :=
  fun x y => if Ord__WriterT_op_zlze__ x y : bool then x else y.

Program Instance Ord__WriterT {w : Type} {m : Type -> Type} {a : Type}
  `{GHC.Base.Ord w} `{Data.Functor.Classes.Ord1 m} `{GHC.Base.Ord a}
   : GHC.Base.Ord (WriterT w m a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__WriterT_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__WriterT_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__WriterT_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__WriterT_op_zgze__ ;
           GHC.Base.compare__ := Ord__WriterT_compare ;
           GHC.Base.max__ := Ord__WriterT_max ;
           GHC.Base.min__ := Ord__WriterT_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Control.Monad.Trans.Writer.Lazy.Read__WriterT' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Monad.Trans.Writer.Lazy.Show__WriterT' *)

Definition mapWriterT {m : Type -> Type} {a : Type} {w : Type} {n
   : Type -> Type} {b : Type} {w' : Type}
   : (m (a * w)%type -> n (b * w')%type) -> WriterT w m a -> WriterT w' n b :=
  fun f m => Mk_WriterT (f (runWriterT m)).

Local Definition Functor__WriterT_fmap {inst_m : Type -> Type} {inst_w : Type}
  `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> WriterT inst_w inst_m a -> WriterT inst_w inst_m b :=
  fun {a : Type} {b : Type} =>
    fun f => mapWriterT (GHC.Base.fmap (fun '(pair a w) => pair (f a) w)).

Local Definition Functor__WriterT_op_zlzd__ {inst_m : Type -> Type} {inst_w
   : Type} `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type}, a -> WriterT inst_w inst_m b -> WriterT inst_w inst_m a :=
  fun {a : Type} {b : Type} => Functor__WriterT_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__WriterT {m : Type -> Type} {w : Type}
  `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (WriterT w m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__WriterT_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__WriterT_op_zlzd__ |}.

Local Definition Foldable__WriterT_foldMap {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> WriterT inst_w inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Data.Foldable.foldMap (f GHC.Base.∘ Data.Tuple.fst) GHC.Base.∘ runWriterT.

Local Definition Foldable__WriterT_fold {inst_f : Type -> Type} {inst_w : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, WriterT inst_w inst_f m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__WriterT_foldMap GHC.Base.id.

Local Definition Foldable__WriterT_foldl {inst_f : Type -> Type} {inst_w : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> WriterT inst_w inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__WriterT_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

Local Definition Foldable__WriterT_foldr {inst_f : Type -> Type} {inst_w : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> WriterT inst_w inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__WriterT_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__WriterT_foldl' {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> WriterT inst_w inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__WriterT_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__WriterT_foldr' {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> WriterT inst_w inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__WriterT_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__WriterT_length {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, WriterT inst_w inst_f a -> GHC.Num.Int :=
  fun {a : Type} => fun '(Mk_WriterT t) => Data.Foldable.length t.

Local Definition Foldable__WriterT_null {inst_f : Type -> Type} {inst_w : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, WriterT inst_w inst_f a -> bool :=
  fun {a : Type} => fun '(Mk_WriterT t) => Data.Foldable.null t.

Local Definition Foldable__WriterT_product {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, WriterT inst_w inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__WriterT_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__WriterT_sum {inst_f : Type -> Type} {inst_w : Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, WriterT inst_w inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__WriterT_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__WriterT_toList {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, WriterT inst_w inst_f a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__WriterT_foldr c n t)).

Program Instance Foldable__WriterT {f : Type -> Type} {w : Type}
  `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (WriterT w f) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__WriterT_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__WriterT_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__WriterT_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} =>
             Foldable__WriterT_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__WriterT_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} =>
             Foldable__WriterT_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__WriterT_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__WriterT_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__WriterT_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__WriterT_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__WriterT_toList |}.

Local Definition Traversable__WriterT_traverse {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> WriterT inst_w inst_f a -> f (WriterT inst_w inst_f b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun f =>
      let f' := fun '(pair a b) => GHC.Base.fmap (fun c => pair c b) (f a) in
      GHC.Base.fmap Mk_WriterT GHC.Base.∘
      (Data.Traversable.traverse f' GHC.Base.∘ runWriterT).

Local Definition Traversable__WriterT_mapM {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> WriterT inst_w inst_f a -> m (WriterT inst_w inst_f b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__WriterT_traverse.

Local Definition Traversable__WriterT_sequenceA {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     WriterT inst_w inst_f (f a) -> f (WriterT inst_w inst_f a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__WriterT_traverse GHC.Base.id.

Local Definition Traversable__WriterT_sequence {inst_f : Type -> Type} {inst_w
   : Type} `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     WriterT inst_w inst_f (m a) -> m (WriterT inst_w inst_f a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__WriterT_sequenceA.

Program Instance Traversable__WriterT {f : Type -> Type} {w : Type}
  `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (WriterT w f) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__WriterT_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__WriterT_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__WriterT_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__WriterT_traverse |}.

Local Definition Applicative__WriterT_op_zlztzg__ {inst_w : Type} {inst_m
   : Type -> Type} `{GHC.Base.Monoid inst_w} `{GHC.Base.Applicative inst_m}
   : forall {a : Type},
     forall {b : Type},
     WriterT inst_w inst_m (a -> b) ->
     WriterT inst_w inst_m a -> WriterT inst_w inst_m b :=
  fun {a : Type} {b : Type} =>
    fun f v =>
      let k :=
        fun arg_0__ arg_1__ =>
          match arg_0__, arg_1__ with
          | pair a w, pair b w' => pair (a b) (GHC.Base.mappend w w')
          end in
      Mk_WriterT (GHC.Base.liftA2 k (runWriterT f) (runWriterT v)).

Local Definition Applicative__WriterT_liftA2 {inst_w : Type} {inst_m
   : Type -> Type} `{GHC.Base.Monoid inst_w} `{GHC.Base.Applicative inst_m}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     WriterT inst_w inst_m a -> WriterT inst_w inst_m b -> WriterT inst_w inst_m c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__WriterT_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__WriterT_pure {inst_w : Type} {inst_m
   : Type -> Type} `{GHC.Base.Monoid inst_w} `{GHC.Base.Applicative inst_m}
   : forall {a : Type}, a -> WriterT inst_w inst_m a :=
  fun {a : Type} => fun a => Mk_WriterT (GHC.Base.pure (pair a GHC.Base.mempty)).

Local Definition Applicative__WriterT_op_ztzg__ {inst_w : Type} {inst_m
   : Type -> Type} `{GHC.Base.Monoid inst_w} `{GHC.Base.Applicative inst_m}
   : forall {a : Type},
     forall {b : Type},
     WriterT inst_w inst_m a -> WriterT inst_w inst_m b -> WriterT inst_w inst_m b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__WriterT_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Program Instance Applicative__WriterT {w : Type} {m : Type -> Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Applicative m}
   : GHC.Base.Applicative (WriterT w m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__WriterT_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__WriterT_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__WriterT_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__WriterT_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Monad.Trans.Writer.Lazy.Alternative__WriterT' *)

Definition Monad__WriterT_op_zgzgze__ {inst_w} {inst_m} `{_
   : GHC.Base.Monoid inst_w} `{_ : GHC.Base.Monad inst_m}
   : forall {a} {b},
     WriterT inst_w inst_m a ->
     (a -> WriterT inst_w inst_m b) -> WriterT inst_w inst_m b :=
  fun {a} {b} => Monad__WriterT_tmp.

Local Definition Monad__WriterT_op_zgzg__ {inst_w : Type} {inst_m
   : Type -> Type} `{GHC.Base.Monoid inst_w} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     WriterT inst_w inst_m a -> WriterT inst_w inst_m b -> WriterT inst_w inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__WriterT_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__WriterT_return_ {inst_w : Type} {inst_m : Type -> Type}
  `{GHC.Base.Monoid inst_w} `{GHC.Base.Monad inst_m}
   : forall {a : Type}, a -> WriterT inst_w inst_m a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__WriterT {w : Type} {m : Type -> Type} `{GHC.Base.Monoid
  w} `{GHC.Base.Monad m}
   : GHC.Base.Monad (WriterT w m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__WriterT_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__WriterT_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__WriterT_return_ |}.

Local Definition MonadTrans__WriterT_lift {inst_w : Type} `{(GHC.Base.Monoid
   inst_w)}
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, m a -> WriterT inst_w m a :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    fun m =>
      Mk_WriterT (m GHC.Base.>>=
                  (fun a => GHC.Base.return_ (pair a GHC.Base.mempty))).

Program Instance MonadTrans__WriterT {w : Type} `{(GHC.Base.Monoid w)}
   : Control.Monad.Trans.Class.MonadTrans (WriterT w) :=
  fun _ k__ =>
    k__ {| Control.Monad.Trans.Class.lift__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             MonadTrans__WriterT_lift |}.

Local Definition MonadFail__WriterT_fail {inst_w : Type} {inst_m : Type -> Type}
  `{GHC.Base.Monoid inst_w} `{Control.Monad.Fail.MonadFail inst_m}
   : forall {a : Type}, GHC.Base.String -> WriterT inst_w inst_m a :=
  fun {a : Type} => fun msg => Mk_WriterT (Control.Monad.Fail.fail msg).

Program Instance MonadFail__WriterT {w : Type} {m : Type -> Type}
  `{GHC.Base.Monoid w} `{Control.Monad.Fail.MonadFail m}
   : Control.Monad.Fail.MonadFail (WriterT w m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun {a : Type} =>
             MonadFail__WriterT_fail |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Monad.Trans.Writer.Lazy.MonadPlus__WriterT' *)

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Control.Monad.Trans.Writer.Lazy.MonadFix__WriterT' *)

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `Control.Monad.Trans.Writer.Lazy.MonadIO__WriterT' *)

(* Skipping all instances of class `Control.Monad.Zip.MonadZip', including
   `Control.Monad.Trans.Writer.Lazy.MonadZip__WriterT' *)

Definition writer {m : Type -> Type} {a : Type} {w : Type} `{GHC.Base.Monad m}
   : (a * w)%type -> WriterT w m a :=
  Mk_WriterT GHC.Base.∘ GHC.Base.return_.

Definition runWriter {w : Type} {a : Type} : Writer w a -> (a * w)%type :=
  Data.Functor.Identity.runIdentity GHC.Base.∘ runWriterT.

Definition execWriter {w : Type} {a : Type} : Writer w a -> w :=
  fun m => Data.Tuple.snd (runWriter m).

Definition mapWriter {a : Type} {w : Type} {b : Type} {w' : Type}
   : ((a * w)%type -> (b * w')%type) -> Writer w a -> Writer w' b :=
  fun f =>
    mapWriterT (Data.Functor.Identity.Mk_Identity GHC.Base.∘
                (f GHC.Base.∘ Data.Functor.Identity.runIdentity)).

Definition execWriterT {m : Type -> Type} {w : Type} {a : Type} `{GHC.Base.Monad
  m}
   : WriterT w m a -> m w :=
  fun m =>
    let cont_0__ arg_1__ := let 'pair _ w := arg_1__ in GHC.Base.return_ w in
    runWriterT m GHC.Base.>>= cont_0__.

Definition tell {m : Type -> Type} {w : Type} `{GHC.Base.Monad m}
   : w -> WriterT w m unit :=
  fun w => writer (pair tt w).

Definition listen {m : Type -> Type} {w : Type} {a : Type} `{GHC.Base.Monad m}
   : WriterT w m a -> WriterT w m (a * w)%type :=
  fun m =>
    Mk_WriterT (let cont_0__ arg_1__ :=
                  let 'pair a w := arg_1__ in
                  GHC.Base.return_ (pair (pair a w) w) in
                runWriterT m GHC.Base.>>= cont_0__).

Definition listens {m : Type -> Type} {w : Type} {b : Type} {a : Type}
  `{GHC.Base.Monad m}
   : (w -> b) -> WriterT w m a -> WriterT w m (a * b)%type :=
  fun f m =>
    Mk_WriterT (let cont_0__ arg_1__ :=
                  let 'pair a w := arg_1__ in
                  GHC.Base.return_ (pair (pair a (f w)) w) in
                runWriterT m GHC.Base.>>= cont_0__).

Definition pass {m : Type -> Type} {w : Type} {a : Type} `{GHC.Base.Monad m}
   : WriterT w m (a * (w -> w))%type -> WriterT w m a :=
  fun m =>
    Mk_WriterT (let cont_0__ arg_1__ :=
                  let 'pair (pair a f) w := arg_1__ in
                  GHC.Base.return_ (pair a (f w)) in
                runWriterT m GHC.Base.>>= cont_0__).

Definition censor {m : Type -> Type} {w : Type} {a : Type} `{GHC.Base.Monad m}
   : (w -> w) -> WriterT w m a -> WriterT w m a :=
  fun f m =>
    Mk_WriterT (let cont_0__ arg_1__ :=
                  let 'pair a w := arg_1__ in
                  GHC.Base.return_ (pair a (f w)) in
                runWriterT m GHC.Base.>>= cont_0__).

Definition liftCallCC {w : Type} {m : Type -> Type} {a : Type} {b : Type}
  `{GHC.Base.Monoid w}
   : Control.Monad.Signatures.CallCC m (a * w)%type (b * w)%type ->
     Control.Monad.Signatures.CallCC (WriterT w m) a b :=
  fun callCC f =>
    Mk_WriterT (callCC (fun c =>
                          runWriterT (f (fun a => Mk_WriterT (c (pair a GHC.Base.mempty)))))).

(* Skipping definition `Control.Monad.Trans.Writer.Lazy.liftCatch' *)

(* External variables:
     Gt Lt Monad__WriterT_tmp Type bool comparison list negb op_zt__ pair tt unit
     Control.Monad.Fail.MonadFail Control.Monad.Fail.fail Control.Monad.Fail.fail__
     Control.Monad.Signatures.CallCC Control.Monad.Trans.Class.MonadTrans
     Control.Monad.Trans.Class.lift__ Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl'__ Data.Foldable.foldl__
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length
     Data.Foldable.length__ Data.Foldable.null Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.Classes.Eq1 Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1
     Data.Functor.Classes.eq1 Data.Functor.Classes.liftCompare
     Data.Functor.Classes.liftCompare2 Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq2
     Data.Functor.Classes.liftEq__ Data.Functor.Identity.Identity
     Data.Functor.Identity.Mk_Identity Data.Functor.Identity.runIdentity
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ Data.Tuple.fst
     Data.Tuple.snd GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.String GHC.Base.build' GHC.Base.compare
     GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.id GHC.Base.liftA2 GHC.Base.liftA2__ GHC.Base.mappend GHC.Base.max__
     GHC.Base.mempty GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return_
     GHC.Base.return___ GHC.Num.Int GHC.Num.Num
*)
