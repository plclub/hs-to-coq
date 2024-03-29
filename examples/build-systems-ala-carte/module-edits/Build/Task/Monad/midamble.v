Polymorphic Cumulative Record Functor__Dict@{i j} (f : Type@{i} -> Type@{j}) := Functor__Dict_Build {
  fmap__ : forall {a b : Type@{i}}, (a -> b) -> f a -> f b ;
  op_zlzd____ : forall {a b : Type@{i}}, a -> f b -> f a }.

Polymorphic Definition Functor@{i j k} f :=
  forall (r__ : Type@{k}), (Functor__Dict@{i j} f -> r__) -> r__.
Existing Class Functor.


(* -------------- Applicative type class --------------------------- *)

Polymorphic Cumulative Record Applicative__Dict@{i j} (f : Type@{i} -> Type@{j}) := Applicative__Dict_Build {
  liftA2__ : forall {a : Type@{i}} {b : Type@{i}} {c : Type@{i}}, (a -> b -> c) -> f a -> f b -> f c ;
  op_zlztzg____ : forall {a : Type@{i}} {b : Type@{i}}, f (a -> b) -> f a -> f b ;
  op_ztzg____ : forall {a : Type@{i}} {b : Type@{i}}, f a -> f b -> f b ;
  pure__ : forall {a : Type@{i}}, a -> f a }.

Polymorphic Definition fmap `{g__0__ : Functor f}
   : forall {a} {b}, (a -> b) -> f a -> f b :=
  g__0__ _ (fmap__ f).

Polymorphic Definition op_zlzd__ `{g__0__ : Functor f} : forall {a} {b}, a -> f b -> f a :=
  g__0__ _ (op_zlzd____ f).

Notation "'_<$_'" := (op_zlzd__).

Infix "<$" := (_<$_) (at level 99).

Polymorphic Definition Applicative@{i j k} (f : Type@{i} -> Type@{j}) `{Functor@{i j k} f} :=
  forall (r__ : Type@{k}), (Applicative__Dict f -> r__) -> r__.
Existing Class Applicative.

Polymorphic Instance Applicative__eta@{i j k a} (F : Type@{i} -> Type@{j})
            `{Applicative@{i j k} F} `{Functor@{a j k} (fun A => F A)} : Applicative@{a j k} (fun A => F A).
intros r k. apply k, H0.
intros AF. destruct AF.
constructor.
- intros a b c. exact (liftA2__0 a b c).
- intros a b. exact (op_zlztzg____0 a b).
- intros a b. exact (op_ztzg____0 a b).
- intros a. exact (pure__0 a).
Defined.

(* -------------- Monad type class --------------------------- *)

Polymorphic Cumulative Record Monad__Dict@{i j} (m : Type@{i} -> Type@{j}) := Monad__Dict_Build {
  op_zgzg____ : forall {a b : Type@{i}}, m a -> m b -> m b ;
  op_zgzgze____ : forall {a b : Type@{i}}, m a -> (a -> m b) -> m b ;
  return___ : forall {a : Type@{i}}, a -> m a }.

Polymorphic Definition Monad@{i j k} (m : Type@{i} -> Type@{j}) `{Applicative@{i j k} m} :=
  forall (r__ : Type@{k}), (Monad__Dict m -> r__) -> r__.
Existing Class Monad.

Polymorphic Instance Monad__beta@{i j k a} (F : Type@{i} -> Type@{j})
             `{Monad@{i j k} F} `{Applicative@{a j k} (fun A => F A)} :
  Monad@{a j k} (fun A => F A).
intros r k. apply k, H1.
intros MF. destruct MF.
constructor.
- intros a b. exact (op_zgzg____0 a b).
- intros a b. exact (op_zgzgze____0 a b).
- intros a. exact (return___0 a).
Defined.

Polymorphic Definition op_zgzg__ `{g__0__ : Monad m} : forall {a} {b}, m a -> m b -> m b :=
  g__0__ _ (op_zgzg____ m).

Polymorphic Definition op_zgzgze__ `{g__0__ : Monad m}
   : forall {a} {b}, m a -> (a -> m b) -> m b :=
  g__0__ _ (op_zgzgze____ m).

Polymorphic Definition return_ `{g__0__ : Monad m} : forall {a}, a -> m a :=
  g__0__ _ (return___ m).

Notation "'_>>_'" := (op_zgzg__).

Infix ">>" := (_>>_) (at level 99, right associativity).

Notation "'_>>=_'" := (op_zgzgze__).

Infix ">>=" := (_>>=_) (at level 99, right associativity).



(* current best attempt at tracePure*)
(* Definition trackPure {k : Type} {v : Type} *)
(*    : Build.Task.Task Monad__Dict k v -> (k -> v) -> (v * list k)%type := *)
(*   ( fun (task : Build.Task.Task Monad__Dict k v) (fetch: k->v) => *)
(*     Control.Monad.Trans.Writer.Lazy.runWriter (Build.Task.run task (fun (i:k) => *)
(*                                                                  Control.Monad.Trans.Writer.Lazy.writer (pair (fetch i) (cons *)
(*                                                                                                           i nil))))). *)

(* Current best attempt at trace *)
(* Definition track {m : Type -> Type} {k : Type} {v : Type} `{Monad__Dict m} *)
(*    : Build.Task.Task Monad__Dict k v -> *)
(*      (k -> m v) -> m (v * list (k * v)%type)%type := *)
(*   fun task fetch => *)
(*     let trackingFetch *)
(*      : k -> Control.Monad.Trans.Writer.Lazy.WriterT (list (k * v)%type) m v := *)
(*       fun k => *)
(*         Control.Monad.Trans.Class.lift (fetch k) GHC.Base.>>= *)
(*         (fun v => *)
(*            Control.Monad.Trans.Writer.Lazy.tell (cons (pair k v) nil) GHC.Base.>> *)
(*            GHC.Base.return_ v) in *)
(*     Control.Monad.Trans.Writer.Lazy.runWriterT (Build.Task.run task trackingFetch). *)
