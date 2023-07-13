(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Either.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Size :=
  GHC.Num.Int%type.

Record Monoidal__Dict (f : Type -> Type) := Monoidal__Dict_Build {
  pair___ : forall {a : Type}, forall {b : Type}, f a -> f b -> f (a * b)%type }.

Definition Monoidal (f : Type -> Type) :=
  forall r__, (Monoidal__Dict f -> r__) -> r__.
Existing Class Monoidal.

Record Contravariant__Dict (f : Type -> Type) := Contravariant__Dict_Build {
  contramap__ : forall {b : Type}, forall {a : Type}, (b -> a) -> f a -> f b }.

Definition pair_ `{g__0__ : Monoidal f}
   : forall {a : Type}, forall {b : Type}, f a -> f b -> f (a * b)%type :=
  g__0__ _ (pair___ f).

Inductive FixedPrim a : Type :=
  | FP
   : GHC.Num.Int ->
     (a -> GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO unit) -> FixedPrim a.

Definition Contravariant (f : Type -> Type) :=
  forall r__, (Contravariant__Dict f -> r__) -> r__.
Existing Class Contravariant.

Definition contramap `{g__0__ : Contravariant f}
   : forall {b : Type}, forall {a : Type}, (b -> a) -> f a -> f b :=
  g__0__ _ (contramap__ f).

Inductive BoundedPrim a : Type :=
  | BP
   : GHC.Num.Int ->
     (a ->
      GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO (GHC.Ptr.Ptr GHC.Word.Word8)) ->
     BoundedPrim a.

Arguments FP {_} _ _.

Arguments BP {_} _ _.

(* Converted value declarations: *)

Definition contramapF {b : Type} {a : Type}
   : (b -> a) -> FixedPrim a -> FixedPrim b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, FP l io => FP l (io GHC.Base.∘ f)
    end.

Local Definition Contravariant__FixedPrim_contramap
   : forall {b : Type},
     forall {a : Type}, (b -> a) -> FixedPrim a -> FixedPrim b :=
  fun {b : Type} {a : Type} => contramapF.

Program Instance Contravariant__FixedPrim : Contravariant FixedPrim :=
  fun _ k__ =>
    k__ {| contramap__ := fun {b : Type} {a : Type} =>
             Contravariant__FixedPrim_contramap |}.

Definition contramapB {b : Type} {a : Type}
   : (b -> a) -> BoundedPrim a -> BoundedPrim b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, BP b io => BP b (io GHC.Base.∘ f)
    end.

Local Definition Contravariant__BoundedPrim_contramap
   : forall {b : Type},
     forall {a : Type}, (b -> a) -> BoundedPrim a -> BoundedPrim b :=
  fun {b : Type} {a : Type} => contramapB.

Program Instance Contravariant__BoundedPrim : Contravariant BoundedPrim :=
  fun _ k__ =>
    k__ {| contramap__ := fun {b : Type} {a : Type} =>
             Contravariant__BoundedPrim_contramap |}.

Definition pairF {a : Type} {b : Type}
   : FixedPrim a -> FixedPrim b -> FixedPrim (a * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FP l1 io1, FP l2 io2 =>
        FP (l1 GHC.Num.+ l2) (fun arg_2__ arg_3__ =>
                                match arg_2__, arg_3__ with
                                | pair x1 x2, op => io1 x1 op GHC.Base.>> io2 x2 (GHC.Ptr.plusPtr op l1)
                                end)
    end.

Local Definition Monoidal__FixedPrim_pair_
   : forall {a : Type},
     forall {b : Type}, FixedPrim a -> FixedPrim b -> FixedPrim (a * b)%type :=
  fun {a : Type} {b : Type} => pairF.

Program Instance Monoidal__FixedPrim : Monoidal FixedPrim :=
  fun _ k__ =>
    k__ {| pair___ := fun {a : Type} {b : Type} => Monoidal__FixedPrim_pair_ |}.

Definition pairB {a : Type} {b : Type}
   : BoundedPrim a -> BoundedPrim b -> BoundedPrim (a * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | BP b1 io1, BP b2 io2 =>
        BP (b1 GHC.Num.+ b2) (fun arg_2__ arg_3__ =>
                                match arg_2__, arg_3__ with
                                | pair x1 x2, op => io1 x1 op GHC.Base.>>= io2 x2
                                end)
    end.

Local Definition Monoidal__BoundedPrim_pair_
   : forall {a : Type},
     forall {b : Type}, BoundedPrim a -> BoundedPrim b -> BoundedPrim (a * b)%type :=
  fun {a : Type} {b : Type} => pairB.

Program Instance Monoidal__BoundedPrim : Monoidal BoundedPrim :=
  fun _ k__ =>
    k__ {| pair___ := fun {a : Type} {b : Type} => Monoidal__BoundedPrim_pair_ |}.

Definition op_zgzdzl__ {f : Type -> Type} {b : Type} {a : Type} `{Contravariant
  f}
   : (b -> a) -> f a -> f b :=
  contramap.

Notation "'_>$<_'" := (op_zgzdzl__).

Infix ">$<" := (_>$<_) (at level 99).

Definition op_zgztzl__ {f : Type -> Type} {a : Type} {b : Type} `{Monoidal f}
   : f a -> f b -> f (a * b)%type :=
  pair_.

Notation "'_>*<_'" := (op_zgztzl__).

Infix ">*<" := (_>*<_) (at level 99).

Definition fixedPrim {a : Type}
   : GHC.Num.Int ->
     (a -> GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO unit) -> FixedPrim a :=
  FP.

Definition size {a : Type} : FixedPrim a -> GHC.Num.Int :=
  fun '(FP l _) => l.

Definition runF {a : Type}
   : FixedPrim a -> a -> GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO unit :=
  fun '(FP _ io) => io.

Definition emptyF {a : Type} : FixedPrim a :=
  FP #0 (fun arg_0__ arg_1__ => GHC.Base.return_ tt).

Definition toB {a : Type} : FixedPrim a -> BoundedPrim a :=
  fun '(FP l io) =>
    BP l (fun x op =>
            io x op GHC.Base.>> (GHC.Base.return_ (GHC.Ptr.plusPtr op l))).

Definition liftFixedToBounded {a : Type} : FixedPrim a -> BoundedPrim a :=
  toB.

Definition storableToF {a : Type} `{Foreign.Storable.Storable a}
   : FixedPrim a :=
  FP (Foreign.Storable.sizeOf (GHC.Err.undefined : a)) (fun x op =>
                                                          Foreign.Storable.poke (GHC.Ptr.castPtr op) x).

Definition sizeBound {a : Type} : BoundedPrim a -> GHC.Num.Int :=
  fun '(BP b _) => b.

Definition boundedPrim {a : Type}
   : GHC.Num.Int ->
     (a ->
      GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO (GHC.Ptr.Ptr GHC.Word.Word8)) ->
     BoundedPrim a :=
  BP.

Definition boudedPrim {a : Type}
   : GHC.Num.Int ->
     (a ->
      GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO (GHC.Ptr.Ptr GHC.Word.Word8)) ->
     BoundedPrim a :=
  BP.

Definition runB {a : Type}
   : BoundedPrim a ->
     a -> GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO (GHC.Ptr.Ptr GHC.Word.Word8) :=
  fun '(BP _ io) => io.

Definition emptyB {a : Type} : BoundedPrim a :=
  BP #0 (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | _, op => GHC.Base.return_ op
           end).

Definition eitherB {a : Type} {b : Type}
   : BoundedPrim a -> BoundedPrim b -> BoundedPrim (Data.Either.Either a b) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | BP b1 io1, BP b2 io2 =>
        BP (GHC.Base.max b1 b2) (fun x op =>
                                   match x with
                                   | Data.Either.Left x1 => io1 x1 op
                                   | Data.Either.Right x2 => io2 x2 op
                                   end)
    end.

Definition condB {a : Type}
   : (a -> bool) -> BoundedPrim a -> BoundedPrim a -> BoundedPrim a :=
  fun p be1 be2 =>
    contramapB (fun x =>
                  if p x : bool
                  then Data.Either.Left x
                  else Data.Either.Right x) (eitherB be1 be2).

Definition caseWordSize_32_64 {a : Type} : a -> a -> a :=
  GHC.Base.const GHC.Base.id.

Module Notations.
Notation "'_Data.ByteString.Builder.Prim.Internal.>$<_'" := (op_zgzdzl__).
Infix "Data.ByteString.Builder.Prim.Internal.>$<" := (_>$<_) (at level 99).
Notation "'_Data.ByteString.Builder.Prim.Internal.>*<_'" := (op_zgztzl__).
Infix "Data.ByteString.Builder.Prim.Internal.>*<" := (_>*<_) (at level 99).
End Notations.

(* External variables:
     Type bool op_zt__ pair tt unit Data.Either.Either Data.Either.Left
     Data.Either.Right Foreign.Storable.Storable Foreign.Storable.poke
     Foreign.Storable.sizeOf GHC.Base.const GHC.Base.id GHC.Base.max
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.return_
     GHC.Err.undefined GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Ptr.Ptr
     GHC.Ptr.castPtr GHC.Ptr.plusPtr GHC.Types.IO GHC.Word.Word8
*)
