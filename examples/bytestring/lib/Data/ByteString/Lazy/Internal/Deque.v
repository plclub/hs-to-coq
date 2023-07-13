(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.ByteString.
Require Data.ByteString.Internal.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Require HsToCoq.Err.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Deque : Type :=
  | Deque (front : list Data.ByteString.Internal.ByteString) (rear
    : list Data.ByteString.Internal.ByteString) (byteLength : GHC.Int.Int64)
   : Deque.

Instance Default__Deque : HsToCoq.Err.Default Deque :=
  HsToCoq.Err.Build_Default _ (Deque HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

Definition byteLength (arg_0__ : Deque) :=
  let 'Deque _ _ byteLength := arg_0__ in
  byteLength.

Definition front (arg_0__ : Deque) :=
  let 'Deque front _ _ := arg_0__ in
  front.

Definition rear (arg_0__ : Deque) :=
  let 'Deque _ rear _ := arg_0__ in
  rear.

(* Converted value declarations: *)

Definition empty : Deque :=
  Deque nil nil #0.

Definition null : Deque -> bool :=
  fun deque => byteLength deque GHC.Base.== #0.

Definition len : Data.ByteString.Internal.ByteString -> GHC.Int.Int64 :=
  fun x => GHC.Real.fromIntegral (Data.ByteString.length x).

Definition cons_ : Data.ByteString.Internal.ByteString -> Deque -> Deque :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, Deque fs rs acc => Deque (cons x fs) rs (acc GHC.Num.+ len x)
    end.

Definition snoc : Data.ByteString.Internal.ByteString -> Deque -> Deque :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, Deque fs rs acc => Deque fs (cons x rs) (acc GHC.Num.+ len x)
    end.

Definition popFront
   : Deque -> option (Data.ByteString.Internal.ByteString * Deque)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Deque nil rs acc =>
        match GHC.List.reverse rs with
        | nil => None
        | cons x xs => Some (pair x (Deque xs nil (acc GHC.Num.- len x)))
        end
    | Deque (cons x xs) rs acc => Some (pair x (Deque xs rs (acc GHC.Num.- len x)))
    end.

Definition popRear
   : Deque -> option (Deque * Data.ByteString.Internal.ByteString)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Deque fs nil acc =>
        match GHC.List.reverse fs with
        | nil => None
        | cons x xs => Some (pair (Deque nil xs (acc GHC.Num.- len x)) x)
        end
    | Deque fs (cons x xs) acc => Some (pair (Deque fs xs (acc GHC.Num.- len x)) x)
    end.

(* External variables:
     None Some bool cons list nil op_zt__ option pair Data.ByteString.length
     Data.ByteString.Internal.ByteString GHC.Base.op_zeze__ GHC.Int.Int64
     GHC.List.reverse GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Real.fromIntegral HsToCoq.Err.Build_Default HsToCoq.Err.Default
     HsToCoq.Err.default
*)
