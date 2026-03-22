(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Data.ByteString.Internal.
Require Data.Foldable.
Require GHC.Base.
Require GHC.Char.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Prim.Notations.

(* Converted type declarations: *)

Inductive ShortByteString : Type :=
  | SBS : _GHC.Prim.ByteArray#_ -> ShortByteString.

Inductive MBA s : Type :=
  | op_MBAzh__ : (_GHC.Prim.MutableByteArray#_ s) -> MBA s.

Inductive BA : Type := | op_BAzh__ : _GHC.Prim.ByteArray#_ -> BA.

Arguments op_MBAzh__ {_} _.

Notation "'_MBA#_'" := (op_MBAzh__).

Infix "MBA#" := (_MBA#_) (at level 99).

Notation "'_BA#_'" := (op_BAzh__).

Infix "BA#" := (_BA#_) (at level 99).

(* Converted value declarations: *)

(* Translating `instance Lift__ShortByteString' failed: Could not find
   information for the class `Language.Haskell.TH.Syntax.Lift' when defining the
   instance `Data.ByteString.Short.Internal.Lift__ShortByteString' *)

Definition asBA : ShortByteString -> BA :=
  fun '(SBS lop_bazh__) => _BA#_ lop_bazh__.

Definition length : ShortByteString -> GHC.Num.Int :=
  fun '(SBS lop_barrzh__) =>
    _GHC.Types.I#_ (_GHC.Prim.sizeofByteArray#_ lop_barrzh__).

Definition memcmp_ByteArray
   : BA -> BA -> GHC.Num.Int -> GHC.Types.IO Foreign.C.Types.CInt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | op_BAzh__ lop_ba1zh__, op_BAzh__ lop_ba2zh__, len =>
        c_memcmp_ByteArray lop_ba1zh__ lop_ba2zh__ (GHC.Real.fromIntegral len)
    end.

Definition equateBytes : ShortByteString -> ShortByteString -> bool :=
  fun sbs1 sbs2 =>
    let len2 := length sbs2 in
    let len1 := length sbs1 in
    andb (len1 GHC.Base.== len2) (#0 GHC.Base.==
          Data.ByteString.Internal.accursedUnutterablePerformIO (memcmp_ByteArray (asBA
                                                                                   sbs1) (asBA sbs2) len1)).

Local Definition Eq___ShortByteString_op_zeze__
   : ShortByteString -> ShortByteString -> bool :=
  equateBytes.

Local Definition Eq___ShortByteString_op_zsze__
   : ShortByteString -> ShortByteString -> bool :=
  fun x y => negb (Eq___ShortByteString_op_zeze__ x y).

Program Instance Eq___ShortByteString : GHC.Base.Eq_ ShortByteString :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ShortByteString_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ShortByteString_op_zsze__ |}.

Definition compareBytes : ShortByteString -> ShortByteString -> comparison :=
  fun sbs1 sbs2 =>
    let len2 := length sbs2 in
    let len1 := length sbs1 in
    let len := GHC.Base.min len1 len2 in
    let 'i := Data.ByteString.Internal.accursedUnutterablePerformIO
                (memcmp_ByteArray (asBA sbs1) (asBA sbs2) len) in
    if i GHC.Base.< #0 : bool then Lt else
    if i GHC.Base.> #0 : bool then Gt else
    if len2 GHC.Base.> len1 : bool then Lt else
    if len2 GHC.Base.< len1 : bool then Gt else
    Eq.

Local Definition Ord__ShortByteString_compare
   : ShortByteString -> ShortByteString -> comparison :=
  compareBytes.

Local Definition Ord__ShortByteString_op_zl__
   : ShortByteString -> ShortByteString -> bool :=
  fun x y => Ord__ShortByteString_compare x y GHC.Base.== Lt.

Local Definition Ord__ShortByteString_op_zlze__
   : ShortByteString -> ShortByteString -> bool :=
  fun x y => Ord__ShortByteString_compare x y GHC.Base./= Gt.

Local Definition Ord__ShortByteString_op_zg__
   : ShortByteString -> ShortByteString -> bool :=
  fun x y => Ord__ShortByteString_compare x y GHC.Base.== Gt.

Local Definition Ord__ShortByteString_op_zgze__
   : ShortByteString -> ShortByteString -> bool :=
  fun x y => Ord__ShortByteString_compare x y GHC.Base./= Lt.

Local Definition Ord__ShortByteString_max
   : ShortByteString -> ShortByteString -> ShortByteString :=
  fun x y => if Ord__ShortByteString_op_zlze__ x y : bool then y else x.

Local Definition Ord__ShortByteString_min
   : ShortByteString -> ShortByteString -> ShortByteString :=
  fun x y => if Ord__ShortByteString_op_zlze__ x y : bool then x else y.

Program Instance Ord__ShortByteString : GHC.Base.Ord ShortByteString :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__ShortByteString_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__ShortByteString_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__ShortByteString_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__ShortByteString_op_zgze__ ;
           GHC.Base.compare__ := Ord__ShortByteString_compare ;
           GHC.Base.max__ := Ord__ShortByteString_max ;
           GHC.Base.min__ := Ord__ShortByteString_min |}.

Definition op_copyByteArrayzh__ {s}
   : _GHC.Prim.ByteArray#_ ->
     _GHC.Prim.Int#_ ->
     _GHC.Prim.MutableByteArray#_ s ->
     _GHC.Prim.Int#_ ->
     _GHC.Prim.Int#_ -> _GHC.Prim.State#_ s -> _GHC.Prim.State#_ s :=
  _GHC.Prim.copyByteArray#_.

Notation "'_copyByteArray#_'" := (op_copyByteArrayzh__).

Infix "copyByteArray#" := (_copyByteArray#_) (at level 99).

Definition copyByteArray {s}
   : BA ->
     GHC.Num.Int -> MBA s -> GHC.Num.Int -> GHC.Num.Int -> GHC.ST.ST s unit :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | op_BAzh__ lop_srczh__
    , GHC.Types.op_Izh__ lop_srczuoffzh__
    , op_MBAzh__ lop_dstzh__
    , GHC.Types.op_Izh__ lop_dstzuoffzh__
    , GHC.Types.op_Izh__ lop_lenzh__ =>
        GHC.ST.ST (fun s =>
                     let 's := _copyByteArray#_ lop_srczh__ lop_srczuoffzh__ lop_dstzh__
                                 lop_dstzuoffzh__ lop_lenzh__ s in
                     pair s tt)
    end.

Definition newByteArray {s} : GHC.Num.Int -> GHC.ST.ST s (MBA s) :=
  fun '(GHC.Types.op_Izh__ lop_lenzh__) =>
    GHC.ST.ST (fun s =>
                 let 'pair s lop_mbazh__ := _GHC.Prim.newByteArray#_ lop_lenzh__ s in
                 pair s (_MBA#_ lop_mbazh__)).

Definition unsafeFreezeByteArray {s} : MBA s -> GHC.ST.ST s BA :=
  fun '(op_MBAzh__ lop_mbazh__) =>
    GHC.ST.ST (fun s =>
                 let 'pair s lop_bazh__ := _GHC.Prim.unsafeFreezeByteArray#_ lop_mbazh__ s in
                 pair s (_BA#_ lop_bazh__)).

Definition create
   : GHC.Num.Int -> (forall {s}, MBA s -> GHC.ST.ST s unit) -> ShortByteString :=
  fun len fill =>
    GHC.ST.runST (newByteArray len GHC.Base.>>=
                  (fun mba =>
                     fill mba GHC.Base.>>
                     (let cont_0__ arg_1__ :=
                        let 'op_BAzh__ lop_bazh__ := arg_1__ in
                        GHC.Base.return_ (SBS lop_bazh__) in
                      unsafeFreezeByteArray mba GHC.Base.>>= cont_0__))).

Definition append : ShortByteString -> ShortByteString -> ShortByteString :=
  fun src1 src2 =>
    let len2 := length src2 in
    let len1 := length src1 in
    create (len1 GHC.Num.+ len2) (fun dst =>
                                    copyByteArray (asBA src1) #0 dst #0 len1 GHC.Base.>>
                                    copyByteArray (asBA src2) #0 dst len1 len2).

Local Definition Semigroup__ShortByteString_op_zlzlzgzg__
   : ShortByteString -> ShortByteString -> ShortByteString :=
  append.

Program Instance Semigroup__ShortByteString
   : GHC.Base.Semigroup ShortByteString :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__ShortByteString_op_zlzlzgzg__ |}.

Local Definition Monoid__ShortByteString_mappend
   : ShortByteString -> ShortByteString -> ShortByteString :=
  _GHC.Base.<<>>_.

Definition concat : list ShortByteString -> ShortByteString :=
  fun sbss =>
    let copy {s}
     : MBA s -> GHC.Num.Int -> list ShortByteString -> GHC.ST.ST s unit :=
      fix copy (arg_0__ : MBA s) (arg_1__ : GHC.Num.Int) (arg_2__
                 : list ShortByteString) : GHC.ST.ST s unit
        := match arg_0__, arg_1__, arg_2__ with
           | _, _, nil => GHC.Base.return_ tt
           | dst, off, cons src sbss =>
               let len := length src in
               copyByteArray (asBA src) #0 dst off len GHC.Base.>>
               copy dst (off GHC.Num.+ len) sbss
           end in
    let fix totalLen arg_7__ arg_8__
      := match arg_7__, arg_8__ with
         | acc, nil => acc
         | acc, cons sbs sbss => totalLen (acc GHC.Num.+ length sbs) sbss
         end in
    create (totalLen #0 sbss) (fun dst => copy dst #0 sbss).

Local Definition Monoid__ShortByteString_mconcat
   : list ShortByteString -> ShortByteString :=
  concat.

Definition empty : ShortByteString :=
  create #0 (fun arg_0__ => GHC.Base.return_ tt).

Local Definition Monoid__ShortByteString_mempty : ShortByteString :=
  empty.

Program Instance Monoid__ShortByteString : GHC.Base.Monoid ShortByteString :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__ShortByteString_mappend ;
           GHC.Base.mconcat__ := Monoid__ShortByteString_mconcat ;
           GHC.Base.mempty__ := Monoid__ShortByteString_mempty |}.

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Data.ByteString.Short.Internal.NFData__ShortByteString' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.ByteString.Short.Internal.Show__ShortByteString' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.ByteString.Short.Internal.Read__ShortByteString' *)

(* Skipping all instances of class `GHC.Exts.IsList', including
   `Data.ByteString.Short.Internal.IsList__ShortByteString' *)

(* Translating `instance IsString__ShortByteString' failed: Could not find
   information for the class `Data.String.IsString' when defining the instance
   `Data.ByteString.Short.Internal.IsString__ShortByteString' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.ByteString.Short.Internal.Data__ShortByteString' *)

Definition null : ShortByteString -> bool :=
  fun sbs => length sbs GHC.Base.== #0.

Definition indexError {a} : ShortByteString -> GHC.Num.Int -> a :=
  fun sbs i =>
    GHC.Err.error (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                           "Data.ByteString.Short.index: error in array index; ")
                                          (Coq.Init.Datatypes.app (GHC.Show.show i) (Coq.Init.Datatypes.app
                                                                   (GHC.Base.hs_string__ " not in range [0..")
                                                                   (Coq.Init.Datatypes.app (GHC.Show.show (length sbs))
                                                                                           (GHC.Base.hs_string__
                                                                                            ")"))))).

Definition indexWord8Array : BA -> GHC.Num.Int -> GHC.Word.Word8 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | op_BAzh__ lop_bazh__, GHC.Types.op_Izh__ lop_izh__ =>
        _GHC.Word.W8#_ (_GHC.Prim.indexWord8Array#_ lop_bazh__ lop_izh__)
    end.

Definition unsafeIndex : ShortByteString -> GHC.Num.Int -> GHC.Word.Word8 :=
  fun sbs => indexWord8Array (asBA sbs).

Definition index : ShortByteString -> GHC.Num.Int -> GHC.Word.Word8 :=
  fun sbs i =>
    if andb (i GHC.Base.>= #0) (i GHC.Base.< length sbs) : bool
    then unsafeIndex sbs i else
    indexError sbs i.

Definition indexMaybe
   : ShortByteString -> GHC.Num.Int -> option GHC.Word.Word8 :=
  fun sbs i =>
    if andb (i GHC.Base.>= #0) (i GHC.Base.< length sbs) : bool
    then Some (unsafeIndex sbs i) else
    None.

Definition op_znz3fU__
   : ShortByteString -> GHC.Num.Int -> option GHC.Word.Word8 :=
  indexMaybe.

Notation "'_!?_'" := (op_znz3fU__).

Infix "!?" := (_!?_) (at level 99).

Definition op_copyAddrToByteArrayzh__
   : _GHC.Prim.Addr#_ ->
     _GHC.Prim.MutableByteArray#_ GHC.Prim.RealWorld ->
     _GHC.Prim.Int#_ ->
     _GHC.Prim.Int#_ ->
     _GHC.Prim.State#_ GHC.Prim.RealWorld -> _GHC.Prim.State#_ GHC.Prim.RealWorld :=
  _GHC.Prim.copyAddrToByteArray#_.

Notation "'_copyAddrToByteArray#_'" := (op_copyAddrToByteArrayzh__).

Infix "copyAddrToByteArray#" := (_copyAddrToByteArray#_) (at level 99).

Definition copyAddrToByteArray {a}
   : GHC.Ptr.Ptr a ->
     MBA GHC.Prim.RealWorld ->
     GHC.Num.Int -> GHC.Num.Int -> GHC.ST.ST GHC.Prim.RealWorld unit :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | GHC.Ptr.Ptr lop_srczh__
    , op_MBAzh__ lop_dstzh__
    , GHC.Types.op_Izh__ lop_dstzuoffzh__
    , GHC.Types.op_Izh__ lop_lenzh__ =>
        GHC.ST.ST (fun s =>
                     let 's := _copyAddrToByteArray#_ lop_srczh__ lop_dstzh__ lop_dstzuoffzh__
                                 lop_lenzh__ s in
                     pair s tt)
    end.

Definition createFromPtr {a : Type}
   : GHC.Ptr.Ptr a -> GHC.Num.Int -> GHC.Types.IO ShortByteString :=
  fun ptr len =>
    GHC.IO.stToIO (newByteArray len GHC.Base.>>=
                   (fun mba =>
                      copyAddrToByteArray ptr mba #0 len GHC.Base.>>
                      (let cont_0__ arg_1__ :=
                         let 'op_BAzh__ lop_bazh__ := arg_1__ in
                         GHC.Base.return_ (SBS lop_bazh__) in
                       unsafeFreezeByteArray mba GHC.Base.>>= cont_0__))).

Definition unsafePackLenLiteral
   : GHC.Num.Int -> _GHC.Prim.Addr#_ -> ShortByteString :=
  fun len lop_addrzh__ =>
    Data.ByteString.Internal.accursedUnutterablePerformIO (createFromPtr
                                                           (GHC.Ptr.Ptr lop_addrzh__) len).

Definition toShortIO
   : Data.ByteString.Internal.ByteString -> GHC.Types.IO ShortByteString :=
  fun '(Data.ByteString.Internal.BS fptr len) =>
    GHC.IO.stToIO (newByteArray len) GHC.Base.>>=
    (fun mba =>
       let ptr := GHC.ForeignPtr.unsafeForeignPtrToPtr fptr in
       GHC.IO.stToIO (copyAddrToByteArray ptr mba #0 len) GHC.Base.>>
       (GHC.ForeignPtr.touchForeignPtr fptr GHC.Base.>>
        (let cont_2__ arg_3__ :=
           let 'op_BAzh__ lop_bazh__ := arg_3__ in
           GHC.Base.return_ (SBS lop_bazh__) in
         GHC.IO.stToIO (unsafeFreezeByteArray mba) GHC.Base.>>= cont_2__))).

Definition toShort : Data.ByteString.Internal.ByteString -> ShortByteString :=
  fun bs => GHC.IO.Unsafe.unsafeDupablePerformIO (toShortIO bs).

Definition newPinnedByteArray {s} : GHC.Num.Int -> GHC.ST.ST s (MBA s) :=
  fun '(GHC.Types.op_Izh__ lop_lenzh__) =>
    GHC.ST.ST (fun s =>
                 let 'pair s lop_mbazh__ := _GHC.Prim.newPinnedByteArray#_ lop_lenzh__ s in
                 pair s (_MBA#_ lop_mbazh__)).

Definition fromShortIO
   : ShortByteString -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun sbs =>
    let len := length sbs in
    let cont_1__ arg_2__ :=
      let '(op_MBAzh__ lop_mbazh__ as mba) := arg_2__ in
      GHC.IO.stToIO (copyByteArray (asBA sbs) #0 mba #0 len) GHC.Base.>>
      (let fp :=
         GHC.ForeignPtr.ForeignPtr (_GHC.Prim.byteArrayContents#_
                                    (_GHC.Prim.unsafeCoerce#_ lop_mbazh__)) (GHC.ForeignPtr.PlainPtr lop_mbazh__) in
       GHC.Base.return_ (Data.ByteString.Internal.BS fp len)) in
    GHC.IO.stToIO (newPinnedByteArray len) GHC.Base.>>= cont_1__.

Definition fromShort : ShortByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ =>
    let 'SBS lop_bzh__ := arg_0__ in
    let j_2__ :=
      let 'sbs := arg_0__ in
      GHC.IO.Unsafe.unsafeDupablePerformIO (fromShortIO sbs) in
    let len := _GHC.Types.I#_ (_GHC.Prim.sizeofByteArray#_ lop_bzh__) in
    let lop_addrzh__ := _GHC.Prim.byteArrayContents#_ lop_bzh__ in
    let fp :=
      GHC.ForeignPtr.ForeignPtr lop_addrzh__ (GHC.ForeignPtr.PlainPtr
                                              (_GHC.Prim.unsafeCoerce#_ lop_bzh__)) in
    if _GHC.Types.isTrue#_ (_GHC.Prim.isByteArrayPinned#_ lop_bzh__) : bool
    then Data.ByteString.Internal.BS fp len else
    j_2__.

Definition writeWord8Array {s}
   : MBA s -> GHC.Num.Int -> GHC.Word.Word8 -> GHC.ST.ST s unit :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | op_MBAzh__ lop_mbazh__
    , GHC.Types.op_Izh__ lop_izh__
    , GHC.Word.op_W8zh__ lop_wzh__ =>
        GHC.ST.ST (fun s =>
                     let 's := _GHC.Prim.writeWord8Array#_ lop_mbazh__ lop_izh__ lop_wzh__ s in
                     pair s tt)
    end.

Definition packLenBytes
   : GHC.Num.Int -> list GHC.Word.Word8 -> ShortByteString :=
  fun len ws0 =>
    let go {s} : MBA s -> GHC.Num.Int -> list GHC.Word.Word8 -> GHC.ST.ST s unit :=
      fix go (arg_0__ : MBA s) (arg_1__ : GHC.Num.Int) (arg_2__ : list GHC.Word.Word8)
        : GHC.ST.ST s unit
        := match arg_0__, arg_1__, arg_2__ with
           | _, _, nil => GHC.Base.return_ tt
           | mba, i, cons w ws =>
               writeWord8Array mba i w GHC.Base.>> go mba (i GHC.Num.+ #1) ws
           end in
    create len (fun mba => go mba #0 ws0).

Definition packBytes : list GHC.Word.Word8 -> ShortByteString :=
  fun cs => packLenBytes (Data.Foldable.length cs) cs.

Definition pack : list GHC.Word.Word8 -> ShortByteString :=
  packBytes.

Definition unpackAppendBytesStrict
   : ShortByteString ->
     GHC.Num.Int -> GHC.Num.Int -> list GHC.Word.Word8 -> list GHC.Word.Word8 :=
  fun sbs off len =>
    let fix go sentinal i acc
      := if i GHC.Base.== sentinal : bool then acc else
         let w := indexWord8Array (asBA sbs) i in
         go sentinal (i GHC.Num.- #1) (cons w acc) in
    go (off GHC.Num.- #1) ((off GHC.Num.- #1) GHC.Num.+ len).

Definition unpackAppendBytesLazy
   : ShortByteString -> list GHC.Word.Word8 -> list GHC.Word.Word8 :=
  fun sbs =>
    let sz := #100 in
    let fix go off len ws
      := let remainder := go (off GHC.Num.+ sz) (len GHC.Num.- sz) ws in
         if len GHC.Base.<= sz : bool then unpackAppendBytesStrict sbs off len ws else
         unpackAppendBytesStrict sbs off sz remainder in
    go #0 (length sbs).

Definition unpackBytes : ShortByteString -> list GHC.Word.Word8 :=
  fun bs => unpackAppendBytesLazy bs nil.

Definition unpack : ShortByteString -> list GHC.Word.Word8 :=
  unpackBytes.

Definition writeCharArray {s}
   : MBA s -> GHC.Num.Int -> GHC.Char.Char -> GHC.ST.ST s unit :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | op_MBAzh__ lop_mbazh__
    , GHC.Types.op_Izh__ lop_izh__
    , GHC.Types.op_Czh__ lop_czh__ =>
        GHC.ST.ST (fun s =>
                     let 's := _GHC.Prim.writeCharArray#_ lop_mbazh__ lop_izh__ lop_czh__ s in
                     pair s tt)
    end.

Definition packLenChars
   : GHC.Num.Int -> list GHC.Char.Char -> ShortByteString :=
  fun len cs0 =>
    let go {s} : MBA s -> GHC.Num.Int -> list GHC.Char.Char -> GHC.ST.ST s unit :=
      fix go (arg_0__ : MBA s) (arg_1__ : GHC.Num.Int) (arg_2__ : list GHC.Char.Char)
        : GHC.ST.ST s unit
        := match arg_0__, arg_1__, arg_2__ with
           | _, _, nil => GHC.Base.return_ tt
           | mba, i, cons c cs =>
               writeCharArray mba i c GHC.Base.>> go mba (i GHC.Num.+ #1) cs
           end in
    create len (fun mba => go mba #0 cs0).

Definition packChars : list GHC.Char.Char -> ShortByteString :=
  fun cs => packLenChars (Data.Foldable.length cs) cs.

Definition indexCharArray : BA -> GHC.Num.Int -> GHC.Char.Char :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | op_BAzh__ lop_bazh__, GHC.Types.op_Izh__ lop_izh__ =>
        _GHC.Types.C#_ (_GHC.Prim.indexCharArray#_ lop_bazh__ lop_izh__)
    end.

Definition unpackAppendCharsStrict
   : ShortByteString ->
     GHC.Num.Int -> GHC.Num.Int -> list GHC.Char.Char -> list GHC.Char.Char :=
  fun sbs off len =>
    let fix go sentinal i acc
      := if i GHC.Base.== sentinal : bool then acc else
         let c := indexCharArray (asBA sbs) i in
         go sentinal (i GHC.Num.- #1) (cons c acc) in
    go (off GHC.Num.- #1) ((off GHC.Num.- #1) GHC.Num.+ len).

Definition unpackAppendCharsLazy
   : ShortByteString -> list GHC.Char.Char -> list GHC.Char.Char :=
  fun sbs =>
    let sz := #100 in
    let fix go off len cs
      := let remainder := go (off GHC.Num.+ sz) (len GHC.Num.- sz) cs in
         if len GHC.Base.<= sz : bool then unpackAppendCharsStrict sbs off len cs else
         unpackAppendCharsStrict sbs off sz remainder in
    go #0 (length sbs).

Definition unpackChars : ShortByteString -> list GHC.Char.Char :=
  fun bs => unpackAppendCharsLazy bs nil.

Definition op_copyByteArrayToAddrzh__
   : _GHC.Prim.ByteArray#_ ->
     _GHC.Prim.Int#_ ->
     _GHC.Prim.Addr#_ ->
     _GHC.Prim.Int#_ ->
     _GHC.Prim.State#_ GHC.Prim.RealWorld -> _GHC.Prim.State#_ GHC.Prim.RealWorld :=
  _GHC.Prim.copyByteArrayToAddr#_.

Notation "'_copyByteArrayToAddr#_'" := (op_copyByteArrayToAddrzh__).

Infix "copyByteArrayToAddr#" := (_copyByteArrayToAddr#_) (at level 99).

Definition copyByteArrayToAddr {a}
   : BA ->
     GHC.Num.Int ->
     GHC.Ptr.Ptr a -> GHC.Num.Int -> GHC.ST.ST GHC.Prim.RealWorld unit :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | op_BAzh__ lop_srczh__
    , GHC.Types.op_Izh__ lop_srczuoffzh__
    , GHC.Ptr.Ptr lop_dstzh__
    , GHC.Types.op_Izh__ lop_lenzh__ =>
        GHC.ST.ST (fun s =>
                     let 's := _copyByteArrayToAddr#_ lop_srczh__ lop_srczuoffzh__ lop_dstzh__
                                 lop_lenzh__ s in
                     pair s tt)
    end.

Definition copyToPtr {a : Type}
   : ShortByteString ->
     GHC.Num.Int -> GHC.Ptr.Ptr a -> GHC.Num.Int -> GHC.Types.IO unit :=
  fun src off dst len =>
    GHC.IO.stToIO (copyByteArrayToAddr (asBA src) off dst len).

Definition moduleErrorMsg
   : GHC.Base.String -> GHC.Base.String -> GHC.Base.String :=
  fun fun_ msg =>
    Coq.Init.Datatypes.app (GHC.Base.hs_string__ "Data.ByteString.Short.")
                           (Coq.Init.Datatypes.app fun_ (cons (GHC.Char.hs_char__ ":") (cons
                                                               (GHC.Char.hs_char__ " ") msg))).

Definition moduleErrorIO {a}
   : GHC.Base.String -> GHC.Base.String -> GHC.Types.IO a :=
  fun fun_ msg =>
    (GHC.IO.throwIO GHC.Base.∘ GHC.IO.Exception.userError) (moduleErrorMsg fun_
                                                                           msg).

Definition packCStringLen
   : Foreign.C.String.CStringLen -> GHC.Types.IO ShortByteString :=
  fun arg_0__ =>
    let 'pair cstr len := arg_0__ in
    if len GHC.Base.>= #0 : bool then createFromPtr cstr len else
    let 'pair _ len := arg_0__ in
    moduleErrorIO (GHC.Base.hs_string__ "packCStringLen") (Coq.Init.Datatypes.app
                                                           (GHC.Base.hs_string__ "negative length: ") (GHC.Show.show
                                                            len)).

Definition packCString
   : Foreign.C.String.CString -> GHC.Types.IO ShortByteString :=
  fun cstr =>
    Data.ByteString.Internal.c_strlen cstr GHC.Base.>>=
    (fun len => packCStringLen (pair cstr (GHC.Real.fromIntegral len))).

Definition useAsCString {a : Type}
   : ShortByteString ->
     (Foreign.C.String.CString -> GHC.Types.IO a) -> GHC.Types.IO a :=
  fun bs action =>
    let l := length bs in
    Foreign.Marshal.Alloc.allocaBytes (l GHC.Num.+ #1) (fun buf =>
                                                          copyToPtr bs #0 buf (GHC.Real.fromIntegral l) GHC.Base.>>
                                                          (Foreign.Storable.pokeByteOff buf l (#0 : GHC.Word.Word8)
                                                           GHC.Base.>>
                                                           action buf)).

Definition useAsCStringLen {a : Type}
   : ShortByteString ->
     (Foreign.C.String.CStringLen -> GHC.Types.IO a) -> GHC.Types.IO a :=
  fun bs action =>
    let l := length bs in
    Foreign.Marshal.Alloc.allocaBytes l (fun buf =>
                                           copyToPtr bs #0 buf (GHC.Real.fromIntegral l) GHC.Base.>>
                                           action (pair buf l)).

Module Notations.
Notation "'_Data.ByteString.Short.Internal.MBA#_'" := (op_MBAzh__).
Infix "Data.ByteString.Short.Internal.MBA#" := (_MBA#_) (at level 99).
Notation "'_Data.ByteString.Short.Internal.BA#_'" := (op_BAzh__).
Infix "Data.ByteString.Short.Internal.BA#" := (_BA#_) (at level 99).
Notation "'_Data.ByteString.Short.Internal.copyByteArray#_'" :=
  (op_copyByteArrayzh__).
Infix "Data.ByteString.Short.Internal.copyByteArray#" := (_copyByteArray#_)
  (at level 99).
Notation "'_Data.ByteString.Short.Internal.!?_'" := (op_znz3fU__).
Infix "Data.ByteString.Short.Internal.!?" := (_!?_) (at level 99).
Notation "'_Data.ByteString.Short.Internal.copyAddrToByteArray#_'" :=
  (op_copyAddrToByteArrayzh__).
Infix "Data.ByteString.Short.Internal.copyAddrToByteArray#" :=
(_copyAddrToByteArray#_) (at level 99).
Notation "'_Data.ByteString.Short.Internal.copyByteArrayToAddr#_'" :=
  (op_copyByteArrayToAddrzh__).
Infix "Data.ByteString.Short.Internal.copyByteArrayToAddr#" :=
(_copyByteArrayToAddr#_) (at level 99).
End Notations.

(* External variables:
     Eq Gt Lt None Some Type andb bool c_memcmp_ByteArray comparison cons list negb
     nil option pair tt unit Coq.Init.Datatypes.app Data.ByteString.Internal.BS
     Data.ByteString.Internal.ByteString
     Data.ByteString.Internal.accursedUnutterablePerformIO
     Data.ByteString.Internal.c_strlen Data.Foldable.length Foreign.C.String.CString
     Foreign.C.String.CStringLen Foreign.C.Types.CInt
     Foreign.Marshal.Alloc.allocaBytes Foreign.Storable.pokeByteOff GHC.Base.Eq_
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.String
     GHC.Base.compare__ GHC.Base.mappend__ GHC.Base.max__ GHC.Base.mconcat__
     GHC.Base.mempty__ GHC.Base.min GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.return_ GHC.Char.Char GHC.Err.error
     GHC.ForeignPtr.ForeignPtr GHC.ForeignPtr.PlainPtr GHC.ForeignPtr.touchForeignPtr
     GHC.ForeignPtr.unsafeForeignPtrToPtr GHC.IO.stToIO GHC.IO.throwIO
     GHC.IO.Exception.userError GHC.IO.Unsafe.unsafeDupablePerformIO GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Prim.RealWorld
     GHC.Prim.op_Addrzh__ GHC.Prim.op_ByteArrayzh__ GHC.Prim.op_Intzh__
     GHC.Prim.op_MutableByteArrayzh__ GHC.Prim.op_Statezh__
     GHC.Prim.op_byteArrayContentszh__ GHC.Prim.op_copyAddrToByteArrayzh__
     GHC.Prim.op_copyByteArrayToAddrzh__ GHC.Prim.op_copyByteArrayzh__
     GHC.Prim.op_indexCharArrayzh__ GHC.Prim.op_indexWord8Arrayzh__
     GHC.Prim.op_isByteArrayPinnedzh__ GHC.Prim.op_newByteArrayzh__
     GHC.Prim.op_newPinnedByteArrayzh__ GHC.Prim.op_sizzeofByteArrayzh__
     GHC.Prim.op_unsafeCoercezh__ GHC.Prim.op_unsafeFreezzeByteArrayzh__
     GHC.Prim.op_writeCharArrayzh__ GHC.Prim.op_writeWord8Arrayzh__ GHC.Ptr.Ptr
     GHC.Real.fromIntegral GHC.ST.ST GHC.ST.runST GHC.Show.show GHC.Types.IO
     GHC.Types.op_Czh__ GHC.Types.op_Izh__ GHC.Types.op_isTruezh__ GHC.Word.Word8
     GHC.Word.op_W8zh__
*)
