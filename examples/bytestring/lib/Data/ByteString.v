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
Require Coq.Lists.List.
Require Data.Bits.
Require Data.ByteString.Internal.
Require Data.ByteString.Unsafe.
Require Data.Functor.
Require Data.OldList.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Enum.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Import Data.Bits.Notations.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Real.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition empty : Data.ByteString.Internal.ByteString :=
  Data.ByteString.Internal.BS Data.ByteString.Internal.nullForeignPtr #0.

Definition singleton : GHC.Word.Word8 -> Data.ByteString.Internal.ByteString :=
  fun c =>
    Data.ByteString.Internal.unsafeCreate #1 (fun p => Foreign.Storable.poke p c).

Definition pack : list GHC.Word.Word8 -> Data.ByteString.Internal.ByteString :=
  Data.ByteString.Internal.packBytes.

Definition foldr {a : Type}
   : (GHC.Word.Word8 -> a -> a) ->
     a -> Data.ByteString.Internal.ByteString -> a :=
  fun k z =>
    fun '(Data.ByteString.Internal.BS fp len) =>
      let ptr := GHC.ForeignPtr.unsafeForeignPtrToPtr fp in
      let end := GHC.Ptr.plusPtr ptr len in
      let fix go p
        := if p GHC.Base.== end : bool then z else
           let x :=
             Data.ByteString.Internal.accursedUnutterablePerformIO (Foreign.Storable.peek p
                                                                    GHC.Base.>>=
                                                                    (fun x' =>
                                                                       GHC.ForeignPtr.touchForeignPtr fp GHC.Base.>>
                                                                       GHC.Base.return_ x')) in
           k x (go (GHC.Ptr.plusPtr p #1)) in
      go ptr.

Definition unpackFoldr {a}
   : Data.ByteString.Internal.ByteString ->
     (GHC.Word.Word8 -> a -> a) -> a -> a :=
  fun bs k z => foldr k z bs.

Definition unpack
   : Data.ByteString.Internal.ByteString -> list GHC.Word.Word8 :=
  fun bs => GHC.Base.build' (fun _ => unpackFoldr bs).

Definition fromFilePath
   : GHC.Base.String -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun path =>
    GHC.IO.Encoding.getFileSystemEncoding GHC.Base.>>=
    (fun enc =>
       GHC.Foreign.newCStringLen enc path GHC.Base.>>=
       Data.ByteString.Unsafe.unsafePackMallocCStringLen).

Definition useAsCString {a : Type}
   : Data.ByteString.Internal.ByteString ->
     (Foreign.C.String.CString -> GHC.Types.IO a) -> GHC.Types.IO a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.ByteString.Internal.BS fp l, action =>
        Foreign.Marshal.Alloc.allocaBytes (l GHC.Num.+ #1) (fun buf =>
                                                              Foreign.ForeignPtr.Imp.withForeignPtr fp (fun p =>
                                                                                                          Data.ByteString.Internal.memcpy
                                                                                                          buf p
                                                                                                          (GHC.Real.fromIntegral
                                                                                                           l)
                                                                                                          GHC.Base.>>
                                                                                                          (Foreign.Storable.pokeByteOff
                                                                                                           buf l
                                                                                                           (#0 : GHC.Word.Word8)
                                                                                                           GHC.Base.>>
                                                                                                           action
                                                                                                           (GHC.Ptr.castPtr
                                                                                                            buf))))
    end.

Definition useAsCStringLen {a : Type}
   : Data.ByteString.Internal.ByteString ->
     (Foreign.C.String.CStringLen -> GHC.Types.IO a) -> GHC.Types.IO a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Data.ByteString.Internal.BS _ l as p), f =>
        useAsCString p (fun cstr => f (pair cstr l))
    end.

Definition toFilePath
   : Data.ByteString.Internal.ByteString -> GHC.Types.IO GHC.Base.String :=
  fun path =>
    GHC.IO.Encoding.getFileSystemEncoding GHC.Base.>>=
    (fun enc => useAsCStringLen path (GHC.Foreign.peekCStringLen enc)).

Definition null : Data.ByteString.Internal.ByteString -> bool :=
  fun '(Data.ByteString.Internal.BS _ l) =>
    GHC.Base.assert (l GHC.Base.>= #0) (l GHC.Base.<= #0).

Definition length : Data.ByteString.Internal.ByteString -> GHC.Num.Int :=
  fun '(Data.ByteString.Internal.BS _ l) => GHC.Base.assert (l GHC.Base.>= #0) l.

Definition cons_
   : GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | c, Data.ByteString.Internal.BS x l =>
        Data.ByteString.Internal.unsafeCreate (l GHC.Num.+ #1) (fun p =>
                                                                  Data.ByteString.Internal.unsafeWithForeignPtr x
                                                                  (fun f =>
                                                                     Foreign.Storable.poke p c GHC.Base.>>
                                                                     Data.ByteString.Internal.memcpy (GHC.Ptr.plusPtr p
                                                                                                                      #1)
                                                                     f (GHC.Real.fromIntegral l)))
    end.

Definition snoc
   : Data.ByteString.Internal.ByteString ->
     GHC.Word.Word8 -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.ByteString.Internal.BS x l, c =>
        Data.ByteString.Internal.unsafeCreate (l GHC.Num.+ #1) (fun p =>
                                                                  Data.ByteString.Internal.unsafeWithForeignPtr x
                                                                  (fun f =>
                                                                     Data.ByteString.Internal.memcpy p f
                                                                     (GHC.Real.fromIntegral l) GHC.Base.>>
                                                                     Foreign.Storable.poke (GHC.Ptr.plusPtr p l) c))
    end.

Definition moduleErrorMsg
   : GHC.Base.String -> GHC.Base.String -> GHC.Base.String :=
  fun fun_ msg =>
    Coq.Init.Datatypes.app (GHC.Base.hs_string__ "Data.ByteString.")
                           (Coq.Init.Datatypes.app fun_ (cons (GHC.Char.hs_char__ ":") (cons
                                                               (GHC.Char.hs_char__ " ") msg))).

Definition moduleError {a} : GHC.Base.String -> GHC.Base.String -> a :=
  fun fun_ msg => GHC.Err.error (moduleErrorMsg fun_ msg).

Definition errorEmptyList {a} : GHC.Base.String -> a :=
  fun fun_ => moduleError fun_ (GHC.Base.hs_string__ "empty ByteString").

Definition head : Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun '(Data.ByteString.Internal.BS x l) =>
    if l GHC.Base.<= #0 : bool
    then errorEmptyList (GHC.Base.hs_string__ "head") else
    Data.ByteString.Internal.accursedUnutterablePerformIO
    (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                      Foreign.Storable.peek p)).

Definition tail
   : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun '(Data.ByteString.Internal.BS p l) =>
    if l GHC.Base.<= #0 : bool
    then errorEmptyList (GHC.Base.hs_string__ "tail") else
    Data.ByteString.Internal.BS (GHC.ForeignPtr.plusForeignPtr p #1) (l GHC.Num.-
                                                                      #1).

Definition uncons
   : Data.ByteString.Internal.ByteString ->
     option (GHC.Word.Word8 * Data.ByteString.Internal.ByteString)%type :=
  fun '(Data.ByteString.Internal.BS x l) =>
    if l GHC.Base.<= #0 : bool then None else
    Some (pair (Data.ByteString.Internal.accursedUnutterablePerformIO
                (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                                  Foreign.Storable.peek p)))
               (Data.ByteString.Internal.BS (GHC.ForeignPtr.plusForeignPtr x #1) (l GHC.Num.-
                                                                                  #1))).

Definition last : Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun '((Data.ByteString.Internal.BS x l as ps)) =>
    if null ps : bool then errorEmptyList (GHC.Base.hs_string__ "last") else
    Data.ByteString.Internal.accursedUnutterablePerformIO
    (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                      Foreign.Storable.peekByteOff p (l GHC.Num.- #1))).

Definition init
   : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun '((Data.ByteString.Internal.BS p l as ps)) =>
    if null ps : bool then errorEmptyList (GHC.Base.hs_string__ "init") else
    Data.ByteString.Internal.BS p (l GHC.Num.- #1).

Definition unsnoc
   : Data.ByteString.Internal.ByteString ->
     option (Data.ByteString.Internal.ByteString * GHC.Word.Word8)%type :=
  fun '(Data.ByteString.Internal.BS x l) =>
    if l GHC.Base.<= #0 : bool then None else
    Some (pair (Data.ByteString.Internal.BS x (l GHC.Num.- #1))
               (Data.ByteString.Internal.accursedUnutterablePerformIO
                (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                                  Foreign.Storable.peekByteOff p (l GHC.Num.- #1))))).

Definition append
   : Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  GHC.Base.mappend.

Definition map
   : (GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Data.ByteString.Internal.BS fp len =>
        let m :=
          fun p1 p2 =>
            let map_ : GHC.Num.Int -> GHC.Types.IO unit :=
              fix map_ (n : GHC.Num.Int) : GHC.Types.IO unit
                := if n GHC.Base.>= len : bool then GHC.Base.return_ tt else
                   Foreign.Storable.peekByteOff p1 n GHC.Base.>>=
                   (fun x =>
                      Foreign.Storable.pokeByteOff p2 n (f x) GHC.Base.>> map_ (n GHC.Num.+ #1)) in
            map_ #0 in
        GHC.IO.Unsafe.unsafeDupablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr fp (fun srcPtr =>
                                                          Data.ByteString.Internal.create len (fun dstPtr =>
                                                                                                 m srcPtr dstPtr)))
    end.

Definition reverse
   : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun '(Data.ByteString.Internal.BS x l) =>
    Data.ByteString.Internal.unsafeCreate l (fun p =>
                                               Data.ByteString.Internal.unsafeWithForeignPtr x (fun f =>
                                                                                                  Data.ByteString.Internal.c_reverse
                                                                                                  p f
                                                                                                  (GHC.Real.fromIntegral
                                                                                                   l))).

Definition intersperse
   : GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | c, (Data.ByteString.Internal.BS x l as ps) =>
        if length ps GHC.Base.< #2 : bool then ps else
        Data.ByteString.Internal.unsafeCreate ((#2 GHC.Num.* l) GHC.Num.- #1) (fun p =>
                                                                                 Data.ByteString.Internal.unsafeWithForeignPtr
                                                                                 x (fun f =>
                                                                                      Data.ByteString.Internal.c_intersperse
                                                                                      p f (GHC.Real.fromIntegral l) c))
    end.

Definition transpose
   : list Data.ByteString.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString :=
  GHC.Base.map pack GHC.Base.∘
  (Data.OldList.transpose GHC.Base.∘ GHC.Base.map unpack).

Definition foldl {a : Type}
   : (a -> GHC.Word.Word8 -> a) ->
     a -> Data.ByteString.Internal.ByteString -> a :=
  fun f z =>
    fun '(Data.ByteString.Internal.BS fp len) =>
      let end :=
        GHC.Ptr.plusPtr (GHC.ForeignPtr.unsafeForeignPtrToPtr fp) (GHC.Num.negate #1) in
      let fix go p
        := if p GHC.Base.== end : bool then z else
           let x :=
             Data.ByteString.Internal.accursedUnutterablePerformIO (Foreign.Storable.peek p
                                                                    GHC.Base.>>=
                                                                    (fun x' =>
                                                                       GHC.ForeignPtr.touchForeignPtr fp GHC.Base.>>
                                                                       GHC.Base.return_ x')) in
           f (go (GHC.Ptr.plusPtr p (GHC.Num.negate #1))) x in
      go (GHC.Ptr.plusPtr end len).

Definition foldl' {a : Type}
   : (a -> GHC.Word.Word8 -> a) ->
     a -> Data.ByteString.Internal.ByteString -> a :=
  fun f v =>
    fun '(Data.ByteString.Internal.BS fp len) =>
      let g :=
        fun ptr =>
          let end := GHC.Ptr.plusPtr ptr len in
          let fix go z p
            := if p GHC.Base.== end : bool then GHC.Base.return_ z else
               Foreign.Storable.peek p GHC.Base.>>=
               (fun x => go (f z x) (GHC.Ptr.plusPtr p #1)) in
          go v ptr in
      Data.ByteString.Internal.accursedUnutterablePerformIO
      (Data.ByteString.Internal.unsafeWithForeignPtr fp g).

Definition foldr' {a : Type}
   : (GHC.Word.Word8 -> a -> a) ->
     a -> Data.ByteString.Internal.ByteString -> a :=
  fun k v =>
    fun '(Data.ByteString.Internal.BS fp len) =>
      let g :=
        fun ptr =>
          let end := GHC.Ptr.plusPtr ptr (GHC.Num.negate #1) in
          let fix go z p
            := if p GHC.Base.== end : bool then GHC.Base.return_ z else
               Foreign.Storable.peek p GHC.Base.>>=
               (fun x => go (k x z) (GHC.Ptr.plusPtr p (GHC.Num.negate #1))) in
          go v (GHC.Ptr.plusPtr end len) in
      Data.ByteString.Internal.accursedUnutterablePerformIO
      (Data.ByteString.Internal.unsafeWithForeignPtr fp g).

Definition foldl1
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun f ps =>
    match uncons ps with
    | None => errorEmptyList (GHC.Base.hs_string__ "foldl1")
    | Some (pair h t) => foldl f h t
    end.

Definition foldl1'
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun f ps =>
    match uncons ps with
    | None => errorEmptyList (GHC.Base.hs_string__ "foldl1'")
    | Some (pair h t) => foldl' f h t
    end.

Definition foldr1
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun f ps =>
    match unsnoc ps with
    | None => errorEmptyList (GHC.Base.hs_string__ "foldr1")
    | Some (pair b c) => foldr f c b
    end.

Definition foldr1'
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun f ps =>
    match unsnoc ps with
    | None => errorEmptyList (GHC.Base.hs_string__ "foldr1'")
    | Some (pair b c) => foldr' f c b
    end.

Definition concat
   : list Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString :=
  GHC.Base.mconcat.

Definition concatMap
   : (GHC.Word.Word8 -> Data.ByteString.Internal.ByteString) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f => concat GHC.Base.∘ foldr (cons GHC.Base.∘ f) nil.

Definition any
   : (GHC.Word.Word8 -> bool) -> Data.ByteString.Internal.ByteString -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Internal.BS _ num_2__ =>
        if num_2__ GHC.Base.== #0 : bool then false else
        match arg_0__, arg_1__ with
        | f, Data.ByteString.Internal.BS x len =>
            let g :=
              fun ptr =>
                let end := GHC.Ptr.plusPtr ptr len in
                let fix go p
                  := if p GHC.Base.== end : bool then GHC.Base.return_ false else
                     Foreign.Storable.peek p GHC.Base.>>=
                     (fun c =>
                        if f c : bool
                        then GHC.Base.return_ true
                        else go (GHC.Ptr.plusPtr p #1)) in
                go ptr in
            Data.ByteString.Internal.accursedUnutterablePerformIO
            (Data.ByteString.Internal.unsafeWithForeignPtr x g)
        end
    end.

Definition anyByte
   : GHC.Word.Word8 -> Data.ByteString.Internal.ByteString -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | c, Data.ByteString.Internal.BS x l =>
        Data.ByteString.Internal.accursedUnutterablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                          Data.ByteString.Internal.memchr p c (GHC.Real.fromIntegral l)
                                                          GHC.Base.>>=
                                                          (fun q => GHC.Base.return_ (q GHC.Base./= GHC.Ptr.nullPtr))))
    end.

Definition all
   : (GHC.Word.Word8 -> bool) -> Data.ByteString.Internal.ByteString -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Internal.BS _ num_2__ =>
        if num_2__ GHC.Base.== #0 : bool then true else
        match arg_0__, arg_1__ with
        | f, Data.ByteString.Internal.BS x len =>
            let g :=
              fun ptr =>
                let end := GHC.Ptr.plusPtr ptr len in
                let fix go p
                  := if p GHC.Base.== end : bool then GHC.Base.return_ true else
                     Foreign.Storable.peek p GHC.Base.>>=
                     (fun c =>
                        if f c : bool
                        then go (GHC.Ptr.plusPtr p #1)
                        else GHC.Base.return_ false) in
                go ptr in
            Data.ByteString.Internal.accursedUnutterablePerformIO
            (Data.ByteString.Internal.unsafeWithForeignPtr x g)
        end
    end.

Definition maximum : Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun '((Data.ByteString.Internal.BS x l as xs)) =>
    if null xs : bool then errorEmptyList (GHC.Base.hs_string__ "maximum") else
    Data.ByteString.Internal.accursedUnutterablePerformIO
    (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                      Data.ByteString.Internal.c_maximum p (GHC.Real.fromIntegral l))).

Definition minimum : Data.ByteString.Internal.ByteString -> GHC.Word.Word8 :=
  fun '((Data.ByteString.Internal.BS x l as xs)) =>
    if null xs : bool then errorEmptyList (GHC.Base.hs_string__ "minimum") else
    Data.ByteString.Internal.accursedUnutterablePerformIO
    (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                      Data.ByteString.Internal.c_minimum p (GHC.Real.fromIntegral l))).

Definition mapAccumL {acc : Type}
   : (acc -> GHC.Word.Word8 -> (acc * GHC.Word.Word8)%type) ->
     acc ->
     Data.ByteString.Internal.ByteString ->
     (acc * Data.ByteString.Internal.ByteString)%type :=
  fun f acc =>
    fun '(Data.ByteString.Internal.BS fp len) =>
      GHC.IO.Unsafe.unsafeDupablePerformIO
      (Data.ByteString.Internal.unsafeWithForeignPtr fp (fun a =>
                                                        Data.ByteString.Internal.mallocByteString len GHC.Base.>>=
                                                        (fun gp =>
                                                           let go :=
                                                             fun src dst =>
                                                               let fix mapAccumL_ s n
                                                                 := if n GHC.Base.>= len : bool
                                                                    then GHC.Base.return_ s else
                                                                    Foreign.Storable.peekByteOff src n GHC.Base.>>=
                                                                    (fun x =>
                                                                       let 'pair s' y := f s x in
                                                                       Foreign.Storable.pokeByteOff dst n y GHC.Base.>>
                                                                       mapAccumL_ s' (n GHC.Num.+ #1)) in
                                                               mapAccumL_ acc #0 in
                                                           Data.ByteString.Internal.unsafeWithForeignPtr gp (go a)
                                                           GHC.Base.>>=
                                                           (fun acc' =>
                                                              GHC.Base.return_ (pair acc' (Data.ByteString.Internal.BS
                                                                                      gp len)))))).

Definition mapAccumR {acc : Type}
   : (acc -> GHC.Word.Word8 -> (acc * GHC.Word.Word8)%type) ->
     acc ->
     Data.ByteString.Internal.ByteString ->
     (acc * Data.ByteString.Internal.ByteString)%type :=
  fun f acc =>
    fun '(Data.ByteString.Internal.BS fp len) =>
      GHC.IO.Unsafe.unsafeDupablePerformIO
      (Data.ByteString.Internal.unsafeWithForeignPtr fp (fun a =>
                                                        Data.ByteString.Internal.mallocByteString len GHC.Base.>>=
                                                        (fun gp =>
                                                           let go :=
                                                             fun src dst =>
                                                               let fix mapAccumR_ arg_1__ arg_2__
                                                                 := match arg_1__, arg_2__ with
                                                                    | s, num_3__ =>
                                                                        if num_3__ GHC.Base.== #1 : bool
                                                                        then GHC.Base.return_ s else
                                                                        match arg_1__, arg_2__ with
                                                                        | s, n =>
                                                                            Foreign.Storable.peekByteOff src n
                                                                            GHC.Base.>>=
                                                                            (fun x =>
                                                                               let 'pair s' y := f s x in
                                                                               Foreign.Storable.pokeByteOff dst n y
                                                                               GHC.Base.>>
                                                                               mapAccumR_ s' (n GHC.Num.- #1))
                                                                        end
                                                                    end in
                                                               mapAccumR_ acc (len GHC.Num.- #1) in
                                                           Data.ByteString.Internal.unsafeWithForeignPtr gp (go a)
                                                           GHC.Base.>>=
                                                           (fun acc' =>
                                                              GHC.Base.return_ (pair acc' (Data.ByteString.Internal.BS
                                                                                      gp len)))))).

Definition scanl
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f v =>
    fun '(Data.ByteString.Internal.BS fp len) =>
      GHC.IO.Unsafe.unsafeDupablePerformIO
      (Data.ByteString.Internal.unsafeWithForeignPtr fp (fun a =>
                                                        Data.ByteString.Internal.create (len GHC.Num.+ #1) (fun q =>
                                                                                                              Foreign.Storable.poke
                                                                                                              q v
                                                                                                              GHC.Base.>>
                                                                                                              (let go :=
                                                                                                                 fun src
                                                                                                                 dst =>
                                                                                                                   let fix scanl_
                                                                                                                     z n
                                                                                                                     := if n
                                                                                                                           GHC.Base.>=
                                                                                                                           len : bool
                                                                                                                        then GHC.Base.return_
                                                                                                                             tt else
                                                                                                                        Foreign.Storable.peekByteOff
                                                                                                                        src
                                                                                                                        n
                                                                                                                        GHC.Base.>>=
                                                                                                                        (fun x =>
                                                                                                                           let z' :=
                                                                                                                             f
                                                                                                                             z
                                                                                                                             x in
                                                                                                                           Foreign.Storable.pokeByteOff
                                                                                                                           dst
                                                                                                                           n
                                                                                                                           z'
                                                                                                                           GHC.Base.>>
                                                                                                                           scanl_
                                                                                                                           z'
                                                                                                                           (n
                                                                                                                            GHC.Num.+
                                                                                                                            #1)) in
                                                                                                                   scanl_
                                                                                                                   v
                                                                                                                   #0 in
                                                                                                               go a
                                                                                                               (GHC.Ptr.plusPtr
                                                                                                                q
                                                                                                                #1))))).

Definition scanl1
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f ps =>
    match uncons ps with
    | None => empty
    | Some (pair h t) => scanl f h t
    end.

Definition scanr
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f v =>
    fun '(Data.ByteString.Internal.BS fp len) =>
      GHC.IO.Unsafe.unsafeDupablePerformIO
      (Data.ByteString.Internal.unsafeWithForeignPtr fp (fun a =>
                                                        Data.ByteString.Internal.create (len GHC.Num.+ #1) (fun b =>
                                                                                                              Foreign.Storable.poke
                                                                                                              (GHC.Ptr.plusPtr
                                                                                                               b len) v
                                                                                                              GHC.Base.>>
                                                                                                              (let go :=
                                                                                                                 fun p
                                                                                                                 q =>
                                                                                                                   let fix scanr_
                                                                                                                     z n
                                                                                                                     := if n
                                                                                                                           GHC.Base.<
                                                                                                                           #0 : bool
                                                                                                                        then GHC.Base.return_
                                                                                                                             tt else
                                                                                                                        Foreign.Storable.peekByteOff
                                                                                                                        p
                                                                                                                        n
                                                                                                                        GHC.Base.>>=
                                                                                                                        (fun x =>
                                                                                                                           let z' :=
                                                                                                                             f
                                                                                                                             x
                                                                                                                             z in
                                                                                                                           Foreign.Storable.pokeByteOff
                                                                                                                           q
                                                                                                                           n
                                                                                                                           z'
                                                                                                                           GHC.Base.>>
                                                                                                                           scanr_
                                                                                                                           z'
                                                                                                                           (n
                                                                                                                            GHC.Num.-
                                                                                                                            #1)) in
                                                                                                                   scanr_
                                                                                                                   v
                                                                                                                   (len
                                                                                                                    GHC.Num.-
                                                                                                                    #1) in
                                                                                                               go a
                                                                                                               b)))).

Definition scanr1
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f ps =>
    match unsnoc ps with
    | None => empty
    | Some (pair b c) => scanr f c b
    end.

Definition replicate
   : GHC.Num.Int -> GHC.Word.Word8 -> Data.ByteString.Internal.ByteString :=
  fun w c =>
    if w GHC.Base.<= #0 : bool then empty else
    Data.ByteString.Internal.unsafeCreate w (fun ptr =>
                                               Data.Functor.void (Data.ByteString.Internal.memset ptr c
                                                                                                  (GHC.Real.fromIntegral
                                                                                                   w))).

Definition unfoldrN {a : Type}
   : GHC.Num.Int ->
     (a -> option (GHC.Word.Word8 * a)%type) ->
     a -> (Data.ByteString.Internal.ByteString * option a)%type :=
  fun i f x0 =>
    let go :=
      fun p x n =>
        let fix go' x' n'
          := if n' GHC.Base.== i : bool
             then GHC.Base.return_ (pair (pair #0 n') (Some x')) else
             match f x' with
             | None => GHC.Base.return_ (pair (pair #0 n') None)
             | Some (pair w x'') =>
                 Foreign.Storable.pokeByteOff p n' w GHC.Base.>> go' x'' (n' GHC.Num.+ #1)
             end in
        go' x n in
    if i GHC.Base.< #0 : bool then pair empty (Some x0) else
    GHC.IO.Unsafe.unsafePerformIO (Data.ByteString.Internal.createAndTrim' i
                                                                           (fun p => go p x0 #0)).

Definition unfoldr {a : Type}
   : (a -> option (GHC.Word.Word8 * a)%type) ->
     a -> Data.ByteString.Internal.ByteString :=
  fun f =>
    let fix unfoldChunk n n' x
      := match unfoldrN n f x with
         | pair s None => cons s nil
         | pair s (Some x') => cons s (unfoldChunk n' (n GHC.Num.+ n') x')
         end in
    concat GHC.Base.∘ unfoldChunk #32 #64.

Definition take
   : GHC.Num.Int ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, (Data.ByteString.Internal.BS x l as ps) =>
        if n GHC.Base.<= #0 : bool then empty else
        if n GHC.Base.>= l : bool then ps else
        Data.ByteString.Internal.BS x n
    end.

Definition takeEnd
   : GHC.Num.Int ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, (Data.ByteString.Internal.BS x len as ps) =>
        if n GHC.Base.>= len : bool then ps else
        if n GHC.Base.<= #0 : bool then empty else
        Data.ByteString.Internal.BS (GHC.ForeignPtr.plusForeignPtr x (len GHC.Num.- n))
        n
    end.

Definition drop
   : GHC.Num.Int ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, (Data.ByteString.Internal.BS x l as ps) =>
        if n GHC.Base.<= #0 : bool then ps else
        if n GHC.Base.>= l : bool then empty else
        Data.ByteString.Internal.BS (GHC.ForeignPtr.plusForeignPtr x n) (l GHC.Num.- n)
    end.

Definition dropEnd
   : GHC.Num.Int ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, (Data.ByteString.Internal.BS x len as ps) =>
        if n GHC.Base.<= #0 : bool then ps else
        if n GHC.Base.>= len : bool then empty else
        Data.ByteString.Internal.BS x (len GHC.Num.- n)
    end.

Definition splitAt
   : GHC.Num.Int ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, (Data.ByteString.Internal.BS x l as ps) =>
        if n GHC.Base.<= #0 : bool then pair empty ps else
        if n GHC.Base.>= l : bool then pair ps empty else
        pair (Data.ByteString.Internal.BS x n) (Data.ByteString.Internal.BS
              (GHC.ForeignPtr.plusForeignPtr x n) (l GHC.Num.- n))
    end.

Definition takeWhile
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f ps =>
    Data.ByteString.Unsafe.unsafeTake (Data.ByteString.Internal.findIndexOrLength
                                       (negb GHC.Base.∘ f) ps) ps.

Fixpoint findFromEndUntil (arg_0__ : (GHC.Word.Word8 -> bool)) (arg_1__
                            : Data.ByteString.Internal.ByteString) : GHC.Num.Int
  := match arg_0__, arg_1__ with
     | f, (Data.ByteString.Internal.BS _ l as ps) =>
         match unsnoc ps with
         | None => #0
         | Some (pair b c) => if f c : bool then l else findFromEndUntil f b
         end
     end.

Definition takeWhileEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f ps =>
    Data.ByteString.Unsafe.unsafeDrop (findFromEndUntil (negb GHC.Base.∘ f) ps) ps.

Definition dropWhile
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f ps =>
    Data.ByteString.Unsafe.unsafeDrop (Data.ByteString.Internal.findIndexOrLength
                                       (negb GHC.Base.∘ f) ps) ps.

Definition dropWhileEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f ps =>
    Data.ByteString.Unsafe.unsafeTake (findFromEndUntil (negb GHC.Base.∘ f) ps) ps.

Definition break
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun p ps =>
    let 'n := Data.ByteString.Internal.findIndexOrLength p ps in
    pair (Data.ByteString.Unsafe.unsafeTake n ps) (Data.ByteString.Unsafe.unsafeDrop
          n ps).

Definition elemIndex
   : GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString -> option GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | c, Data.ByteString.Internal.BS x l =>
        Data.ByteString.Internal.accursedUnutterablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                          Data.ByteString.Internal.memchr p c (GHC.Real.fromIntegral l)
                                                          GHC.Base.>>=
                                                          (fun q =>
                                                             GHC.Base.return_ (if q GHC.Base.== GHC.Ptr.nullPtr : bool
                                                                               then None
                                                                               else Some (GHC.Ptr.minusPtr q p)))))
    end.

Definition breakByte
   : GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun c p =>
    match elemIndex c p with
    | None => pair p empty
    | Some n =>
        pair (Data.ByteString.Unsafe.unsafeTake n p) (Data.ByteString.Unsafe.unsafeDrop
              n p)
    end.

Definition breakEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun p ps => splitAt (findFromEndUntil p ps) ps.

Definition span
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun p => break (negb GHC.Base.∘ p).

Definition spanByte
   : GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | c, (Data.ByteString.Internal.BS x l as ps) =>
        let g :=
          fun p =>
            let fix go i
              := if i GHC.Base.>= l : bool then GHC.Base.return_ (pair ps empty) else
                 Foreign.Storable.peekByteOff p i GHC.Base.>>=
                 (fun c' =>
                    if c GHC.Base./= c' : bool
                    then GHC.Base.return_ (pair (Data.ByteString.Unsafe.unsafeTake i ps)
                                                (Data.ByteString.Unsafe.unsafeDrop i ps))
                    else go (i GHC.Num.+ #1)) in
            go #0 in
        Data.ByteString.Internal.accursedUnutterablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr x g)
    end.

Definition spanEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun p ps => splitAt (findFromEndUntil (negb GHC.Base.∘ p) ps) ps.

Definition splitWith
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Internal.BS _ num_2__ =>
        if num_2__ GHC.Base.== #0 : bool then nil else
        match arg_0__, arg_1__ with
        | predicate, Data.ByteString.Internal.BS fp len =>
            let splitWith0 :=
              fix splitLoop (p : GHC.Ptr.Ptr GHC.Word.Word8) (idx2 off' len' : GHC.Num.Int)
                            (fp' : GHC.ForeignPtr.ForeignPtr GHC.Word.Word8) : GHC.Types.IO (list
                                                                                             Data.ByteString.Internal.ByteString)
                := let fix go idx'
                     := if idx' GHC.Base.>= len' : bool
                        then GHC.Base.return_ (cons (Data.ByteString.Internal.BS
                                                     (GHC.ForeignPtr.plusForeignPtr fp' off') idx') nil) else
                        Foreign.Storable.peekElemOff p (off' GHC.Num.+ idx') GHC.Base.>>=
                        (fun w =>
                           if predicate w : bool
                           then GHC.Base.return_ (cons (Data.ByteString.Internal.BS
                                                        (GHC.ForeignPtr.plusForeignPtr fp' off') idx') (splitWith0
                                                        ((off' GHC.Num.+ idx') GHC.Num.+ #1) ((len' GHC.Num.- idx')
                                                                                              GHC.Num.-
                                                                                              #1) fp'))
                           else go (idx' GHC.Num.+ #1)) in
                   go idx2
              with splitWith0 off' len' fp'
                := Data.ByteString.Internal.accursedUnutterablePerformIO
                   (Data.ByteString.Internal.unsafeWithForeignPtr fp (fun p =>
                                                                     splitLoop p #0 off' len' fp')) for splitWith0 in
            let splitLoop
             : GHC.Ptr.Ptr GHC.Word.Word8 ->
               GHC.Num.Int ->
               GHC.Num.Int ->
               GHC.Num.Int ->
               GHC.ForeignPtr.ForeignPtr GHC.Word.Word8 ->
               GHC.Types.IO (list Data.ByteString.Internal.ByteString) :=
              fix splitLoop (p : GHC.Ptr.Ptr GHC.Word.Word8) (idx2 off' len' : GHC.Num.Int)
                            (fp' : GHC.ForeignPtr.ForeignPtr GHC.Word.Word8) : GHC.Types.IO (list
                                                                                             Data.ByteString.Internal.ByteString)
                := let fix go idx'
                     := if idx' GHC.Base.>= len' : bool
                        then GHC.Base.return_ (cons (Data.ByteString.Internal.BS
                                                     (GHC.ForeignPtr.plusForeignPtr fp' off') idx') nil) else
                        Foreign.Storable.peekElemOff p (off' GHC.Num.+ idx') GHC.Base.>>=
                        (fun w =>
                           if predicate w : bool
                           then GHC.Base.return_ (cons (Data.ByteString.Internal.BS
                                                        (GHC.ForeignPtr.plusForeignPtr fp' off') idx') (splitWith0
                                                        ((off' GHC.Num.+ idx') GHC.Num.+ #1) ((len' GHC.Num.- idx')
                                                                                              GHC.Num.-
                                                                                              #1) fp'))
                           else go (idx' GHC.Num.+ #1)) in
                   go idx2
              with splitWith0 off' len' fp'
                := Data.ByteString.Internal.accursedUnutterablePerformIO
                   (Data.ByteString.Internal.unsafeWithForeignPtr fp (fun p =>
                                                                     splitLoop p #0 off' len' fp')) for splitLoop in
            splitWith0 #0 len fp
        end
    end.

Definition split
   : GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Internal.BS _ num_2__ =>
        if num_2__ GHC.Base.== #0 : bool then nil else
        match arg_0__, arg_1__ with
        | w, Data.ByteString.Internal.BS x l =>
            let fix loop n
              := let q :=
                   Data.ByteString.Internal.accursedUnutterablePerformIO
                   (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                                     Data.ByteString.Internal.memchr (GHC.Ptr.plusPtr p
                                                                                                                      n)
                                                                     w (GHC.Real.fromIntegral (l GHC.Num.- n)))) in
                 if q GHC.Base.== GHC.Ptr.nullPtr : bool
                 then cons (Data.ByteString.Internal.BS (GHC.ForeignPtr.plusForeignPtr x n) (l
                                                                                             GHC.Num.-
                                                                                             n)) nil
                 else let i := GHC.Ptr.minusPtr q (GHC.ForeignPtr.unsafeForeignPtrToPtr x) in
                      cons (Data.ByteString.Internal.BS (GHC.ForeignPtr.plusForeignPtr x n) (i
                                                                                             GHC.Num.-
                                                                                             n)) (loop (i GHC.Num.+
                                                                                                        #1)) in
            loop #0
        end
    end.

Fixpoint group (xs : Data.ByteString.Internal.ByteString) : list
                                                            Data.ByteString.Internal.ByteString
  := match uncons xs with
     | None => nil
     | Some (pair h _) => let 'pair ys zs := spanByte h xs in cons ys (group zs)
     end.

Fixpoint groupBy (k : GHC.Word.Word8 -> GHC.Word.Word8 -> bool) (xs
                   : Data.ByteString.Internal.ByteString) : list
                                                            Data.ByteString.Internal.ByteString
  := match uncons xs with
     | None => nil
     | Some (pair h t) =>
         let n :=
           #1 GHC.Num.+
           Data.ByteString.Internal.findIndexOrLength (negb GHC.Base.∘ k h) t in
         cons (Data.ByteString.Unsafe.unsafeTake n xs) (groupBy k
               (Data.ByteString.Unsafe.unsafeDrop n xs))
     end.

Definition intercalate
   : Data.ByteString.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString :=
  fun s => concat GHC.Base.∘ Data.OldList.intersperse s.

Definition intercalateWithByte
   : GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | c
    , (Data.ByteString.Internal.BS ffp l as f)
    , (Data.ByteString.Internal.BS fgp m as g) =>
        let len := (length f GHC.Num.+ length g) GHC.Num.+ #1 in
        Data.ByteString.Internal.unsafeCreate len (fun ptr =>
                                                     Data.ByteString.Internal.unsafeWithForeignPtr ffp (fun fp =>
                                                                                                          Data.ByteString.Internal.unsafeWithForeignPtr
                                                                                                          fgp (fun gp =>
                                                                                                                 Data.ByteString.Internal.memcpy
                                                                                                                 ptr fp
                                                                                                                 (GHC.Real.fromIntegral
                                                                                                                  l)
                                                                                                                 GHC.Base.>>
                                                                                                                 (Foreign.Storable.poke
                                                                                                                  (GHC.Ptr.plusPtr
                                                                                                                   ptr
                                                                                                                   l) c
                                                                                                                  GHC.Base.>>
                                                                                                                  Data.ByteString.Internal.memcpy
                                                                                                                  (GHC.Ptr.plusPtr
                                                                                                                   ptr
                                                                                                                   (l
                                                                                                                    GHC.Num.+
                                                                                                                    #1))
                                                                                                                  gp
                                                                                                                  (GHC.Real.fromIntegral
                                                                                                                   m)))))
    end.

Definition index
   : Data.ByteString.Internal.ByteString -> GHC.Num.Int -> GHC.Word.Word8 :=
  fun ps n =>
    if n GHC.Base.< #0 : bool
    then moduleError (GHC.Base.hs_string__ "index") (Coq.Init.Datatypes.app
                                                     (GHC.Base.hs_string__ "negative index: ") (GHC.Show.show n)) else
    if n GHC.Base.>= length ps : bool
    then moduleError (GHC.Base.hs_string__ "index") (Coq.Init.Datatypes.app
                                                     (GHC.Base.hs_string__ "index too large: ") (Coq.Init.Datatypes.app
                                                      (GHC.Show.show n) (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                                                                 ", length = ")
                                                                                                (GHC.Show.show (length
                                                                                                                ps))))) else
    Data.ByteString.Unsafe.unsafeIndex ps n.

Definition indexMaybe
   : Data.ByteString.Internal.ByteString ->
     GHC.Num.Int -> option GHC.Word.Word8 :=
  fun ps n =>
    if n GHC.Base.< #0 : bool then None else
    if n GHC.Base.>= length ps : bool then None else
    Some (Data.ByteString.Unsafe.unsafeIndex ps n).

Definition op_znz3fU__
   : Data.ByteString.Internal.ByteString ->
     GHC.Num.Int -> option GHC.Word.Word8 :=
  indexMaybe.

Notation "'_!?_'" := (op_znz3fU__).

Infix "!?" := (_!?_) (at level 99).

Definition findIndexEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString -> option GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, Data.ByteString.Internal.BS x l =>
        let g :=
          fun ptr =>
            let fix go n
              := if n GHC.Base.< #0 : bool then GHC.Base.return_ None else
                 Foreign.Storable.peekByteOff ptr n GHC.Base.>>=
                 (fun w =>
                    if k w : bool
                    then GHC.Base.return_ (Some n)
                    else go (n GHC.Num.- #1)) in
            go (l GHC.Num.- #1) in
        Data.ByteString.Internal.accursedUnutterablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr x g)
    end.

Definition elemIndexEnd
   : GHC.Word.Word8 ->
     Data.ByteString.Internal.ByteString -> option GHC.Num.Int :=
  findIndexEnd GHC.Base.∘ _GHC.Base.==_.

Definition elemIndices
   : GHC.Word.Word8 -> Data.ByteString.Internal.ByteString -> list GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | w, Data.ByteString.Internal.BS x l =>
        let fix loop n
          := Data.ByteString.Internal.accursedUnutterablePerformIO
             (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                               Data.ByteString.Internal.memchr (GHC.Ptr.plusPtr p n) w
                                                               (GHC.Real.fromIntegral (l GHC.Num.- n)) GHC.Base.>>=
                                                               (fun q =>
                                                                  if q GHC.Base.== GHC.Ptr.nullPtr : bool
                                                                  then GHC.Base.return_ nil
                                                                  else let i := GHC.Ptr.minusPtr q p in
                                                                       GHC.Base.return_ (cons i (loop (i GHC.Num.+
                                                                                                       #1)))))) in
        loop #0
    end.

Definition count
   : GHC.Word.Word8 -> Data.ByteString.Internal.ByteString -> GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | w, Data.ByteString.Internal.BS x m =>
        Data.ByteString.Internal.accursedUnutterablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                          GHC.Real.fromIntegral Data.Functor.<$>
                                                          Data.ByteString.Internal.c_count p (GHC.Real.fromIntegral m)
                                                          w))
    end.

Definition findIndex
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString -> option GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, Data.ByteString.Internal.BS x l =>
        let g :=
          fun ptr =>
            let fix go n
              := if n GHC.Base.>= l : bool then GHC.Base.return_ None else
                 Foreign.Storable.peek (GHC.Ptr.plusPtr ptr n) GHC.Base.>>=
                 (fun w =>
                    if k w : bool
                    then GHC.Base.return_ (Some n)
                    else go (n GHC.Num.+ #1)) in
            go #0 in
        Data.ByteString.Internal.accursedUnutterablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr x g)
    end.

Definition findIndices
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString -> list GHC.Num.Int :=
  fun p =>
    let fix loop n qs
      := match findIndex p qs with
         | Some i =>
             let j := n GHC.Num.+ i in
             cons j (loop (j GHC.Num.+ #1) (Data.ByteString.Unsafe.unsafeDrop (i GHC.Num.+
                                                                               #1) qs))
         | None => nil
         end in
    loop #0.

Definition elem
   : GHC.Word.Word8 -> Data.ByteString.Internal.ByteString -> bool :=
  fun c ps => match elemIndex c ps with | None => false | _ => true end.

Definition notElem
   : GHC.Word.Word8 -> Data.ByteString.Internal.ByteString -> bool :=
  fun c ps => negb (elem c ps).

Definition filter
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun k =>
    fun '((Data.ByteString.Internal.BS x l as ps)) =>
      if null ps : bool
      then ps
      else GHC.IO.Unsafe.unsafePerformIO (Data.ByteString.Internal.createAndTrim l
                                                                                 (fun pOut =>
                                                                                    Data.ByteString.Internal.unsafeWithForeignPtr
                                                                                    x (fun pIn =>
                                                                                         let go' :=
                                                                                           fun pf pt =>
                                                                                             let end :=
                                                                                               GHC.Ptr.plusPtr pf l in
                                                                                             let fix go f t
                                                                                               := if f GHC.Base.==
                                                                                                     end : bool
                                                                                                  then GHC.Base.return_
                                                                                                       t else
                                                                                                  Foreign.Storable.peek
                                                                                                  f GHC.Base.>>=
                                                                                                  (fun w =>
                                                                                                     if k w : bool
                                                                                                     then Foreign.Storable.poke
                                                                                                          t w
                                                                                                          GHC.Base.>>
                                                                                                          go
                                                                                                          (GHC.Ptr.plusPtr
                                                                                                           f #1)
                                                                                                          (GHC.Ptr.plusPtr
                                                                                                           t #1)
                                                                                                     else go
                                                                                                          (GHC.Ptr.plusPtr
                                                                                                           f #1) t) in
                                                                                             go pf pt in
                                                                                         go' pIn pOut GHC.Base.>>=
                                                                                         (fun t =>
                                                                                            GHC.Base.return_
                                                                                            (GHC.Ptr.minusPtr t
                                                                                                              pOut))))).

Definition find
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString -> option GHC.Word.Word8 :=
  fun f p =>
    match findIndex f p with
    | Some n => Some (Data.ByteString.Unsafe.unsafeIndex p n)
    | _ => None
    end.

Definition partition
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun f s =>
    let decr := (fun arg_0__ => GHC.Ptr.plusPtr arg_0__ (GHC.Num.negate #1)) in
    let incr := (fun arg_2__ => GHC.Ptr.plusPtr arg_2__ #1) in
    let fix rev p1 p2
      := if p1 GHC.Base.>= p2 : bool then GHC.Base.return_ tt else
         Foreign.Storable.peek p1 GHC.Base.>>=
         (fun a =>
            Foreign.Storable.peek p2 GHC.Base.>>=
            (fun b =>
               Foreign.Storable.poke p1 b GHC.Base.>>
               (Foreign.Storable.poke p2 a GHC.Base.>> rev (incr p1) (decr p2)))) in
    let len := length s in
    let fix sep i p1 p2
      := let w := Data.ByteString.Unsafe.unsafeIndex s i in
         if i GHC.Base.== len : bool then GHC.Base.return_ p1 else
         if f w : bool
         then Foreign.Storable.poke p1 w GHC.Base.>>
              sep (i GHC.Num.+ #1) (incr p1) p2 else
         Foreign.Storable.poke p2 w GHC.Base.>> sep (i GHC.Num.+ #1) p1 (decr p2) in
    GHC.IO.Unsafe.unsafeDupablePerformIO (Data.ByteString.Internal.mallocByteString
                                          len GHC.Base.>>=
                                          (fun fp' =>
                                             Data.ByteString.Internal.unsafeWithForeignPtr fp' (fun p =>
                                                                                                  let end :=
                                                                                                    GHC.Ptr.plusPtr p
                                                                                                                    (len
                                                                                                                     GHC.Num.-
                                                                                                                     #1) in
                                                                                                  sep #0 p end
                                                                                                  GHC.Base.>>=
                                                                                                  (fun mid =>
                                                                                                     rev mid end
                                                                                                     GHC.Base.>>
                                                                                                     (let i :=
                                                                                                        GHC.Ptr.minusPtr
                                                                                                        mid p in
                                                                                                      GHC.Base.return_
                                                                                                      (pair
                                                                                                       (Data.ByteString.Internal.BS
                                                                                                        fp' i)
                                                                                                       (Data.ByteString.Internal.BS
                                                                                                        (GHC.ForeignPtr.plusForeignPtr
                                                                                                         fp' i) (len
                                                                                                                 GHC.Num.-
                                                                                                                 i)))))))).

Definition isPrefixOf
   : Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.ByteString.Internal.BS x1 l1, Data.ByteString.Internal.BS x2 l2 =>
        if l1 GHC.Base.== #0 : bool then true else
        if l2 GHC.Base.< l1 : bool then false else
        Data.ByteString.Internal.accursedUnutterablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr x1 (fun p1 =>
                                                          Data.ByteString.Internal.unsafeWithForeignPtr x2 (fun p2 =>
                                                                                                              Data.ByteString.Internal.memcmp
                                                                                                              p1 p2
                                                                                                              (GHC.Real.fromIntegral
                                                                                                               l1)
                                                                                                              GHC.Base.>>=
                                                                                                              (fun i =>
                                                                                                                 GHC.Base.return_
                                                                                                                 (i
                                                                                                                  GHC.Base.==
                                                                                                                  #0)))))
    end.

Definition stripPrefix
   : Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString ->
     option Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Data.ByteString.Internal.BS _ l1 as bs1), bs2 =>
        if isPrefixOf bs1 bs2 : bool
        then Some (Data.ByteString.Unsafe.unsafeDrop l1 bs2) else
        None
    end.

Definition isSuffixOf
   : Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.ByteString.Internal.BS x1 l1, Data.ByteString.Internal.BS x2 l2 =>
        if l1 GHC.Base.== #0 : bool then true else
        if l2 GHC.Base.< l1 : bool then false else
        Data.ByteString.Internal.accursedUnutterablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr x1 (fun p1 =>
                                                          Data.ByteString.Internal.unsafeWithForeignPtr x2 (fun p2 =>
                                                                                                              Data.ByteString.Internal.memcmp
                                                                                                              p1
                                                                                                              (GHC.Ptr.plusPtr
                                                                                                               p2 (l2
                                                                                                                GHC.Num.-
                                                                                                                l1))
                                                                                                              (GHC.Real.fromIntegral
                                                                                                               l1)
                                                                                                              GHC.Base.>>=
                                                                                                              (fun i =>
                                                                                                                 GHC.Base.return_
                                                                                                                 (i
                                                                                                                  GHC.Base.==
                                                                                                                  #0)))))
    end.

Definition stripSuffix
   : Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString ->
     option Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Data.ByteString.Internal.BS _ l1 as bs1)
    , (Data.ByteString.Internal.BS _ l2 as bs2) =>
        if isSuffixOf bs1 bs2 : bool
        then Some (Data.ByteString.Unsafe.unsafeTake (l2 GHC.Num.- l1) bs2) else
        None
    end.

Definition breakSubstring
   : Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun pat =>
    let lp := length pat in
    let unsafeSplitAt :=
      fun i s =>
        pair (Data.ByteString.Unsafe.unsafeTake i s) (Data.ByteString.Unsafe.unsafeDrop
              i s) in
    let karpRabin
     : Data.ByteString.Internal.ByteString ->
       (Data.ByteString.Internal.ByteString *
        Data.ByteString.Internal.ByteString)%type :=
      fun src =>
        let get :=
          GHC.Real.fromIntegral GHC.Base.∘ Data.ByteString.Unsafe.unsafeIndex src in
        let k := #2891336453 : GHC.Word.Word32 in
        let rollingHash :=
          foldl' (fun h b => (h GHC.Num.* k) GHC.Num.+ GHC.Real.fromIntegral b) #0 in
        let hp := rollingHash pat in
        let m := k GHC.Real.^ lp in
        let fix search hs i
          := let hs' :=
               ((hs GHC.Num.* k) GHC.Num.+ get i) GHC.Num.-
               (m GHC.Num.* get (i GHC.Num.- lp)) in
             let '(pair _ b as u) := unsafeSplitAt (i GHC.Num.- lp) src in
             if andb (hp GHC.Base.== hs) (pat GHC.Base.==
                      Data.ByteString.Unsafe.unsafeTake lp b) : bool
             then u else
             if length src GHC.Base.<= i : bool then pair src empty else
             search hs' (i GHC.Num.+ #1) in
        if length src GHC.Base.< lp : bool then pair src empty else
        search (rollingHash (Data.ByteString.Unsafe.unsafeTake lp src)) lp in
    let shift
     : Data.ByteString.Internal.ByteString ->
       (Data.ByteString.Internal.ByteString *
        Data.ByteString.Internal.ByteString)%type :=
      fun src =>
        let mask := (Data.Bits.shiftL #1 (#8 GHC.Num.* lp)) GHC.Num.- #1 in
        let intoWord : Data.ByteString.Internal.ByteString -> GHC.Num.Word :=
          foldl' (fun w b =>
                    (Data.Bits.shiftL w #8) Data.Bits..|.(**) GHC.Real.fromIntegral b) #0 in
        let wp := intoWord pat in
        let fix search w i
          := let b := GHC.Real.fromIntegral (Data.ByteString.Unsafe.unsafeIndex src i) in
             let w' :=
               mask Data.Bits..&.(**) ((Data.Bits.shiftL w #8) Data.Bits..|.(**) b) in
             if w GHC.Base.== wp : bool then unsafeSplitAt (i GHC.Num.- lp) src else
             if length src GHC.Base.<= i : bool then pair src empty else
             search w' (i GHC.Num.+ #1) in
        if length src GHC.Base.< lp : bool then pair src empty else
        search (intoWord (Data.ByteString.Unsafe.unsafeTake lp src)) lp in
    let 'num_26__ := lp in
    if num_26__ GHC.Base.== #0 : bool then fun arg_32__ => pair empty arg_32__ else
    let 'num_27__ := lp in
    if num_27__ GHC.Base.== #1 : bool
    then breakByte (Data.ByteString.Unsafe.unsafeHead pat) else
    if (lp GHC.Num.* #8) GHC.Base.<=
       Data.Bits.finiteBitSize (#0 : GHC.Num.Word) : bool
    then shift
    else karpRabin.

Definition isInfixOf
   : Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString -> bool :=
  fun p s => orb (null p) (negb (null (Data.Tuple.snd (breakSubstring p s)))).

Fixpoint zip (ps qs : Data.ByteString.Internal.ByteString) : list
                                                             (GHC.Word.Word8 * GHC.Word.Word8)%type
  := match uncons ps with
     | None => nil
     | Some (pair psH psT) =>
         match uncons qs with
         | None => nil
         | Some (pair qsH qsT) => cons (pair psH qsH) (zip psT qsT)
         end
     end.

Fixpoint zipWith {a : Type} (f : GHC.Word.Word8 -> GHC.Word.Word8 -> a) (ps qs
                   : Data.ByteString.Internal.ByteString) : list a
  := match uncons ps with
     | None => nil
     | Some (pair psH psT) =>
         match uncons qs with
         | None => nil
         | Some (pair qsH qsT) => cons (f psH qsH) (zipWith f psT qsT)
         end
     end.

Definition packZipWith
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, Data.ByteString.Internal.BS fp l, Data.ByteString.Internal.BS fq m =>
        let len := GHC.Base.min l m in
        let go :=
          fun p1 p2 =>
            let zipWith_ : GHC.Num.Int -> GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Types.IO unit :=
              fix zipWith_ (n : GHC.Num.Int) (r : GHC.Ptr.Ptr GHC.Word.Word8) : GHC.Types.IO
                                                                                unit
                := if n GHC.Base.>= len : bool then GHC.Base.return_ tt else
                   Foreign.Storable.peekByteOff p1 n GHC.Base.>>=
                   (fun x =>
                      Foreign.Storable.peekByteOff p2 n GHC.Base.>>=
                      (fun y =>
                         Foreign.Storable.pokeByteOff r n (f x y) GHC.Base.>>
                         zipWith_ (n GHC.Num.+ #1) r)) in
            zipWith_ #0 in
        GHC.IO.Unsafe.unsafeDupablePerformIO
        (Data.ByteString.Internal.unsafeWithForeignPtr fp (fun a =>
                                                          Data.ByteString.Internal.unsafeWithForeignPtr fq (fun b =>
                                                                                                              Data.ByteString.Internal.create
                                                                                                              len (go a
                                                                                                                      b))))
    end.

Definition unzip
   : list (GHC.Word.Word8 * GHC.Word.Word8)%type ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun ls =>
    pair (pack (GHC.Base.map Data.Tuple.fst ls)) (pack (GHC.Base.map Data.Tuple.snd
                                                        ls)).

Definition inits
   : Data.ByteString.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString :=
  fun '(Data.ByteString.Internal.BS x l) =>
    Coq.Lists.List.flat_map (fun n => cons (Data.ByteString.Internal.BS x n) nil)
                            (GHC.Enum.enumFromTo #0 l).

Fixpoint tails (p : Data.ByteString.Internal.ByteString) : list
                                                           Data.ByteString.Internal.ByteString
  := if null p : bool then cons empty nil else
     cons p (tails (Data.ByteString.Unsafe.unsafeTail p)).

Definition sort
   : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun '(Data.ByteString.Internal.BS input l) =>
    let countOccurrences
     : GHC.Ptr.Ptr Foreign.C.Types.CSize ->
       GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Num.Int -> GHC.Types.IO unit :=
      fun counts str len =>
        let fix go i
          := if i GHC.Base.== len : bool then GHC.Base.return_ tt else
             GHC.Base.fmap GHC.Real.fromIntegral (Foreign.Storable.peekElemOff str i)
             GHC.Base.>>=
             (fun k =>
                Foreign.Storable.peekElemOff counts k GHC.Base.>>=
                (fun x =>
                   Foreign.Storable.pokeElemOff counts k (x GHC.Num.+ #1) GHC.Base.>>
                   go (i GHC.Num.+ #1))) in
        go #0 in
    if l GHC.Base.<= #20 : bool
    then Data.ByteString.Internal.unsafeCreate l (fun ptr =>
                                                    Data.ByteString.Internal.unsafeWithForeignPtr input (fun inp =>
                                                                                                           Data.ByteString.Internal.memcpy
                                                                                                           ptr inp
                                                                                                           (GHC.Real.fromIntegral
                                                                                                            l)
                                                                                                           GHC.Base.>>
                                                                                                           Data.ByteString.Internal.c_sort
                                                                                                           ptr
                                                                                                           (GHC.Real.fromIntegral
                                                                                                            l))) else
    Data.ByteString.Internal.unsafeCreate l (fun p =>
                                               Foreign.Marshal.Array.allocaArray #256 (fun arr =>
                                                                                         Data.ByteString.Internal.memset
                                                                                         (GHC.Ptr.castPtr arr) #0 (#256
                                                                                                                   GHC.Num.*
                                                                                                                   GHC.Real.fromIntegral
                                                                                                                   (Foreign.Storable.sizeOf
                                                                                                                    (GHC.Err.undefined : Foreign.C.Types.CSize)))
                                                                                         GHC.Base.>>=
                                                                                         (fun _ =>
                                                                                            Data.ByteString.Internal.unsafeWithForeignPtr
                                                                                            input (fun x =>
                                                                                                     countOccurrences
                                                                                                     arr x l)
                                                                                            GHC.Base.>>
                                                                                            (let fix go arg_7__ arg_8__
                                                                                               := match arg_7__
                                                                                                      , arg_8__ with
                                                                                                  | num_9__, _ =>
                                                                                                      if num_9__
                                                                                                         GHC.Base.==
                                                                                                         #256 : bool
                                                                                                      then GHC.Base.return_
                                                                                                           tt else
                                                                                                      match arg_7__
                                                                                                          , arg_8__ with
                                                                                                      | i, ptr =>
                                                                                                          Foreign.Storable.peekElemOff
                                                                                                          arr i
                                                                                                          GHC.Base.>>=
                                                                                                          (fun n =>
                                                                                                             GHC.Base.when
                                                                                                             (n
                                                                                                              GHC.Base./=
                                                                                                              #0)
                                                                                                             (Data.Functor.void
                                                                                                              (Data.ByteString.Internal.memset
                                                                                                               ptr
                                                                                                               (GHC.Real.fromIntegral
                                                                                                                i) n))
                                                                                                             GHC.Base.>>
                                                                                                             go (i
                                                                                                                 GHC.Num.+
                                                                                                                 #1)
                                                                                                             (GHC.Ptr.plusPtr
                                                                                                              ptr
                                                                                                              (GHC.Real.fromIntegral
                                                                                                               n)))
                                                                                                      end
                                                                                                  end in
                                                                                             go #0 p)))).

Definition moduleErrorIO {a}
   : GHC.Base.String -> GHC.Base.String -> GHC.Types.IO a :=
  fun fun_ msg =>
    (GHC.IO.throwIO GHC.Base.∘ GHC.IO.Exception.userError) (moduleErrorMsg fun_
                                                                           msg).

Definition packCStringLen
   : Foreign.C.String.CStringLen ->
     GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun arg_0__ =>
    let 'pair cstr len := arg_0__ in
    if len GHC.Base.>= #0 : bool
    then Data.ByteString.Internal.create len (fun p =>
                                                Data.ByteString.Internal.memcpy p (GHC.Ptr.castPtr cstr)
                                                (GHC.Real.fromIntegral len)) else
    let 'pair _ len := arg_0__ in
    moduleErrorIO (GHC.Base.hs_string__ "packCStringLen") (Coq.Init.Datatypes.app
                                                           (GHC.Base.hs_string__ "negative length: ") (GHC.Show.show
                                                            len)).

Definition packCString
   : Foreign.C.String.CString ->
     GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun cstr =>
    Data.ByteString.Internal.c_strlen cstr GHC.Base.>>=
    (fun len => packCStringLen (pair cstr (GHC.Real.fromIntegral len))).

Definition copy
   : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun '(Data.ByteString.Internal.BS x l) =>
    Data.ByteString.Internal.unsafeCreate l (fun p =>
                                               Data.ByteString.Internal.unsafeWithForeignPtr x (fun f =>
                                                                                                  Data.ByteString.Internal.memcpy
                                                                                                  p f
                                                                                                  (GHC.Real.fromIntegral
                                                                                                   l))).

Axiom hGetLine : forall {A : Type}, A.

Definition getLine : GHC.Types.IO Data.ByteString.Internal.ByteString :=
  hGetLine GHC.IO.Handle.FD.stdin.

(* Translating `hGetLine' failed: using a record pattern for the unknown
   constructor `Handle__' unsupported [in definition Data.ByteString.hGetLine in
   module Data.ByteString] *)

Definition mkPS
   : GHC.IO.Buffer.RawBuffer GHC.Word.Word8 ->
     GHC.Num.Int ->
     GHC.Num.Int -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun buf start end =>
    let len := end GHC.Num.- start in
    Data.ByteString.Internal.create len (fun p =>
                                           GHC.IO.Buffer.withRawBuffer buf (fun pbuf =>
                                                                              Foreign.Marshal.Utils.copyBytes p
                                                                              (GHC.Ptr.plusPtr pbuf start) len)).

Definition mkBigPS
   : GHC.Num.Int ->
     list Data.ByteString.Internal.ByteString ->
     GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, cons ps nil => GHC.Base.return_ ps
    | _, pss => GHC.Base.return_ (concat (GHC.List.reverse pss))
    end.

Definition hPut
   : GHC.IO.Handle.Types.Handle ->
     Data.ByteString.Internal.ByteString -> GHC.Types.IO unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Internal.BS _ num_2__ =>
        if num_2__ GHC.Base.== #0 : bool then GHC.Base.return_ tt else
        match arg_0__, arg_1__ with
        | h, Data.ByteString.Internal.BS ps l =>
            Data.ByteString.Internal.unsafeWithForeignPtr ps (fun p =>
                                                                GHC.IO.Handle.Text.hPutBuf h p l)
        end
    end.

Definition hPutNonBlocking
   : GHC.IO.Handle.Types.Handle ->
     Data.ByteString.Internal.ByteString ->
     GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | h, (Data.ByteString.Internal.BS ps l as bs) =>
        Data.ByteString.Internal.unsafeWithForeignPtr ps (fun p =>
                                                            GHC.IO.Handle.Text.hPutBufNonBlocking h p l) GHC.Base.>>=
        (fun bytesWritten => GHC.Base.return_ (drop bytesWritten bs))
    end.

Definition hPutStr
   : GHC.IO.Handle.Types.Handle ->
     Data.ByteString.Internal.ByteString -> GHC.Types.IO unit :=
  hPut.

Definition putStr : Data.ByteString.Internal.ByteString -> GHC.Types.IO unit :=
  hPut GHC.IO.Handle.FD.stdout.

Definition illegalBufferSize {a}
   : GHC.IO.Handle.Types.Handle ->
     GHC.Base.String -> GHC.Num.Int -> GHC.Types.IO a :=
  fun handle fn sz =>
    let msg :=
      Coq.Init.Datatypes.app fn (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                         ": illegal ByteString size ") (GHC.Show.showsPrec #9 sz
                                                         nil)) in
    GHC.IO.Exception.ioError (System.IO.Error.mkIOError
                              System.IO.Error.illegalOperationErrorType msg (Some handle) None).

Definition hGet
   : GHC.IO.Handle.Types.Handle ->
     GHC.Num.Int -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun h i =>
    if i GHC.Base.> #0 : bool
    then Data.ByteString.Internal.createAndTrim i (fun p =>
                                                     GHC.IO.Handle.Text.hGetBuf h p i) else
    if i GHC.Base.== #0 : bool then GHC.Base.return_ empty else
    illegalBufferSize h (GHC.Base.hs_string__ "hGet") i.

Definition hGetNonBlocking
   : GHC.IO.Handle.Types.Handle ->
     GHC.Num.Int -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun h i =>
    if i GHC.Base.> #0 : bool
    then Data.ByteString.Internal.createAndTrim i (fun p =>
                                                     GHC.IO.Handle.Text.hGetBufNonBlocking h p i) else
    if i GHC.Base.== #0 : bool then GHC.Base.return_ empty else
    illegalBufferSize h (GHC.Base.hs_string__ "hGetNonBlocking") i.

Definition hGetSome
   : GHC.IO.Handle.Types.Handle ->
     GHC.Num.Int -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun hh i =>
    if i GHC.Base.> #0 : bool
    then Data.ByteString.Internal.createAndTrim i (fun p =>
                                                     GHC.IO.Handle.Text.hGetBufSome hh p i) else
    if i GHC.Base.== #0 : bool then GHC.Base.return_ empty else
    illegalBufferSize hh (GHC.Base.hs_string__ "hGetSome") i.

Definition hGetContentsSizeHint
   : GHC.IO.Handle.Types.Handle ->
     GHC.Num.Int ->
     GHC.Num.Int -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun hnd =>
    let fix readChunks chunks sz sz'
      := Data.ByteString.Internal.mallocByteString sz GHC.Base.>>=
         (fun fp =>
            Data.ByteString.Internal.unsafeWithForeignPtr fp (fun buf =>
                                                                GHC.IO.Handle.Text.hGetBuf hnd buf sz) GHC.Base.>>=
            (fun readcount =>
               let chunk := Data.ByteString.Internal.BS fp readcount in
               if andb (readcount GHC.Base.< sz) (sz GHC.Base.> #0) : bool
               then GHC.Base.return_ (concat (GHC.List.reverse (cons chunk chunks)))
               else readChunks (cons chunk chunks) sz' (GHC.Base.min (sz GHC.Num.+ sz')
                                                                     #32752))) in
    readChunks nil.

Definition hGetContents
   : GHC.IO.Handle.Types.Handle ->
     GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun hnd =>
    Control.Exception.Base.finally (hGetContentsSizeHint hnd #1024 #2048)
                                   (GHC.IO.Handle.hClose hnd) GHC.Base.>>=
    (fun bs =>
       if length bs GHC.Base.< #900 : bool
       then GHC.Base.return_ (copy bs)
       else GHC.Base.return_ bs).

Definition getContents : GHC.Types.IO Data.ByteString.Internal.ByteString :=
  hGetContents GHC.IO.Handle.FD.stdin.

Definition interact
   : (Data.ByteString.Internal.ByteString ->
      Data.ByteString.Internal.ByteString) ->
     GHC.Types.IO unit :=
  fun transformer => (putStr GHC.Base.∘ transformer) GHC.Base.=<< getContents.

Definition readFile
   : GHC.Base.String -> GHC.Types.IO Data.ByteString.Internal.ByteString :=
  fun f =>
    let useZeroIfNotRegularFile
     : GHC.IO.Exception.IOException -> GHC.Types.IO GHC.Integer.Type.Integer :=
      fun arg_0__ => GHC.Base.return_ #0 in
    System.IO.withBinaryFile f GHC.IO.IOMode.ReadMode (fun h =>
                                                         GHC.IO.catch (GHC.IO.Handle.hFileSize h)
                                                         useZeroIfNotRegularFile GHC.Base.>>=
                                                         (fun filesz =>
                                                            let readsz :=
                                                              (GHC.Base.max (GHC.Real.fromIntegral filesz) #0) GHC.Num.+
                                                              #1 in
                                                            hGetContentsSizeHint h readsz (GHC.Base.max readsz #255))).

Definition modifyFile
   : GHC.IO.IOMode.IOMode ->
     GHC.Base.String -> Data.ByteString.Internal.ByteString -> GHC.Types.IO unit :=
  fun mode f txt =>
    System.IO.withBinaryFile f mode (fun arg_0__ => hPut arg_0__ txt).

Definition writeFile
   : GHC.Base.String ->
     Data.ByteString.Internal.ByteString -> GHC.Types.IO unit :=
  modifyFile GHC.IO.IOMode.WriteMode.

Definition appendFile
   : GHC.Base.String ->
     Data.ByteString.Internal.ByteString -> GHC.Types.IO unit :=
  modifyFile GHC.IO.IOMode.AppendMode.

Module Notations.
Notation "'_Data.ByteString.!?_'" := (op_znz3fU__).
Infix "Data.ByteString.!?" := (_!?_) (at level 99).
End Notations.

(* External variables:
     None Some Type andb bool cons false list negb nil op_zt__ option orb pair true
     tt unit Control.Exception.Base.finally Coq.Init.Datatypes.app
     Coq.Lists.List.flat_map Data.Bits.finiteBitSize Data.Bits.op_zizazi__
     Data.Bits.op_zizbzi__ Data.Bits.shiftL Data.ByteString.Internal.BS
     Data.ByteString.Internal.ByteString
     Data.ByteString.Internal.accursedUnutterablePerformIO
     Data.ByteString.Internal.c_count Data.ByteString.Internal.c_intersperse
     Data.ByteString.Internal.c_maximum Data.ByteString.Internal.c_minimum
     Data.ByteString.Internal.c_reverse Data.ByteString.Internal.c_sort
     Data.ByteString.Internal.c_strlen Data.ByteString.Internal.create
     Data.ByteString.Internal.createAndTrim Data.ByteString.Internal.createAndTrim'
     Data.ByteString.Internal.findIndexOrLength
     Data.ByteString.Internal.mallocByteString Data.ByteString.Internal.memchr
     Data.ByteString.Internal.memcmp Data.ByteString.Internal.memcpy
     Data.ByteString.Internal.memset Data.ByteString.Internal.nullForeignPtr
     Data.ByteString.Internal.packBytes Data.ByteString.Internal.unsafeCreate
     Data.ByteString.Internal.unsafeWithForeignPtr Data.ByteString.Unsafe.unsafeDrop
     Data.ByteString.Unsafe.unsafeHead Data.ByteString.Unsafe.unsafeIndex
     Data.ByteString.Unsafe.unsafePackMallocCStringLen
     Data.ByteString.Unsafe.unsafeTail Data.ByteString.Unsafe.unsafeTake
     Data.Functor.op_zlzdzg__ Data.Functor.void Data.OldList.intersperse
     Data.OldList.transpose Data.Tuple.fst Data.Tuple.snd Foreign.C.String.CString
     Foreign.C.String.CStringLen Foreign.C.Types.CSize
     Foreign.ForeignPtr.Imp.withForeignPtr Foreign.Marshal.Alloc.allocaBytes
     Foreign.Marshal.Array.allocaArray Foreign.Marshal.Utils.copyBytes
     Foreign.Storable.peek Foreign.Storable.peekByteOff Foreign.Storable.peekElemOff
     Foreign.Storable.poke Foreign.Storable.pokeByteOff Foreign.Storable.pokeElemOff
     Foreign.Storable.sizeOf GHC.Base.String GHC.Base.assert GHC.Base.build'
     GHC.Base.fmap GHC.Base.map GHC.Base.mappend GHC.Base.max GHC.Base.mconcat
     GHC.Base.min GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zezlzl__
     GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Base.return_
     GHC.Base.when GHC.Enum.enumFromTo GHC.Err.error GHC.Err.undefined
     GHC.Foreign.newCStringLen GHC.Foreign.peekCStringLen GHC.ForeignPtr.ForeignPtr
     GHC.ForeignPtr.plusForeignPtr GHC.ForeignPtr.touchForeignPtr
     GHC.ForeignPtr.unsafeForeignPtrToPtr GHC.IO.catch GHC.IO.throwIO
     GHC.IO.Buffer.RawBuffer GHC.IO.Buffer.withRawBuffer
     GHC.IO.Encoding.getFileSystemEncoding GHC.IO.Exception.IOException
     GHC.IO.Exception.ioError GHC.IO.Exception.userError GHC.IO.Handle.hClose
     GHC.IO.Handle.hFileSize GHC.IO.Handle.FD.stdin GHC.IO.Handle.FD.stdout
     GHC.IO.Handle.Text.hGetBuf GHC.IO.Handle.Text.hGetBufNonBlocking
     GHC.IO.Handle.Text.hGetBufSome GHC.IO.Handle.Text.hPutBuf
     GHC.IO.Handle.Text.hPutBufNonBlocking GHC.IO.Handle.Types.Handle
     GHC.IO.IOMode.AppendMode GHC.IO.IOMode.IOMode GHC.IO.IOMode.ReadMode
     GHC.IO.IOMode.WriteMode GHC.IO.Unsafe.unsafeDupablePerformIO
     GHC.IO.Unsafe.unsafePerformIO GHC.Integer.Type.Integer GHC.List.reverse
     GHC.Num.Int GHC.Num.Word GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Ptr.Ptr GHC.Ptr.castPtr GHC.Ptr.minusPtr
     GHC.Ptr.nullPtr GHC.Ptr.plusPtr GHC.Real.fromIntegral GHC.Real.op_zc__
     GHC.Show.show GHC.Show.showsPrec GHC.Types.IO GHC.Word.Word32 GHC.Word.Word8
     System.IO.withBinaryFile System.IO.Error.illegalOperationErrorType
     System.IO.Error.mkIOError
*)
