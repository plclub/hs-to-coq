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
Require Data.Bifunctor.
Require Data.ByteString.
Require Data.ByteString.Internal.
Require Data.ByteString.Lazy.Internal.
Require Data.ByteString.Lazy.Internal.Deque.
Require Data.ByteString.Unsafe.
Require Data.Foldable.
Require Data.Functor.
Require Data.OldList.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Require GHC.Tuple.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition empty : Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.Internal.Empty.

Definition singleton
   : GHC.Word.Word8 -> Data.ByteString.Lazy.Internal.ByteString :=
  fun w =>
    Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.singleton w)
    Data.ByteString.Lazy.Internal.Empty.

Definition pack
   : list GHC.Word.Word8 -> Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.Internal.packBytes.

Definition unpack
   : Data.ByteString.Lazy.Internal.ByteString -> list GHC.Word.Word8 :=
  Data.ByteString.Lazy.Internal.unpackBytes.

Definition fromChunks
   : list Data.ByteString.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  Data.Foldable.foldr Data.ByteString.Lazy.Internal.chunk
  Data.ByteString.Lazy.Internal.Empty.

Definition toChunks
   : Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString :=
  Data.ByteString.Lazy.Internal.foldrChunks cons nil.

Definition null : Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty => true
    | _ => false
    end.

Definition length : Data.ByteString.Lazy.Internal.ByteString -> GHC.Int.Int64 :=
  Data.ByteString.Lazy.Internal.foldlChunks (fun n c =>
                                               n GHC.Num.+ GHC.Real.fromIntegral (Data.ByteString.length c)) #0.

Definition cons_
   : GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun c => Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.singleton c).

Definition cons'
   : GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    let j_3__ :=
      match arg_0__, arg_1__ with
      | w, cs => Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.singleton w) cs
      end in
    match arg_0__, arg_1__ with
    | w, Data.ByteString.Lazy.Internal.Chunk c cs =>
        if Data.ByteString.length c GHC.Base.< #16 : bool
        then Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.cons_ w c) cs else
        j_3__
    | _, _ => j_3__
    end.

Definition snoc
   : Data.ByteString.Lazy.Internal.ByteString ->
     GHC.Word.Word8 -> Data.ByteString.Lazy.Internal.ByteString :=
  fun cs w =>
    Data.ByteString.Lazy.Internal.foldrChunks Data.ByteString.Lazy.Internal.Chunk
    (singleton w) cs.

Definition moduleError {a} : GHC.Base.String -> GHC.Base.String -> a :=
  fun fun_ msg =>
    GHC.Err.error (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                           "Data.ByteString.Lazy.") (Coq.Init.Datatypes.app fun_ (cons
                                                                                             (GHC.Char.hs_char__ ":")
                                                                                             (cons (GHC.Char.hs_char__
                                                                                                    " ") msg)))).

Definition errorEmptyList {a} : GHC.Base.String -> a :=
  fun fun_ => moduleError fun_ (GHC.Base.hs_string__ "empty ByteString").

Definition head : Data.ByteString.Lazy.Internal.ByteString -> GHC.Word.Word8 :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "head")
    | Data.ByteString.Lazy.Internal.Chunk c _ => Data.ByteString.Unsafe.unsafeHead c
    end.

Definition uncons
   : Data.ByteString.Lazy.Internal.ByteString ->
     option (GHC.Word.Word8 * Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty => None
    | Data.ByteString.Lazy.Internal.Chunk c cs =>
        Some (pair (Data.ByteString.Unsafe.unsafeHead c) (if Data.ByteString.length c
                                                             GHC.Base.==
                                                             #1 : bool
                    then cs
                    else Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeTail c)
                         cs))
    end.

Definition tail
   : Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "tail")
    | Data.ByteString.Lazy.Internal.Chunk c cs =>
        if Data.ByteString.length c GHC.Base.== #1 : bool then cs else
        Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeTail c) cs
    end.

Definition last : Data.ByteString.Lazy.Internal.ByteString -> GHC.Word.Word8 :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "last")
    | Data.ByteString.Lazy.Internal.Chunk c0 cs0 =>
        let fix go arg_2__ arg_3__
          := match arg_2__, arg_3__ with
             | c, Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Unsafe.unsafeLast c
             | _, Data.ByteString.Lazy.Internal.Chunk c cs => go c cs
             end in
        go c0 cs0
    end.

Definition init
   : Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "init")
    | Data.ByteString.Lazy.Internal.Chunk c0 cs0 =>
        let fix go arg_2__ arg_3__
          := match arg_2__, arg_3__ with
             | c, Data.ByteString.Lazy.Internal.Empty =>
                 if Data.ByteString.length c GHC.Base.== #1 : bool
                 then Data.ByteString.Lazy.Internal.Empty else
                 Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeInit c)
                 Data.ByteString.Lazy.Internal.Empty
             | c, Data.ByteString.Lazy.Internal.Chunk c' cs =>
                 Data.ByteString.Lazy.Internal.Chunk c (go c' cs)
             end in
        go c0 cs0
    end.

Definition unsnoc
   : Data.ByteString.Lazy.Internal.ByteString ->
     option (Data.ByteString.Lazy.Internal.ByteString * GHC.Word.Word8)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty => None
    | Data.ByteString.Lazy.Internal.Chunk c cs =>
        Some (pair (init (Data.ByteString.Lazy.Internal.Chunk c cs)) (last
                    (Data.ByteString.Lazy.Internal.Chunk c cs)))
    end.

Definition append
   : Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  GHC.Base.mappend.

Definition map
   : (GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let fix go arg_0__
      := match arg_0__ with
         | Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
         | Data.ByteString.Lazy.Internal.Chunk x xs =>
             let ys := go xs in
             let y := Data.ByteString.map f x in Data.ByteString.Lazy.Internal.Chunk y ys
         end in
    go.

Definition reverse
   : Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  let fix rev arg_0__ arg_1__
    := match arg_0__, arg_1__ with
       | a, Data.ByteString.Lazy.Internal.Empty => a
       | a, Data.ByteString.Lazy.Internal.Chunk c cs =>
           rev (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.reverse c) a) cs
       end in
  rev Data.ByteString.Lazy.Internal.Empty.

Definition intersperse
   : GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
    | w, Data.ByteString.Lazy.Internal.Chunk c cs =>
        let intersperse'
         : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
          fun '(Data.ByteString.Internal.BS fp l) =>
            Data.ByteString.Internal.unsafeCreate (#2 GHC.Num.* l) (fun p' =>
                                                                      Data.ByteString.Internal.unsafeWithForeignPtr fp
                                                                      (fun p =>
                                                                         Foreign.Storable.poke p' w GHC.Base.>>
                                                                         Data.ByteString.Internal.c_intersperse
                                                                         (GHC.Ptr.plusPtr p' #1) p
                                                                         (GHC.Real.fromIntegral l) w)) in
        Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.intersperse w c)
        (Data.ByteString.Lazy.Internal.foldrChunks (Data.ByteString.Lazy.Internal.Chunk
                                                    GHC.Base.∘
                                                    intersperse') Data.ByteString.Lazy.Internal.Empty cs)
    end.

Definition transpose
   : list Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  fun css =>
    GHC.Base.map (fun ss =>
                    Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.pack ss)
                    Data.ByteString.Lazy.Internal.Empty) (Data.OldList.transpose (GHC.Base.map
                                                                                  unpack css)).

Definition foldl {a : Type}
   : (a -> GHC.Word.Word8 -> a) ->
     a -> Data.ByteString.Lazy.Internal.ByteString -> a :=
  fun f =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | a, Data.ByteString.Lazy.Internal.Empty => a
         | a, Data.ByteString.Lazy.Internal.Chunk c cs =>
             go (Data.ByteString.foldl f a c) cs
         end in
    go.

Definition foldl' {a : Type}
   : (a -> GHC.Word.Word8 -> a) ->
     a -> Data.ByteString.Lazy.Internal.ByteString -> a :=
  fun f =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | a, Data.ByteString.Lazy.Internal.Empty => a
         | a, Data.ByteString.Lazy.Internal.Chunk c cs =>
             go (Data.ByteString.foldl' f a c) cs
         end in
    go.

Definition foldr {a : Type}
   : (GHC.Word.Word8 -> a -> a) ->
     a -> Data.ByteString.Lazy.Internal.ByteString -> a :=
  fun k =>
    Data.ByteString.Lazy.Internal.foldrChunks (GHC.Base.flip (Data.ByteString.foldr
                                                              k)).

Fixpoint foldr' {a : Type} (f : GHC.Word.Word8 -> a -> a) (a : a)
  : Data.ByteString.Lazy.Internal.ByteString -> a
  := let go :=
       fun arg_0__ =>
         match arg_0__ with
         | Data.ByteString.Lazy.Internal.Empty => a
         | Data.ByteString.Lazy.Internal.Chunk c cs =>
             Data.ByteString.foldr' f (foldr' f a cs) c
         end in
     go.

Definition foldl1
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Word.Word8 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "foldl1")
    | f, Data.ByteString.Lazy.Internal.Chunk c cs =>
        foldl f (Data.ByteString.Unsafe.unsafeHead c)
        (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeTail c) cs)
    end.

Definition foldl1'
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Word.Word8 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "foldl1'")
    | f, Data.ByteString.Lazy.Internal.Chunk c cs =>
        foldl' f (Data.ByteString.Unsafe.unsafeHead c)
        (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeTail c) cs)
    end.

Definition foldr1
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Word.Word8 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "foldr1")
    | f, Data.ByteString.Lazy.Internal.Chunk c0 cs0 =>
        let fix go arg_3__ arg_4__
          := match arg_3__, arg_4__ with
             | c, Data.ByteString.Lazy.Internal.Empty => Data.ByteString.foldr1 f c
             | c, Data.ByteString.Lazy.Internal.Chunk c' cs =>
                 Data.ByteString.foldr f (go c' cs) c
             end in
        go c0 cs0
    end.

Definition foldr1'
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Word.Word8 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "foldr1'")
    | f, Data.ByteString.Lazy.Internal.Chunk c0 cs0 =>
        let fix go arg_3__ arg_4__
          := match arg_3__, arg_4__ with
             | c, Data.ByteString.Lazy.Internal.Empty => Data.ByteString.foldr1' f c
             | c, Data.ByteString.Lazy.Internal.Chunk c' cs =>
                 Data.ByteString.foldr' f (go c' cs) c
             end in
        go c0 cs0
    end.

Definition concat
   : list Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  GHC.Base.mconcat.

Definition concatMap
   : (GHC.Word.Word8 -> Data.ByteString.Lazy.Internal.ByteString) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
    | f, Data.ByteString.Lazy.Internal.Chunk c0 cs0 =>
        let go
         : Data.ByteString.Lazy.Internal.ByteString ->
           Data.ByteString.Internal.ByteString ->
           Data.ByteString.Lazy.Internal.ByteString ->
           Data.ByteString.Lazy.Internal.ByteString :=
          fix go (arg_2__ : Data.ByteString.Lazy.Internal.ByteString) (arg_3__
                   : Data.ByteString.Internal.ByteString) (arg_4__
                   : Data.ByteString.Lazy.Internal.ByteString)
            : Data.ByteString.Lazy.Internal.ByteString
            := match arg_2__, arg_3__, arg_4__ with
               | Data.ByteString.Lazy.Internal.Empty, c', cs' => to c' cs'
               | Data.ByteString.Lazy.Internal.Chunk c cs, c', cs' =>
                   Data.ByteString.Lazy.Internal.Chunk c (go cs c' cs')
               end
          with to (c : Data.ByteString.Internal.ByteString) (cs
                    : Data.ByteString.Lazy.Internal.ByteString)
            : Data.ByteString.Lazy.Internal.ByteString
            := if Data.ByteString.null c : bool
               then match cs with
                    | Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
                    | Data.ByteString.Lazy.Internal.Chunk c' cs' => to c' cs'
                    end else
               go (f (Data.ByteString.Unsafe.unsafeHead c)) (Data.ByteString.Unsafe.unsafeTail
                                                             c) cs for go in
        let to
         : Data.ByteString.Internal.ByteString ->
           Data.ByteString.Lazy.Internal.ByteString ->
           Data.ByteString.Lazy.Internal.ByteString :=
          fix go (arg_2__ : Data.ByteString.Lazy.Internal.ByteString) (arg_3__
                   : Data.ByteString.Internal.ByteString) (arg_4__
                   : Data.ByteString.Lazy.Internal.ByteString)
            : Data.ByteString.Lazy.Internal.ByteString
            := match arg_2__, arg_3__, arg_4__ with
               | Data.ByteString.Lazy.Internal.Empty, c', cs' => to c' cs'
               | Data.ByteString.Lazy.Internal.Chunk c cs, c', cs' =>
                   Data.ByteString.Lazy.Internal.Chunk c (go cs c' cs')
               end
          with to (c : Data.ByteString.Internal.ByteString) (cs
                    : Data.ByteString.Lazy.Internal.ByteString)
            : Data.ByteString.Lazy.Internal.ByteString
            := if Data.ByteString.null c : bool
               then match cs with
                    | Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
                    | Data.ByteString.Lazy.Internal.Chunk c' cs' => to c' cs'
                    end else
               go (f (Data.ByteString.Unsafe.unsafeHead c)) (Data.ByteString.Unsafe.unsafeTail
                                                             c) cs for to in
        to c0 cs0
    end.

Definition any
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun f =>
    Data.ByteString.Lazy.Internal.foldrChunks (fun c rest =>
                                                 orb (Data.ByteString.any f c) rest) false.

Definition all
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun f =>
    Data.ByteString.Lazy.Internal.foldrChunks (fun c rest =>
                                                 andb (Data.ByteString.all f c) rest) true.

Definition maximum
   : Data.ByteString.Lazy.Internal.ByteString -> GHC.Word.Word8 :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "maximum")
    | Data.ByteString.Lazy.Internal.Chunk c cs =>
        Data.ByteString.Lazy.Internal.foldlChunks (fun n c' =>
                                                     GHC.Base.max n (Data.ByteString.maximum c'))
        (Data.ByteString.maximum c) cs
    end.

Definition minimum
   : Data.ByteString.Lazy.Internal.ByteString -> GHC.Word.Word8 :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty =>
        errorEmptyList (GHC.Base.hs_string__ "minimum")
    | Data.ByteString.Lazy.Internal.Chunk c cs =>
        Data.ByteString.Lazy.Internal.foldlChunks (fun n c' =>
                                                     GHC.Base.min n (Data.ByteString.minimum c'))
        (Data.ByteString.minimum c) cs
    end.

Fixpoint compareLength (arg_0__ : Data.ByteString.Lazy.Internal.ByteString)
                       (arg_1__ : GHC.Int.Int64) : comparison
  := match arg_0__, arg_1__ with
     | _, toCmp =>
         if toCmp GHC.Base.< #0 : bool then Gt else
         match arg_0__, arg_1__ with
         | Data.ByteString.Lazy.Internal.Empty, toCmp => GHC.Base.compare #0 toCmp
         | Data.ByteString.Lazy.Internal.Chunk c cs, toCmp =>
             compareLength cs (toCmp GHC.Num.-
                               GHC.Real.fromIntegral (Data.ByteString.length c))
         end
     end.

Definition mapAccumL {acc : Type}
   : (acc -> GHC.Word.Word8 -> (acc * GHC.Word.Word8)%type) ->
     acc ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (acc * Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | s, Data.ByteString.Lazy.Internal.Empty =>
             pair s Data.ByteString.Lazy.Internal.Empty
         | s, Data.ByteString.Lazy.Internal.Chunk c cs =>
             let 'pair s' c' := Data.ByteString.mapAccumL f s c in
             let 'pair s'' cs' := go s' cs in
             pair s'' (Data.ByteString.Lazy.Internal.Chunk c' cs')
         end in
    go.

Definition mapAccumR {acc : Type}
   : (acc -> GHC.Word.Word8 -> (acc * GHC.Word.Word8)%type) ->
     acc ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (acc * Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | s, Data.ByteString.Lazy.Internal.Empty =>
             pair s Data.ByteString.Lazy.Internal.Empty
         | s, Data.ByteString.Lazy.Internal.Chunk c cs =>
             let 'pair s' cs' := go s cs in
             let 'pair s'' c' := Data.ByteString.mapAccumR f s' c in
             pair s'' (Data.ByteString.Lazy.Internal.Chunk c' cs')
         end in
    go.

Definition scanl
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun function =>
    GHC.Base.fmap (Data.Tuple.uncurry (GHC.Base.flip snoc)) GHC.Base.∘
    mapAccumL (fun x y => pair (function x y) x).

Definition scanl1
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun function byteStream =>
    match uncons byteStream with
    | None => Data.ByteString.Lazy.Internal.Empty
    | Some (pair firstByte remainingBytes) =>
        scanl function firstByte remainingBytes
    end.

Definition scanr
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun function =>
    GHC.Base.fmap (Data.Tuple.uncurry cons_) GHC.Base.∘
    mapAccumR (fun x y => pair (function y x) x).

Definition scanr1
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun function byteStream =>
    match unsnoc byteStream with
    | None => Data.ByteString.Lazy.Internal.Empty
    | Some (pair initialBytes lastByte) => scanr function lastByte initialBytes
    end.

Definition unfoldr {a : Type}
   : (a -> option (GHC.Word.Word8 * a)%type) ->
     a -> Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let fix unfoldChunk n x
      := match Data.ByteString.unfoldrN n f x with
         | pair c None =>
             if Data.ByteString.null c : bool then Data.ByteString.Lazy.Internal.Empty else
             Data.ByteString.Lazy.Internal.Chunk c Data.ByteString.Lazy.Internal.Empty
         | pair c (Some x') =>
             Data.ByteString.Lazy.Internal.Chunk c (unfoldChunk (n GHC.Num.* #2) x')
         end in
    unfoldChunk #32.

Definition iterate
   : (GHC.Word.Word8 -> GHC.Word.Word8) ->
     GHC.Word.Word8 -> Data.ByteString.Lazy.Internal.ByteString :=
  fun f => unfoldr (fun x => let 'x' := f x in Some (pair x' x')).

(* Translating `repeat' failed: recursion through non-lambda value unsupported
   [in definition cs in module Data.ByteString.Lazy] *)

Axiom repeat : forall {A : Type}, A.

Definition replicate
   : GHC.Int.Int64 ->
     GHC.Word.Word8 -> Data.ByteString.Lazy.Internal.ByteString :=
  fun n w =>
    let 'pair q r := GHC.Real.quotRem n (GHC.Real.fromIntegral
                                         Data.ByteString.Lazy.Internal.smallChunkSize) in
    let c :=
      Data.ByteString.replicate Data.ByteString.Lazy.Internal.smallChunkSize w in
    let fix nChunks arg_2__
      := let 'num_3__ := arg_2__ in
         if num_3__ GHC.Base.== #0 : bool then Data.ByteString.Lazy.Internal.Empty else
         let 'm := arg_2__ in
         Data.ByteString.Lazy.Internal.Chunk c (nChunks (m GHC.Num.- #1)) in
    let cs := nChunks q in
    if n GHC.Base.<= #0 : bool then Data.ByteString.Lazy.Internal.Empty else
    if n GHC.Base.<
       GHC.Real.fromIntegral Data.ByteString.Lazy.Internal.smallChunkSize : bool
    then Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.replicate
                                              (GHC.Real.fromIntegral n) w) Data.ByteString.Lazy.Internal.Empty else
    if r GHC.Base.== #0 : bool then cs else
    Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeTake
                                         (GHC.Real.fromIntegral r) c) cs.

(* Translating `cycle' failed: recursion through non-lambda value unsupported
   [in definition cs' in module Data.ByteString.Lazy] *)

Axiom cycle : forall {A : Type}, A.

Definition take
   : GHC.Int.Int64 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | i, _ =>
        if i GHC.Base.<= #0 : bool then Data.ByteString.Lazy.Internal.Empty else
        match arg_0__, arg_1__ with
        | i, cs0 =>
            let fix take' arg_2__ arg_3__
              := match arg_2__, arg_3__ with
                 | num_4__, _ =>
                     if num_4__ GHC.Base.== #0 : bool then Data.ByteString.Lazy.Internal.Empty else
                     match arg_2__, arg_3__ with
                     | _, Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
                     | n, Data.ByteString.Lazy.Internal.Chunk c cs =>
                         if n GHC.Base.< GHC.Real.fromIntegral (Data.ByteString.length c) : bool
                         then Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.take
                                                                   (GHC.Real.fromIntegral n) c)
                              Data.ByteString.Lazy.Internal.Empty
                         else Data.ByteString.Lazy.Internal.Chunk c (take' (n GHC.Num.-
                                                                            GHC.Real.fromIntegral
                                                                            (Data.ByteString.length c)) cs)
                     end
                 end in
            take' i cs0
        end
    end.

Definition takeEnd
   : GHC.Int.Int64 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | i, _ =>
        if i GHC.Base.<= #0 : bool then Data.ByteString.Lazy.Internal.Empty else
        match arg_0__, arg_1__ with
        | i, cs0 =>
            let takeTuple :=
              fun arg_2__ arg_3__ =>
                match arg_2__, arg_3__ with
                | _, pair num_4__ cs =>
                    if num_4__ GHC.Base.== #0 : bool then pair #0 cs else
                    match arg_2__, arg_3__ with
                    | c, pair n cs =>
                        if n GHC.Base.> GHC.Real.fromIntegral (Data.ByteString.length c) : bool
                        then pair (n GHC.Num.- GHC.Real.fromIntegral (Data.ByteString.length c))
                                  (Data.ByteString.Lazy.Internal.Chunk c cs) else
                        pair #0 (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.takeEnd
                                                                      (GHC.Real.fromIntegral n) c) cs)
                    end
                end in
            let takeEnd' :=
              fun arg_10__ arg_11__ =>
                match arg_10__, arg_11__ with
                | num_12__, _ =>
                    if num_12__ GHC.Base.== #0 : bool then Data.ByteString.Lazy.Internal.Empty else
                    match arg_10__, arg_11__ with
                    | n, cs =>
                        Data.Tuple.snd (Data.ByteString.Lazy.Internal.foldrChunks takeTuple (pair n
                                                                                                  Data.ByteString.Lazy.Internal.Empty)
                                                                                  cs)
                    end
                end in
            takeEnd' i cs0
        end
    end.

Definition drop
   : GHC.Int.Int64 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | i, p =>
        if i GHC.Base.<= #0 : bool then p else
        match arg_0__, arg_1__ with
        | i, cs0 =>
            let fix drop' arg_2__ arg_3__
              := match arg_2__, arg_3__ with
                 | num_4__, cs =>
                     if num_4__ GHC.Base.== #0 : bool then cs else
                     match arg_2__, arg_3__ with
                     | _, Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
                     | n, Data.ByteString.Lazy.Internal.Chunk c cs =>
                         if n GHC.Base.< GHC.Real.fromIntegral (Data.ByteString.length c) : bool
                         then Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.drop
                                                                   (GHC.Real.fromIntegral n) c) cs
                         else drop' (n GHC.Num.- GHC.Real.fromIntegral (Data.ByteString.length c)) cs
                     end
                 end in
            drop' i cs0
        end
    end.

Definition dropEnd
   : GHC.Int.Int64 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | i, p =>
        if i GHC.Base.<= #0 : bool then p else
        match arg_0__, arg_1__ with
        | i, p =>
            let fromDeque
             : Data.ByteString.Lazy.Internal.Deque.Deque ->
               Data.ByteString.Lazy.Internal.ByteString :=
              fun deque =>
                append (Data.Foldable.foldr Data.ByteString.Lazy.Internal.chunk
                        Data.ByteString.Lazy.Internal.Empty (Data.ByteString.Lazy.Internal.Deque.front
                                                             deque)) (Data.Foldable.foldl' (GHC.Base.flip
                                                                                            Data.ByteString.Lazy.Internal.chunk)
                        Data.ByteString.Lazy.Internal.Empty (Data.ByteString.Lazy.Internal.Deque.rear
                                                             deque)) in
            let reverseChunks :=
              Data.ByteString.Lazy.Internal.foldlChunks (GHC.Base.flip
                                                         Data.ByteString.Lazy.Internal.Chunk) empty in
            let getOutput
             : Data.ByteString.Lazy.Internal.ByteString ->
               Data.ByteString.Lazy.Internal.Deque.Deque ->
               (Data.ByteString.Lazy.Internal.ByteString *
                Data.ByteString.Lazy.Internal.Deque.Deque)%type :=
              fix getOutput (out : Data.ByteString.Lazy.Internal.ByteString) (deque
                              : Data.ByteString.Lazy.Internal.Deque.Deque)
                : (Data.ByteString.Lazy.Internal.ByteString *
                   Data.ByteString.Lazy.Internal.Deque.Deque)%type
                := match Data.ByteString.Lazy.Internal.Deque.popFront deque with
                   | None => pair (reverseChunks out) deque
                   | Some (pair x deque') =>
                       if Data.ByteString.Lazy.Internal.Deque.byteLength deque' GHC.Base.>= i : bool
                       then getOutput (Data.ByteString.Lazy.Internal.Chunk x out) deque' else
                       pair (reverseChunks out) deque
                   end in
            let len := fun c => GHC.Real.fromIntegral (Data.ByteString.length c) in
            let dropEndBytes
             : Data.ByteString.Lazy.Internal.Deque.Deque ->
               GHC.Int.Int64 -> Data.ByteString.Lazy.Internal.Deque.Deque :=
              fix dropEndBytes (deque : Data.ByteString.Lazy.Internal.Deque.Deque) (n
                                 : GHC.Int.Int64) : Data.ByteString.Lazy.Internal.Deque.Deque
                := match Data.ByteString.Lazy.Internal.Deque.popRear deque with
                   | None => deque
                   | Some (pair deque' x) =>
                       if len x GHC.Base.<= n : bool then dropEndBytes deque' (n GHC.Num.- len x) else
                       Data.ByteString.Lazy.Internal.Deque.snoc (Data.ByteString.dropEnd
                                                                 (GHC.Real.fromIntegral n) x) deque'
                   end in
            let go
             : Data.ByteString.Lazy.Internal.Deque.Deque ->
               Data.ByteString.Lazy.Internal.ByteString ->
               Data.ByteString.Lazy.Internal.ByteString :=
              fix go (arg_17__ : Data.ByteString.Lazy.Internal.Deque.Deque) (arg_18__
                       : Data.ByteString.Lazy.Internal.ByteString)
                : Data.ByteString.Lazy.Internal.ByteString
                := match arg_17__, arg_18__ with
                   | deque, Data.ByteString.Lazy.Internal.Chunk c cs =>
                       if Data.ByteString.Lazy.Internal.Deque.byteLength deque GHC.Base.< i : bool
                       then go (Data.ByteString.Lazy.Internal.Deque.snoc c deque) cs else
                       let 'pair output deque' := getOutput empty
                                                    (Data.ByteString.Lazy.Internal.Deque.snoc c deque) in
                       Data.ByteString.Lazy.Internal.foldrChunks Data.ByteString.Lazy.Internal.Chunk
                       (go deque' cs) output
                   | deque, Data.ByteString.Lazy.Internal.Empty => fromDeque (dropEndBytes deque i)
                   end in
            go Data.ByteString.Lazy.Internal.Deque.empty p
        end
    end.

Definition splitAt
   : GHC.Int.Int64 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | i, cs0 =>
        if i GHC.Base.<= #0 : bool
        then pair Data.ByteString.Lazy.Internal.Empty cs0 else
        match arg_0__, arg_1__ with
        | i, cs0 =>
            let fix splitAt' arg_2__ arg_3__
              := match arg_2__, arg_3__ with
                 | num_4__, cs =>
                     if num_4__ GHC.Base.== #0 : bool
                     then pair Data.ByteString.Lazy.Internal.Empty cs else
                     match arg_2__, arg_3__ with
                     | _, Data.ByteString.Lazy.Internal.Empty =>
                         pair Data.ByteString.Lazy.Internal.Empty Data.ByteString.Lazy.Internal.Empty
                     | n, Data.ByteString.Lazy.Internal.Chunk c cs =>
                         if n GHC.Base.< GHC.Real.fromIntegral (Data.ByteString.length c) : bool
                         then pair (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.take
                                                                         (GHC.Real.fromIntegral n) c)
                                    Data.ByteString.Lazy.Internal.Empty) (Data.ByteString.Lazy.Internal.Chunk
                                    (Data.ByteString.drop (GHC.Real.fromIntegral n) c) cs)
                         else let 'pair cs' cs'' := splitAt' (n GHC.Num.-
                                                              GHC.Real.fromIntegral (Data.ByteString.length c)) cs in
                              pair (Data.ByteString.Lazy.Internal.Chunk c cs') cs''
                     end
                 end in
            splitAt' i cs0
        end
    end.

Definition takeWhile
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let fix takeWhile' arg_0__
      := match arg_0__ with
         | Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
         | Data.ByteString.Lazy.Internal.Chunk c cs =>
             let scrut_1__ :=
               Data.ByteString.Internal.findIndexOrLength (negb GHC.Base.∘ f) c in
             let 'num_2__ := scrut_1__ in
             if num_2__ GHC.Base.== #0 : bool then Data.ByteString.Lazy.Internal.Empty else
             let 'n := scrut_1__ in
             if n GHC.Base.< Data.ByteString.length c : bool
             then Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.take n c)
                  Data.ByteString.Lazy.Internal.Empty else
             Data.ByteString.Lazy.Internal.Chunk c (takeWhile' cs)
         end in
    takeWhile'.

Definition takeWhileEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let takeTuple :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | _, pair false bs => pair false bs
        | c, pair true bs =>
            let 'c' := Data.ByteString.takeWhileEnd f c in
            if Data.ByteString.length c' GHC.Base.== Data.ByteString.length c : bool
            then pair true (Data.ByteString.Lazy.Internal.Chunk c bs) else
            pair false (append (Data.ByteString.Lazy.Internal.fromStrict c') bs)
        end in
    let takeWhileEnd' :=
      fun arg_9__ =>
        match arg_9__ with
        | Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
        | cs =>
            Data.Tuple.snd (Data.ByteString.Lazy.Internal.foldrChunks takeTuple (pair true
                                                                                      Data.ByteString.Lazy.Internal.Empty)
                                                                      cs)
        end in
    takeWhileEnd'.

Definition dropWhile
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let fix dropWhile' arg_0__
      := match arg_0__ with
         | Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
         | Data.ByteString.Lazy.Internal.Chunk c cs =>
             let 'n := Data.ByteString.Internal.findIndexOrLength (negb GHC.Base.∘ f) c in
             if n GHC.Base.< Data.ByteString.length c : bool
             then Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.drop n c) cs else
             dropWhile' cs
         end in
    dropWhile'.

Definition dropWhileEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let fix dropEndBytes arg_0__
      := match arg_0__ with
         | nil => Data.ByteString.Lazy.Internal.Empty
         | cons x xs =>
             let 'x' := Data.ByteString.dropWhileEnd f x in
             if Data.ByteString.null x' : bool then dropEndBytes xs else
             Data.Foldable.foldl' (GHC.Base.flip Data.ByteString.Lazy.Internal.Chunk)
             Data.ByteString.Lazy.Internal.Empty (cons x' xs)
         end in
    let fix go arg_7__ arg_8__
      := match arg_7__, arg_8__ with
         | acc, Data.ByteString.Lazy.Internal.Chunk c cs =>
             if f (Data.ByteString.last c) : bool then go (cons c acc) cs else
             Data.Foldable.foldl (GHC.Base.flip Data.ByteString.Lazy.Internal.Chunk) (go nil
                                                                                      cs) (cons c acc)
         | acc, Data.ByteString.Lazy.Internal.Empty => dropEndBytes acc
         end in
    go nil.

Definition break
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f =>
    let fix break' arg_0__
      := match arg_0__ with
         | Data.ByteString.Lazy.Internal.Empty =>
             pair Data.ByteString.Lazy.Internal.Empty Data.ByteString.Lazy.Internal.Empty
         | Data.ByteString.Lazy.Internal.Chunk c cs =>
             let scrut_2__ := Data.ByteString.Internal.findIndexOrLength f c in
             let 'num_3__ := scrut_2__ in
             if num_3__ GHC.Base.== #0 : bool
             then pair Data.ByteString.Lazy.Internal.Empty
                       (Data.ByteString.Lazy.Internal.Chunk c cs) else
             let 'n := scrut_2__ in
             if n GHC.Base.< Data.ByteString.length c : bool
             then pair (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.take n c)
                        Data.ByteString.Lazy.Internal.Empty) (Data.ByteString.Lazy.Internal.Chunk
                        (Data.ByteString.drop n c) cs) else
             let 'pair cs' cs'' := break' cs in
             pair (Data.ByteString.Lazy.Internal.Chunk c cs') cs''
         end in
    break'.

Definition breakEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f =>
    let fix dropEndBytes arg_0__
      := match arg_0__ with
         | nil =>
             pair Data.ByteString.Lazy.Internal.Empty Data.ByteString.Lazy.Internal.Empty
         | cons x xs =>
             let 'pair x' x'' := Data.ByteString.breakEnd f x in
             if Data.ByteString.null x' : bool
             then let 'pair y y' := dropEndBytes xs in
                  pair y (append y' (Data.ByteString.Lazy.Internal.fromStrict x)) else
             Data.Foldable.foldl' (GHC.Base.flip (Data.Bifunctor.first GHC.Base.∘
                                                  Data.ByteString.Lazy.Internal.Chunk)) (pair
                                                                                         (Data.ByteString.Lazy.Internal.fromStrict
                                                                                          x')
                                                                                         (Data.ByteString.Lazy.Internal.fromStrict
                                                                                          x'')) xs
         end in
    let fix go arg_9__ arg_10__
      := match arg_9__, arg_10__ with
         | acc, Data.ByteString.Lazy.Internal.Chunk c cs =>
             if f (Data.ByteString.last c) : bool
             then Data.Foldable.foldl (GHC.Base.flip (Data.Bifunctor.first GHC.Base.∘
                                                      Data.ByteString.Lazy.Internal.Chunk)) (go nil cs) (cons c
                                                                                                              acc) else
             go (cons c acc) cs
         | acc, Data.ByteString.Lazy.Internal.Empty => dropEndBytes acc
         end in
    go nil.

Definition span
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun p => break (negb GHC.Base.∘ p).

Definition spanEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun p => breakEnd (negb GHC.Base.∘ p).

Definition revChunks
   : list Data.ByteString.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  Data.Foldable.foldl' (GHC.Base.flip Data.ByteString.Lazy.Internal.chunk)
  Data.ByteString.Lazy.Internal.Empty.

Definition splitWith
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Lazy.Internal.Empty => nil
    | p, Data.ByteString.Lazy.Internal.Chunk c0 cs0 =>
        let comb
         : list Data.ByteString.Internal.ByteString ->
           list Data.ByteString.Internal.ByteString ->
           Data.ByteString.Lazy.Internal.ByteString ->
           list Data.ByteString.Lazy.Internal.ByteString :=
          fix comb (arg_2__ arg_3__ : list Data.ByteString.Internal.ByteString) (arg_4__
                     : Data.ByteString.Lazy.Internal.ByteString) : list
                                                                   Data.ByteString.Lazy.Internal.ByteString
            := match arg_2__, arg_3__, arg_4__ with
               | acc, cons s nil, Data.ByteString.Lazy.Internal.Empty =>
                   cons (revChunks (cons s acc)) nil
               | acc, cons s nil, Data.ByteString.Lazy.Internal.Chunk c cs =>
                   comb (cons s acc) (Data.ByteString.splitWith p c) cs
               | acc, cons s ss, cs => cons (revChunks (cons s acc)) (comb nil ss cs)
               | _, _, _ => GHC.Err.patternFailure
               end in
        comb nil (Data.ByteString.splitWith p c0) cs0
    end.

Definition split
   : GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Data.ByteString.Lazy.Internal.Empty => nil
    | w, Data.ByteString.Lazy.Internal.Chunk c0 cs0 =>
        let comb
         : list Data.ByteString.Internal.ByteString ->
           list Data.ByteString.Internal.ByteString ->
           Data.ByteString.Lazy.Internal.ByteString ->
           list Data.ByteString.Lazy.Internal.ByteString :=
          fix comb (arg_2__ arg_3__ : list Data.ByteString.Internal.ByteString) (arg_4__
                     : Data.ByteString.Lazy.Internal.ByteString) : list
                                                                   Data.ByteString.Lazy.Internal.ByteString
            := match arg_2__, arg_3__, arg_4__ with
               | acc, cons s nil, Data.ByteString.Lazy.Internal.Empty =>
                   cons (revChunks (cons s acc)) nil
               | acc, cons s nil, Data.ByteString.Lazy.Internal.Chunk c cs =>
                   comb (cons s acc) (Data.ByteString.split w c) cs
               | acc, cons s ss, cs => cons (revChunks (cons s acc)) (comb nil ss cs)
               | _, _, _ => GHC.Err.patternFailure
               end in
        comb nil (Data.ByteString.split w c0) cs0
    end.

Definition revNonEmptyChunks
   : list Data.ByteString.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  Data.Foldable.foldl' (GHC.Base.flip Data.ByteString.Lazy.Internal.Chunk)
  Data.ByteString.Lazy.Internal.Empty.

Definition group
   : Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  let go :=
    fix go arg_0__
      := match arg_0__ with
         | Data.ByteString.Lazy.Internal.Empty => nil
         | Data.ByteString.Lazy.Internal.Chunk c cs =>
             if Data.ByteString.length c GHC.Base.== #1 : bool
             then to (cons c nil) (Data.ByteString.Unsafe.unsafeHead c) cs else
             to (cons (Data.ByteString.Unsafe.unsafeTake #1 c) nil)
             (Data.ByteString.Unsafe.unsafeHead c) (Data.ByteString.Lazy.Internal.Chunk
                                                    (Data.ByteString.Unsafe.unsafeTail c) cs)
         end
    with to arg_4__ arg_5__ arg_6__
      := match arg_4__, arg_5__, arg_6__ with
         | acc, _, Data.ByteString.Lazy.Internal.Empty =>
             cons (revNonEmptyChunks acc) nil
         | acc, w, Data.ByteString.Lazy.Internal.Chunk c cs =>
             let scrut_9__ :=
               Data.ByteString.Internal.findIndexOrLength (fun arg_8__ =>
                                                             arg_8__ GHC.Base./= w) c in
             let 'num_10__ := scrut_9__ in
             if num_10__ GHC.Base.== #0 : bool
             then cons (revNonEmptyChunks acc) (go (Data.ByteString.Lazy.Internal.Chunk c
                                                    cs)) else
             let 'n := scrut_9__ in
             if n GHC.Base.== Data.ByteString.length c : bool
             then to (cons (Data.ByteString.Unsafe.unsafeTake n c) acc) w cs else
             cons (revNonEmptyChunks (cons (Data.ByteString.Unsafe.unsafeTake n c) acc)) (go
                   (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeDrop n c)
                    cs))
         end for go in
  let to :=
    fix go arg_0__
      := match arg_0__ with
         | Data.ByteString.Lazy.Internal.Empty => nil
         | Data.ByteString.Lazy.Internal.Chunk c cs =>
             if Data.ByteString.length c GHC.Base.== #1 : bool
             then to (cons c nil) (Data.ByteString.Unsafe.unsafeHead c) cs else
             to (cons (Data.ByteString.Unsafe.unsafeTake #1 c) nil)
             (Data.ByteString.Unsafe.unsafeHead c) (Data.ByteString.Lazy.Internal.Chunk
                                                    (Data.ByteString.Unsafe.unsafeTail c) cs)
         end
    with to arg_4__ arg_5__ arg_6__
      := match arg_4__, arg_5__, arg_6__ with
         | acc, _, Data.ByteString.Lazy.Internal.Empty =>
             cons (revNonEmptyChunks acc) nil
         | acc, w, Data.ByteString.Lazy.Internal.Chunk c cs =>
             let scrut_9__ :=
               Data.ByteString.Internal.findIndexOrLength (fun arg_8__ =>
                                                             arg_8__ GHC.Base./= w) c in
             let 'num_10__ := scrut_9__ in
             if num_10__ GHC.Base.== #0 : bool
             then cons (revNonEmptyChunks acc) (go (Data.ByteString.Lazy.Internal.Chunk c
                                                    cs)) else
             let 'n := scrut_9__ in
             if n GHC.Base.== Data.ByteString.length c : bool
             then to (cons (Data.ByteString.Unsafe.unsafeTake n c) acc) w cs else
             cons (revNonEmptyChunks (cons (Data.ByteString.Unsafe.unsafeTake n c) acc)) (go
                   (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeDrop n c)
                    cs))
         end for to in
  go.

Definition groupBy
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  fun k =>
    let go :=
      fix go arg_0__
        := match arg_0__ with
           | Data.ByteString.Lazy.Internal.Empty => nil
           | Data.ByteString.Lazy.Internal.Chunk c cs =>
               if Data.ByteString.length c GHC.Base.== #1 : bool
               then to (cons c nil) (Data.ByteString.Unsafe.unsafeHead c) cs else
               to (cons (Data.ByteString.Unsafe.unsafeTake #1 c) nil)
               (Data.ByteString.Unsafe.unsafeHead c) (Data.ByteString.Lazy.Internal.Chunk
                                                      (Data.ByteString.Unsafe.unsafeTail c) cs)
           end
      with to arg_4__ arg_5__ arg_6__
        := match arg_4__, arg_5__, arg_6__ with
           | acc, _, Data.ByteString.Lazy.Internal.Empty =>
               cons (revNonEmptyChunks acc) nil
           | acc, w, Data.ByteString.Lazy.Internal.Chunk c cs =>
               let scrut_8__ :=
                 Data.ByteString.Internal.findIndexOrLength (negb GHC.Base.∘ k w) c in
               let 'num_9__ := scrut_8__ in
               if num_9__ GHC.Base.== #0 : bool
               then cons (revNonEmptyChunks acc) (go (Data.ByteString.Lazy.Internal.Chunk c
                                                      cs)) else
               let 'n := scrut_8__ in
               if n GHC.Base.== Data.ByteString.length c : bool
               then to (cons (Data.ByteString.Unsafe.unsafeTake n c) acc) w cs else
               cons (revNonEmptyChunks (cons (Data.ByteString.Unsafe.unsafeTake n c) acc)) (go
                     (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeDrop n c)
                      cs))
           end for go in
    let to :=
      fix go arg_0__
        := match arg_0__ with
           | Data.ByteString.Lazy.Internal.Empty => nil
           | Data.ByteString.Lazy.Internal.Chunk c cs =>
               if Data.ByteString.length c GHC.Base.== #1 : bool
               then to (cons c nil) (Data.ByteString.Unsafe.unsafeHead c) cs else
               to (cons (Data.ByteString.Unsafe.unsafeTake #1 c) nil)
               (Data.ByteString.Unsafe.unsafeHead c) (Data.ByteString.Lazy.Internal.Chunk
                                                      (Data.ByteString.Unsafe.unsafeTail c) cs)
           end
      with to arg_4__ arg_5__ arg_6__
        := match arg_4__, arg_5__, arg_6__ with
           | acc, _, Data.ByteString.Lazy.Internal.Empty =>
               cons (revNonEmptyChunks acc) nil
           | acc, w, Data.ByteString.Lazy.Internal.Chunk c cs =>
               let scrut_8__ :=
                 Data.ByteString.Internal.findIndexOrLength (negb GHC.Base.∘ k w) c in
               let 'num_9__ := scrut_8__ in
               if num_9__ GHC.Base.== #0 : bool
               then cons (revNonEmptyChunks acc) (go (Data.ByteString.Lazy.Internal.Chunk c
                                                      cs)) else
               let 'n := scrut_8__ in
               if n GHC.Base.== Data.ByteString.length c : bool
               then to (cons (Data.ByteString.Unsafe.unsafeTake n c) acc) w cs else
               cons (revNonEmptyChunks (cons (Data.ByteString.Unsafe.unsafeTake n c) acc)) (go
                     (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Unsafe.unsafeDrop n c)
                      cs))
           end for to in
    go.

Definition intercalate
   : Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun s => concat GHC.Base.∘ Data.OldList.intersperse s.

Definition index
   : Data.ByteString.Lazy.Internal.ByteString ->
     GHC.Int.Int64 -> GHC.Word.Word8 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, i =>
        if i GHC.Base.< #0 : bool
        then moduleError (GHC.Base.hs_string__ "index") (Coq.Init.Datatypes.app
                                                         (GHC.Base.hs_string__ "negative index: ") (GHC.Show.show
                                                          i)) else
        match arg_0__, arg_1__ with
        | cs0, i =>
            let fix index' arg_2__ arg_3__
              := match arg_2__, arg_3__ with
                 | Data.ByteString.Lazy.Internal.Empty, n =>
                     moduleError (GHC.Base.hs_string__ "index") (Coq.Init.Datatypes.app
                                                                 (GHC.Base.hs_string__ "index too large: ")
                                                                 (GHC.Show.show n))
                 | Data.ByteString.Lazy.Internal.Chunk c cs, n =>
                     if n GHC.Base.>= GHC.Real.fromIntegral (Data.ByteString.length c) : bool
                     then index' cs (n GHC.Num.-
                                     GHC.Real.fromIntegral (Data.ByteString.length c)) else
                     Data.ByteString.Unsafe.unsafeIndex c (GHC.Real.fromIntegral n)
                 end in
            index' cs0 i
        end
    end.

Definition indexMaybe
   : Data.ByteString.Lazy.Internal.ByteString ->
     GHC.Int.Int64 -> option GHC.Word.Word8 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, i =>
        if i GHC.Base.< #0 : bool then None else
        match arg_0__, arg_1__ with
        | cs0, i =>
            let fix index' arg_2__ arg_3__
              := match arg_2__, arg_3__ with
                 | Data.ByteString.Lazy.Internal.Empty, _ => None
                 | Data.ByteString.Lazy.Internal.Chunk c cs, n =>
                     if n GHC.Base.>= GHC.Real.fromIntegral (Data.ByteString.length c) : bool
                     then index' cs (n GHC.Num.-
                                     GHC.Real.fromIntegral (Data.ByteString.length c)) else
                     Some (Data.ByteString.Unsafe.unsafeIndex c (GHC.Real.fromIntegral n))
                 end in
            index' cs0 i
        end
    end.

Definition op_znz3fU__
   : Data.ByteString.Lazy.Internal.ByteString ->
     GHC.Int.Int64 -> option GHC.Word.Word8 :=
  indexMaybe.

Notation "'_!?_'" := (op_znz3fU__).

Infix "!?" := (_!?_) (at level 99).

Definition elemIndex
   : GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Int.Int64 :=
  fun w =>
    let fix elemIndex' arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | _, Data.ByteString.Lazy.Internal.Empty => None
         | n, Data.ByteString.Lazy.Internal.Chunk c cs =>
             match Data.ByteString.elemIndex w c with
             | None =>
                 elemIndex' (n GHC.Num.+ GHC.Real.fromIntegral (Data.ByteString.length c)) cs
             | Some i => Some (n GHC.Num.+ GHC.Real.fromIntegral i)
             end
         end in
    elemIndex' #0.

Definition findIndexEnd
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Int.Int64 :=
  fun k =>
    let fix findIndexEnd' arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | _, Data.ByteString.Lazy.Internal.Empty => None
         | n, Data.ByteString.Lazy.Internal.Chunk c cs =>
             let i :=
               (GHC.Real.fromIntegral GHC.Base.∘ (fun arg_2__ => n GHC.Num.+ arg_2__))
               Data.Functor.<$>
               Data.ByteString.findIndexEnd k c in
             let n' := n GHC.Num.+ Data.ByteString.length c in
             GHC.Base.mplus (findIndexEnd' n' cs) i
         end in
    findIndexEnd' #0.

Definition elemIndexEnd
   : GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Int.Int64 :=
  findIndexEnd GHC.Base.∘ _GHC.Base.==_.

Definition elemIndices
   : GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString -> list GHC.Int.Int64 :=
  fun w =>
    let fix elemIndices' arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | _, Data.ByteString.Lazy.Internal.Empty => nil
         | n, Data.ByteString.Lazy.Internal.Chunk c cs =>
             Coq.Init.Datatypes.app (GHC.Base.map ((fun arg_2__ => arg_2__ GHC.Num.+ n)
                                                   GHC.Base.∘
                                                   GHC.Real.fromIntegral) (Data.ByteString.elemIndices w c))
                                    (elemIndices' (n GHC.Num.+ GHC.Real.fromIntegral (Data.ByteString.length c)) cs)
         end in
    elemIndices' #0.

Definition count
   : GHC.Word.Word8 ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Int.Int64 :=
  fun w =>
    Data.ByteString.Lazy.Internal.foldlChunks (fun n c =>
                                                 n GHC.Num.+ GHC.Real.fromIntegral (Data.ByteString.count w c)) #0.

Definition findIndex
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Int.Int64 :=
  fun k =>
    let fix findIndex' arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | _, Data.ByteString.Lazy.Internal.Empty => None
         | n, Data.ByteString.Lazy.Internal.Chunk c cs =>
             match Data.ByteString.findIndex k c with
             | None =>
                 findIndex' (n GHC.Num.+ GHC.Real.fromIntegral (Data.ByteString.length c)) cs
             | Some i => Some (n GHC.Num.+ GHC.Real.fromIntegral i)
             end
         end in
    findIndex' #0.

Definition find
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Word.Word8 :=
  fun f =>
    let fix find' arg_0__
      := match arg_0__ with
         | Data.ByteString.Lazy.Internal.Empty => None
         | Data.ByteString.Lazy.Internal.Chunk c cs =>
             match Data.ByteString.find f c with
             | None => find' cs
             | Some w => Some w
             end
         end in
    find'.

Definition findIndices
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> list GHC.Int.Int64 :=
  fun k =>
    let fix findIndices' arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | _, Data.ByteString.Lazy.Internal.Empty => nil
         | n, Data.ByteString.Lazy.Internal.Chunk c cs =>
             Coq.Init.Datatypes.app (GHC.Base.map ((fun arg_2__ => arg_2__ GHC.Num.+ n)
                                                   GHC.Base.∘
                                                   GHC.Real.fromIntegral) (Data.ByteString.findIndices k c))
                                    (findIndices' (n GHC.Num.+ GHC.Real.fromIntegral (Data.ByteString.length c)) cs)
         end in
    findIndices' #0.

Definition elem
   : GHC.Word.Word8 -> Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun w cs => match elemIndex w cs with | None => false | _ => true end.

Definition notElem
   : GHC.Word.Word8 -> Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun w cs => negb (elem w cs).

Definition filter
   : (GHC.Word.Word8 -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun p =>
    let fix go arg_0__
      := match arg_0__ with
         | Data.ByteString.Lazy.Internal.Empty => Data.ByteString.Lazy.Internal.Empty
         | Data.ByteString.Lazy.Internal.Chunk x xs =>
             Data.ByteString.Lazy.Internal.chunk (Data.ByteString.filter p x) (go xs)
         end in
    go.

Fixpoint partition (arg_0__ : GHC.Word.Word8 -> bool) (arg_1__
                     : Data.ByteString.Lazy.Internal.ByteString)
  : (Data.ByteString.Lazy.Internal.ByteString *
     Data.ByteString.Lazy.Internal.ByteString)%type
  := match arg_0__, arg_1__ with
     | _, Data.ByteString.Lazy.Internal.Empty =>
         pair Data.ByteString.Lazy.Internal.Empty Data.ByteString.Lazy.Internal.Empty
     | p, Data.ByteString.Lazy.Internal.Chunk x xs =>
         let 'pair ts fs := partition p xs in
         let 'pair t f := Data.ByteString.partition p x in
         pair (Data.ByteString.Lazy.Internal.chunk t ts)
              (Data.ByteString.Lazy.Internal.chunk f fs)
     end.

Fixpoint isPrefixOf (arg_0__ arg_1__ : Data.ByteString.Lazy.Internal.ByteString)
  : bool
  := match arg_0__, arg_1__ with
     | Data.ByteString.Lazy.Internal.Empty, _ => true
     | _, Data.ByteString.Lazy.Internal.Empty => false
     | Data.ByteString.Lazy.Internal.Chunk x xs
     , Data.ByteString.Lazy.Internal.Chunk y ys =>
         let 'pair yh yt := Data.ByteString.splitAt (Data.ByteString.length x) y in
         let 'pair xh xt := Data.ByteString.splitAt (Data.ByteString.length y) x in
         if Data.ByteString.length x GHC.Base.== Data.ByteString.length y : bool
         then andb (x GHC.Base.== y) (isPrefixOf xs ys) else
         if Data.ByteString.length x GHC.Base.< Data.ByteString.length y : bool
         then andb (x GHC.Base.== yh) (isPrefixOf xs (Data.ByteString.Lazy.Internal.Chunk
                                                      yt ys)) else
         andb (xh GHC.Base.== y) (isPrefixOf (Data.ByteString.Lazy.Internal.Chunk xt xs)
               ys)
     end.

Fixpoint stripPrefix (arg_0__ arg_1__
                       : Data.ByteString.Lazy.Internal.ByteString) : option
                                                                     Data.ByteString.Lazy.Internal.ByteString
  := match arg_0__, arg_1__ with
     | Data.ByteString.Lazy.Internal.Empty, bs => Some bs
     | _, Data.ByteString.Lazy.Internal.Empty => None
     | Data.ByteString.Lazy.Internal.Chunk x xs
     , Data.ByteString.Lazy.Internal.Chunk y ys =>
         if Data.ByteString.length x GHC.Base.== Data.ByteString.length y : bool
         then if x GHC.Base.== y : bool
              then stripPrefix xs ys
              else None else
         if Data.ByteString.length x GHC.Base.< Data.ByteString.length y : bool
         then Data.ByteString.stripPrefix x y GHC.Base.>>=
              (fun yt => stripPrefix xs (Data.ByteString.Lazy.Internal.Chunk yt ys)) else
         Data.ByteString.stripPrefix y x GHC.Base.>>=
         (fun xt => stripPrefix (Data.ByteString.Lazy.Internal.Chunk xt xs) ys)
     end.

Definition isSuffixOf
   : Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun x y => isPrefixOf (reverse x) (reverse y).

Definition stripSuffix
   : Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString ->
     option Data.ByteString.Lazy.Internal.ByteString :=
  fun x y => reverse Data.Functor.<$> stripPrefix (reverse x) (reverse y).

Definition zipWith {a : Type}
   : (GHC.Word.Word8 -> GHC.Word.Word8 -> a) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString -> list a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, Data.ByteString.Lazy.Internal.Empty, _ => nil
    | _, _, Data.ByteString.Lazy.Internal.Empty => nil
    | f
    , Data.ByteString.Lazy.Internal.Chunk a as_
    , Data.ByteString.Lazy.Internal.Chunk b bs =>
        let go :=
          fix go x xs y ys
            := cons (f (Data.ByteString.Unsafe.unsafeHead x)
                     (Data.ByteString.Unsafe.unsafeHead y)) (to (Data.ByteString.Unsafe.unsafeTail x)
                     xs (Data.ByteString.Unsafe.unsafeTail y) ys)
          with to arg_4__ arg_5__ arg_6__ arg_7__
            := let j_9__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | _
                 , Data.ByteString.Lazy.Internal.Chunk x' xs
                 , _
                 , Data.ByteString.Lazy.Internal.Chunk y' ys =>
                     go x' xs y' ys
                 | _, _, _, _ => GHC.Err.patternFailure
                 end in
               let j_11__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | _, Data.ByteString.Lazy.Internal.Chunk x' xs, y, ys =>
                     if negb (Data.ByteString.null y) : bool then go x' xs y ys else
                     j_9__
                 | _, _, _, _ => j_9__
                 end in
               let j_13__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | x, xs, _, Data.ByteString.Lazy.Internal.Chunk y' ys =>
                     if negb (Data.ByteString.null x) : bool then go x xs y' ys else
                     j_11__
                 | _, _, _, _ => j_11__
                 end in
               let j_15__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | x, xs, y, ys =>
                     if andb (negb (Data.ByteString.null x)) (negb (Data.ByteString.null y)) : bool
                     then go x xs y ys else
                     j_13__
                 end in
               let j_17__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | _, _, y, Data.ByteString.Lazy.Internal.Empty =>
                     if Data.ByteString.null y : bool then nil else
                     j_15__
                 | _, _, _, _ => j_15__
                 end in
               match arg_4__, arg_5__, arg_6__, arg_7__ with
               | x, Data.ByteString.Lazy.Internal.Empty, _, _ =>
                   if Data.ByteString.null x : bool then nil else
                   j_17__
               | _, _, _, _ => j_17__
               end for go in
        let to :=
          fix go x xs y ys
            := cons (f (Data.ByteString.Unsafe.unsafeHead x)
                     (Data.ByteString.Unsafe.unsafeHead y)) (to (Data.ByteString.Unsafe.unsafeTail x)
                     xs (Data.ByteString.Unsafe.unsafeTail y) ys)
          with to arg_4__ arg_5__ arg_6__ arg_7__
            := let j_9__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | _
                 , Data.ByteString.Lazy.Internal.Chunk x' xs
                 , _
                 , Data.ByteString.Lazy.Internal.Chunk y' ys =>
                     go x' xs y' ys
                 | _, _, _, _ => GHC.Err.patternFailure
                 end in
               let j_11__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | _, Data.ByteString.Lazy.Internal.Chunk x' xs, y, ys =>
                     if negb (Data.ByteString.null y) : bool then go x' xs y ys else
                     j_9__
                 | _, _, _, _ => j_9__
                 end in
               let j_13__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | x, xs, _, Data.ByteString.Lazy.Internal.Chunk y' ys =>
                     if negb (Data.ByteString.null x) : bool then go x xs y' ys else
                     j_11__
                 | _, _, _, _ => j_11__
                 end in
               let j_15__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | x, xs, y, ys =>
                     if andb (negb (Data.ByteString.null x)) (negb (Data.ByteString.null y)) : bool
                     then go x xs y ys else
                     j_13__
                 end in
               let j_17__ :=
                 match arg_4__, arg_5__, arg_6__, arg_7__ with
                 | _, _, y, Data.ByteString.Lazy.Internal.Empty =>
                     if Data.ByteString.null y : bool then nil else
                     j_15__
                 | _, _, _, _ => j_15__
                 end in
               match arg_4__, arg_5__, arg_6__, arg_7__ with
               | x, Data.ByteString.Lazy.Internal.Empty, _, _ =>
                   if Data.ByteString.null x : bool then nil else
                   j_17__
               | _, _, _, _ => j_17__
               end for to in
        go a as_ b bs
    end.

Definition zip
   : Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString ->
     list (GHC.Word.Word8 * GHC.Word.Word8)%type :=
  zipWith GHC.Tuple.pair2.

Fixpoint packZipWith (arg_0__
                       : GHC.Word.Word8 -> GHC.Word.Word8 -> GHC.Word.Word8) (arg_1__ arg_2__
                       : Data.ByteString.Lazy.Internal.ByteString)
  : Data.ByteString.Lazy.Internal.ByteString
  := match arg_0__, arg_1__, arg_2__ with
     | _, Data.ByteString.Lazy.Internal.Empty, _ =>
         Data.ByteString.Lazy.Internal.Empty
     | _, _, Data.ByteString.Lazy.Internal.Empty =>
         Data.ByteString.Lazy.Internal.Empty
     | f
     , Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Internal.BS _ al as a)
     as_
     , Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.Internal.BS _ bl as b)
     bs =>
         Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.packZipWith f a b)
         (match GHC.Base.compare al bl with
          | Lt =>
              packZipWith f as_ (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.drop al
                                                                      b) bs)
          | Eq => packZipWith f as_ bs
          | Gt =>
              packZipWith f (Data.ByteString.Lazy.Internal.Chunk (Data.ByteString.drop bl a)
                             as_) bs
          end)
     end.

Definition unzip
   : list (GHC.Word.Word8 * GHC.Word.Word8)%type ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun ls =>
    pair (pack (GHC.Base.map Data.Tuple.fst ls)) (pack (GHC.Base.map Data.Tuple.snd
                                                        ls)).

Definition inits
   : Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  let fix inits' arg_0__
    := match arg_0__ with
       | Data.ByteString.Lazy.Internal.Empty => nil
       | Data.ByteString.Lazy.Internal.Chunk c cs =>
           Coq.Init.Datatypes.app (GHC.Base.map (fun arg_1__ =>
                                                   Data.ByteString.Lazy.Internal.Chunk arg_1__
                                                                                       Data.ByteString.Lazy.Internal.Empty)
                                   (GHC.List.tail (Data.ByteString.inits c))) (GHC.Base.map
                                   (Data.ByteString.Lazy.Internal.Chunk c) (inits' cs))
       end in
  (fun arg_4__ => cons Data.ByteString.Lazy.Internal.Empty arg_4__) GHC.Base.∘
  inits'.

Fixpoint tails (arg_0__ : Data.ByteString.Lazy.Internal.ByteString) : list
                                                                      Data.ByteString.Lazy.Internal.ByteString
  := match arg_0__ with
     | Data.ByteString.Lazy.Internal.Empty =>
         cons Data.ByteString.Lazy.Internal.Empty nil
     | (Data.ByteString.Lazy.Internal.Chunk c cs' as cs) =>
         if Data.ByteString.length c GHC.Base.== #1 : bool then cons cs (tails cs') else
         cons cs (tails (Data.ByteString.Lazy.Internal.Chunk
                         (Data.ByteString.Unsafe.unsafeTail c) cs'))
     end.

Definition copy
   : Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.Internal.foldrChunks (Data.ByteString.Lazy.Internal.Chunk
                                             GHC.Base.∘
                                             Data.ByteString.copy) Data.ByteString.Lazy.Internal.Empty.

(* Translating `hGetContentsN' failed: recursion through non-lambda value
   unsupported [in definition lazyRead in module Data.ByteString.Lazy] *)

Axiom hGetContentsN : forall {A : Type}, A.

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

Definition hGetN
   : GHC.Num.Int ->
     GHC.IO.Handle.Types.Handle ->
     GHC.Num.Int -> GHC.Types.IO Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, h, n =>
        let j_5__ :=
          match arg_0__, arg_1__, arg_2__ with
          | _, h, n => illegalBufferSize h (GHC.Base.hs_string__ "hGet") n
          end in
        let j_7__ :=
          match arg_0__, arg_1__, arg_2__ with
          | _, _, num_3__ =>
              if num_3__ GHC.Base.== #0 : bool
              then GHC.Base.return_ Data.ByteString.Lazy.Internal.Empty else
              j_5__
          end in
        let fix readChunks i
          := Data.ByteString.hGet h (GHC.Base.min k i) GHC.Base.>>=
             (fun c =>
                let scrut_8__ := Data.ByteString.length c in
                let 'num_9__ := scrut_8__ in
                if num_9__ GHC.Base.== #0 : bool
                then GHC.Base.return_ Data.ByteString.Lazy.Internal.Empty else
                let 'm := scrut_8__ in
                readChunks (i GHC.Num.- m) GHC.Base.>>=
                (fun cs => GHC.Base.return_ (Data.ByteString.Lazy.Internal.Chunk c cs))) in
        if n GHC.Base.> #0 : bool then readChunks n else
        j_7__
    end.

Definition hGetNonBlockingN
   : GHC.Num.Int ->
     GHC.IO.Handle.Types.Handle ->
     GHC.Num.Int -> GHC.Types.IO Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, h, n =>
        let j_5__ :=
          match arg_0__, arg_1__, arg_2__ with
          | _, h, n => illegalBufferSize h (GHC.Base.hs_string__ "hGetNonBlocking") n
          end in
        let j_7__ :=
          match arg_0__, arg_1__, arg_2__ with
          | _, _, num_3__ =>
              if num_3__ GHC.Base.== #0 : bool
              then GHC.Base.return_ Data.ByteString.Lazy.Internal.Empty else
              j_5__
          end in
        let fix readChunks i
          := Data.ByteString.hGetNonBlocking h (GHC.Base.min k i) GHC.Base.>>=
             (fun c =>
                let scrut_8__ := Data.ByteString.length c in
                let 'num_9__ := scrut_8__ in
                if num_9__ GHC.Base.== #0 : bool
                then GHC.Base.return_ Data.ByteString.Lazy.Internal.Empty else
                let 'm := scrut_8__ in
                readChunks (i GHC.Num.- m) GHC.Base.>>=
                (fun cs => GHC.Base.return_ (Data.ByteString.Lazy.Internal.Chunk c cs))) in
        if n GHC.Base.> #0 : bool then readChunks n else
        j_7__
    end.

Definition hGetContents
   : GHC.IO.Handle.Types.Handle ->
     GHC.Types.IO Data.ByteString.Lazy.Internal.ByteString :=
  hGetContentsN Data.ByteString.Lazy.Internal.defaultChunkSize.

Definition hGet
   : GHC.IO.Handle.Types.Handle ->
     GHC.Num.Int -> GHC.Types.IO Data.ByteString.Lazy.Internal.ByteString :=
  hGetN Data.ByteString.Lazy.Internal.defaultChunkSize.

Definition hGetNonBlocking
   : GHC.IO.Handle.Types.Handle ->
     GHC.Num.Int -> GHC.Types.IO Data.ByteString.Lazy.Internal.ByteString :=
  hGetNonBlockingN Data.ByteString.Lazy.Internal.defaultChunkSize.

Definition readFile
   : GHC.Base.String -> GHC.Types.IO Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    GHC.IO.Handle.FD.openBinaryFile f GHC.IO.IOMode.ReadMode GHC.Base.>>=
    hGetContents.

Definition hPut
   : GHC.IO.Handle.Types.Handle ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Types.IO unit :=
  fun h =>
    Data.ByteString.Lazy.Internal.foldrChunks (fun c rest =>
                                                 Data.ByteString.hPut h c GHC.Base.>> rest) (GHC.Base.return_ tt).

Definition modifyFile
   : GHC.IO.IOMode.IOMode ->
     GHC.Base.String ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Types.IO unit :=
  fun mode f txt =>
    System.IO.withBinaryFile f mode (fun arg_0__ => hPut arg_0__ txt).

Definition writeFile
   : GHC.Base.String ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Types.IO unit :=
  modifyFile GHC.IO.IOMode.WriteMode.

Definition appendFile
   : GHC.Base.String ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Types.IO unit :=
  modifyFile GHC.IO.IOMode.AppendMode.

Definition getContents
   : GHC.Types.IO Data.ByteString.Lazy.Internal.ByteString :=
  hGetContents GHC.IO.Handle.FD.stdin.

Fixpoint hPutNonBlocking (arg_0__ : GHC.IO.Handle.Types.Handle) (arg_1__
                           : Data.ByteString.Lazy.Internal.ByteString) : GHC.Types.IO
                                                                         Data.ByteString.Lazy.Internal.ByteString
  := match arg_0__, arg_1__ with
     | _, Data.ByteString.Lazy.Internal.Empty =>
         GHC.Base.return_ Data.ByteString.Lazy.Internal.Empty
     | h, (Data.ByteString.Lazy.Internal.Chunk c cs as bs) =>
         Data.ByteString.hPutNonBlocking h c GHC.Base.>>=
         (fun c' =>
            let scrut_3__ := Data.ByteString.length c' in
            let 'l' := scrut_3__ in
            if l' GHC.Base.== Data.ByteString.length c : bool then hPutNonBlocking h cs else
            let 'num_4__ := scrut_3__ in
            if num_4__ GHC.Base.== #0 : bool then GHC.Base.return_ bs else
            GHC.Base.return_ (Data.ByteString.Lazy.Internal.Chunk c' cs))
     end.

Definition hPutStr
   : GHC.IO.Handle.Types.Handle ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Types.IO unit :=
  hPut.

Definition putStr
   : Data.ByteString.Lazy.Internal.ByteString -> GHC.Types.IO unit :=
  hPut GHC.IO.Handle.FD.stdout.

Definition interact
   : (Data.ByteString.Lazy.Internal.ByteString ->
      Data.ByteString.Lazy.Internal.ByteString) ->
     GHC.Types.IO unit :=
  fun transformer => (putStr GHC.Base.∘ transformer) GHC.Base.=<< getContents.

Module Notations.
Notation "'_Data.ByteString.Lazy.!?_'" := (op_znz3fU__).
Infix "Data.ByteString.Lazy.!?" := (_!?_) (at level 99).
End Notations.

(* External variables:
     Eq Gt Lt None Some Type andb bool comparison cons false list negb nil op_zt__
     option orb pair true tt unit Coq.Init.Datatypes.app Data.Bifunctor.first
     Data.ByteString.all Data.ByteString.any Data.ByteString.breakEnd
     Data.ByteString.cons_ Data.ByteString.copy Data.ByteString.count
     Data.ByteString.drop Data.ByteString.dropEnd Data.ByteString.dropWhileEnd
     Data.ByteString.elemIndex Data.ByteString.elemIndices Data.ByteString.filter
     Data.ByteString.find Data.ByteString.findIndex Data.ByteString.findIndexEnd
     Data.ByteString.findIndices Data.ByteString.foldl Data.ByteString.foldl'
     Data.ByteString.foldr Data.ByteString.foldr' Data.ByteString.foldr1
     Data.ByteString.foldr1' Data.ByteString.hGet Data.ByteString.hGetNonBlocking
     Data.ByteString.hPut Data.ByteString.hPutNonBlocking Data.ByteString.inits
     Data.ByteString.intersperse Data.ByteString.last Data.ByteString.length
     Data.ByteString.map Data.ByteString.mapAccumL Data.ByteString.mapAccumR
     Data.ByteString.maximum Data.ByteString.minimum Data.ByteString.null
     Data.ByteString.pack Data.ByteString.packZipWith Data.ByteString.partition
     Data.ByteString.replicate Data.ByteString.reverse Data.ByteString.singleton
     Data.ByteString.split Data.ByteString.splitAt Data.ByteString.splitWith
     Data.ByteString.stripPrefix Data.ByteString.take Data.ByteString.takeEnd
     Data.ByteString.takeWhileEnd Data.ByteString.unfoldrN
     Data.ByteString.Internal.BS Data.ByteString.Internal.ByteString
     Data.ByteString.Internal.c_intersperse
     Data.ByteString.Internal.findIndexOrLength Data.ByteString.Internal.unsafeCreate
     Data.ByteString.Internal.unsafeWithForeignPtr
     Data.ByteString.Lazy.Internal.ByteString Data.ByteString.Lazy.Internal.Chunk
     Data.ByteString.Lazy.Internal.Empty Data.ByteString.Lazy.Internal.chunk
     Data.ByteString.Lazy.Internal.defaultChunkSize
     Data.ByteString.Lazy.Internal.foldlChunks
     Data.ByteString.Lazy.Internal.foldrChunks
     Data.ByteString.Lazy.Internal.fromStrict Data.ByteString.Lazy.Internal.packBytes
     Data.ByteString.Lazy.Internal.smallChunkSize
     Data.ByteString.Lazy.Internal.unpackBytes
     Data.ByteString.Lazy.Internal.Deque.Deque
     Data.ByteString.Lazy.Internal.Deque.byteLength
     Data.ByteString.Lazy.Internal.Deque.empty
     Data.ByteString.Lazy.Internal.Deque.front
     Data.ByteString.Lazy.Internal.Deque.popFront
     Data.ByteString.Lazy.Internal.Deque.popRear
     Data.ByteString.Lazy.Internal.Deque.rear
     Data.ByteString.Lazy.Internal.Deque.snoc Data.ByteString.Unsafe.unsafeDrop
     Data.ByteString.Unsafe.unsafeHead Data.ByteString.Unsafe.unsafeIndex
     Data.ByteString.Unsafe.unsafeInit Data.ByteString.Unsafe.unsafeLast
     Data.ByteString.Unsafe.unsafeTail Data.ByteString.Unsafe.unsafeTake
     Data.Foldable.foldl Data.Foldable.foldl' Data.Foldable.foldr
     Data.Functor.op_zlzdzg__ Data.OldList.intersperse Data.OldList.transpose
     Data.Tuple.fst Data.Tuple.snd Data.Tuple.uncurry Foreign.Storable.poke
     GHC.Base.String GHC.Base.compare GHC.Base.flip GHC.Base.fmap GHC.Base.map
     GHC.Base.mappend GHC.Base.max GHC.Base.mconcat GHC.Base.min GHC.Base.mplus
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zezlzl__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Base.return_ GHC.Err.error
     GHC.Err.patternFailure GHC.IO.Exception.ioError GHC.IO.Handle.FD.openBinaryFile
     GHC.IO.Handle.FD.stdin GHC.IO.Handle.FD.stdout GHC.IO.Handle.Types.Handle
     GHC.IO.IOMode.AppendMode GHC.IO.IOMode.IOMode GHC.IO.IOMode.ReadMode
     GHC.IO.IOMode.WriteMode GHC.Int.Int64 GHC.List.tail GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__
     GHC.Ptr.plusPtr GHC.Real.fromIntegral GHC.Real.quotRem GHC.Show.show
     GHC.Show.showsPrec GHC.Tuple.pair2 GHC.Types.IO GHC.Word.Word8
     System.IO.withBinaryFile System.IO.Error.illegalOperationErrorType
     System.IO.Error.mkIOError
*)
