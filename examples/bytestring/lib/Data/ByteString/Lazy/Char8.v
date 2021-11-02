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
Require Data.ByteString.Lazy.
Require Data.ByteString.Lazy.Internal.
Require Data.ByteString.Unsafe.
Require Data.Foldable.
Require Data.Functor.
Require Data.OldList.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Char.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Real.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition singleton
   : GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.singleton GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition pack
   : list GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.Internal.packChars.

Definition unpack
   : Data.ByteString.Lazy.Internal.ByteString -> list GHC.Char.Char :=
  Data.ByteString.Lazy.Internal.unpackChars.

Definition cons_
   : GHC.Char.Char ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.cons_ GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition cons'
   : GHC.Char.Char ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.cons' GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition snoc
   : Data.ByteString.Lazy.Internal.ByteString ->
     GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString :=
  fun p => Data.ByteString.Lazy.snoc p GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition head : Data.ByteString.Lazy.Internal.ByteString -> GHC.Char.Char :=
  Data.ByteString.Internal.w2c GHC.Base.∘ Data.ByteString.Lazy.head.

Definition uncons
   : Data.ByteString.Lazy.Internal.ByteString ->
     option (GHC.Char.Char * Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun bs =>
    match Data.ByteString.Lazy.uncons bs with
    | None => None
    | Some (pair w bs') => Some (pair (Data.ByteString.Internal.w2c w) bs')
    end.

Definition unsnoc
   : Data.ByteString.Lazy.Internal.ByteString ->
     option (Data.ByteString.Lazy.Internal.ByteString * GHC.Char.Char)%type :=
  fun bs =>
    match Data.ByteString.Lazy.unsnoc bs with
    | None => None
    | Some (pair bs' w) => Some (pair bs' (Data.ByteString.Internal.w2c w))
    end.

Definition last : Data.ByteString.Lazy.Internal.ByteString -> GHC.Char.Char :=
  Data.ByteString.Internal.w2c GHC.Base.∘ Data.ByteString.Lazy.last.

Definition map
   : (GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.map (Data.ByteString.Internal.c2w GHC.Base.∘
                              (f GHC.Base.∘ Data.ByteString.Internal.w2c)).

Definition intersperse
   : GHC.Char.Char ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.intersperse GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition foldl {a : Type}
   : (a -> GHC.Char.Char -> a) ->
     a -> Data.ByteString.Lazy.Internal.ByteString -> a :=
  fun f =>
    Data.ByteString.Lazy.foldl (fun a c => f a (Data.ByteString.Internal.w2c c)).

Definition foldl' {a : Type}
   : (a -> GHC.Char.Char -> a) ->
     a -> Data.ByteString.Lazy.Internal.ByteString -> a :=
  fun f =>
    Data.ByteString.Lazy.foldl' (fun a c => f a (Data.ByteString.Internal.w2c c)).

Definition foldr {a : Type}
   : (GHC.Char.Char -> a -> a) ->
     a -> Data.ByteString.Lazy.Internal.ByteString -> a :=
  fun f => Data.ByteString.Lazy.foldr (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition foldr' {a : Type}
   : (GHC.Char.Char -> a -> a) ->
     a -> Data.ByteString.Lazy.Internal.ByteString -> a :=
  fun f =>
    Data.ByteString.Lazy.foldr' (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition foldl1
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Char.Char :=
  fun f ps =>
    Data.ByteString.Internal.w2c (Data.ByteString.Lazy.foldl1 (fun x y =>
                                                                 Data.ByteString.Internal.c2w (f
                                                                                               (Data.ByteString.Internal.w2c
                                                                                                x)
                                                                                               (Data.ByteString.Internal.w2c
                                                                                                y))) ps).

Definition foldl1'
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Char.Char :=
  fun f ps =>
    Data.ByteString.Internal.w2c (Data.ByteString.Lazy.foldl1' (fun x y =>
                                                                  Data.ByteString.Internal.c2w (f
                                                                                                (Data.ByteString.Internal.w2c
                                                                                                 x)
                                                                                                (Data.ByteString.Internal.w2c
                                                                                                 y))) ps).

Definition foldr1
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Char.Char :=
  fun f ps =>
    Data.ByteString.Internal.w2c (Data.ByteString.Lazy.foldr1 (fun x y =>
                                                                 Data.ByteString.Internal.c2w (f
                                                                                               (Data.ByteString.Internal.w2c
                                                                                                x)
                                                                                               (Data.ByteString.Internal.w2c
                                                                                                y))) ps).

Definition foldr1'
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Char.Char :=
  fun f ps =>
    Data.ByteString.Internal.w2c (Data.ByteString.Lazy.foldr1' (fun x y =>
                                                                  Data.ByteString.Internal.c2w (f
                                                                                                (Data.ByteString.Internal.w2c
                                                                                                 x)
                                                                                                (Data.ByteString.Internal.w2c
                                                                                                 y))) ps).

Definition concatMap
   : (GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.concatMap (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition any
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun f => Data.ByteString.Lazy.any (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition all
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun f => Data.ByteString.Lazy.all (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition maximum
   : Data.ByteString.Lazy.Internal.ByteString -> GHC.Char.Char :=
  Data.ByteString.Internal.w2c GHC.Base.∘ Data.ByteString.Lazy.maximum.

Definition minimum
   : Data.ByteString.Lazy.Internal.ByteString -> GHC.Char.Char :=
  Data.ByteString.Internal.w2c GHC.Base.∘ Data.ByteString.Lazy.minimum.

Definition scanl
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     GHC.Char.Char ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f z =>
    Data.ByteString.Lazy.scanl (fun a b =>
                                  Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c a)
                                                                (Data.ByteString.Internal.w2c b)))
    (Data.ByteString.Internal.c2w z).

Definition scanl1
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let f' :=
      fun accumulator value =>
        Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c accumulator)
                                      (Data.ByteString.Internal.w2c value)) in
    Data.ByteString.Lazy.scanl1 f'.

Definition scanr
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     GHC.Char.Char ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let f' :=
      fun accumulator value =>
        Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c accumulator)
                                      (Data.ByteString.Internal.w2c value)) in
    Data.ByteString.Lazy.scanr f' GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition scanr1
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let f' :=
      fun accumulator value =>
        Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c accumulator)
                                      (Data.ByteString.Internal.w2c value)) in
    Data.ByteString.Lazy.scanr1 f'.

Definition mapAccumL {acc : Type}
   : (acc -> GHC.Char.Char -> (acc * GHC.Char.Char)%type) ->
     acc ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (acc * Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f =>
    Data.ByteString.Lazy.mapAccumL (fun a w =>
                                      let 'pair a' c := f a (Data.ByteString.Internal.w2c w) in
                                      pair a' (Data.ByteString.Internal.c2w c)).

Definition mapAccumR {acc : Type}
   : (acc -> GHC.Char.Char -> (acc * GHC.Char.Char)%type) ->
     acc ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (acc * Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f =>
    Data.ByteString.Lazy.mapAccumR (fun acc w =>
                                      let 'pair acc' c := f acc (Data.ByteString.Internal.w2c w) in
                                      pair acc' (Data.ByteString.Internal.c2w c)).

Definition iterate
   : (GHC.Char.Char -> GHC.Char.Char) ->
     GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.iterate (Data.ByteString.Internal.c2w GHC.Base.∘
                                  (f GHC.Base.∘ Data.ByteString.Internal.w2c)) GHC.Base.∘
    Data.ByteString.Internal.c2w.

Definition repeat : GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.repeat GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition replicate
   : GHC.Int.Int64 -> GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString :=
  fun w c => Data.ByteString.Lazy.replicate w (Data.ByteString.Internal.c2w c).

Definition unfoldr {a : Type}
   : (a -> option (GHC.Char.Char * a)%type) ->
     a -> Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.unfoldr (fun a =>
                                    match f a with
                                    | None => None
                                    | Some (pair c a') => Some (pair (Data.ByteString.Internal.c2w c) a')
                                    end).

Definition takeWhile
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.takeWhile (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition takeWhileEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.takeWhileEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition dropWhile
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.dropWhile (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition dropWhileEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.dropWhileEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition break
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f => Data.ByteString.Lazy.break (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition breakEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f =>
    Data.ByteString.Lazy.breakEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition span
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f => Data.ByteString.Lazy.span (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition spanEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f =>
    Data.ByteString.Lazy.spanEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition split
   : GHC.Char.Char ->
     Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.split GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition splitWith
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.splitWith (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition groupBy
   : (GHC.Char.Char -> GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  fun k =>
    Data.ByteString.Lazy.groupBy (fun a b =>
                                    k (Data.ByteString.Internal.w2c a) (Data.ByteString.Internal.w2c b)).

Definition index
   : Data.ByteString.Lazy.Internal.ByteString -> GHC.Int.Int64 -> GHC.Char.Char :=
  (fun arg_0__ => Data.ByteString.Internal.w2c GHC.Base.∘ arg_0__) GHC.Base.∘
  Data.ByteString.Lazy.index.

Definition indexMaybe
   : Data.ByteString.Lazy.Internal.ByteString ->
     GHC.Int.Int64 -> option GHC.Char.Char :=
  (fun arg_0__ => GHC.Base.fmap Data.ByteString.Internal.w2c GHC.Base.∘ arg_0__)
  GHC.Base.∘
  Data.ByteString.Lazy.indexMaybe.

Definition op_znz3fU__
   : Data.ByteString.Lazy.Internal.ByteString ->
     GHC.Int.Int64 -> option GHC.Char.Char :=
  indexMaybe.

Notation "'_!?_'" := (op_znz3fU__).

Infix "!?" := (_!?_) (at level 99).

Definition elemIndex
   : GHC.Char.Char ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Int.Int64 :=
  Data.ByteString.Lazy.elemIndex GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition elemIndexEnd
   : GHC.Char.Char ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Int.Int64 :=
  Data.ByteString.Lazy.elemIndexEnd GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition elemIndices
   : GHC.Char.Char ->
     Data.ByteString.Lazy.Internal.ByteString -> list GHC.Int.Int64 :=
  Data.ByteString.Lazy.elemIndices GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition findIndex
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Int.Int64 :=
  fun f =>
    Data.ByteString.Lazy.findIndex (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition findIndexEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Int.Int64 :=
  fun f =>
    Data.ByteString.Lazy.findIndexEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition findIndices
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> list GHC.Int.Int64 :=
  fun f =>
    Data.ByteString.Lazy.findIndices (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition count
   : GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString -> GHC.Int.Int64 :=
  fun c => Data.ByteString.Lazy.count (Data.ByteString.Internal.c2w c).

Definition elem
   : GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun c => Data.ByteString.Lazy.elem (Data.ByteString.Internal.c2w c).

Definition notElem
   : GHC.Char.Char -> Data.ByteString.Lazy.Internal.ByteString -> bool :=
  fun c => Data.ByteString.Lazy.notElem (Data.ByteString.Internal.c2w c).

Definition filter
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    Data.ByteString.Lazy.filter (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition partition
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun f =>
    Data.ByteString.Lazy.partition (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition find
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Lazy.Internal.ByteString -> option GHC.Char.Char :=
  fun f ps =>
    GHC.Base.fmap Data.ByteString.Internal.w2c (Data.ByteString.Lazy.find (f
                                                                           GHC.Base.∘
                                                                           Data.ByteString.Internal.w2c) ps).

Fixpoint zip (ps qs : Data.ByteString.Lazy.Internal.ByteString) : list
                                                                  (GHC.Char.Char * GHC.Char.Char)%type
  := if orb (Data.ByteString.Lazy.null ps) (Data.ByteString.Lazy.null qs) : bool
     then nil else
     cons (pair (head ps) (head qs)) (zip (Data.ByteString.Lazy.tail ps)
           (Data.ByteString.Lazy.tail qs)).

Definition zipWith {a : Type}
   : (GHC.Char.Char -> GHC.Char.Char -> a) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString -> list a :=
  fun f =>
    Data.ByteString.Lazy.zipWith ((fun arg_0__ =>
                                     arg_0__ GHC.Base.∘ Data.ByteString.Internal.w2c) GHC.Base.∘
                                  (f GHC.Base.∘ Data.ByteString.Internal.w2c)).

Definition packZipWith
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun f =>
    let f' :=
      fun c1 c2 =>
        Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c c1)
                                        (Data.ByteString.Internal.w2c c2)) in
    Data.ByteString.Lazy.packZipWith f'.

Definition unzip
   : list (GHC.Char.Char * GHC.Char.Char)%type ->
     (Data.ByteString.Lazy.Internal.ByteString *
      Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun ls =>
    pair (pack (GHC.Base.fmap Data.Tuple.fst ls)) (pack (GHC.Base.fmap
                                                         Data.Tuple.snd ls)).

Definition revChunks
   : list Data.ByteString.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  Data.Foldable.foldl' (GHC.Base.flip Data.ByteString.Lazy.Internal.chunk)
  Data.ByteString.Lazy.Internal.Empty.

Definition lines
   : Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty => nil
    | Data.ByteString.Lazy.Internal.Chunk c0 cs0 =>
        let loop0
         : Data.ByteString.Internal.ByteString ->
           Data.ByteString.Lazy.Internal.ByteString ->
           list Data.ByteString.Lazy.Internal.ByteString :=
          fix loop (c : Data.ByteString.Internal.ByteString) (line
                     : list Data.ByteString.Internal.ByteString) (cs
                     : Data.ByteString.Lazy.Internal.ByteString) : list
                                                                   Data.ByteString.Lazy.Internal.ByteString
            := match Data.ByteString.elemIndex (Data.ByteString.Internal.c2w
                                                (GHC.Char.hs_char__ "")) c with
               | None =>
                   match cs with
                   | Data.ByteString.Lazy.Internal.Empty =>
                       let c' := revChunks (cons c line) in cons c' nil
                   | Data.ByteString.Lazy.Internal.Chunk c' cs' => loop c' (cons c line) cs'
                   end
               | Some n =>
                   let c' := revChunks (cons (Data.ByteString.Unsafe.unsafeTake n c) line) in
                   cons c' (loop0 (Data.ByteString.Unsafe.unsafeDrop (n GHC.Num.+ #1) c) cs)
               end
          with loop0 (c : Data.ByteString.Internal.ByteString) (cs
                       : Data.ByteString.Lazy.Internal.ByteString) : list
                                                                     Data.ByteString.Lazy.Internal.ByteString
            := match Data.ByteString.elemIndex (Data.ByteString.Internal.c2w
                                                (GHC.Char.hs_char__ "")) c with
               | None =>
                   match cs with
                   | Data.ByteString.Lazy.Internal.Empty =>
                       if Data.ByteString.null c : bool then nil else
                       cons (Data.ByteString.Lazy.Internal.Chunk c Data.ByteString.Lazy.Internal.Empty)
                            nil
                   | Data.ByteString.Lazy.Internal.Chunk c' cs' =>
                       if Data.ByteString.null c : bool then loop0 c' cs' else
                       loop c' (cons c nil) cs'
                   end
               | Some n =>
                   if n GHC.Base./= #0 : bool
                   then cons (Data.ByteString.Lazy.Internal.Chunk
                              (Data.ByteString.Unsafe.unsafeTake n c) Data.ByteString.Lazy.Internal.Empty)
                             (loop0 (Data.ByteString.Unsafe.unsafeDrop (n GHC.Num.+ #1) c) cs) else
                   cons Data.ByteString.Lazy.Internal.Empty (loop0
                         (Data.ByteString.Unsafe.unsafeTail c) cs)
               end for loop0 in
        let loop
         : Data.ByteString.Internal.ByteString ->
           list Data.ByteString.Internal.ByteString ->
           Data.ByteString.Lazy.Internal.ByteString ->
           list Data.ByteString.Lazy.Internal.ByteString :=
          fix loop (c : Data.ByteString.Internal.ByteString) (line
                     : list Data.ByteString.Internal.ByteString) (cs
                     : Data.ByteString.Lazy.Internal.ByteString) : list
                                                                   Data.ByteString.Lazy.Internal.ByteString
            := match Data.ByteString.elemIndex (Data.ByteString.Internal.c2w
                                                (GHC.Char.hs_char__ "")) c with
               | None =>
                   match cs with
                   | Data.ByteString.Lazy.Internal.Empty =>
                       let c' := revChunks (cons c line) in cons c' nil
                   | Data.ByteString.Lazy.Internal.Chunk c' cs' => loop c' (cons c line) cs'
                   end
               | Some n =>
                   let c' := revChunks (cons (Data.ByteString.Unsafe.unsafeTake n c) line) in
                   cons c' (loop0 (Data.ByteString.Unsafe.unsafeDrop (n GHC.Num.+ #1) c) cs)
               end
          with loop0 (c : Data.ByteString.Internal.ByteString) (cs
                       : Data.ByteString.Lazy.Internal.ByteString) : list
                                                                     Data.ByteString.Lazy.Internal.ByteString
            := match Data.ByteString.elemIndex (Data.ByteString.Internal.c2w
                                                (GHC.Char.hs_char__ "")) c with
               | None =>
                   match cs with
                   | Data.ByteString.Lazy.Internal.Empty =>
                       if Data.ByteString.null c : bool then nil else
                       cons (Data.ByteString.Lazy.Internal.Chunk c Data.ByteString.Lazy.Internal.Empty)
                            nil
                   | Data.ByteString.Lazy.Internal.Chunk c' cs' =>
                       if Data.ByteString.null c : bool then loop0 c' cs' else
                       loop c' (cons c nil) cs'
                   end
               | Some n =>
                   if n GHC.Base./= #0 : bool
                   then cons (Data.ByteString.Lazy.Internal.Chunk
                              (Data.ByteString.Unsafe.unsafeTake n c) Data.ByteString.Lazy.Internal.Empty)
                             (loop0 (Data.ByteString.Unsafe.unsafeDrop (n GHC.Num.+ #1) c) cs) else
                   cons Data.ByteString.Lazy.Internal.Empty (loop0
                         (Data.ByteString.Unsafe.unsafeTail c) cs)
               end for loop in
        loop0 c0 cs0
    end.

Definition unlines
   : list Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => Data.ByteString.Lazy.empty
    | ss =>
        let nl := singleton (GHC.Char.hs_char__ "") in
        Data.ByteString.Lazy.append (Data.ByteString.Lazy.concat
                                     (Data.OldList.intersperse nl ss)) nl
    end.

Definition words
   : Data.ByteString.Lazy.Internal.ByteString ->
     list Data.ByteString.Lazy.Internal.ByteString :=
  GHC.List.filter (negb GHC.Base.∘ Data.ByteString.Lazy.null) GHC.Base.∘
  Data.ByteString.Lazy.splitWith Data.ByteString.Internal.isSpaceWord8.

Definition unwords
   : list Data.ByteString.Lazy.Internal.ByteString ->
     Data.ByteString.Lazy.Internal.ByteString :=
  Data.ByteString.Lazy.intercalate (singleton (GHC.Char.hs_char__ " ")).

Definition readInt
   : Data.ByteString.Lazy.Internal.ByteString ->
     option (GHC.Num.Int * Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun bs =>
    let readDec :=
      fun positive =>
        let w2int :=
          fun n =>
            if positive : bool then GHC.Real.fromIntegral n else
            GHC.Num.negate (GHC.Real.fromIntegral n) in
        let result :=
          fun nbytes acc str =>
            if nbytes GHC.Base.> #0 : bool then let i := w2int acc in Some (pair i str) else
            None in
        let accumWord :=
          fun arg_4__ arg_5__ =>
            match arg_4__, arg_5__ with
            | acc, Data.ByteString.Internal.BS fp len =>
                let digits :=
                  fun maxq maxr e ptr =>
                    let go
                     : GHC.Ptr.Ptr GHC.Word.Word8 ->
                       GHC.Num.Int ->
                       GHC.Num.Word -> GHC.Types.IO (GHC.Num.Int * GHC.Num.Word * bool)%type :=
                      fix go (arg_6__ : GHC.Ptr.Ptr GHC.Word.Word8) (arg_7__ : GHC.Num.Int) (arg_8__
                               : GHC.Num.Word) : GHC.Types.IO (GHC.Num.Int * GHC.Num.Word * bool)%type
                        := match arg_6__, arg_7__, arg_8__ with
                           | p, b, a =>
                               if p GHC.Base.== e : bool then GHC.Base.return_ (pair (pair b a) true) else
                               match arg_6__, arg_7__, arg_8__ with
                               | p, b, a =>
                                   (GHC.Real.fromIntegral Data.Functor.<$> Foreign.Storable.peek p) GHC.Base.>>=
                                   (fun w =>
                                      let d := w GHC.Num.- #48 in
                                      if d GHC.Base.> #9 : bool
                                      then GHC.Base.return_ (pair (pair b a) true)
                                      else if a GHC.Base.< maxq : bool
                                           then go (GHC.Ptr.plusPtr p #1) (b GHC.Num.+ #1) ((a GHC.Num.* #10) GHC.Num.+
                                                                                            d)
                                           else if a GHC.Base.> maxq : bool
                                                then GHC.Base.return_ (pair (pair b a) false)
                                                else if d GHC.Base.<= maxr : bool
                                                     then go (GHC.Ptr.plusPtr p #1) (b GHC.Num.+ #1) ((a GHC.Num.* #10)
                                                                                                      GHC.Num.+
                                                                                                      d)
                                                     else GHC.Base.return_ (pair (pair b a) false))
                               end
                           end in
                    go ptr in
                Data.ByteString.Internal.accursedUnutterablePerformIO
                (Data.ByteString.Internal.unsafeWithForeignPtr fp (fun ptr =>
                                                                  let end := GHC.Ptr.plusPtr ptr len in
                                                                  let cont_16__ arg_17__ :=
                                                                    let '(pair (pair _ _) _ as x) := arg_17__ in
                                                                    GHC.Base.return_ x in
                                                                  (if positive : bool
                                                                   then digits Data.ByteString.Internal.intmaxQuot10
                                                                        Data.ByteString.Internal.intmaxRem10 end ptr #0
                                                                        acc
                                                                   else digits Data.ByteString.Internal.intminQuot10
                                                                        Data.ByteString.Internal.intminRem10 end ptr #0
                                                                        acc) GHC.Base.>>=
                                                                  cont_16__))
            end in
        let fix loop nbytes acc
          := fun str =>
               match str with
               | Data.ByteString.Lazy.Internal.Empty => result nbytes acc str
               | Data.ByteString.Lazy.Internal.Chunk c cs =>
                   let scrut_22__ := Data.ByteString.length c in
                   let 'num_23__ := scrut_22__ in
                   if num_23__ GHC.Base.== #0 : bool then loop nbytes acc cs else
                   let 'l := scrut_22__ in
                   let scrut_24__ := accumWord acc c in
                   let 'pair (pair num_25__ _) inrange := scrut_24__ in
                   let j_29__ :=
                     let 'pair (pair n a) inrange := scrut_24__ in
                     if negb inrange : bool then None else
                     if n GHC.Base.< l : bool
                     then result (nbytes GHC.Num.+ n) a (Data.ByteString.Lazy.Internal.Chunk
                                                         (Data.ByteString.drop n c) cs) else
                     loop (nbytes GHC.Num.+ n) a cs in
                   let j_30__ := if num_25__ GHC.Base.== #0 : bool then None else j_29__ in
                   if num_25__ GHC.Base.== #0 : bool
                   then if inrange : bool then result nbytes acc str else
                        j_30__ else
                   j_30__
               end in
        loop #0 #0 in
    match Data.ByteString.Lazy.uncons bs with
    | Some (pair w rest) =>
        if (w GHC.Num.- #48) GHC.Base.<= #9 : bool then readDec true bs else
        if w GHC.Base.== #45 : bool then readDec false rest else
        if w GHC.Base.== #43 : bool then readDec true rest else
        None
    | _ => None
    end.

Definition readInteger
   : Data.ByteString.Lazy.Internal.ByteString ->
     option (GHC.Integer.Type.Integer *
             Data.ByteString.Lazy.Internal.ByteString)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.ByteString.Lazy.Internal.Empty => None
    | Data.ByteString.Lazy.Internal.Chunk c0 cs0 =>
        let end :=
          fun n c cs => let c' := Data.ByteString.Lazy.Internal.chunk c cs in pair n c' in
        let fix combine2 arg_3__ arg_4__
          := match arg_3__, arg_4__ with
             | b, cons n (cons m ns) =>
                 let t := n GHC.Num.+ (m GHC.Num.* b) in cons t (combine2 b ns)
             | _, ns => ns
             end in
        let fix combine1 arg_8__ arg_9__
          := match arg_8__, arg_9__ with
             | _, cons n nil => n
             | b, ns => combine1 (b GHC.Num.* b) (combine2 b ns)
             end in
        let combine :=
          fun arg_12__ arg_13__ arg_14__ arg_15__ arg_16__ =>
            match arg_12__, arg_13__, arg_14__, arg_15__, arg_16__ with
            | _, acc, nil, c, cs => end (GHC.Real.fromIntegral acc) c cs
            | d, acc, ns, c, cs =>
                end (((#10 GHC.Real.^ d) GHC.Num.* combine1 #1000000000 ns) GHC.Num.+
                     GHC.Real.fromIntegral acc) c cs
            end in
        let loop
         : GHC.Num.Int ->
           GHC.Num.Int ->
           list GHC.Integer.Type.Integer ->
           Data.ByteString.Internal.ByteString ->
           Data.ByteString.Lazy.Internal.ByteString ->
           (GHC.Integer.Type.Integer * Data.ByteString.Lazy.Internal.ByteString)%type :=
          fix loop (d acc : GHC.Num.Int) (ns : list GHC.Integer.Type.Integer) (c
                     : Data.ByteString.Internal.ByteString) (cs
                     : Data.ByteString.Lazy.Internal.ByteString) : (GHC.Integer.Type.Integer *
                                                                    Data.ByteString.Lazy.Internal.ByteString)%type
            := if Data.ByteString.null c : bool
               then match cs with
                    | Data.ByteString.Lazy.Internal.Empty => combine d acc ns c cs
                    | Data.ByteString.Lazy.Internal.Chunk c' cs' => loop d acc ns c' cs'
                    end else
               let 'w := Data.ByteString.Unsafe.unsafeHead c in
               if andb (w GHC.Base.>= #48) (w GHC.Base.<= #57) : bool
               then if d GHC.Base.< #9 : bool
                    then loop (d GHC.Num.+ #1) ((#10 GHC.Num.* acc) GHC.Num.+
                                                (GHC.Real.fromIntegral w GHC.Num.- #48)) ns
                         (Data.ByteString.Unsafe.unsafeTail c) cs
                    else loop #1 (GHC.Real.fromIntegral w GHC.Num.- #48) (cons
                                                                          (GHC.Real.fromIntegral acc) ns)
                         (Data.ByteString.Unsafe.unsafeTail c) cs else
               combine d acc ns c cs in
        let first' :=
          fun c cs =>
            let 'w := Data.ByteString.Unsafe.unsafeHead c in
            if andb (w GHC.Base.>= #48) (w GHC.Base.<= #57) : bool
            then Some (loop #1 (GHC.Real.fromIntegral w GHC.Num.- #48) nil
                            (Data.ByteString.Unsafe.unsafeTail c) cs) else
            None in
        let first :=
          fun c cs =>
            if Data.ByteString.null c : bool
            then match cs with
                 | Data.ByteString.Lazy.Internal.Empty => None
                 | Data.ByteString.Lazy.Internal.Chunk c' cs' => first' c' cs'
                 end else
            first' c cs in
        match Data.ByteString.Internal.w2c (Data.ByteString.Unsafe.unsafeHead c0) with
        | ("-"%char) =>
            first (Data.ByteString.Unsafe.unsafeTail c0) cs0 GHC.Base.>>=
            (fun '(pair n cs') => GHC.Base.return_ (pair (GHC.Num.negate n) cs'))
        | ("+"%char) => first (Data.ByteString.Unsafe.unsafeTail c0) cs0
        | _ => first c0 cs0
        end
    end.

Definition hPutStrLn
   : GHC.IO.Handle.Types.Handle ->
     Data.ByteString.Lazy.Internal.ByteString -> GHC.Types.IO unit :=
  fun h ps =>
    Data.ByteString.Lazy.hPut h ps GHC.Base.>>
    Data.ByteString.Lazy.hPut h (Data.ByteString.Lazy.singleton #10).

Definition putStrLn
   : Data.ByteString.Lazy.Internal.ByteString -> GHC.Types.IO unit :=
  hPutStrLn GHC.IO.Handle.FD.stdout.

Module Notations.
Notation "'_Data.ByteString.Lazy.Char8.!?_'" := (op_znz3fU__).
Infix "Data.ByteString.Lazy.Char8.!?" := (_!?_) (at level 99).
End Notations.

(* External variables:
     None Some Type andb bool cons false list negb nil op_zt__ option orb pair true
     unit Data.ByteString.drop Data.ByteString.elemIndex Data.ByteString.length
     Data.ByteString.null Data.ByteString.Internal.BS
     Data.ByteString.Internal.ByteString
     Data.ByteString.Internal.accursedUnutterablePerformIO
     Data.ByteString.Internal.c2w Data.ByteString.Internal.intmaxQuot10
     Data.ByteString.Internal.intmaxRem10 Data.ByteString.Internal.intminQuot10
     Data.ByteString.Internal.intminRem10 Data.ByteString.Internal.isSpaceWord8
     Data.ByteString.Internal.unsafeWithForeignPtr Data.ByteString.Internal.w2c
     Data.ByteString.Lazy.all Data.ByteString.Lazy.any Data.ByteString.Lazy.append
     Data.ByteString.Lazy.break Data.ByteString.Lazy.breakEnd
     Data.ByteString.Lazy.concat Data.ByteString.Lazy.concatMap
     Data.ByteString.Lazy.cons' Data.ByteString.Lazy.cons_ Data.ByteString.Lazy.count
     Data.ByteString.Lazy.dropWhile Data.ByteString.Lazy.dropWhileEnd
     Data.ByteString.Lazy.elem Data.ByteString.Lazy.elemIndex
     Data.ByteString.Lazy.elemIndexEnd Data.ByteString.Lazy.elemIndices
     Data.ByteString.Lazy.empty Data.ByteString.Lazy.filter Data.ByteString.Lazy.find
     Data.ByteString.Lazy.findIndex Data.ByteString.Lazy.findIndexEnd
     Data.ByteString.Lazy.findIndices Data.ByteString.Lazy.foldl
     Data.ByteString.Lazy.foldl' Data.ByteString.Lazy.foldl1
     Data.ByteString.Lazy.foldl1' Data.ByteString.Lazy.foldr
     Data.ByteString.Lazy.foldr' Data.ByteString.Lazy.foldr1
     Data.ByteString.Lazy.foldr1' Data.ByteString.Lazy.groupBy
     Data.ByteString.Lazy.hPut Data.ByteString.Lazy.head Data.ByteString.Lazy.index
     Data.ByteString.Lazy.indexMaybe Data.ByteString.Lazy.intercalate
     Data.ByteString.Lazy.intersperse Data.ByteString.Lazy.iterate
     Data.ByteString.Lazy.last Data.ByteString.Lazy.map
     Data.ByteString.Lazy.mapAccumL Data.ByteString.Lazy.mapAccumR
     Data.ByteString.Lazy.maximum Data.ByteString.Lazy.minimum
     Data.ByteString.Lazy.notElem Data.ByteString.Lazy.null
     Data.ByteString.Lazy.packZipWith Data.ByteString.Lazy.partition
     Data.ByteString.Lazy.repeat Data.ByteString.Lazy.replicate
     Data.ByteString.Lazy.scanl Data.ByteString.Lazy.scanl1
     Data.ByteString.Lazy.scanr Data.ByteString.Lazy.scanr1
     Data.ByteString.Lazy.singleton Data.ByteString.Lazy.snoc
     Data.ByteString.Lazy.span Data.ByteString.Lazy.spanEnd
     Data.ByteString.Lazy.split Data.ByteString.Lazy.splitWith
     Data.ByteString.Lazy.tail Data.ByteString.Lazy.takeWhile
     Data.ByteString.Lazy.takeWhileEnd Data.ByteString.Lazy.uncons
     Data.ByteString.Lazy.unfoldr Data.ByteString.Lazy.unsnoc
     Data.ByteString.Lazy.zipWith Data.ByteString.Lazy.Internal.ByteString
     Data.ByteString.Lazy.Internal.Chunk Data.ByteString.Lazy.Internal.Empty
     Data.ByteString.Lazy.Internal.chunk Data.ByteString.Lazy.Internal.packChars
     Data.ByteString.Lazy.Internal.unpackChars Data.ByteString.Unsafe.unsafeDrop
     Data.ByteString.Unsafe.unsafeHead Data.ByteString.Unsafe.unsafeTail
     Data.ByteString.Unsafe.unsafeTake Data.Foldable.foldl' Data.Functor.op_zlzdzg__
     Data.OldList.intersperse Data.Tuple.fst Data.Tuple.snd Foreign.Storable.peek
     GHC.Base.flip GHC.Base.fmap GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Base.return_
     GHC.Char.Char GHC.IO.Handle.FD.stdout GHC.IO.Handle.Types.Handle GHC.Int.Int64
     GHC.Integer.Type.Integer GHC.List.filter GHC.Num.Int GHC.Num.Word
     GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Num.op_zt__ GHC.Ptr.Ptr GHC.Ptr.plusPtr GHC.Real.fromIntegral
     GHC.Real.op_zc__ GHC.Types.IO GHC.Word.Word8
*)
