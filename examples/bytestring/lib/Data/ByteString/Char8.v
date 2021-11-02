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
Require Data.ByteString.Unsafe.
Require Data.Functor.
Require Data.OldList.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Char.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Require GHC.Unicode.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Real.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition singleton : GHC.Char.Char -> Data.ByteString.Internal.ByteString :=
  Data.ByteString.singleton GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition pack : GHC.Base.String -> Data.ByteString.Internal.ByteString :=
  Data.ByteString.Internal.packChars.

Definition unpack : Data.ByteString.Internal.ByteString -> list GHC.Char.Char :=
  Data.ByteString.Internal.unpackChars.

Definition cons_
   : GHC.Char.Char ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  Data.ByteString.cons_ GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition snoc
   : Data.ByteString.Internal.ByteString ->
     GHC.Char.Char -> Data.ByteString.Internal.ByteString :=
  fun p => Data.ByteString.snoc p GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition uncons
   : Data.ByteString.Internal.ByteString ->
     option (GHC.Char.Char * Data.ByteString.Internal.ByteString)%type :=
  fun bs =>
    match Data.ByteString.uncons bs with
    | None => None
    | Some (pair w bs') => Some (pair (Data.ByteString.Internal.w2c w) bs')
    end.

Definition unsnoc
   : Data.ByteString.Internal.ByteString ->
     option (Data.ByteString.Internal.ByteString * GHC.Char.Char)%type :=
  fun bs =>
    match Data.ByteString.unsnoc bs with
    | None => None
    | Some (pair bs' w) => Some (pair bs' (Data.ByteString.Internal.w2c w))
    end.

Definition head : Data.ByteString.Internal.ByteString -> GHC.Char.Char :=
  Data.ByteString.Internal.w2c GHC.Base.∘ Data.ByteString.head.

Definition last : Data.ByteString.Internal.ByteString -> GHC.Char.Char :=
  Data.ByteString.Internal.w2c GHC.Base.∘ Data.ByteString.last.

Definition map
   : (GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f =>
    Data.ByteString.map (Data.ByteString.Internal.c2w GHC.Base.∘
                         (f GHC.Base.∘ Data.ByteString.Internal.w2c)).

Definition intersperse
   : GHC.Char.Char ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  Data.ByteString.intersperse GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition foldl {a : Type}
   : (a -> GHC.Char.Char -> a) -> a -> Data.ByteString.Internal.ByteString -> a :=
  fun f =>
    Data.ByteString.foldl (fun a c => f a (Data.ByteString.Internal.w2c c)).

Definition foldl' {a : Type}
   : (a -> GHC.Char.Char -> a) -> a -> Data.ByteString.Internal.ByteString -> a :=
  fun f =>
    Data.ByteString.foldl' (fun a c => f a (Data.ByteString.Internal.w2c c)).

Definition foldr {a : Type}
   : (GHC.Char.Char -> a -> a) -> a -> Data.ByteString.Internal.ByteString -> a :=
  fun f => Data.ByteString.foldr (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition foldr' {a : Type}
   : (GHC.Char.Char -> a -> a) -> a -> Data.ByteString.Internal.ByteString -> a :=
  fun f => Data.ByteString.foldr' (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition foldl1
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Internal.ByteString -> GHC.Char.Char :=
  fun f ps =>
    Data.ByteString.Internal.w2c (Data.ByteString.foldl1 (fun x y =>
                                                            Data.ByteString.Internal.c2w (f
                                                                                          (Data.ByteString.Internal.w2c
                                                                                           x)
                                                                                          (Data.ByteString.Internal.w2c
                                                                                           y))) ps).

Definition foldl1'
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Internal.ByteString -> GHC.Char.Char :=
  fun f ps =>
    Data.ByteString.Internal.w2c (Data.ByteString.foldl1' (fun x y =>
                                                             Data.ByteString.Internal.c2w (f
                                                                                           (Data.ByteString.Internal.w2c
                                                                                            x)
                                                                                           (Data.ByteString.Internal.w2c
                                                                                            y))) ps).

Definition foldr1
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Internal.ByteString -> GHC.Char.Char :=
  fun f ps =>
    Data.ByteString.Internal.w2c (Data.ByteString.foldr1 (fun x y =>
                                                            Data.ByteString.Internal.c2w (f
                                                                                          (Data.ByteString.Internal.w2c
                                                                                           x)
                                                                                          (Data.ByteString.Internal.w2c
                                                                                           y))) ps).

Definition foldr1'
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Internal.ByteString -> GHC.Char.Char :=
  fun f ps =>
    Data.ByteString.Internal.w2c (Data.ByteString.foldr1' (fun x y =>
                                                             Data.ByteString.Internal.c2w (f
                                                                                           (Data.ByteString.Internal.w2c
                                                                                            x)
                                                                                           (Data.ByteString.Internal.w2c
                                                                                            y))) ps).

Definition concatMap
   : (GHC.Char.Char -> Data.ByteString.Internal.ByteString) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f => Data.ByteString.concatMap (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition any
   : (GHC.Char.Char -> bool) -> Data.ByteString.Internal.ByteString -> bool :=
  fun f => Data.ByteString.any (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition all
   : (GHC.Char.Char -> bool) -> Data.ByteString.Internal.ByteString -> bool :=
  fun f => Data.ByteString.all (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition maximum : Data.ByteString.Internal.ByteString -> GHC.Char.Char :=
  Data.ByteString.Internal.w2c GHC.Base.∘ Data.ByteString.maximum.

Definition minimum : Data.ByteString.Internal.ByteString -> GHC.Char.Char :=
  Data.ByteString.Internal.w2c GHC.Base.∘ Data.ByteString.minimum.

Definition mapAccumL {acc : Type}
   : (acc -> GHC.Char.Char -> (acc * GHC.Char.Char)%type) ->
     acc ->
     Data.ByteString.Internal.ByteString ->
     (acc * Data.ByteString.Internal.ByteString)%type :=
  fun f =>
    Data.ByteString.mapAccumL (fun acc w =>
                                 let 'pair acc' c := f acc (Data.ByteString.Internal.w2c w) in
                                 pair acc' (Data.ByteString.Internal.c2w c)).

Definition mapAccumR {acc : Type}
   : (acc -> GHC.Char.Char -> (acc * GHC.Char.Char)%type) ->
     acc ->
     Data.ByteString.Internal.ByteString ->
     (acc * Data.ByteString.Internal.ByteString)%type :=
  fun f =>
    Data.ByteString.mapAccumR (fun acc w =>
                                 let 'pair acc' c := f acc (Data.ByteString.Internal.w2c w) in
                                 pair acc' (Data.ByteString.Internal.c2w c)).

Definition scanl
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     GHC.Char.Char ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f z =>
    Data.ByteString.scanl (fun a b =>
                             Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c a)
                                                           (Data.ByteString.Internal.w2c b)))
    (Data.ByteString.Internal.c2w z).

Definition scanl1
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f =>
    Data.ByteString.scanl1 (fun a b =>
                              Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c a)
                                                            (Data.ByteString.Internal.w2c b))).

Definition scanr
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     GHC.Char.Char ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f z =>
    Data.ByteString.scanr (fun a b =>
                             Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c a)
                                                           (Data.ByteString.Internal.w2c b)))
    (Data.ByteString.Internal.c2w z).

Definition scanr1
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f =>
    Data.ByteString.scanr1 (fun a b =>
                              Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c a)
                                                            (Data.ByteString.Internal.w2c b))).

Definition replicate
   : GHC.Num.Int -> GHC.Char.Char -> Data.ByteString.Internal.ByteString :=
  fun n => Data.ByteString.replicate n GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition unfoldr {a : Type}
   : (a -> option (GHC.Char.Char * a)%type) ->
     a -> Data.ByteString.Internal.ByteString :=
  fun f =>
    let k := fun '(pair i j) => pair (Data.ByteString.Internal.c2w i) j in
    Data.ByteString.unfoldr (GHC.Base.fmap k GHC.Base.∘ f).

Definition unfoldrN {a : Type}
   : GHC.Num.Int ->
     (a -> option (GHC.Char.Char * a)%type) ->
     a -> (Data.ByteString.Internal.ByteString * option a)%type :=
  fun n f =>
    let k := fun '(pair i j) => pair (Data.ByteString.Internal.c2w i) j in
    Data.ByteString.unfoldrN n ((fun arg_3__ => GHC.Base.fmap k arg_3__) GHC.Base.∘
                                f).

Definition takeWhile
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f => Data.ByteString.takeWhile (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition takeWhileEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f =>
    Data.ByteString.takeWhileEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition dropWhile
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f => Data.ByteString.dropWhile (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition dropWhileEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f =>
    Data.ByteString.dropWhileEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition break
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun f => Data.ByteString.break (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition elemIndex
   : GHC.Char.Char -> Data.ByteString.Internal.ByteString -> option GHC.Num.Int :=
  Data.ByteString.elemIndex GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition breakChar
   : GHC.Char.Char ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun c p =>
    match elemIndex c p with
    | None => pair p Data.ByteString.empty
    | Some n =>
        pair (Data.ByteString.Unsafe.unsafeTake n p) (Data.ByteString.Unsafe.unsafeDrop
              n p)
    end.

Definition span
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun f => Data.ByteString.span (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition spanEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun f => Data.ByteString.spanEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition breakEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun f => Data.ByteString.breakEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition split
   : GHC.Char.Char ->
     Data.ByteString.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString :=
  Data.ByteString.split GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition splitWith
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString :=
  fun f => Data.ByteString.splitWith (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition groupBy
   : (GHC.Char.Char -> GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString :=
  fun k =>
    Data.ByteString.groupBy (fun a b =>
                               k (Data.ByteString.Internal.w2c a) (Data.ByteString.Internal.w2c b)).

Definition index
   : Data.ByteString.Internal.ByteString -> GHC.Num.Int -> GHC.Char.Char :=
  (fun arg_0__ => Data.ByteString.Internal.w2c GHC.Base.∘ arg_0__) GHC.Base.∘
  Data.ByteString.index.

Definition indexMaybe
   : Data.ByteString.Internal.ByteString -> GHC.Num.Int -> option GHC.Char.Char :=
  (fun arg_0__ => GHC.Base.fmap Data.ByteString.Internal.w2c GHC.Base.∘ arg_0__)
  GHC.Base.∘
  Data.ByteString.indexMaybe.

Definition op_znz3fU__
   : Data.ByteString.Internal.ByteString -> GHC.Num.Int -> option GHC.Char.Char :=
  indexMaybe.

Notation "'_!?_'" := (op_znz3fU__).

Infix "!?" := (_!?_) (at level 99).

Definition elemIndexEnd
   : GHC.Char.Char -> Data.ByteString.Internal.ByteString -> option GHC.Num.Int :=
  Data.ByteString.elemIndexEnd GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition elemIndices
   : GHC.Char.Char -> Data.ByteString.Internal.ByteString -> list GHC.Num.Int :=
  Data.ByteString.elemIndices GHC.Base.∘ Data.ByteString.Internal.c2w.

Definition findIndex
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString -> option GHC.Num.Int :=
  fun f => Data.ByteString.findIndex (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition findIndexEnd
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString -> option GHC.Num.Int :=
  fun f =>
    Data.ByteString.findIndexEnd (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition findIndices
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString -> list GHC.Num.Int :=
  fun f =>
    Data.ByteString.findIndices (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition count
   : GHC.Char.Char -> Data.ByteString.Internal.ByteString -> GHC.Num.Int :=
  fun c => Data.ByteString.count (Data.ByteString.Internal.c2w c).

Definition elem
   : GHC.Char.Char -> Data.ByteString.Internal.ByteString -> bool :=
  fun c => Data.ByteString.elem (Data.ByteString.Internal.c2w c).

Definition notElem
   : GHC.Char.Char -> Data.ByteString.Internal.ByteString -> bool :=
  fun c => Data.ByteString.notElem (Data.ByteString.Internal.c2w c).

Definition filter
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f => Data.ByteString.filter (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition partition
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun f => Data.ByteString.partition (f GHC.Base.∘ Data.ByteString.Internal.w2c).

Definition find
   : (GHC.Char.Char -> bool) ->
     Data.ByteString.Internal.ByteString -> option GHC.Char.Char :=
  fun f ps =>
    GHC.Base.fmap Data.ByteString.Internal.w2c (Data.ByteString.find (f GHC.Base.∘
                                                                      Data.ByteString.Internal.w2c) ps).

Fixpoint zip (ps qs : Data.ByteString.Internal.ByteString) : list (GHC.Char.Char
                                                                   *
                                                                   GHC.Char.Char)%type
  := match uncons ps with
     | None => nil
     | Some (pair psH psT) =>
         match uncons qs with
         | None => nil
         | Some (pair qsH qsT) => cons (pair psH qsH) (zip psT qsT)
         end
     end.

Definition zipWith {a : Type}
   : (GHC.Char.Char -> GHC.Char.Char -> a) ->
     Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString -> list a :=
  fun f =>
    Data.ByteString.zipWith ((fun arg_0__ =>
                                arg_0__ GHC.Base.∘ Data.ByteString.Internal.w2c) GHC.Base.∘
                             (f GHC.Base.∘ Data.ByteString.Internal.w2c)).

Definition packZipWith
   : (GHC.Char.Char -> GHC.Char.Char -> GHC.Char.Char) ->
     Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun f =>
    let f' :=
      fun c1 c2 =>
        Data.ByteString.Internal.c2w (f (Data.ByteString.Internal.w2c c1)
                                        (Data.ByteString.Internal.w2c c2)) in
    Data.ByteString.packZipWith f'.

Definition unzip
   : list (GHC.Char.Char * GHC.Char.Char)%type ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun ls =>
    pair (pack (GHC.Base.map Data.Tuple.fst ls)) (pack (GHC.Base.map Data.Tuple.snd
                                                        ls)).

Definition unsafeHead : Data.ByteString.Internal.ByteString -> GHC.Char.Char :=
  Data.ByteString.Internal.w2c GHC.Base.∘ Data.ByteString.Unsafe.unsafeHead.

Fixpoint firstspace (ptr : GHC.Ptr.Ptr GHC.Word.Word8) (n m : GHC.Num.Int)
  : GHC.Types.IO GHC.Num.Int
  := if n GHC.Base.>= m : bool then GHC.Base.return_ n else
     Foreign.Storable.peekByteOff ptr n GHC.Base.>>=
     (fun w =>
        if (negb GHC.Base.∘ Data.ByteString.Internal.isSpaceWord8) w : bool
        then firstspace ptr (n GHC.Num.+ #1) m
        else GHC.Base.return_ n).

Definition breakSpace
   : Data.ByteString.Internal.ByteString ->
     (Data.ByteString.Internal.ByteString *
      Data.ByteString.Internal.ByteString)%type :=
  fun '(Data.ByteString.Internal.BS x l) =>
    Data.ByteString.Internal.accursedUnutterablePerformIO
    (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                      firstspace p #0 l GHC.Base.>>=
                                                      (fun i =>
                                                         GHC.Base.return_ (if i GHC.Base.== #0 : bool
                                                                           then pair Data.ByteString.empty
                                                                                     (Data.ByteString.Internal.BS x
                                                                                      l) else
                                                                           if i GHC.Base.== l : bool
                                                                           then pair (Data.ByteString.Internal.BS x l)
                                                                                     Data.ByteString.empty else
                                                                           pair (Data.ByteString.Internal.BS x i)
                                                                                (Data.ByteString.Internal.BS
                                                                                 (GHC.ForeignPtr.plusForeignPtr x i) (l
                                                                                                                      GHC.Num.-
                                                                                                                      i)))))).

Fixpoint firstnonspace (ptr : GHC.Ptr.Ptr GHC.Word.Word8) (n m : GHC.Num.Int)
  : GHC.Types.IO GHC.Num.Int
  := if n GHC.Base.>= m : bool then GHC.Base.return_ n else
     Foreign.Storable.peekElemOff ptr n GHC.Base.>>=
     (fun w =>
        if Data.ByteString.Internal.isSpaceWord8 w : bool
        then firstnonspace ptr (n GHC.Num.+ #1) m
        else GHC.Base.return_ n).

Definition dropSpace
   : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  fun '(Data.ByteString.Internal.BS x l) =>
    Data.ByteString.Internal.accursedUnutterablePerformIO
    (Data.ByteString.Internal.unsafeWithForeignPtr x (fun p =>
                                                      firstnonspace p #0 l GHC.Base.>>=
                                                      (fun i =>
                                                         GHC.Base.return_ (if i GHC.Base.== l : bool
                                                                           then Data.ByteString.empty
                                                                           else Data.ByteString.Internal.BS
                                                                                (GHC.ForeignPtr.plusForeignPtr x i) (l
                                                                                                                     GHC.Num.-
                                                                                                                     i))))).

Definition strip
   : Data.ByteString.Internal.ByteString -> Data.ByteString.Internal.ByteString :=
  dropWhile GHC.Unicode.isSpace GHC.Base.∘ dropWhileEnd GHC.Unicode.isSpace.

Fixpoint lines (ps : Data.ByteString.Internal.ByteString) : list
                                                            Data.ByteString.Internal.ByteString
  := let search := elemIndex (GHC.Char.hs_char__ "") in
     if Data.ByteString.null ps : bool then nil else
     match search ps with
     | None => cons ps nil
     | Some n =>
         cons (Data.ByteString.take n ps) (lines (Data.ByteString.drop (n GHC.Num.+ #1)
                                                  ps))
     end.

Definition unlines
   : list Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => Data.ByteString.empty
    | ss =>
        let nl := singleton (GHC.Char.hs_char__ "") in
        Data.ByteString.append (Data.ByteString.concat (Data.OldList.intersperse nl ss))
                               nl
    end.

Definition words
   : Data.ByteString.Internal.ByteString ->
     list Data.ByteString.Internal.ByteString :=
  GHC.List.filter (negb GHC.Base.∘ Data.ByteString.null) GHC.Base.∘
  Data.ByteString.splitWith Data.ByteString.Internal.isSpaceWord8.

Definition unwords
   : list Data.ByteString.Internal.ByteString ->
     Data.ByteString.Internal.ByteString :=
  Data.ByteString.intercalate (singleton (GHC.Char.hs_char__ " ")).

Definition readInt
   : Data.ByteString.Internal.ByteString ->
     option (GHC.Num.Int * Data.ByteString.Internal.ByteString)%type :=
  fun bs =>
    let readDec :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | positive, Data.ByteString.Internal.BS fp len =>
            let w2int :=
              fun n =>
                if positive : bool then GHC.Real.fromIntegral n else
                GHC.Num.negate (GHC.Real.fromIntegral n) in
            let result :=
              fun nbytes acc str =>
                if nbytes GHC.Base.> #0 : bool then let i := w2int acc in Some (pair i str) else
                None in
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
                                       then go (GHC.Ptr.plusPtr p #1) (b GHC.Num.+ #1) ((a GHC.Num.* #10) GHC.Num.+ d)
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
                                                                let 'pair (pair n a) inRange := arg_17__ in
                                                                if inRange : bool
                                                                then if n GHC.Base.< len : bool
                                                                     then let rest :=
                                                                            Data.ByteString.Internal.BS
                                                                            (GHC.ForeignPtr.plusForeignPtr fp n) (len
                                                                                                                  GHC.Num.-
                                                                                                                  n) in
                                                                          GHC.Base.return_ (result n a rest)
                                                                     else GHC.Base.return_ (result n a
                                                                                                   Data.ByteString.empty)
                                                                else GHC.Base.return_ None in
                                                              (if positive : bool
                                                               then digits Data.ByteString.Internal.intmaxQuot10
                                                                    Data.ByteString.Internal.intmaxRem10 end ptr #0 #0
                                                               else digits Data.ByteString.Internal.intminQuot10
                                                                    Data.ByteString.Internal.intminRem10 end ptr #0 #0)
                                                              GHC.Base.>>=
                                                              cont_16__))
        end in
    match Data.ByteString.uncons bs with
    | Some (pair w rest) =>
        if (w GHC.Num.- #48) GHC.Base.<= #9 : bool then readDec true bs else
        if w GHC.Base.== #45 : bool then readDec false rest else
        if w GHC.Base.== #43 : bool then readDec true rest else
        None
    | _ => None
    end.

Definition readInteger
   : Data.ByteString.Internal.ByteString ->
     option (GHC.Integer.Type.Integer * Data.ByteString.Internal.ByteString)%type :=
  fun as_ =>
    let fix combine2 arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | b, cons n (cons m ns) =>
             let t := (m GHC.Num.* b) GHC.Num.+ n in cons t (combine2 b ns)
         | _, ns => ns
         end in
    let fix combine1 arg_5__ arg_6__
      := match arg_5__, arg_6__ with
         | _, cons n nil => n
         | b, ns => combine1 (b GHC.Num.* b) (combine2 b ns)
         end in
    let combine :=
      fun arg_9__ arg_10__ arg_11__ arg_12__ =>
        match arg_9__, arg_10__, arg_11__, arg_12__ with
        | _, acc, nil, ps => pair (GHC.Real.toInteger acc) ps
        | d, acc, ns, ps =>
            pair (((#10 GHC.Real.^ d) GHC.Num.* combine1 #1000000000 ns) GHC.Num.+
                  GHC.Real.toInteger acc) ps
        end in
    let loop
     : GHC.Num.Int ->
       GHC.Num.Int ->
       list GHC.Integer.Type.Integer ->
       Data.ByteString.Internal.ByteString ->
       (GHC.Integer.Type.Integer * Data.ByteString.Internal.ByteString)%type :=
      fix loop (d acc : GHC.Num.Int) (ns : list GHC.Integer.Type.Integer) (ps
                 : Data.ByteString.Internal.ByteString) : (GHC.Integer.Type.Integer *
                                                           Data.ByteString.Internal.ByteString)%type
        := if Data.ByteString.null ps : bool
           then combine d acc ns Data.ByteString.empty else
           let 'w := Data.ByteString.Unsafe.unsafeHead ps in
           if andb (w GHC.Base.>= #48) (w GHC.Base.<= #57) : bool
           then if d GHC.Base.== #9 : bool
                then loop #1 (GHC.Real.fromIntegral w GHC.Num.- #48) (cons (GHC.Real.toInteger
                                                                            acc) ns) (Data.ByteString.Unsafe.unsafeTail
                                                                                      ps)
                else loop (d GHC.Num.+ #1) ((#10 GHC.Num.* acc) GHC.Num.+
                                            (GHC.Real.fromIntegral w GHC.Num.- #48)) ns
                     (Data.ByteString.Unsafe.unsafeTail ps) else
           combine d acc ns ps in
    let first :=
      fun ps =>
        if Data.ByteString.null ps : bool then None else
        let 'w := Data.ByteString.Unsafe.unsafeHead ps in
        if andb (w GHC.Base.>= #48) (w GHC.Base.<= #57) : bool
        then Some (loop #1 (GHC.Real.fromIntegral w GHC.Num.- #48) nil
                        (Data.ByteString.Unsafe.unsafeTail ps)) else
        None in
    if Data.ByteString.null as_ : bool then None else
    match unsafeHead as_ with
    | ("-"%char) =>
        first (Data.ByteString.Unsafe.unsafeTail as_) GHC.Base.>>=
        (fun '(pair n bs) => GHC.Base.return_ (pair (GHC.Num.negate n) bs))
    | ("+"%char) => first (Data.ByteString.Unsafe.unsafeTail as_)
    | _ => first as_
    end.

Definition hPutStrLn
   : GHC.IO.Handle.Types.Handle ->
     Data.ByteString.Internal.ByteString -> GHC.Types.IO unit :=
  fun h ps =>
    if Data.ByteString.length ps GHC.Base.< #1024 : bool
    then Data.ByteString.hPut h (Data.ByteString.snoc ps #10) else
    Data.ByteString.hPut h ps GHC.Base.>>
    Data.ByteString.hPut h (Data.ByteString.singleton #10).

Definition putStrLn
   : Data.ByteString.Internal.ByteString -> GHC.Types.IO unit :=
  hPutStrLn GHC.IO.Handle.FD.stdout.

Module Notations.
Notation "'_Data.ByteString.Char8.!?_'" := (op_znz3fU__).
Infix "Data.ByteString.Char8.!?" := (_!?_) (at level 99).
End Notations.

(* External variables:
     None Some Type andb bool cons false list negb nil op_zt__ option pair true unit
     Data.ByteString.all Data.ByteString.any Data.ByteString.append
     Data.ByteString.break Data.ByteString.breakEnd Data.ByteString.concat
     Data.ByteString.concatMap Data.ByteString.cons_ Data.ByteString.count
     Data.ByteString.drop Data.ByteString.dropWhile Data.ByteString.dropWhileEnd
     Data.ByteString.elem Data.ByteString.elemIndex Data.ByteString.elemIndexEnd
     Data.ByteString.elemIndices Data.ByteString.empty Data.ByteString.filter
     Data.ByteString.find Data.ByteString.findIndex Data.ByteString.findIndexEnd
     Data.ByteString.findIndices Data.ByteString.foldl Data.ByteString.foldl'
     Data.ByteString.foldl1 Data.ByteString.foldl1' Data.ByteString.foldr
     Data.ByteString.foldr' Data.ByteString.foldr1 Data.ByteString.foldr1'
     Data.ByteString.groupBy Data.ByteString.hPut Data.ByteString.head
     Data.ByteString.index Data.ByteString.indexMaybe Data.ByteString.intercalate
     Data.ByteString.intersperse Data.ByteString.last Data.ByteString.length
     Data.ByteString.map Data.ByteString.mapAccumL Data.ByteString.mapAccumR
     Data.ByteString.maximum Data.ByteString.minimum Data.ByteString.notElem
     Data.ByteString.null Data.ByteString.packZipWith Data.ByteString.partition
     Data.ByteString.replicate Data.ByteString.scanl Data.ByteString.scanl1
     Data.ByteString.scanr Data.ByteString.scanr1 Data.ByteString.singleton
     Data.ByteString.snoc Data.ByteString.span Data.ByteString.spanEnd
     Data.ByteString.split Data.ByteString.splitWith Data.ByteString.take
     Data.ByteString.takeWhile Data.ByteString.takeWhileEnd Data.ByteString.uncons
     Data.ByteString.unfoldr Data.ByteString.unfoldrN Data.ByteString.unsnoc
     Data.ByteString.zipWith Data.ByteString.Internal.BS
     Data.ByteString.Internal.ByteString
     Data.ByteString.Internal.accursedUnutterablePerformIO
     Data.ByteString.Internal.c2w Data.ByteString.Internal.intmaxQuot10
     Data.ByteString.Internal.intmaxRem10 Data.ByteString.Internal.intminQuot10
     Data.ByteString.Internal.intminRem10 Data.ByteString.Internal.isSpaceWord8
     Data.ByteString.Internal.packChars Data.ByteString.Internal.unpackChars
     Data.ByteString.Internal.unsafeWithForeignPtr Data.ByteString.Internal.w2c
     Data.ByteString.Unsafe.unsafeDrop Data.ByteString.Unsafe.unsafeHead
     Data.ByteString.Unsafe.unsafeTail Data.ByteString.Unsafe.unsafeTake
     Data.Functor.op_zlzdzg__ Data.OldList.intersperse Data.Tuple.fst Data.Tuple.snd
     Foreign.Storable.peek Foreign.Storable.peekByteOff Foreign.Storable.peekElemOff
     GHC.Base.String GHC.Base.fmap GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.return_
     GHC.Char.Char GHC.ForeignPtr.plusForeignPtr GHC.IO.Handle.FD.stdout
     GHC.IO.Handle.Types.Handle GHC.Integer.Type.Integer GHC.List.filter GHC.Num.Int
     GHC.Num.Word GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Num.op_zt__ GHC.Ptr.Ptr GHC.Ptr.plusPtr GHC.Real.fromIntegral
     GHC.Real.op_zc__ GHC.Real.toInteger GHC.Types.IO GHC.Unicode.isSpace
     GHC.Word.Word8
*)
