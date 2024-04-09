(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import HsToCoq.Unpeel.
Require Coq.Lists.List.

(* Converted imports: *)

Require Build.Store.
Require Coq.Lists.List.
Require Data.Foldable.
Require Data.Functor.
Require Data.Maybe.
Require Data.OldList.
Require Data.Ord.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive TraceST k r : Type := | Mk_TraceST : k -> list k -> r -> TraceST k r.

Inductive Trace k v r : Type :=
  | Mk_Trace (key : k) (depends : list (k * Build.Store.Hash v)%type) (result : r)
   : Trace k v r.

Inductive VT k v : Type :=
  | Mk_VT : list (Trace k v (Build.Store.Hash v)) -> VT k v.

Inductive Step : Type := | Mk_Step : GHC.Num.Int -> Step.

Inductive ST k v : Type :=
  | Mk_ST : list (TraceST k (Build.Store.Hash v * Step * Step)%type) -> ST k v.

Inductive DCT k v : Type := | Mk_DCT : list (Trace k v v) -> DCT k v.

Inductive CT k v : Type := | Mk_CT : list (Trace k v v) -> CT k v.

Arguments Mk_TraceST {_} {_} _ _ _.

Arguments Mk_Trace {_} {_} {_} _ _ _.

Arguments Mk_VT {_} {_} _.

Arguments Mk_ST {_} {_} _.

Arguments Mk_DCT {_} {_} _.

Arguments Mk_CT {_} {_} _.

Definition depends {k} {v} {r} (arg_0__ : Trace k v r) :=
  let 'Mk_Trace _ depends _ := arg_0__ in
  depends.

Definition key {k} {v} {r} (arg_0__ : Trace k v r) :=
  let 'Mk_Trace key _ _ := arg_0__ in
  key.

Definition result {k} {v} {r} (arg_0__ : Trace k v r) :=
  let 'Mk_Trace _ _ result := arg_0__ in
  result.

(* Midamble *)

Instance Unpeel_VT_to_TraceList {a b}
  : Unpeel (VT a b) (list (Trace a b (Build.Store.Hash b))) :=
  {| unpeel '(Mk_VT x) := x
   ; repeel l := Mk_VT l|}.


Instance Unpeel_CT_to_TraceList {a b}
  : Unpeel (CT a b) (list (Trace a b b)) :=
  {| unpeel '(Mk_CT x) := x
   ; repeel l := Mk_CT l|}.


Instance Unpeel_DCT_to_TraceList {a b}
  : Unpeel (DCT a b) (list (Trace a b b)) :=
  {| unpeel '(Mk_DCT x) := x
   ; repeel l := Mk_DCT l|}.


Instance Unpeel_ST_to_TraceList {k v}
  : Unpeel (ST k v) (list (TraceST k (Store.Hash v * Step * Step))) :=
  {| unpeel '(Mk_ST x) := x
   ; repeel l := Mk_ST l|}.

Instance Unpeel_Step_to_Int : Unpeel Step GHC.Num.Int :=
  {| unpeel '(Mk_Step x) := x
   ; repeel x := Mk_Step x |}.




(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Build.Trace.Show__Trace' *)

Local Definition Semigroup__VT_op_zlzlzgzg__ {inst_k : Type} {inst_v : Type}
   : VT inst_k inst_v -> VT inst_k inst_v -> VT inst_k inst_v :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__VT {k : Type} {v : Type}
   : GHC.Base.Semigroup (VT k v) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__VT_op_zlzlzgzg__ |}.

Local Definition Monoid__VT_mappend {inst_k : Type} {inst_v : Type}
   : VT inst_k inst_v -> VT inst_k inst_v -> VT inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Monoid__VT_mconcat {inst_k : Type} {inst_v : Type}
   : list (VT inst_k inst_v) -> VT inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__VT_mempty {inst_k : Type} {inst_v : Type}
   : VT inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mempty.

Program Instance Monoid__VT {k : Type} {v : Type} : GHC.Base.Monoid (VT k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__VT_mappend ;
           GHC.Base.mconcat__ := Monoid__VT_mconcat ;
           GHC.Base.mempty__ := Monoid__VT_mempty |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Build.Trace.Show__VT' *)

Local Definition Semigroup__CT_op_zlzlzgzg__ {inst_k : Type} {inst_v : Type}
   : CT inst_k inst_v -> CT inst_k inst_v -> CT inst_k inst_v :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__CT {k : Type} {v : Type}
   : GHC.Base.Semigroup (CT k v) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__CT_op_zlzlzgzg__ |}.

Local Definition Monoid__CT_mappend {inst_k : Type} {inst_v : Type}
   : CT inst_k inst_v -> CT inst_k inst_v -> CT inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Monoid__CT_mconcat {inst_k : Type} {inst_v : Type}
   : list (CT inst_k inst_v) -> CT inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__CT_mempty {inst_k : Type} {inst_v : Type}
   : CT inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mempty.

Program Instance Monoid__CT {k : Type} {v : Type} : GHC.Base.Monoid (CT k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__CT_mappend ;
           GHC.Base.mconcat__ := Monoid__CT_mconcat ;
           GHC.Base.mempty__ := Monoid__CT_mempty |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Build.Trace.Show__CT' *)

Local Definition Semigroup__DCT_op_zlzlzgzg__ {inst_k : Type} {inst_v : Type}
   : DCT inst_k inst_v -> DCT inst_k inst_v -> DCT inst_k inst_v :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__DCT {k : Type} {v : Type}
   : GHC.Base.Semigroup (DCT k v) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__DCT_op_zlzlzgzg__ |}.

Local Definition Monoid__DCT_mappend {inst_k : Type} {inst_v : Type}
   : DCT inst_k inst_v -> DCT inst_k inst_v -> DCT inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Monoid__DCT_mconcat {inst_k : Type} {inst_v : Type}
   : list (DCT inst_k inst_v) -> DCT inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__DCT_mempty {inst_k : Type} {inst_v : Type}
   : DCT inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mempty.

Program Instance Monoid__DCT {k : Type} {v : Type}
   : GHC.Base.Monoid (DCT k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__DCT_mappend ;
           GHC.Base.mconcat__ := Monoid__DCT_mconcat ;
           GHC.Base.mempty__ := Monoid__DCT_mempty |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Build.Trace.Show__DCT' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Build.Trace.Enum__Step' *)

Local Definition Eq___Step_op_zeze__ : Step -> Step -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Step_op_zsze__ : Step -> Step -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Step : GHC.Base.Eq_ Step :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Step_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Step_op_zsze__ |}.

Local Definition Ord__Step_op_zl__ : Step -> Step -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Step_op_zlze__ : Step -> Step -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Step_op_zg__ : Step -> Step -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Step_op_zgze__ : Step -> Step -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Step_compare : Step -> Step -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Step_max : Step -> Step -> Step :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Step_min : Step -> Step -> Step :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Step : GHC.Base.Ord Step :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Step_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Step_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Step_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Step_op_zgze__ ;
           GHC.Base.compare__ := Ord__Step_compare ;
           GHC.Base.max__ := Ord__Step_max ;
           GHC.Base.min__ := Ord__Step_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Build.Trace.Show__Step' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Build.Trace.Show__TraceST' *)

Local Definition Semigroup__ST_op_zlzlzgzg__ {inst_k : Type} {inst_v : Type}
   : ST inst_k inst_v -> ST inst_k inst_v -> ST inst_k inst_v :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__ST {k : Type} {v : Type}
   : GHC.Base.Semigroup (ST k v) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__ST_op_zlzlzgzg__ |}.

Local Definition Monoid__ST_mappend {inst_k : Type} {inst_v : Type}
   : ST inst_k inst_v -> ST inst_k inst_v -> ST inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Monoid__ST_mconcat {inst_k : Type} {inst_v : Type}
   : list (ST inst_k inst_v) -> ST inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__ST_mempty {inst_k : Type} {inst_v : Type}
   : ST inst_k inst_v :=
  GHC.Prim.coerce GHC.Base.mempty.

Program Instance Monoid__ST {k : Type} {v : Type} : GHC.Base.Monoid (ST k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__ST_mappend ;
           GHC.Base.mconcat__ := Monoid__ST_mconcat ;
           GHC.Base.mempty__ := Monoid__ST_mempty |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Build.Trace.Show__ST' *)

Local Definition Semigroup__Step_op_zlzlzgzg__ : Step -> Step -> Step :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Step a, Mk_Step b => Mk_Step (a GHC.Num.+ b)
    end.

Program Instance Semigroup__Step : GHC.Base.Semigroup Step :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Step_op_zlzlzgzg__ |}.

Local Definition Monoid__Step_mappend : Step -> Step -> Step :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Step_mempty : Step :=
  Mk_Step #0.

Local Definition Monoid__Step_mconcat : list Step -> Step :=
  GHC.Base.foldr Monoid__Step_mappend Monoid__Step_mempty.

Program Instance Monoid__Step : GHC.Base.Monoid Step :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Step_mappend ;
           GHC.Base.mconcat__ := Monoid__Step_mconcat ;
           GHC.Base.mempty__ := Monoid__Step_mempty |}.

Definition recordVT {k : Type} {v : Type}
   : k ->
     Build.Store.Hash v -> list (k * Build.Store.Hash v)%type -> VT k v -> VT k v :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | key, valueHash, deps, Mk_VT ts =>
        Mk_VT (cons (Mk_Trace key deps valueHash) ts)
    end.

Definition andM {m} `{GHC.Base.Monad m} : list (m bool) -> m bool :=
  GHC.Base.fmap Data.Foldable.and GHC.Base.∘ Data.Traversable.sequence.

Definition anyM {m} {a} `{GHC.Base.Monad m}
   : (a -> m bool) -> list a -> m bool :=
  fun f => GHC.Base.fmap Data.Foldable.or GHC.Base.∘ Data.Traversable.mapM f.

Definition verifyVT {m : Type -> Type} {k : Type} {v : Type} `{GHC.Base.Monad m}
  `{GHC.Base.Eq_ k} `{GHC.Base.Eq_ v}
   : k ->
     Build.Store.Hash v -> (k -> m (Build.Store.Hash v)) -> VT k v -> m bool :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | key, valueHash, fetchHash, Mk_VT ts =>
        let match_ :=
          fun '(Mk_Trace k deps result) =>
            if orb (k GHC.Base./= key) (result GHC.Base./= valueHash) : bool
            then GHC.Base.return_ false else
            andM (let cont_5__ arg_6__ :=
                    let 'pair k h := arg_6__ in
                    cons ((fun arg_7__ => h GHC.Base.== arg_7__) Data.Functor.<$> fetchHash k)
                         nil in
                  Coq.Lists.List.flat_map cont_5__ deps) in
        anyM match_ ts
    end.

Definition isDirtyCT {k : Type} {v : Type} `{GHC.Base.Eq_ k}
  `{Build.Store.Hashable v}
   : k -> Build.Store.Store (CT k v) k v -> bool :=
  fun key store =>
    let match_ :=
      fun '(Mk_Trace k deps result) =>
        andb (k GHC.Base.== key) (andb (result GHC.Base.==
                                        Build.Store.getValue key store) (Data.Foldable.and (let cont_1__ arg_2__ :=
                                                                                              let 'pair k h :=
                                                                                                arg_2__ in
                                                                                              cons (Build.Store.getHash
                                                                                                    k store GHC.Base.==
                                                                                                    h) nil in
                                                                                            Coq.Lists.List.flat_map
                                                                                            cont_1__ deps))) in
    let 'Mk_CT ts := Build.Store.getInfo store in
    negb (Data.Foldable.any match_ ts).

Definition recordCT {k : Type} {v : Type}
   : k -> v -> list (k * Build.Store.Hash v)%type -> CT k v -> CT k v :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | key, value, deps, Mk_CT ts => Mk_CT (cons (Mk_Trace key deps value) ts)
    end.

Definition constructCT {m : Type -> Type} {k : Type} {v : Type} `{GHC.Base.Monad
  m} `{GHC.Base.Eq_ k} `{GHC.Base.Eq_ v}
   : k -> (k -> m (Build.Store.Hash v)) -> CT k v -> m (list v) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | key, fetchHash, Mk_CT ts =>
        let match_ :=
          fun '(Mk_Trace k deps result) =>
            if k GHC.Base./= key : bool then GHC.Base.return_ None else
            andM (let cont_4__ arg_5__ :=
                    let 'pair k h := arg_5__ in
                    cons ((fun arg_6__ => h GHC.Base.== arg_6__) Data.Functor.<$> fetchHash k)
                         nil in
                  Coq.Lists.List.flat_map cont_4__ deps) GHC.Base.>>=
            (fun sameInputs =>
               GHC.Base.return_ (if sameInputs : bool then Some result else None)) in
        Data.Maybe.catMaybes Data.Functor.<$> Data.Traversable.mapM match_ ts
    end.

Definition deepDependencies {k} {v} `{GHC.Base.Eq_ k} `{Build.Store.Hashable v}
   : DCT k v -> Build.Store.Hash v -> k -> list k :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_DCT ts, valueHash, key =>
        match (let cont_3__ arg_4__ :=
                   let 'Mk_Trace k deps v := arg_4__ in
                   if k GHC.Base.== key : bool
                   then if Build.Store.hash v GHC.Base.== valueHash : bool
                        then cons (GHC.Base.map Data.Tuple.fst deps) nil else
                        nil else
                   nil in
                 Coq.Lists.List.flat_map cont_3__ ts) with
        | nil => cons key nil
        | cons deps _ => deps
        end
    end.

Definition recordDCT {k : Type} {v : Type} {m : Type -> Type} `{GHC.Base.Eq_ k}
  `{Build.Store.Hashable v} `{GHC.Base.Monad m}
   : k ->
     v -> list k -> (k -> m (Build.Store.Hash v)) -> DCT k v -> m (DCT k v) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | key, value, deps, fetchHash, (Mk_DCT ts as dct) =>
        let deepDeps :=
          Data.Foldable.concatMap (deepDependencies dct (Build.Store.hash value)) deps in
        Data.Traversable.mapM fetchHash deepDeps GHC.Base.>>=
        (fun hs =>
           GHC.Base.return_ (Mk_DCT (cons (Mk_Trace key (GHC.List.zip deepDeps hs) value)
                                          ts)))
    end.

Definition constructDCT {k : Type} {v : Type} {m : Type -> Type} `{GHC.Base.Eq_
  k} `{Build.Store.Hashable v} `{GHC.Base.Monad m}
   : k -> (k -> m (Build.Store.Hash v)) -> DCT k v -> m (list v) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | key, fetchHash, Mk_DCT ts => constructCT key fetchHash (Mk_CT ts)
    end.

Definition latestST {k} {v} `{GHC.Base.Eq_ k}
   : k -> ST k v -> option (TraceST k (Build.Store.Hash v * Step * Step)%type) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, Mk_ST ts =>
        GHC.Base.fmap Data.Tuple.snd (Data.Maybe.listToMaybe (Data.OldList.sortOn
                                                              (Data.Ord.Mk_Down GHC.Base.∘ Data.Tuple.fst)
                                                              (let cont_2__ arg_3__ :=
                                                                 let '(Mk_TraceST k2 _ (pair (pair _ step) _) as t) :=
                                                                   arg_3__ in
                                                                 if k GHC.Base.== k2 : bool
                                                                 then cons (pair step t) nil else
                                                                 nil in
                                                               Coq.Lists.List.flat_map cont_2__ ts)))
    end.

Definition recordST {v : Type} {k : Type} `{Build.Store.Hashable v}
  `{GHC.Base.Eq_ k}
   : Step -> k -> v -> list k -> ST k v -> ST k v :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | step, key, value, deps, Mk_ST ts =>
        let hv := Build.Store.hash value in
        let lastChange :=
          match latestST key (Mk_ST ts) with
          | Some (Mk_TraceST _ _ (pair (pair hv2 _) chng)) =>
              if hv2 GHC.Base.== hv : bool then chng else
              step
          | _ => step
          end in
        Mk_ST (cons (Mk_TraceST key deps (pair (pair (Build.Store.hash value) step)
                                               lastChange)) ts)
    end.

Definition verifyST {m : Type -> Type} {k : Type} {v : Type} `{GHC.Base.Monad m}
  `{GHC.Base.Eq_ k} `{Build.Store.Hashable v}
   : k -> v -> (k -> m unit) -> m (ST k v) -> m bool :=
  fun key value demand st =>
    (latestST key Data.Functor.<$> st) GHC.Base.>>=
    (fun me =>
       let j_1__ := GHC.Base.return_ false in
       match me with
       | Some (Mk_TraceST _ deps (pair (pair hv built) _)) =>
           if Build.Store.hash value GHC.Base.== hv : bool
           then Data.Foldable.mapM_ demand deps GHC.Base.>>
                (st GHC.Base.>>=
                 (fun st =>
                    GHC.Base.return_ (Data.Foldable.and (let cont_3__ arg_4__ :=
                                                           match arg_4__ with
                                                           | Some (Mk_TraceST _ _ (pair (pair _ _) chng)) =>
                                                               cons (built GHC.Base.>= chng) nil
                                                           | _ => nil
                                                           end in
                                                         Coq.Lists.List.flat_map cont_3__ (GHC.Base.map (fun arg_2__ =>
                                                                                                           latestST
                                                                                                           arg_2__ st)
                                                                                  deps))))) else
           j_1__
       | _ => j_1__
       end).

(* External variables:
     None Some Type andb bool comparison cons false list negb nil op_zt__ option orb
     pair unit Build.Store.Hash Build.Store.Hashable Build.Store.Store
     Build.Store.getHash Build.Store.getInfo Build.Store.getValue Build.Store.hash
     Coq.Lists.List.flat_map Data.Foldable.and Data.Foldable.any
     Data.Foldable.concatMap Data.Foldable.mapM_ Data.Foldable.or
     Data.Functor.op_zlzdzg__ Data.Maybe.catMaybes Data.Maybe.listToMaybe
     Data.OldList.sortOn Data.Ord.Mk_Down Data.Traversable.mapM
     Data.Traversable.sequence Data.Tuple.fst Data.Tuple.snd GHC.Base.Eq_
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.compare
     GHC.Base.compare__ GHC.Base.fmap GHC.Base.foldr GHC.Base.map GHC.Base.mappend
     GHC.Base.mappend__ GHC.Base.max GHC.Base.max__ GHC.Base.mconcat
     GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__
     GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.return_ GHC.List.zip
     GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.coerce
*)
