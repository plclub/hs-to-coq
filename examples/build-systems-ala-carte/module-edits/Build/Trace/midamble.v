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
