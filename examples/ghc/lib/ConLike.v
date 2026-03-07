(* ConLike — re-exports from Core where the type is mutually defined *)

Require Core.
Require AxiomatizedTypes.
Require BasicTypes.
Require FieldLabel.
Require GHC.Base.
Require HsSyn.
Require Name.
Require Unique.

Definition ConLike := Core.ConLike.
Definition RealDataCon := Core.RealDataCon.
Definition PatSynCon := Core.PatSynCon.

Instance Eq___ConLike : GHC.Base.Eq_ ConLike.
Proof.
Admitted.

Instance Uniquable__ConLike : Unique.Uniquable ConLike.
Proof.
Admitted.

Instance NamedThing__ConLike : Name.NamedThing ConLike.
Proof.
Admitted.

Axiom isVanillaConLike : ConLike -> bool.

Axiom eqConLike : ConLike -> ConLike -> bool.

Axiom conLikeArity : ConLike -> BasicTypes.Arity.

Axiom conLikeFieldLabels : ConLike -> list FieldLabel.FieldLabel.

Axiom conLikeInstOrigArgTys : ConLike ->
                              list AxiomatizedTypes.Type_ -> list (Core.Scaled AxiomatizedTypes.Type_).

Axiom conLikeUserTyVarBinders : ConLike -> list Core.InvisTVBinder.

Axiom conLikeExTyCoVars : ConLike -> list Core.TyCoVar.

Axiom conLikeName : ConLike -> Name.Name.

Axiom conLikeStupidTheta : ConLike -> AxiomatizedTypes.ThetaType.

Axiom conLikeHasBuilder : ConLike -> bool.

Axiom conLikeImplBangs : ConLike -> list Core.HsImplBang.

Axiom conLikeResTy : ConLike ->
                     list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom conLikeFullSig : ConLike ->
                       (list Core.TyVar * list Core.TyCoVar * list Core.EqSpec *
                        AxiomatizedTypes.ThetaType *
                        AxiomatizedTypes.ThetaType *
                        list (Core.Scaled AxiomatizedTypes.Type_) *
                        AxiomatizedTypes.Type_)%type.

Axiom conLikeFieldType : ConLike ->
                         HsSyn.FieldLabelString -> AxiomatizedTypes.Type_.

Axiom conLikesWithFields : list ConLike ->
                           list HsSyn.FieldLabelString -> (list ConLike * list ConLike)%type.

Axiom conLikeIsInfix : ConLike -> bool.
