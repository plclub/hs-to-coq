(** This should not be here. Ideally, [GHC.Base] should automatically export
    [GHC.Maybe], but we cannot do that because [GHC.Maybe] depends on
    [GHC.Base]. *)
Require GHC.Maybe.
