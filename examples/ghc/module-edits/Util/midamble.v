(* HasDebugCallStack is a type alias for HasCallStack in GHC.
   We define it as a trivial typeclass so references in other modules compile. *)
Class HasDebugCallStack := {}.
#[global] Instance hasDebugCallStack : HasDebugCallStack := {}.
