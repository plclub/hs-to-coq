Require Coq.Program.Tactics.
Require Lia.
Ltac prog_lia := Coq.Program.Tactics.program_simpl;simpl;Lia.lia.
