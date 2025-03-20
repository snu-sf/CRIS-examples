Require Import CRIS.
Require Import ImpPrelude.

Module AddHdr.
  Definition mn := "Add".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition succ := fn "succ".
  Definition add := fn "add".
End AddHdr.

Module AddGEnv.
Definition t : GEnv.t :=
  [(AddHdr.succ, Gfun↑); 
   (AddHdr.add, Gfun↑)].
End AddGEnv.