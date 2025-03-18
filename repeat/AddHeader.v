Require Import CRIS.
Require Import ImpPrelude.

Module AddName.
  Definition mn := "Add".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition succ := fn "succ".
  Definition add := fn "add".
End AddName.

Module AddGEnv.
Definition t : GEnv.t :=
  [(AddName.succ, Gfun↑); 
   (AddName.add, Gfun↑)].
End AddGEnv.