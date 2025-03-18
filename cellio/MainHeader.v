Require Import CRIS.

Module MainName.

  Definition mn := "Main".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition main := "CRIS_init".

End MainName.
