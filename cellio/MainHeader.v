Require Import CRIS.

Module MainHdr.

  Definition mn := "Main".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition main := "CRIS_init".

End MainHdr.
