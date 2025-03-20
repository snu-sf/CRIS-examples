Require Import CRIS.

Module CtxHdr.

  Definition mn := "Ctx".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".
  Definition input := fn "input".

End CtxHdr.
