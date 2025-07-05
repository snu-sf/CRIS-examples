Require Import CRIS.

Module CtxcbHdr.

  Definition mn := "Ctxcb".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".
  
End CtxcbHdr.
