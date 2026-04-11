Require Import CRIS.

Module CtxHdr.

  Definition mn := "Ctx".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".
  Definition foo_t := cftyp () ().
  
  Definition input := fn "input".
  Definition input_t := cftyp () Z.

End CtxHdr.
