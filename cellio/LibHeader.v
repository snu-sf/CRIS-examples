Require Import CRIS.

Module LibHdr.

  Definition mn := "Lib".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".
  Definition input := fn "input".

End LibHdr.
