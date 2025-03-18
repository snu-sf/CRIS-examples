Require Import CRIS.

Module LibName.

  Definition mn := "Lib".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".
  Definition input := fn "input".

End LibName.
