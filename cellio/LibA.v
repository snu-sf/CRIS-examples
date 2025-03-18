Require Import CRIS.
Require Import MainHeader CellioHeader LibHeader.

Set Implicit Arguments.

Module LibName.

  Definition mn := "Lib".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".
  Definition input := fn "input".

End LibName.


Module LibAS.
Section LibAS.
  Context `{Σ: GRA}.

  Definition spc: alist string fspec :=
    Seal.sealing CRIS [(LibName.foo, fspec_trivial); (LibName.input, fspec_trivial)].
  
  Lemma spc_nodup: List.NoDup (List.map fst spc).
  Proof.
    unfold spc. unseal CRIS. prove_nodup.
  Qed.

End LibAS. End LibAS.
