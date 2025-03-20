Require Import CRIS.
Require Import MainHeader CellioHeader CtxHeader.

Set Implicit Arguments.

Module CtxHdr.

  Definition mn := "Ctx".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".
  Definition input := fn "input".

End CtxHdr.


Module CtxAS.
Section CtxAS.
  Context `{Σ: GRA}.

  Definition spc: alist string fspec :=
    Seal.sealing CRIS [(CtxHdr.foo, fspec_trivial); (CtxHdr.input, fspec_trivial)].
  
  Lemma spc_nodup: List.NoDup (List.map fst spc).
  Proof.
    unfold spc. unseal CRIS. prove_nodup.
  Qed.

End CtxAS. End CtxAS.
