Require Import CRIS.
Require Import MaincbHeader CelliocbHeader CtxcbHeader.

Set Implicit Arguments.

Module CtxcbAS.
Section CtxcbAS.
  Context `{Σ: GRA}.

  Definition sp: spl_type :=
    Seal.sealing CRIS [(Some CtxcbHdr.foo, None)].
  
  Lemma sp_nodup: List.NoDup (List.map fst sp).
  Proof.
    unfold sp. unseal CRIS. prove_nodup.
  Qed.

End CtxcbAS. End CtxcbAS.
