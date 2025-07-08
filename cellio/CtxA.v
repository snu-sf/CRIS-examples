Require Import CRIS.
Require Import CellioHeader CtxHeader.

Set Implicit Arguments.

Module CtxAS.
Section CtxAS.
  Context `{Σ: GRA}.

  Definition sp: spl_type :=
    Seal.sealing CRIS [(Some CtxHdr.foo, Some fspec_trivial); (Some CtxHdr.input, Some fspec_trivial)].
  
  Lemma sp_nodup: List.NoDup (List.map fst sp).
  Proof.
    unfold sp. unseal CRIS. prove_nodup.
  Qed.

End CtxAS. End CtxAS.
