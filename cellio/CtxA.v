Require Import CRIS.
Require Import MainHeader CellioHeader CtxHeader.

Set Implicit Arguments.

(* Module CtxHdr.

  Definition mn := "Ctx".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".
  Definition input := fn "input".

End CtxHdr. *)

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
