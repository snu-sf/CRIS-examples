Require Import CRIS.
Require Import ImpPrelude MemHeader MemA SchA SchTactics SchHeader.
From CRIS.incr_faa Require Import Header.

Module FaaI. Section FaaI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition faa2 : list val → itree crisE unit :=
    λ arg,
      𝒴;;; '_ : val <- MemHdr.faa arg;;
      𝒴;;; '_ : val <- MemHdr.faa arg;;
      𝒴;;; Ret tt.

  Definition fnsems : fnsems_type :=
    [(Some FaaHdr.faa2, (false, wmask_all, scopes, (None, cfunU faa2)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End FaaI. End FaaI.
