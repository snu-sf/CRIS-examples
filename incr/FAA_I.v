Require Import CRIS.
Require Import ImpPrelude IncrHeader MemHeader MemA SchA SchTactics SchHeader.

Module FaaI. Section FaaI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition faa2 : list val → itree pmodE unit :=
    λ arg,
      𝒴;;; '_ : val <- MemHdr.faa arg;;
      𝒴;;; '_ : val <- MemHdr.faa arg;;
      𝒴;;; Ret tt.

  Definition fnsems := [(FaaHdr.faa2, (wmask_all, scopes, cfunU faa2))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End FaaI. End FaaI.
