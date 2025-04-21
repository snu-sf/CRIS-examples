Require Import CRIS.
Require Import ImpPrelude IncrHeader MemHeader SchHeader.

Module IncrI. Section IncrI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition incr : list val → itree pmodE unit :=
    λ arg,
      𝒴;;; '_ : unit <- ccallU FaaHdr.faa2 arg;;
      𝒴;;; Ret tt.

  Definition main : unit → itree pmodE unit :=
    λ _,
      𝒴;;; 'ptr_raw : val <- ccallU MemHdr.alloc [Vint 1%Z];;
      𝒴;;; bofs <- (pargs [Tptr] [ptr_raw])?;;
      𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr bofs; Vint 0%Z];;
      𝒴;;; tid1 <- Sch.spawn (IncrHdr.incr, [Vptr bofs]↑↑);;
      𝒴;;; tid2 <- Sch.spawn (IncrHdr.incr, [Vptr bofs]↑↑);;
      𝒴;;; Sch.join tid1;;;
      𝒴;;; Sch.join tid2;;;
      𝒴;;; 'v_raw : val <- ccallU MemHdr.load [Vptr bofs];;
      𝒴;;; 'v : Z <- (pargs [Tint] [v_raw])?;;
      𝒴;;; '_ : unit <- trigger (IO "OUT" v);;
      𝒴;;; Ret tt.

  Definition fnsems :=
    [(IncrHdr.incr, (scopes, cfunU (sfunU incr)));
     (IncrHdr.main, (scopes, cfunU main))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End IncrI. End IncrI.
