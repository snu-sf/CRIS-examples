Require Import CRIS.
Require Import ImpPrelude IncrHeader MemHeader SchHeader.

Module FaaI. Section FaaI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition faa : list val → itree pmodE unit :=
    λ arg,
      𝒴;;; '_ : val <- MemHdr.faa arg;;
      𝒴;;; Ret tt.

  Definition fnsems := [(FaaHdr.faa, (scopes, cfunU faa))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End FaaI. End FaaI.

Module IncrI. Section IncrI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition incr : list val → itree pmodE unit :=
    λ arg,
      𝒴;;; '_ : unit <- ccallU FaaHdr.faa arg;;
      𝒴;;; '_ : unit <- ccallU FaaHdr.faa arg;;
      𝒴;;; Ret tt.

  Definition main : unit → itree pmodE unit :=
    λ _,
      𝒴;;; 'ptr_raw : val <- ccallU MemHdr.alloc [Vint 1%Z];;
      𝒴;;; '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] [ptr_raw])?;;
      𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr blk ofs; Vint 0%Z];;
      𝒴;;; tid1 <- Sch.spawn (IncrHdr.incr, [Vptr blk ofs]↑↑);;
      𝒴;;; tid2 <- Sch.spawn (IncrHdr.incr, [Vptr blk ofs]↑↑);;
      𝒴;;; Sch.join tid1;;;
      𝒴;;; Sch.join tid2;;;
      𝒴;;; 'v_raw : val <- ccallU MemHdr.load [Vptr blk ofs];;
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
