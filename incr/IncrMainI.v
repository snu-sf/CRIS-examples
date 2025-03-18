Require Import CRIS.
Require Import ImpPrelude IncrMainHeader MemHeader SchHeader.

Module IncrMainI. Section IncrMainI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition main : unit → itree pmodE unit :=
    λ _,
      𝒴;;; 'ptr_raw : val <- ccallU MemName.alloc [Vint 1%Z];;
      𝒴;;; '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] [ptr_raw])?;;
      𝒴;;; '_ : val <- ccallU MemName.store [Vptr blk ofs; Vint 0%Z];;
      𝒴;;; tid1 <- Sch.spawn ("f", [Vptr blk ofs]↑↑);;
      𝒴;;; tid2 <- Sch.spawn ("f", [Vptr blk ofs]↑↑);;
      𝒴;;; Sch.join tid1;;;
      𝒴;;; Sch.join tid2;;;
      𝒴;;; 'v_raw : val <- ccallU MemName.load [Vptr blk ofs];;
      𝒴;;; 'v : Z <- (pargs [Tint] [v_raw])?;;
      𝒴;;; '_ : unit <- trigger (IO "OUT" v);;
      𝒴;;; Ret tt.
  
  Definition f : list val → itree pmodE unit :=
    λ arg,
      𝒴;;; '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] arg)?;;
      (* atomic update *)
      𝒴;;; 'v_raw : val <- ccallU MemName.load [Vptr blk ofs];;
            'v : Z <- (pargs [Tint] [v_raw])?;;
            '_ : val <- ccallU MemName.store [Vptr blk ofs; Vint (v + 1)%Z];;
      𝒴;;; Ret tt.

  Definition fnsems :=
    [(MainName.main, (scopes, cfunU main));
     (MainName.f,    (scopes, cfunU (sfunU f)))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End IncrMainI. End IncrMainI.
