Require Import CRIS.
Require Export KnotHeader MemHeader.

Module KnotI. Section KnotI.
  Context `{!crisG Σ Γ α β τ Hinv Hsub}.

  Definition scopes := ["Knot"].

  Definition knotF genv : list val → itree crisE val :=
    λ varg,
      fb <- (pargs [Tblk] varg)?;;
      blk <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotHdr._f)?;;
      '_: val <- ccallU MemHdr.store [Vptr (blk, 0%Z); Vptr (fb, 0%Z)];;
      rb <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotHdr.rec)?;;
      Ret (Vptr (rb, 0%Z)).

  Definition recF genv : list val → itree crisE val :=
    λ varg,
      n <- (pargs [Tint] varg)?;;
      blk <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotHdr._f)?;;
      'fb: val <- ccallU MemHdr.load [Vptr (blk, 0%Z)];; fb <- (unblk fb)?;;
      fn <- ((CEnv.load_genv genv).(CEnv.blk2id) fb)?;;
      rb <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotHdr.rec)?;;
      ccallU fn [Vptr (rb, 0%Z); Vint n].

  Definition fnsems (genv : GEnv.t) : fnsemmap :=
    {[Some KnotHdr.rec := Some (msk_scp scopes msk_true, (None, cfunU (recF genv)));
      Some KnotHdr.knot := Some (msk_scp scopes msk_true, (None, cfunU (knotF genv)))]}.
  
  Program Definition smod genv : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t genv := SMod.to_mod ∅ (smod genv).
End KnotI. End KnotI.
