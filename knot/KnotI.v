Require Import CRIS.

Require Import KnotHeader MemHeader.

Set Implicit Arguments.

Module KnotI. Section KnotI.
  Local Open Scope string_scope.
  Context {Σ: GRA}.

  Definition scopes := ["Knot"].

  Definition knotF genv : list val -> itree hmodE val :=
    fun varg =>
      fb <- (pargs [Tblk] varg)?;;
      blk <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotHdr._f)?;;
      '_: val <- ccallU MemHdr.store [Vptr (blk, 0%Z); Vptr (fb, 0%Z)];;
      rb <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotHdr.rec)?;;
      Ret (Vptr (rb, 0%Z))
  .

  Definition recF genv : list val -> itree hmodE val :=
    fun varg =>
      n <- (pargs [Tint] varg)?;;
      blk <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotHdr._f)?;;
      'fb: val <- ccallU MemHdr.load [Vptr (blk, 0%Z)];; fb <- (unblk fb)?;;
      fn <- ((CEnv.load_genv genv).(CEnv.blk2id) fb)?;;
      rb <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotHdr.rec)?;;
      ccallU fn [Vptr (rb, 0%Z); Vint n]
  .

  Definition fnsems genv :=
    [(KnotHdr.rec, (wmask_all, scopes, cfunU (recF genv)));
     (KnotHdr.knot, (wmask_all, scopes, cfunU (knotF genv)))].
  
  Program Definition Mod genv : PMod.t :=
  {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems genv;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t genv := Seal.sealing CRIS (PMod.to_hmod (Mod genv)).
End KnotI. End KnotI.
