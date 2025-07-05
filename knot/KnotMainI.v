Require Import CRIS.

Require Import KnotHeader KnotMainHeader.

Set Implicit Arguments.

Module KnotMainI. Section KnotMainI.
  Context {Σ: GRA}.

  Definition scopes := ["KnotMain"].

  Definition fibF genv : list val -> itree hmodE val :=
    fun varg =>
      '(fb, n):_ <- (pargs [Tblk; Tint] varg)?;;
      fn <- ((CEnv.load_genv genv).(CEnv.blk2id) fb)?;;
      assume(intrange_64 n);;;
      if(Z_le_gt_dec n 1)
      then Ret (Vint 1)
      else
        'n0: val <- ccallU fn [Vint (n - 1)];; 'n0: Z <- (unint n0)?;;
        'n1: val <- ccallU fn [Vint (n - 2)];; 'n1: Z <- (unint n1)?;;
        Ret (Vint (n0 + n1)).

  Definition mainF genv : () -> itree hmodE val :=
    fun '() =>
      fibb <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotMainHdr.fib)?;;
      'fb: val <- ccallU KnotHdr.knot [Vptr (fibb, 0%Z)];; 'fb: mblock <- (unblk fb)?;;
      fn <- ((CEnv.load_genv genv).(CEnv.blk2id) fb)?;;
      ccallU fn [Vint 10].

  Definition fnsems genv : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some KnotMainHdr.fib, (false, wmask_all, scopes, (None, cfunU (fibF genv))));
     (None, (false, wmask_all, scopes, (None, cfunU (mainF genv))))].
  
  Program Definition Mod genv: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t genv := Seal.sealing CRIS (SMod.to_hmod sp_none (Mod genv)).
End KnotMainI. End KnotMainI.
