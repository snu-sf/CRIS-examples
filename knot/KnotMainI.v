Require Import CRIS.

Require Import KnotHeader KnotMainHeader.

Set Implicit Arguments.

Module KnotMainI. Section KnotMainI.
  Context {Σ: GRA}.

  Definition scopes := ["KnotMain"].

  Definition fibF genv : list val -> itree pmodE val :=
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

  Definition mainF genv : () -> itree pmodE val :=
    fun '() =>
      fibb <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotMainHdr.fib)?;;
      'fb: val <- ccallU KnotHdr.knot [Vptr fibb 0];; 'fb: mblock <- (unblk fb)?;;
      fn <- ((CEnv.load_genv genv).(CEnv.blk2id) fb)?;;
      ccallU fn [Vint 10].

  Definition fnsems genv :=
    [(KnotMainHdr.fib, (scopes, cfunU (fibF genv)));
     (KnotMainHdr.main, (scopes, cfunU (mainF genv)))].
  
  Program Definition Mod genv: PMod.t :=
  {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems genv;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t genv := Seal.sealing CRIS (PMod.to_hmod (Mod genv)).
End KnotMainI. End KnotMainI.