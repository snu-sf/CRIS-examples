Require Import CRIS.
Require Export KnotHeader KnotMainHeader.

Module KnotMainI. Section KnotMainI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := ["KnotMain"].

  Definition fibF genv : list val → itree crisE val :=
    λ varg,
      '(fb, n):_ <- (pargs [Tblk; Tint] varg)?;;
      fn <- ((CEnv.load_genv genv).(CEnv.blk2id) fb)?;;
      assume(intrange_64 n);;;
      if(Z_le_gt_dec n 1)
      then Ret (Vint 1)
      else
        'n0: val <- ccallU fn [Vint (n - 1)];; 'n0: Z <- (unint n0)?;;
        'n1: val <- ccallU fn [Vint (n - 2)];; 'n1: Z <- (unint n1)?;;
        Ret (Vint (n0 + n1)).

  Definition mainF genv : () → itree crisE val :=
    λ '(),
      fibb <- ((CEnv.load_genv genv).(CEnv.id2blk) KnotMainHdr.fib)?;;
      'fb: val <- ccallU KnotHdr.knot [Vptr (fibb, 0%Z)];; 'fb: mblock <- (unblk fb)?;;
      fn <- ((CEnv.load_genv genv).(CEnv.blk2id) fb)?;;
      ccallU fn [Vint 10].

  Definition fnsems (genv : GEnv.t) : fnsemmap :=
    {[Some KnotMainHdr.fib := Some (msk_scp scopes msk_true, (None, cfunU (fibF genv)));
      None := Some (msk_scp scopes msk_true, (None, cfunU (mainF genv)))]}.

  Program Definition smod genv : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t genv := SMod.to_mod ∅ (smod genv).
End KnotMainI. End KnotMainI.
