Require Import CRIS.
From CRIS.imp_system Require Import mem.MemA.
From CRIS.celliostk Require Import CellioHeader CtxHeader.

Module CellioA. Section CellioA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_MEM: !memGS}.

  Fixpoint ll_points_to (p: val) (l: list Z) : iProp Σ :=
    match l with
    | [] => ⌜p = Vnullptr⌝
    | i :: l' =>
        ∃ bo p', ⌜p = Vptr bo⌝ ∗ bo |-> [Vint i; p'] ∗ ll_points_to p' l'
    end.

  Definition new: unit -> itree crisE val :=
    λ _,
      p <- trigger (Choose val);;
      trigger (Guarantee (ll_points_to p []));;;
      Ret p.

  Definition push: string * val -> itree crisE val :=
    λ '(cb,p),
      l <- trigger (Take (list Z));;
      trigger (Assume (ll_points_to p l));;;
      'i: Z <- ccallU (fnsig cb CtxHdr.cb_t) tt;;
      p' <- trigger (Choose val);;
      trigger (Guarantee (ll_points_to p' (i::l)));;;
      Ret p'.

  Definition pop: val -> itree crisE (option Z * val) :=
    λ p,
      l <- trigger (Take (list Z));;
      trigger (Assume (ll_points_to p l));;;
      p' <- trigger (Choose val);;
      trigger (Guarantee (ll_points_to p' (tl l)));;;
      Ret (hd_error l, p').

  Definition scopes := [CellioHdr.mn].
  
  Definition fnsems : fnsemmap :=
    {[fid CellioHdr.new  # (msk_scp scopes msk_true, (None, cfunU CellioHdr.new new));
      fid CellioHdr.push # (msk_scp scopes msk_true, (None, cfunU CellioHdr.push push));
      fid CellioHdr.pop  # (msk_scp scopes msk_true, (None, cfunU CellioHdr.pop pop))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.

  (* We can use sp_none because Cellio will be removed before cancellation *)
  Definition t := SMod.to_mod ∅ smod.
End CellioA. End CellioA.
