Require Import CRIS.
Require Import ImpPrelude.
Require Import RingHeader CellHeader.

Module CtrlI. Section CtrlI.
  Context `{!crisG Γ Σ α β τ _I _S}.

  (* A maximum size of the ring buffer *)
  Variable max_size : nat.

  Definition scopes : list string := ["Ring"].
  Definition v_hd := "Ring" ↯ "hd".
  Definition v_tl := "Ring" ↯ "tl".

  (* Implementations of init, get_size, enqueue, dequeue *)
  Definition init : unit -> itree crisE unit :=
    λ _,
      cput v_hd 0;;;
      cput v_tl 0
  .

  Definition get_size : unit -> itree crisE nat :=
    λ _,
      'hd : nat <- cgetU v_hd;;
      'tl : nat <- cgetU v_tl;;
      Ret (hd - tl)
  .

  Definition enqueue : Z -> itree crisE unit :=
    λ x,
      'hd : nat <- cgetU v_hd;;
      'tl : nat <- cgetU v_tl;;
      if (hd - tl <? max_size)
      then
        'u: () <- ccallU (cftyp _ _) (CellHdr.set (hd mod max_size)) x;;
        cput v_hd (hd+1)
      else
        trigger (@IO _ void "error" "enqueue failed: queue reached its maximum capacity");;; Ret tt
  .

  Definition dequeue : unit -> itree crisE Z :=
    λ _,
      'hd : nat <- cgetU v_hd;;
      'tl : nat <- cgetU v_tl;;
      if (0 <? hd - tl)
      then
        x <- ccallU (cftyp _ _) (CellHdr.get (tl mod max_size)) tt;;
        cput v_tl (tl+1);;;
        Ret x
      else
        trigger (@IO _ void "error" "dequeue failed: cannot dequeue from an empty queue");;; Ret 0%Z
  .

  Definition fnsems : fnsemmap :=
    {[fid RingHdr.init     # (msk_real (msk_scp scopes msk_true), (None, cfunU (cftyp _ _) init));
      fid RingHdr.get_size # (msk_real (msk_scp scopes msk_true), (None, cfunU (cftyp _ _) get_size));
      fid RingHdr.enqueue  # (msk_real (msk_scp scopes msk_true), (None, cfunU (cftyp _ _) enqueue));
      fid RingHdr.dequeue  # (msk_real (msk_scp scopes msk_true), (None, cfunU (cftyp _ _) dequeue))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_hd # 0↑; v_tl # 0↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CtrlI. End CtrlI.
