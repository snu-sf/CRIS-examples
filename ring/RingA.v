Require Import CRIS.
Require Import ImpPrelude.
Require Import RingHeader CellA.

Module RingA. Section RingA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELL: !cellGS}.

  (* Definition sp : specmap :=
    {[fid RingHdr.init     @ fspec_trivial;
      fid RingHdr.get_size @ fspec_trivial;
      fid RingHdr.enqueue  @ fspec_trivial;
      fid RingHdr.dequeue  @ fspec_trivial]}. *)

  (* A maximum size of the ring buffer *)
  Variable max_size : nat.

  (* Define scopes and a member variable `que` *)
  Definition scopes : list string := ["Ring"].
  Definition v_que := "Ring" ↯ "que".

  (* Specifications of functions in RingA *)
  Definition init : unit -> itree crisE unit := λ _, cput v_que ([]:list Z).

  Definition get_size : unit -> itree crisE nat :=
    λ _,
      'que : list Z <- cgetU v_que;;
      Ret (List.length que).

  Definition enqueue : Z -> itree crisE unit :=
    λ x,
      'que : list Z <- cgetU v_que;;
      if (List.length que <? max_size)%nat
      then cput v_que (que ++ [x])
      else trigger (@IO _ void "error" "enqueue failed: queue reached its maximum capacity");;;
      Ret tt.

  Definition dequeue : unit -> itree crisE Z :=
    λ _,
      'que : list Z <- cgetU v_que;;
      match que with
      | x :: que' => cput v_que que';;; Ret x
      | _ => trigger (@IO _ void "error" "dequeue failed: cannot dequeue from an empty queue");;; Ret 0%Z
      end.

  Definition fnsems : fnsemmap :=
    {[fid RingHdr.init     # (msk_real (msk_scp scopes msk_true), (None, cfunU init));
      fid RingHdr.get_size # (msk_real (msk_scp scopes msk_true), (None, cfunU get_size));
      fid RingHdr.enqueue  # (msk_real (msk_scp scopes msk_true), (None, cfunU enqueue));
      fid RingHdr.dequeue  # (msk_real (msk_scp scopes msk_true), (None, cfunU dequeue))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_que # ([]:list Z)↑]};
  |}
  .
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ :=
    ([∗ list] i ↦ _ ∈ (replicate max_size 0%Z), CellA.pending i)%I.

  Definition t sp := SMod.to_mod sp smod.
End RingA. End RingA.
