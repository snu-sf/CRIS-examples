Require Import CRIS.

Require Import ImpPrelude.
Require Import RingHeader CellHeader.

Set Implicit Arguments.

Module CtrlI. Section CtrlI.
  Local Open Scope nat_scope.

  Context `{Σ : GRA}.

  (* A maximum size of the ring buffer *)
  Variable max_size : nat.

  Definition scopes := ["Ring"].
  Definition v_hd := "Ring" ↯ "hd".
  Definition v_tl := "Ring" ↯ "tl".

  (* Implementations of init, get_size, enqueue, dequeue *)
  Definition init : unit -> itree pmodE unit :=
    λ _,
      cput v_hd 0;;;
      cput v_tl 0
  .

  Definition get_size : unit -> itree pmodE nat :=
    λ _,
      'hd : nat <- cgetU v_hd;;
      'tl : nat <- cgetU v_tl;;
      Ret (hd - tl)
  .

  Definition enqueue : Z -> itree pmodE unit :=
    λ x,
      'hd : nat <- cgetU v_hd;;
      'tl : nat <- cgetU v_tl;;
      if (hd - tl <? max_size)
      then
        'u: () <- ccallU (CellName.set (hd mod max_size)) x;;
        cput v_hd (hd+1)
      else
        trigger (@IO _ void "error" "enqueue failed: queue reached its maximum capacity");;; Ret tt
  .

  Definition dequeue : unit -> itree pmodE Z :=
    λ _,
      'hd : nat <- cgetU v_hd;;
      'tl : nat <- cgetU v_tl;;
      if (0 <? hd - tl)
      then
        x <- ccallU (CellName.get (tl mod max_size)) tt;;
        cput v_tl (tl+1);;;
        Ret x
      else
        trigger (@IO _ void "error" "dequeue failed: cannot dequeue from an empty queue");;; Ret 0%Z
  .

  Definition fnsems :=
    [(RingName.init, (scopes, cfunU init));
     (RingName.get_size, (scopes, cfunU get_size));
     (RingName.enqueue, (scopes, cfunU enqueue));
     (RingName.dequeue, (scopes, cfunU dequeue))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [(v_hd,0↑);(v_tl,0↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).

End CtrlI. End CtrlI.
