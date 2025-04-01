Require Import CRIS.

Require Import ImpPrelude.
Require Import RingHeader CellA.

Set Implicit Arguments.

Module RingAS. Section RingAS.
  Context `{Σ : GRA}.

  Definition Sp : alist string fspec :=
    Seal.sealing CRIS [(RingHdr.init, fspec_trivial);
                       (RingHdr.get_size, fspec_trivial);
                       (RingHdr.enqueue, fspec_trivial);
                       (RingHdr.dequeue, fspec_trivial)].

  Lemma Sp_nodup : List.NoDup (List.map fst Sp).
  Proof.
    unfold Sp. unseal CRIS. prove_nodup.
  Qed.

End RingAS.

Global Hint Unfold Sp : stb.

End RingAS.

Module RingA. Section RingA.
  (* Define Ring module *)

  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellAGΓ Γ}.

  (* A maximum size of the ring buffer *)
  Variable max_size : nat.

  (* Define scopes and a member variable `que` *)
  Definition scopes := ["Ring"].
  Definition v_que := "Ring" ↯ "que".

  (* Specifications of functions in RingA *)
  Definition init : unit -> itree hmodE unit :=
    λ _,
      cput v_que ([]:list Z)
  .

  Definition get_size : unit -> itree hmodE nat :=
    λ _,
      'que : list Z <- cgetU v_que;;
      Ret (List.length que)
  .

  Definition enqueue : Z -> itree hmodE unit :=
    λ x,
      'que : list Z <- cgetU v_que;;
      if (List.length que <? max_size)%nat
      then cput v_que (que ++ [x])
      else trigger (@IO _ void "error" "enqueue failed: queue reached its maximum capacity");;; Ret tt
  .

  Definition dequeue : unit -> itree hmodE Z :=
    λ _,
      'que : list Z <- cgetU v_que;;
      match que with
      | x :: que' => cput v_que que';;; Ret x
      | _ => trigger (@IO _ void "error" "dequeue failed: cannot dequeue from an empty queue");;; Ret 0%Z
      end
  .

  Definition fnsems :=
    [(RingHdr.init, (scopes,mk_specbody fspec_trivial (cfunU init)));
     (RingHdr.get_size, (scopes,mk_specbody fspec_trivial (cfunU get_size)));
     (RingHdr.enqueue, (scopes,mk_specbody fspec_trivial (cfunU enqueue)));
     (RingHdr.dequeue, (scopes,mk_specbody fspec_trivial (cfunU dequeue)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_que,([]:list Z)↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ :=
    ([∗ list] i↦_ ∈ (replicate max_size 0%Z), CellAS.pending i)%I.

  Definition t Sp := Seal.sealing CRIS (SMod.to_hmod emp Sp Mod).

End RingA. End RingA.
