Require Import CRIS.

Require Import ImpPrelude.
Require Import RingHeader CellA.

Set Implicit Arguments.

Module RingAS. Section RingAS.
  Context `{Σ : GRA}.

  Definition Spc : alist string fspec :=
    Seal.sealing CRIS [(RingName.init, fspec_trivial);
                       (RingName.get_size, fspec_trivial);
                       (RingName.enqueue, fspec_trivial);
                       (RingName.dequeue, fspec_trivial)].

  Lemma Spc_nodup : List.NoDup (List.map fst Spc).
  Proof.
    unfold Spc. unseal CRIS. prove_nodup.
  Qed.

End RingAS.

Global Hint Unfold Spc : stb.

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
    [(RingName.init, (scopes,mk_specbody fspec_trivial (cfunU init)));
     (RingName.get_size, (scopes,mk_specbody fspec_trivial (cfunU get_size)));
     (RingName.enqueue, (scopes,mk_specbody fspec_trivial (cfunU enqueue)));
     (RingName.dequeue, (scopes,mk_specbody fspec_trivial (cfunU dequeue)))].

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

  Definition t Spc := Seal.sealing CRIS (SMod.to_hmod emp Spc Mod).

End RingA. End RingA.
