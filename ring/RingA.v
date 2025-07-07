Require Import CRIS.

Require Import ImpPrelude.
Require Import RingHeader CellA.

Set Implicit Arguments.

Module RingAS. Section RingAS.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{!cellG}.

  Definition Sp : spl_type :=
    Seal.sealing CRIS [(Some RingHdr.init, Some fspec_trivial);
                       (Some RingHdr.get_size, Some fspec_trivial);
                       (Some RingHdr.enqueue, Some fspec_trivial);
                       (Some RingHdr.dequeue, Some fspec_trivial)].

  Lemma Sp_nodup : List.NoDup (List.map fst Sp).
  Proof. unfold Sp. unseal CRIS. prove_nodup. Qed.
End RingAS. End RingAS.

Module RingA. Section RingA.
  Import RingAS.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{!cellG}.

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

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some RingHdr.init, (true, wmask_all, scopes, (None, cfunU init)));
     (Some RingHdr.get_size, (true, wmask_all, scopes, (None, cfunU get_size)));
     (Some RingHdr.enqueue, (true, wmask_all, scopes, (None, cfunU enqueue)));
     (Some RingHdr.dequeue, (true, wmask_all, scopes, (None, cfunU dequeue)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_que,([]:list Z)↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ :=
    ([∗ list] i↦_ ∈ (replicate max_size 0%Z), CellAS.pending i)%I.

  Definition t sp := Seal.sealing CRIS (SMod.to_hmod sp Mod).
End RingA. End RingA.
