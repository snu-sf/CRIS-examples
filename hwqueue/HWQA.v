Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Export HWQRA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts.
Require Import HelpingTactics.
Require Import HWQI HWQP SchI SchTactics.
From stdpp Require Import streams list.

(* Specification of the queue operations *)
Module HWQA. Section HWQA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !schGS, !memGS, !prophGS, !hwqG}.
  Context (N : namespace).

  Definition scopes : list string := [].

  Definition new_queue : list val → itree crisE val :=
    λ _, 𝒴;;; trigger (Choose val).

  Definition new_queue_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((n, sz) : nat * nat),
        ((λ arg, ⌜arg = [Vint sz]↑ ∧ 0 < 8 * (2 + sz) < Z.to_nat modulus_64⌝),
         (λ ret, ∃ (q : val) (γq : gname), ⌜ret = (q↑)⌝ ∗ is_hwq N n sz γq q ∗ hwq_cont γq []))))%I.

  Definition enqueue_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((n, sz, γq, q, l) : nat * nat * gname * val * val),
        ((λ arg, ∃ blk ofs, ⌜l = Vptr (blk, ofs) ∧ arg = [q; l]↑⌝ ∗
          is_hwq N n sz γq q ∗ ∃ v, (blk, ofs) ↦ v),
         (λ ret, True))))%I.

  Definition dequeue_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((n, sz, γq, q) : nat * nat * gname * val),
        ((λ arg, ⌜arg = [q]↑⌝ ∗ is_hwq N n sz γq q),
         (λ ret, True))))%I.

  Definition enqueue : Any.t → itree crisE Any.t :=
    atomic_body enqueue_spec
      (λ '(_, (_, γq, _, l)) _,
        ls <- trigger (Take (list valO));;
        trigger (Assume (hwq_cont γq ls));;;
        trigger (Guarantee (hwq_cont γq (ls ++ [l])));;;
        Ret Vundef↑).

  Definition dequeue : Any.t → itree crisE Any.t :=
    atomic_body dequeue_spec
      (λ '(_, (_, γq, _)) _, 
        ls <- trigger (Take (list valO));;
        trigger (Assume (hwq_cont γq ls));;;
        l <- trigger (Choose valO);;
        trigger (Guarantee (∃ ls', ⌜ls = l :: ls'⌝ ∗ hwq_cont γq ls'));;;
        Ret (l↑)).

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk_scp scopes msk_true, (fsp_some new_queue_spec, cfunU new_queue));
      fid HWQHdr.enqueue   # (msk_scp scopes msk_true, (None, enqueue));
      fid HWQHdr.dequeue   # (msk_scp scopes msk_true, (None, dequeue))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp Mod.
End HWQA. End HWQA.

Module HWQM. Section HWQM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !memGS, !prophGS, !schGS, !hwqG}.
  Context (N : namespace) (mnh : string).

  Notation jobID := (val * gname)%type. (* idx * gname *)
  Notation retID := val.

  Definition jobCode : jobID → itree crisE retID :=
    λ '(v, γq),
      ls <- trigger (Take (list valO));;
      trigger (Assume (hwq_cont γq ls));;;
      trigger (Guarantee (hwq_cont γq (ls ++ [v])));;;
      Ret Vundef.

  Definition scopes : list string := [].

  Definition enqueue : Any.t → itree crisE Any.t :=
    atomic_body (HWQA.enqueue_spec N)
      (λ '(_, (_, γq, _, l)) _,
        ret <- trigger (Call (Helping.run mnh) (l, γq)↑);;
        ITree.iter (λ _,
          'b : bool <- trigger (Choose bool);;
          if b 
          then trigger (Call (Helping.help mnh) (()↑));;; Ret (inl ()) 
          else Ret (inr ())) ();;;
        Ret ret).

  Definition dequeue : Any.t → itree crisE Any.t :=
    atomic_body (HWQA.dequeue_spec N)
      (λ '(_, (_, γq, _)) _, 
        ls <- trigger (Take (list valO));;
        trigger (Assume (hwq_cont γq ls));;;
        l <- trigger (Choose valO);;
        trigger (Guarantee (∃ ls', ⌜ls = l :: ls'⌝ ∗ hwq_cont γq ls'));;;
        Ret (l↑)).

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk_scp scopes msk_true, (fsp_some (HWQA.new_queue_spec N), cfunU (HWQA.new_queue)));
      fid HWQHdr.enqueue   # (msk_scp scopes msk_true, (None, enqueue));
      fid HWQHdr.dequeue   # (msk_scp scopes msk_true, (None, dequeue))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod (SchA.sp ∅ (↑N)) Mod.
End HWQM. End HWQM.

Module HWQIAInv. Section HWQIAInv.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !memGS, !prophGS, !schGS, !hwqG}.
  Context (mnp mnh : string).
  Context (N : namespace).

  Definition Ist : ist_type Σ := λ st_src st_tgt,
    (IstHelp mnh st_src st_tgt ∗
    ∃ (X : gset val),
      free_id (λ x, (x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type) ∗
      [∗ set] x ∈ X,
        □ ∃ blk ofs nx, ⌜x = Vptr (blk, ofs)⌝ ∗
          ∀ X, helping_auth 1 X =| nx, ↑N |={↑N, ∅}=∗ ∃ v, (blk, ofs) ↦ v)%I.
  Definition IstFull : ist_type Σ :=
    IstProd (IstSB (Mod.scopes (HWQP.t mnp) ++ Mod.scopes (HelpingDummy.t mnh)) Ist) IstEq.

  Lemma Ist_help : Ist_helping mnh IstFull.
  Proof.
    iIntros (??) "[% [% [% [% [[-> ->] [[%Ha [[% [[-> ->] ?]] ?]] ->]]]]]]".
    iModIntro; iExists _, _; iFrame; iSplit; auto.
    iIntros (?) "$ !>"; iExists _, _, _, _; repeat iSplit; eauto.
    iPureIntro. set_solver.
  Qed.
  
End HWQIAInv. End HWQIAInv.
