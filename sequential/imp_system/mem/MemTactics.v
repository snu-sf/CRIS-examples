From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Export ImpPrelude.
From CRIS.imp_system.mem Require Export MemHeader MemA.

Section mem.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Local Definition state : Type := gmap key (option Any.t).
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_src st_tgt : state).

  Context (sp : specmap).

  Lemma wsim_mem_alloc (sz : Z) (msk : emask) k_s k_t E1 E2 g :
    fl_t !! (fid MemHdr.alloc) =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.alloc, fbody_trivial)))) →
    img_msk msk →
    (0 <= 8 * sz < modulus_64)%Z →
    (∀ blk,
      ([∗ list] i ↦ v ∈ replicate (Z.to_nat sz) Vundef, (blk, Z.of_nat i)%Z ↦ v) -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
      (st_src, k_s)
      (st_tgt, k_t (Vptr (blk, 0%Z))↑)) ⊢
    wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt, x <- (trigger (Call MemHdr.alloc.1 [Vint sz]↑));; k_t x).
  Proof using.
    intros Hin [Ht [Hc [Ha [Har Hg]]]] Hsz.
    iIntros "K". cInlineT.
    cStepsT; rewrite Ht; cForceT (Z.to_nat sz).
    cStepsT; rewrite Ht; cForceT _. cStepsT; rewrite Ha; cForceT.
    iSplit; eauto.
    { rewrite Z2Nat.id //; try lia. iSplit; eauto. iSplit; eauto. iPureIntro; lia. }
    cStepsT; rewrite Hc; cStepsT. rewrite Hc; cStepsT. rewrite Hg; cStepsT.
    iDestruct "GRT" as "[-> [% [-> ↦]]]". iApply "K".
    iApply (big_sepL_impl with "↦").
    iIntros "!> % % %"; rewrite Z.add_0_l; iIntros "$".
  Qed.

  Lemma wsim_mem_free b ofs v' (msk : emask) k_s k_t E1 E2 g :
    fl_t !! fid MemHdr.free =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.free, fbody_trivial)))) →
    img_msk msk →
    (b, ofs) ↦ v' -∗
    (wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint 0)↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt, x <- trigger (Call MemHdr.free.1 [Vptr (b, ofs)]↑);; k_t x).
  Proof using.
    intros Hin [Ht [Hc [Ha [Har Hg]]]].
    iIntros "↦ K".
    cInlineT. cStepsT; rewrite Ht. cForceT (b, ofs, v'); cStepsT; rewrite Ht.
    cForcesT; cStepsT; rewrite Ha; cForcesT. iFrame "↦"; iSplit; eauto.
    cStepsT. rewrite Hc; cStepsT. rewrite Hc; cStepsT. rewrite Hg; cStepsT.
    iDestruct "GRT" as "[-> ->]". iApply "K"; iFrame.
  Qed.

  Lemma wsim_mem_store b ofs v v' (msk : emask) k_s k_t E1 E2 g :
    fl_t !! fid MemHdr.store =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.store, fbody_trivial)))) →
    img_msk msk →
    (b, ofs) ↦ v' -∗
    ((b, ofs) ↦ v -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint 0)↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt, x <- trigger (Call MemHdr.store.1 [Vptr (b, ofs); v]↑);; k_t x).
  Proof using.
    intros Hin [Ht [Hc [Ha [Har Hg]]]].
    iIntros "↦ K".
    cInlineT. cStepsT; rewrite Ht. cForceT (b, ofs, v', v); cStepsT; rewrite Ht.
    cForcesT; cStepsT; rewrite Ha; cForcesT. iFrame "↦"; iSplit; eauto.
    cStepsT. rewrite Hc; cStepsT. rewrite Hc; cStepsT. rewrite Hg; cStepsT.
    iDestruct "GRT" as "[-> [↦ ->]]". iApply "K"; iFrame.
  Qed.

  Lemma wsim_mem_load b ofs q v (msk : emask) k_s k_t E1 E2 g :
     fl_t !! fid MemHdr.load =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.load, fbody_trivial)))) →
    img_msk msk →
    (b, ofs) ↦{q} v -∗
    ((b, ofs) ↦{q} v -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t v↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt, x <- trigger (Call MemHdr.load.1 [Vptr (b, ofs)]↑);; k_t x).
  Proof using.
    intros Hin [Ht [Hc [Ha [Har Hg]]]].
    iIntros "↦ K".
    cInlineT. cStepsT; rewrite Ht. cForceT (b, ofs, q, v); cStepsT; rewrite Ht.
    cForcesT; cStepsT; rewrite Ha; cForceT; iFrame "↦"; iSplit; eauto.
    cStepsT; rewrite Hc; cStepsT. rewrite Hc; cStepsT. rewrite Hg; cStepsT.
    iDestruct "GRT" as "[-> [↦ ->]]". iApply "K"; iFrame.
  Qed.

  Lemma wsim_mem_cas b ofs v v_old v_new succ E (msk : emask) k_s k_t E1 E2 g  :
    fl_t !! fid MemHdr.cas =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.cas, fbody_trivial)))) →
    img_msk msk →
    MemA.compare_val v v_old = Vint succ →
    (b, ofs) ↦ v -∗
    E -∗
    (E ==∗ ∃ q0 q1 v0 v1, MemA.val_r v q0 v0 ∗ MemA.val_r v_old q1 v1 ∗
          (MemA.val_r v q0 v0 ∗ MemA.val_r v_old q1 v1 ==∗ E)) -∗
    (((b, ofs) ↦ if (bool_decide (succ = 1)) then v_new else v) -∗
     E -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t v↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt, x <- trigger (Call MemHdr.cas.1 [Vptr (b, ofs); v_old; v_new]↑);; k_t x).
  Proof using.
    intros Hin [Ht [Hc [Ha [Har Hg]]]] Hcmp.
    iIntros "↦ E HE K".
    cInlineT. cStepsT. rewrite Ht; cForceT (b, ofs, v, v_old, v_new, succ, E); cNormT.
    rewrite Ht; cForcesT; cNormT. rewrite Ha; cForcesT.
    iFrame "↦ E HE"; iSplit; eauto.
    cStepsT. rewrite Hc; cStepsT. rewrite Hc; cStepsT.
    rewrite Hg; cStepsT. iDestruct "GRT" as "[-> [-> [↦ E]]]". iApply ("K" with "↦ E"); iFrame.
  Qed.

  Lemma wsim_mem_cmp v1 v2 succ E (msk : emask) k_s k_t E1 E2 g :
    fl_t !! (fid MemHdr.cmp) =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some (MemA.cmp), fbody_trivial)))) →
    img_msk msk →
    MemA.compare_val v1 v2 = Vint succ →
    E -∗
    (E ==∗ ∃ q0 q1 v1' v2', MemA.val_r v1 q0 v1' ∗ MemA.val_r v2 q1 v2' ∗
          (MemA.val_r v1 q0 v1' ∗ MemA.val_r v2 q1 v2' ==∗ E)) -∗
    (E -∗
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint succ)↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt,
        x <- trigger (Call MemHdr.cmp.1 [v1; v2]↑);;
        k_t x).
  Proof using.
    intros Hin [Ht [Hc [Ha [Har Hg]]]] Hcmp.
    iIntros "E HE K".
    cInlineT. cStepsT. rewrite Ht. cForceT (v1, v2, succ, E). cStepsT.
    rewrite Ht. cForcesT. cStepsT. rewrite Ha. cForceT.
    iFrame "E HE"; iSplit; eauto.
    cStepsT. rewrite Hc. cStepsT. rewrite Hc. cStepsT. rewrite Hg. cStepsT.
    iDestruct "GRT" as "[-> [-> E]]". iApply ("K" with "E"); iFrame.
  Qed.

  Lemma wsim_mem_cmp_int n1 n2 (msk : emask) k_s k_t E1 E2 g :
    fl_t !! (fid MemHdr.cmp) =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some (MemA.cmp), fbody_trivial)))) →
    img_msk msk →
    (wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint (if decide (n1 = n2) then 1 else 0)%Z)↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
      (st_src, k_s)
      (st_tgt,
        x <- trigger (Call MemHdr.cmp.1 [Vint n1; Vint n2]↑);;
        k_t x).
  Proof using.
    iIntros (Hin [Ht [Hc [Ha [Har Hg]]]]) "K".
    cInlineT. rewrite Ht.
    cForceT (Vint n1, Vint n2, (if decide (n1 = n2) then 1 else 0)%Z, emp%I).
    rewrite Ht. cForcesT. rewrite Ha. cForceT.
    iSplitR; [iSplitR; first eauto|].
    { iSplit; [iPureIntro; split; [auto|]|iSplit; ss].
      { case_decide; case_bool_decide; case_match; ss. }
      iIntros "_ !>"; iExists 1%Qp, 1%Qp, Vundef, Vundef; repeat iSplit; eauto.
    }
    cStepsT. rewrite Hc. cStepsT. rewrite Hc. cStepsT. rewrite Hg. cStepsT.
    iDestruct "GRT" as "[-> [-> _]]". iFrame.
  Qed.
End mem.

From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export proofmode.
From iris.bi Require Import derived_laws.
Import bi.

Section proofmode.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Local Definition pmem_state : Type := gmap key (option Any.t).
  Local Definition pmem_post (R_s R_t : Type) : Type := pmem_state * R_s → pmem_state * R_t → iProp Σ.

  Lemma tac_wsim_mem_load Δ i b ofs q v Δ2
      fl_s fl_t Ist R_s R_t (RR : pmem_post R_s R_t) ps pt st_src st_tgt sp
      (msk : emask) k_s k_t E1 E2 g :
     fl_t !! fid MemHdr.load =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.load, fbody_trivial)))) →
    img_msk msk →
    envs_lookup_delete true i Δ = Some (false, ((b, ofs) ↦{q} v)%I, Δ2) →
    match envs_simple_replace i false (Esnoc Enil i (((b, ofs) ↦{q} v)%I)) Δ with
    | Some Δ' =>
      envs_entails Δ' (
        wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
          (st_src, k_s)
          (st_tgt, k_t v↑))
    | None => False
    end →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
        (st_src, k_s)
        (st_tgt, x <- trigger (Call MemHdr.load.1 [Vptr (b, ofs)]↑);; k_t x)).
  Proof.
    intros Hin Hmsk Hlook Hcont.
    destruct (envs_simple_replace i false (Esnoc Enil i (((b, ofs) ↦{q} v)%I)) Δ)
      as [Δ'|] eqn:Hrep; last done.
    rewrite envs_entails_unseal in Hcont |- *.
    apply envs_lookup_delete_Some in Hlook as [Hlook ->].
    rewrite envs_lookup_sound' //=.
    iIntros "[Hpt HΔ]".
    iApply (wsim_mem_load with "Hpt"); eauto.
    iIntros "Hpt".
    iApply Hcont.
    iApply (envs_simple_replace_sound' Δ Δ' i false
      (Esnoc Enil i (((b, ofs) ↦{q} v)%I)) Hrep with "HΔ").
    iFrame.
  Unshelve. all: eauto.
  Qed.

  Lemma tac_wsim_mem_store Δ i b ofs v v' Δ2
      fl_s fl_t Ist R_s R_t (RR : pmem_post R_s R_t) ps pt st_src st_tgt sp
      (msk : emask) k_s k_t E1 E2 g :
    fl_t !! fid MemHdr.store =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.store, fbody_trivial)))) →
    img_msk msk →
    envs_lookup_delete true i Δ = Some (false, ((b, ofs) ↦ v')%I, Δ2) →
    match envs_simple_replace i false (Esnoc Enil i (((b, ofs) ↦ v)%I)) Δ with
    | Some Δ' =>
      envs_entails Δ' (
        wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
          (st_src, k_s)
          (st_tgt, k_t (Vint 0)↑))
    | None => False
    end →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
        (st_src, k_s)
        (st_tgt, x <- trigger (Call MemHdr.store.1 [Vptr (b, ofs); v]↑);; k_t x)).
  Proof.
    intros Hin Hmsk Hlook Hcont.
    destruct (envs_simple_replace i false (Esnoc Enil i (((b, ofs) ↦ v)%I)) Δ)
      as [Δ'|] eqn:Hrep; last done.
    rewrite envs_entails_unseal in Hcont |- *.
    apply envs_lookup_delete_Some in Hlook as [Hlook ->].
    rewrite envs_lookup_sound' //=.
    iIntros "[Hpt HΔ]".
    iApply (wsim_mem_store with "Hpt"); eauto.
    iIntros "Hpt".
    iApply Hcont.
    iApply (envs_simple_replace_sound' Δ Δ' i false
      (Esnoc Enil i (((b, ofs) ↦ v)%I)) Hrep with "HΔ").
    iFrame.
  Unshelve. all: eauto.
  Qed.

  Lemma tac_wsim_mem_free Δ i b ofs v' Δ2
      fl_s fl_t Ist R_s R_t (RR : pmem_post R_s R_t) ps pt st_src st_tgt sp
      (msk : emask) k_s k_t E1 E2 g :
    fl_t !! fid MemHdr.free =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.free, fbody_trivial)))) →
    img_msk msk →
    envs_lookup_delete true i Δ = Some (false, ((b, ofs) ↦ v')%I, Δ2) →
    envs_entails Δ2 (
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint 0)↑)) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
        (st_src, k_s)
        (st_tgt, x <- trigger (Call MemHdr.free.1 [Vptr (b, ofs)]↑);; k_t x)).
  Proof.
    rewrite envs_entails_unseal=> Hin Hmsk Hlook Hcont.
    apply envs_lookup_delete_Some in Hlook as [Hlook ->].
    rewrite envs_lookup_sound' //=.
    iIntros "[Hpt HΔ]".
    iApply (wsim_mem_free with "Hpt"); eauto.
    iApply Hcont. iExact "HΔ".
  Unshelve. all: eauto.
  Qed.

  Lemma tac_wsim_mem_cas Δ i b ofs v v_old v_new succ E Δ2
      fl_s fl_t Ist R_s R_t (RR : pmem_post R_s R_t) ps pt st_src st_tgt sp
      (msk : emask) k_s k_t E1 E2 g :
    fl_t !! fid MemHdr.cas =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.cas, fbody_trivial)))) →
    img_msk msk →
    envs_lookup_delete true i Δ = Some (false, ((b, ofs) ↦ v)%I, Δ2) →
    MemA.compare_val v v_old = Vint succ →
    envs_entails Δ2 (
      E ∗
      (E ==∗ ∃ q0 q1 v0 v1, MemA.val_r v q0 v0 ∗ MemA.val_r v_old q1 v1 ∗
            (MemA.val_r v q0 v0 ∗ MemA.val_r v_old q1 v1 ==∗ E)) ∗
      (((b, ofs) ↦ if (bool_decide (succ = 1)) then v_new else v) -∗
       E -∗
        wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
          (st_src, k_s)
          (st_tgt, k_t v↑))) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
        (st_src, k_s)
        (st_tgt, x <- trigger (Call MemHdr.cas.1 [Vptr (b, ofs); v_old; v_new]↑);; k_t x)).
  Proof.
    rewrite envs_entails_unseal=> Hin Hmsk Hlook Hcmp Hcont.
    apply envs_lookup_delete_Some in Hlook as [Hlook ->].
    rewrite envs_lookup_sound' //=.
    iIntros "[Hpt HΔ]".
    iPoseProof (Hcont with "HΔ") as "[E [HE K]]".
    iApply (wsim_mem_cas with "Hpt E HE K"); eauto.
  Unshelve. all: eauto.
  Qed.

  Lemma tac_wsim_mem_cmp Δ v1 v2 succ E
      fl_s fl_t Ist R_s R_t (RR : pmem_post R_s R_t) ps pt st_src st_tgt sp
      (msk : emask) k_s k_t E1 E2 g :
    fl_t !! (fid MemHdr.cmp) =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some (MemA.cmp), fbody_trivial)))) →
    img_msk msk →
    MemA.compare_val v1 v2 = Vint succ →
    envs_entails Δ (
      E ∗
      (E ==∗ ∃ q0 q1 v1' v2', MemA.val_r v1 q0 v1' ∗ MemA.val_r v2 q1 v2' ∗
            (MemA.val_r v1 q0 v1' ∗ MemA.val_r v2 q1 v2' ==∗ E)) ∗
      (E -∗
        wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
          (st_src, k_s)
          (st_tgt, k_t (Vint succ)↑))) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
        (st_src, k_s)
        (st_tgt, x <- trigger (Call MemHdr.cmp.1 [v1; v2]↑);; k_t x)).
  Proof.
    rewrite envs_entails_unseal=> Hin Hmsk Hcmp Hcont.
    rewrite Hcont.
    iIntros "[E [HE K]]".
    iApply (wsim_mem_cmp with "E HE K"); eauto.
  Unshelve. all: eauto.
  Qed.

  Lemma tac_wsim_mem_cmp_int Δ n1 n2
      fl_s fl_t Ist R_s R_t (RR : pmem_post R_s R_t) ps pt st_src st_tgt sp
      (msk : emask) k_s k_t E1 E2 g :
    fl_t !! (fid MemHdr.cmp) =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some (MemA.cmp), fbody_trivial)))) →
    img_msk msk →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint (if decide (n1 = n2) then 1 else 0)%Z)↑)) →
    envs_entails Δ (
      wsim fl_s fl_t Ist (E1, E2) g R_s R_t RR ps pt
        (st_src, k_s)
        (st_tgt, x <- trigger (Call MemHdr.cmp.1 [Vint n1; Vint n2]↑);; k_t x)).
  Proof.
    rewrite envs_entails_unseal=> Hin Hmsk Hcont.
    rewrite Hcont.
    iIntros "K".
    iApply (wsim_mem_cmp_int with "K"); eauto.
  Unshelve. all: eauto.
  Qed.
End proofmode.

Tactic Notation "mLoadT" uconstr(H) :=
  iApply (wsim_mem_load with H); [try by simpl_map|ss|]; last (iIntros H; cStepsT).
Tactic Notation "mStoreT" uconstr(H) :=
  iApply (wsim_mem_store with H); [try by simpl_map|ss|]; last (iIntros H; cStepsT).
Tactic Notation "mAllocT" "as" "(" simple_intropattern(x) ")" uconstr(H) :=
  iApply wsim_mem_alloc; [try by simpl_map|ss|ss|iIntros (x) H; cStepsT].
Tactic Notation "mFreeT" uconstr(H) :=
  iApply (wsim_mem_free with H); [try by simpl_map|ss|cStepsT].

Tactic Notation "mLoad" :=
  eapply tac_wsim_mem_load;
    [try by simpl_map
    |ss
    |iAssumptionCore || fail "mLoad: no matching ↦"
    |pm_reduce; cStepsT].

Tactic Notation "mStore" :=
  eapply tac_wsim_mem_store;
    [try by simpl_map
    |ss
    |iAssumptionCore || fail "mStore: no matching ↦"
    |pm_reduce; cStepsT].

Tactic Notation "mFree" :=
  eapply tac_wsim_mem_free;
    [try by simpl_map
    |ss
    |iAssumptionCore || fail "mFree: no matching ↦"
    |pm_reduce; cStepsT].

Tactic Notation "mCas" :=
  eapply tac_wsim_mem_cas;
    [try solve [simpl_map | prove_inline_cond | prove_sb_cond | ss]
    |ss
    |iAssumptionCore || fail "mCas: no matching ↦"
    |try solve [eauto | rewrite /MemA.compare_val; des_ifs; eauto]
    |pm_reduce].

Tactic Notation "mCas" constr(succ) :=
  eapply (tac_wsim_mem_cas _ _ _ _ _ _ _ succ);
    [try solve [simpl_map | prove_inline_cond | prove_sb_cond | ss]
    |ss
    |iAssumptionCore || fail "mCas: no matching ↦"
    |try solve [eauto | rewrite /MemA.compare_val; des_ifs; eauto]
    |pm_reduce].

Tactic Notation "mCmp" :=
  eapply tac_wsim_mem_cmp;
    [try solve [simpl_map | prove_inline_cond | prove_sb_cond | ss]
    |ss
    |try solve [eauto | rewrite /MemA.compare_val; des_ifs; eauto]
    |pm_reduce].

Tactic Notation "mCmp" constr(succ) :=
  eapply (tac_wsim_mem_cmp _ _ _ succ);
    [try solve [simpl_map | prove_inline_cond | prove_sb_cond | ss]
    |ss
    |try solve [eauto | rewrite /MemA.compare_val; des_ifs; eauto]
    |pm_reduce].

Tactic Notation "mCmpInt" :=
  eapply tac_wsim_mem_cmp_int;
    [try by simpl_map
    |ss
    |cStepsT].

Tactic Notation "mStep" :=
  lazymatch goal with
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _
        (_, _)
        (_, _)) =>
    first [mLoad | mStore | mFree | mCas | mCmpInt | mCmp]
  end.

Tactic Notation "mSteps" := repeat (mStep; try cStepsT).
