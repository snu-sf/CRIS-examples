Require Import CRIS.
From CRIS Require Export ImpPrelude MemHeader MemA.

Section mem.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

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

  Lemma wsim_mem_alloc (sz : Z) (msk : emask) k_s k_t E1 E2 r g :
    fl_t !! (fid MemHdr.alloc) =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.alloc, fbody_trivial)))) →
    img_msk msk →
    (0 <= 8 * sz < modulus_64)%Z →
    (∀ blk,
      ([∗ list] i ↦ v ∈ replicate (Z.to_nat sz) Vundef, (blk, Z.of_nat i)%Z ↦ v) -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
      (st_src, k_s)
      (st_tgt, k_t (Vptr (blk, 0%Z))↑)) ⊢
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
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

  Lemma wsim_mem_free b ofs v' (msk : emask) k_s k_t E1 E2 r g :
    fl_t !! fid MemHdr.free =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.free, fbody_trivial)))) →
    img_msk msk →
    (b, ofs) ↦ v' -∗
    (wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint 0)↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
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

  Lemma wsim_mem_store b ofs v v' (msk : emask) k_s k_t E1 E2 r g :
    fl_t !! fid MemHdr.store =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.store, fbody_trivial)))) →
    img_msk msk →
    (b, ofs) ↦ v' -∗
    ((b, ofs) ↦ v -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint 0)↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
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

  Lemma wsim_mem_load b ofs q v (msk : emask) k_s k_t E1 E2 r g :
     fl_t !! fid MemHdr.load =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some MemA.load, fbody_trivial)))) →
    img_msk msk →
    (b, ofs) ↦{q} v -∗
    ((b, ofs) ↦{q} v -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t v↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
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

  Lemma wsim_mem_cas b ofs v v_old v_new succ E (msk : emask) k_s k_t E1 E2 r g  :
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
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t v↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
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

  Lemma wsim_mem_cmp v1 v2 succ E (msk : emask) k_s k_t E1 E2 r g :
    fl_t !! (fid MemHdr.cmp) =
      Some (Some (SB.sandbox_body
        (msk, SModTr.trans_fnsem sp (fsp_some (MemA.cmp), fbody_trivial)))) →
    img_msk msk →
    MemA.compare_val v1 v2 = Vint succ →
    E -∗
    (E ==∗ ∃ q0 q1 v1' v2', MemA.val_r v1 q0 v1' ∗ MemA.val_r v2 q1 v2' ∗
          (MemA.val_r v1 q0 v1' ∗ MemA.val_r v2 q1 v2' ==∗ E)) -∗
    (E -∗
      wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps true
        (st_src, k_s)
        (st_tgt, k_t (Vint succ)↑)) -∗
    wsim fl_s fl_t Ist (E1, E2) r g R_s R_t RR ps pt
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
End mem.

Tactic Notation "mLoadT" uconstr(H) :=
  iApply (wsim_mem_load with H); [try by simpl_map|ss|]; last (iIntros H; cStepsT).
Tactic Notation "mStoreT" uconstr(H) :=
  iApply (wsim_mem_store with H); [try by simpl_map|ss|]; last (iIntros H; cStepsT).
Tactic Notation "mAllocT" "as" "(" simple_intropattern(x) ")" uconstr(H) :=
  iApply wsim_mem_alloc; [try by simpl_map|ss|ss|iIntros (x) H; cStepsT].
Tactic Notation "mFreeT" uconstr(H) :=
  iApply (wsim_mem_free with H); [try by simpl_map|ss|cStepsT].
