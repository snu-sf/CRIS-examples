Require Import CRIS.common.CRIS.
From CRIS.lib Require Import AList.
Require Import CRIS.simulations.msim.ITactics.
From CRIS.simulations.msim Require Import MSim WSim.
From CRIS.scheduler Require Import NDS.NDSHeader NDS.NDSA.

Require Import CRIS.lib.ltac2_lib.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I, !stateGS Σ, _NDS: !ndsGS}.

  Context (fl_s fl_t : gmap fname (Any.t → itree crisE Any.t)).
  Context (Ist : iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : retr_type Σ R_s R_t).
  Context (ps pt : bool).
  Context (N : namespace).

  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).

  Lemma wsim_yield_tgt_rr
      (E : coPset) (g : WSim.rel)
      (k_s : () → itree crisE R_s) (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask) (sp_s sp_t : specmap) :
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call NDSHdr.yield.1 ()↑))) →
    sp_s.1 !! fid NDSHdr.yield = None →
    sp_t.1 !! fid NDSHdr.yield = None →
    Ist ∗
    (Ist -∗
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒩)) >>= k_t).
  Proof using.
    intros Hchoose Hcall Hsps Hspt. iIntros "?".
    cCoind CIH g' Hg with ps pt. iIntros "[IST SIM]".
    rewrite {2 3}yield_unfold.

    cStepsS.
    cStepsT. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT.
      iPoseProof ("SIM" with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT. cByCoind CIH. iFrame. }

    cForceS (Some true). cStepsT. cStepsS.
    rewrite Hsps Hspt.
    cStepsS. destruct (msk_s _); [cNormS|cStepS; ss].
    cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (ret) "IST".
    destruct Any.downcast; [|cStepS; ss].
    cStepsT. cStepsS.
    cByCoind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_tgt_ir
      (Es : coPset) (g : WSim.rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap)
      (mtid stid ssch : nat) :
    sp_s.1 !! fid NDSHdr.yield = fsp_some (NDSA.yield_spec Es) →
    sp_t.1 !! fid NDSHdr.yield = None →
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call NDSHdr.yield.1 ()↑))) →
    Ist ∗ NDSA.Tid mtid stid ssch ∗
    (Ist -∗ NDSA.Tid mtid stid ssch -∗
      wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒩)) >>= k_t).
  Proof using.
    intros Hsps Hspt Hmsk Hcall. iIntros "?".
    cCoind CIH g' Hg with ps pt. iIntros "[IST [TID SIM]]".
    rewrite {2 3}yield_unfold.

    cStepsS.
    cStepsT. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT.
      iPoseProof ("SIM" with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT. cByCoind CIH. iFrame. }

    cForceS (Some true). cStepsT. cStepsS. rewrite Hsps Hspt.
    cStepsS.
    cForceS (mtid, stid, ssch); ss.
    cStepsS. cForceS (()↑); s.

    cStepsS.
    cForceS; iFrame; iSplit; eauto.
    cNormS. des_if; cStepsS; ss.
    cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (ret) "IST".
    cStepsT. des_if; cStepS; ss. des_if; cStepsS; ss.
    iDestruct "ASM" as "(-> & -> & TID)".
    cStepsS. cStepsT.
    cByCoind CIH. iFrame. 
  (*SLOW*)Qed.

  Lemma wsim_yield_tgt_ii
      (E Es Et : coPset) (g : WSim.rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap) :
    sp_s.1 !! fid NDSHdr.yield = fsp_some (NDSA.yield_spec Es) →
    sp_t.1 !! fid NDSHdr.yield = fsp_some (NDSA.yield_spec Et) →
    img_msk msk_t →
    (∀ fn arg, msk_t _ (subevent _ (Call fn arg)) = true) →
    Et ⊆ Es →
    E = Es ∖ Et →
    Ist ∗
    (Ist -∗
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒩)) >>= k_t).
  Proof using.
    intros Hsps Hspt [Ht [Hc [Ha [Har Hg]]]] Hcall HE ->. iIntros "?".
    cCoind CIH g' Hg' with ps pt. iIntros "[IST SIM]".
    rewrite {2 3}yield_unfold.

    cStepsS.
    cStepsT. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT.
      iPoseProof ("SIM" with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg'; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT. cByCoind CIH. iFrame. }

    cForceS (Some true). cStepsT. cStepsS. rewrite Hsps Hspt.
    cStepsT. destruct _q as [[mtid stid] ssch].
    iDestruct "GRT" as "(% & _ & TID)"; cSimpl. rewrite Hcall. cStepsT.
    cStepsS.
    cForceS (mtid, stid, ssch); ss.
    cStepsS. cForceS (()↑); s.

    cStepsS.
    cForceS. iFrame; iSplit; eauto.
    cNormS. des_if; cStepsS; ss.
    cCall "IST" as (ret) "IST". do 2 (des_if; cStepS; ss).
    iDestruct "ASM" as "[-> [-> TID]]".
    rewrite Ht. cForceT. rewrite Ha. cForceT. iFrame. iSplit; et. cStepsS. cStepsT.
    cByCoind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep g (msk_s : emask) sp_s k_s i_t :
    msk_s _ (subevent _ (Choose (option bool))) →
    wsim fl_s fl_t Ist Ep g R_s R_t RR true pt (k_s tt) i_t ⊢
    wsim fl_s fl_t Ist Ep g R_s R_t RR true pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s) i_t.
  Proof using.
    iIntros "%Hmsk SIM".
    rewrite /NDS.yield; unseal NDS.
    rewrite unfold_iterC; cStepsS.
    cForceS None; cStepsS. iApply "SIM".
  Qed.

  Lemma wsim_yield_global_tgt_rr
      (E : coPset) (g : WSim.rel)
      (k_s : () → itree crisE R_s) (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask) (sp_s sp_t : specmap) :
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call NDSHdr.yield_global.1 ()↑))) →
    sp_s.1 !! fid NDSHdr.yield_global = None →
    sp_t.1 !! fid NDSHdr.yield_global = None →
    Ist ∗
    (Ist -∗
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒴)) >>= k_t).
  Proof using.
    intros Hchoose Hcall Hsps Hspt. iIntros "?".
    cCoind CIH g' Hg with ps pt. iIntros "[IST SIM]".
    rewrite {2 3}yield_global_unfold.

    cStepsS.
    cStepsT. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT.
      iPoseProof ("SIM" with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT. cByCoind CIH. iFrame. }

    cForceS (Some true). cStepsT. cStepsS.
    rewrite Hsps Hspt.
    cStepsS. destruct (msk_s _); [cNormS|cStepS; ss].
    cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (ret) "IST". destruct Any.downcast; [|cStepS; ss].
    cStepsT. cStepsS.
    cByCoind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_global_tgt_ir
      (Es : coPset) (g : WSim.rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap)
      (mtid stid ssch : nat) :
    sp_s.1 !! fid NDSHdr.yield_global = fsp_some (NDSA.yield_global_spec Es) →
    sp_t.1 !! fid NDSHdr.yield_global = None →
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call NDSHdr.yield_global.1 ()↑))) →
    Ist ∗ NDSA.Tid mtid stid ssch ∗
    (Ist -∗ NDSA.Tid mtid stid ssch -∗
      wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt Hmsk Hcall. iIntros "?".
    cCoind CIH g' Hg with ps pt.

    rewrite {2 3}yield_global_unfold.
    iIntros "[IST [TID SIM]]".
    cStepsS.
    cStepsT. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT.
      iPoseProof ("SIM" with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT. cByCoind CIH. iFrame. }

    cForceS (Some true). cStepsT. cStepsS. rewrite Hsps Hspt.
    cStepsS.
    cForceS (mtid, stid, ssch); ss.
    cStepsS. cForceS (()↑); s.

    cStepsS.
    cForceS; iFrame; iSplit; eauto.
    cNormS. des_if; cStepsS; ss.
    cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (ret) "IST".
    cStepsT. des_if; cStepS; ss. des_if; cStepsS; ss.
    iDestruct "ASM" as "(-> & -> & TID)". cStepsS. cStepsT.
    cByCoind CIH. iFrame. 
  (*SLOW*)Qed.

  Lemma wsim_yield_global_tgt_ii
      (E Es Et : coPset) (g : WSim.rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap) :
    sp_s.1 !! fid NDSHdr.yield_global = fsp_some (NDSA.yield_global_spec Es) →
    sp_t.1 !! fid NDSHdr.yield_global = fsp_some (NDSA.yield_global_spec Et) →
    img_msk msk_t →
    (∀ fn arg, msk_t _ (subevent _ (Call fn arg)) = true) →
    Et ⊆ Es →
    E = Es ∖ Et →
    Ist ∗
    (Ist -∗
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
        ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
        (k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
      ((SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt [Ht [Hc [Ha [Har Hg]]]] Hcall HE ->. iIntros "?".
    cCoind CIH g' Hg' with ps pt. iIntros "[IST SIM]".
    rewrite {2 3}yield_global_unfold.

    cStepsS.
    cStepsT. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT.
      iPoseProof ("SIM" with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg'; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT. cByCoind CIH. iFrame. }

    cForceS (Some true). cStepsT. cStepsS. rewrite Hsps Hspt.
    cStepsT. destruct _q as [[mtid stid] ssch].
    iDestruct "GRT" as "(% & _ & TID)"; cSimpl. rewrite Hcall. cStepsT.
    cStepsS.
    cForceS (mtid, stid, ssch); ss.
    cStepsS. cForceS (()↑); s.

    cStepsS.
    cForceS. iFrame; iSplit; eauto.
    cNormS. des_if; cStepsS; ss.
    cCall "IST" as (ret) "IST". do 2 (des_if; cStepS; ss).
    iDestruct "ASM" as "(-> & -> & TID)".
    rewrite Ht. cForceT. rewrite Ha. cForceT. iFrame. iSplit; et. cStepsS. cStepsT.
    cByCoind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_global_src Ep g (msk_s : emask) sp_s k_s i_t :
    msk_s _ (subevent _ (Choose (option bool))) →
    wsim fl_s fl_t Ist Ep g R_s R_t RR true pt (k_s tt) i_t ⊢
    wsim fl_s fl_t Ist Ep g R_s R_t RR true pt
      ((SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s) i_t.
  Proof using.
    iIntros "%Hmsk SIM".
    rewrite /NDS.yield_global; unseal NDS.
    rewrite unfold_iterC; cStepsS.
    cForceS None; cStepsS. iApply "SIM".
  Qed.
End wsim.

Ltac ndsYieldRR IST :=
  cNormS; cNormT; unshelve iApply (wsim_yield_tgt_rr); [ss|ss|ss|ss|];
  iFrame IST; iIntros IST; cShowT; cNormT; cHideT.

Ltac ndsYieldIR H1 H2 :=
  let H2' := eval compute in (H1 ++ " " ++ H2)%string in
  cNormS; cNormT; iApply (wsim_yield_tgt_ir); [cSimpl; ss|cSimpl; ss|ss|ss|iFrame H2'];
  iIntros H2'; cShowT; cNormT; cHideT.

Ltac ndsYieldS :=
  cNormS; iApply wsim_yield_src; [ss|cShowS; cNormS; cHideS].

Ltac ndsYieldGlobalRR IST :=
  cNormS; cNormT; unshelve iApply (wsim_yield_global_tgt_rr); [ss|ss|ss|ss|];
  iFrame IST; iIntros IST; cShowT; cNormT; cHideT.

Ltac ndsYieldGlobalIR H1 H2 :=
  let H2' := eval compute in (H1 ++ " " ++ H2)%string in
  cNormS; cNormT; iApply (wsim_yield_global_tgt_ir); [cSimpl; ss|cSimpl; ss|ss|ss|iFrame H2'];
  iIntros H2'; cShowT; cNormT; cHideT.

Ltac ndsYieldGlobalS :=
  cNormS; iApply wsim_yield_global_src; [ss|cShowS; cNormS; cHideS].
