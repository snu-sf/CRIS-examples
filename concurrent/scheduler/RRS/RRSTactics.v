Require Import CRIS.common.CRIS.
Require Import CRIS.simulations.msim.ITactics.
From CRIS.simulations.msim Require Import MSim WSim.
Require Import RRSHeader RRSA.

Require Import CRIS.lib.ltac2_lib.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I, _RRS: !rrsGS}.

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
  Context (N : namespace).

  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).

  Lemma wsim_yield_tgt_rr
      (E : coPset) (g : rel)
      (k_s : () → itree crisE R_s) (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask) (sp_s sp_t : specmap) :
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call RRSHdr.yield_global.1 ()↑))) →
    sp_s.1 !! fid RRSHdr.yield_global = None →
    sp_t.1 !! fid RRSHdr.yield_global = None →
    Ist st_src st_tgt ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s ℛ𝒴)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s ℛ𝒴)) >>= k_s)
      (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t ℛ𝒴)) >>= k_t).
  Proof using.
    intros Hchoose Hcall Hsps Hspt. iIntros "?".
    cCoind CIH g' Hg with ps pt st_src st_tgt. iIntros "[IST SIM]".
    rewrite {2 3}yield_unfold.

    cStepsS. des_if; cStepS; ss.
    cStepsT. rewrite Hchoose. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT.
      iPoseProof ("SIM" $! _ _ with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT. cByCoind CIH. iFrame. }

    cForceS (Some true). cStepsT. cStepsS.
    rewrite Hsps Hspt.
    cStepsS. destruct (msk_s _); cStepS; ss.
    cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (? st_s st_t) "IST".
    destruct Any.downcast; [|cStepsS; ss]. cStepsT. cStepsS.
    cByCoind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_tgt_ir
      (Es : coPset) (g : rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap)
      (mtid stid ssch : nat) :
    sp_s.1 !! fid RRSHdr.yield_global = fsp_some (RRSAS.yield_global_spec Es) →
    sp_t.1 !! fid RRSHdr.yield_global = None →
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call RRSHdr.yield_global.1 ()↑))) →
    Ist st_src st_tgt ∗ RRSAS.Tid mtid stid ssch ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗ RRSAS.Tid mtid stid ssch -∗
      wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR true true
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s ℛ𝒴)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (Es, Es) g R_s R_t RR ps pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s ℛ𝒴)) >>= k_s)
      (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t ℛ𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt Hmsk Hcall. iIntros "?".
    cCoind CIH g' Hg with ps pt st_src st_tgt. iIntros "[IST [TID SIM]]".
    rewrite {2 3}yield_unfold.

    cStepsS. des_if; cStepS; ss.
    cStepsT. rewrite Hmsk. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT.
      iPoseProof ("SIM" $! _ _ with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT. cByCoind CIH. iFrame. }

    cForceS (Some true). cStepsT. cStepsS. rewrite Hsps Hspt.
    cStepsS. des_if; cStepS; ss. cForceS (mtid, stid, ssch); ss.
    cStepsS. des_if; cStepS; ss. cForceS (()↑); s.

    cStepsS. des_if; cStepS; ss. cForceS; iFrame; iSplit; eauto.
    cStepsS. des_if; cStepS; ss. cStepsT. rewrite Hcall; cStepsT.
    cCall "IST" as (? st_s st_t) "IST".
    cStepsT. des_if; cStepS; ss. des_if; cStepsS; ss.
    iDestruct "ASM" as "(-> & -> & TID)". cStepsS. cStepsT.
    cByCoind CIH. iFrame. 
  (*SLOW*)Qed.

  Lemma wsim_yield_tgt_ii
      (E Es Et : coPset) (g : rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap) :
    sp_s.1 !! fid RRSHdr.yield_global = fsp_some (RRSAS.yield_global_spec Es) →
    sp_t.1 !! fid RRSHdr.yield_global = fsp_some (RRSAS.yield_global_spec Et) →
    img_msk msk_t →
    (∀ fn arg, msk_t _ (subevent _ (Call fn arg)) = true) →
    Et ⊆ Es →
    E = Es ∖ Et →
    Ist st_src st_tgt ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗
      wsim fl_s fl_t Ist (E, E) g R_s R_t RR true true
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s ℛ𝒴)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) g R_s R_t RR ps pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s ℛ𝒴)) >>= k_s)
      (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t ℛ𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt [Ht [Hc [Ha [Har Hg]]]] Hcall HE ->. iIntros "?".
    cCoind CIH g' Hg' with ps pt st_src st_tgt. iIntros "[IST SIM]".
    rewrite {2 3}yield_unfold.

    cStepsS. des_if; cStepS; ss.
    cStepsT. rewrite Hc. cStepsT. destruct _q; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT.
      iPoseProof ("SIM" $! _ _ with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 1.
      { iApply "SIM". }
      { iIntros (???????) "P !>". iApply Hg'; ss. }
    }
    destruct b; cycle 1.
    { cForceS (Some false). cStepsS. cStepsT. cByCoind CIH. iFrame. }

    cForceS (Some true). cStepsT. cStepsS. rewrite Hsps Hspt.
    cStepsT. rewrite Hc. cStepsT. destruct _q as [[mtid stid] ssch]. rewrite Hc.
    cStepsT. rewrite Hg. cStepsT. iDestruct "GRT" as "(% & _ & TID)"; cSimpl. rewrite Hcall. cStepsT.
    cStepsS. des_if; cStepS; ss. cForceS (mtid, stid, ssch); ss.
    cStepsS. des_if; cStepS; ss. cForceS (()↑); s.

    cStepsS. des_if; cStepS; ss.
    cForceS. iFrame; iSplit; eauto.
    cStepsS. des_if; cStepS; ss.
    cCall "IST" as (? st_s st_t) "IST".
    rewrite Ht. do 2 (des_if; cStepS; ss). iDestruct "ASM" as "[-> [-> TID]]".
    cStepsS. cForceT. rewrite Ha. cForceT. iFrame. iSplit; et. cStepsT.
    cByCoind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep g (msk_s : emask) sp_s k_s i_t :
    msk_s _ (subevent _ (Choose (option bool))) →
    wsim fl_s fl_t Ist Ep g R_s R_t RR true pt (st_src, k_s tt) (st_tgt, i_t) ⊢
    wsim fl_s fl_t Ist Ep g R_s R_t RR true pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s ℛ𝒴)) >>= k_s) (st_tgt, i_t).
  Proof using.
    iIntros "%Hmsk SIM".
    rewrite /RRS.yield_global; unseal "RRS".
    unfoldIterCS; cStepsS.
    case_match; cycle 1.
    { rewrite ->Hmsk in *; done. }
    cForceS None; cStepsS. iApply "SIM".
  Qed.
End wsim.

Ltac clear_st :=
  hrepeat do 1 match goal with [st: alist key Any.t |- _] => clear st end.

Ltac rrsYieldRR IST :=
  cNormS; cNormT; unshelve iApply (wsim_yield_tgt_rr); [ss|ss|ss|ss|];
  iFrame IST; clear_st; iIntros (??) IST; cShowT; cNormT; cHideT.

Ltac rrsYieldIR H1 H2 :=
  let H2' := eval compute in (H1 ++ " " ++ H2)%string in
  cNormS; cNormT; iApply (wsim_yield_tgt_ir); [cSimpl; ss|cSimpl; ss|ss|ss|iFrame H2'];
  clear_st; iIntros (??) H2'; cShowT; cNormT; cHideT.

Ltac rrsYieldS :=
  cNormS; iApply wsim_yield_src; [ss|cShowS; cNormS; cHideS].
