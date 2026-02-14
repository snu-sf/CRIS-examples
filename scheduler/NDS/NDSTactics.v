Require Import CRIS.
Require Import ITactics.
Require Import MSim WSim.
Require Import NDSHeader NDSA.

Require Import ltac2_lib.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _NDS: !ndsGS}.

  Local Definition state : Type := gmap key (option Any.t).
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : gmap (option string) (option (Any.t → itree crisE Any.t))).
  Context (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_src st_tgt : state).
  Context (N : namespace).

  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).

  Lemma wsim_yield_tgt_rr
      (E : coPset) (r g : rel)
      (k_s : () → itree crisE R_s) (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask) (sp_s sp_t : specmap) :
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call NDSHdr.yield ()↑))) →
    sp_s !! speckey_fn NDSHdr.yield = None →
    sp_t !! speckey_fn NDSHdr.yield = None →
    Ist st_src st_tgt ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
      (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒩)) >>= k_t).
  Proof using.
    intros Hchoose Hcall Hsps Hspt.
    revert st_src. combine_quant st_tgt.
    combine_quant ps. combine_quant pt.
    eapply wsim_coind. intros g' Hg CIH [pt [ps [st_t st_s]]].
    s; destruct_quant CIH.
    rewrite {2 3}yield_unfold.
    iIntros "[IST SIM]".
    steps_l. destruct (msk_s _); step_l; ss.
    steps_r. rewrite Hchoose. steps_r. destruct _q; cycle 1.
    { force_l (Some false). steps_l. steps_r.
      iPoseProof ("SIM" $! _ _ with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (???????) "$"; done. }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { force_l (Some false). steps_l. steps_r. by_coind CIH. iFrame. }

    force_l (Some true). steps_r. steps_l.
    rewrite Hsps Hspt.
    steps_l. destruct (msk_s _); step_l; ss.
    steps_r. rewrite Hcall; steps_r.
    call "IST". clear st_s st_t; iIntros (? st_s st_t) "IST".
    steps_r. steps_l.
    by_coind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_tgt_ir
      (Es : coPset) (r g : rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap)
      (mtid stid ssch : nat) :
    sp_s !! speckey_fn NDSHdr.yield = fsp_some (NDSA.yield_spec Es) →
    sp_t !! speckey_fn NDSHdr.yield = None →
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call NDSHdr.yield ()↑))) →
    Ist st_src st_tgt ∗ NDSA.Tid mtid stid ssch ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗ NDSA.Tid mtid stid ssch -∗
      wsim fl_s fl_t Ist (Es, Es) r g R_s R_t RR true true
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (Es, Es) r g R_s R_t RR ps pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
      (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒩)) >>= k_t).
  Proof using.
    intros Hsps Hspt Hmsk Hcall.
    revert st_src. combine_quant st_tgt.
    combine_quant ps. combine_quant pt.
    eapply wsim_coind. intros g' Hg CIH [pt [ps [st_t st_s]]].
    s; destruct_quant CIH.

    rewrite {2 3}yield_unfold.
    iIntros "[IST [TID SIM]]".
    steps_l. destruct (msk_s _); step_l; ss.
    steps_r. rewrite Hmsk. steps_r. destruct _q; cycle 1.
    { force_l (Some false). steps_l. steps_r.
      iPoseProof ("SIM" $! _ _ with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (???????) "$"; done. }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { force_l (Some false). steps_l. steps_r. by_coind CIH. iFrame. }

    force_l (Some true). steps_r. steps_l. rewrite Hsps Hspt.
    steps_l. destruct msk_s; step_l; ss. force_l (mtid, stid, ssch); ss.
    steps_l. destruct msk_s; step_l; ss. force_l (()↑); s.

    steps_l. destruct msk_s; step_l; ss. force_l; iFrame; iSplit; eauto.
    steps_l. destruct msk_s; step_l; ss. steps_r. rewrite Hcall; steps_r.
    call "IST". clear st_s st_t; iIntros (? st_s st_t) "IST".
    steps_r.
    steps_l. destruct msk_s; step_l; ss. steps_l. destruct msk_s; steps_l; ss.
    by_coind CIH. iFrame. iDestruct "ASM" as "(? & ? & $)".
  (*SLOW*)Qed.

  Lemma wsim_yield_tgt_ii
      (E Es Et : coPset) (r g : rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap) :
    sp_s !! speckey_fn NDSHdr.yield = fsp_some (NDSA.yield_spec Es) →
    sp_t !! speckey_fn NDSHdr.yield = fsp_some (NDSA.yield_spec Et) →
    img_msk msk_t →
    (∀ fn arg, msk_t _ (subevent _ (Call fn arg)) = true) →
    Et ⊆ Es →
    E = Es ∖ Et →
    Ist st_src st_tgt ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s)
      (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒩)) >>= k_t).
  Proof using.
    intros Hsps Hspt [Ht [Hc [Ha [Har Hg]]]] Hcall HE ->.
    revert st_src. combine_quant st_tgt.
    combine_quant ps. combine_quant pt.
    eapply wsim_coind. intros g' Hg' CIH [pt [ps [st_t st_s]]].
    s; destruct_quant CIH.

    rewrite {2 3}yield_unfold.
    iIntros "[IST SIM]".
    steps_l. destruct (msk_s _); step_l; ss.
    steps_r. rewrite Hc. steps_r. destruct _q; cycle 1.
    { force_l (Some false). steps_l. steps_r.
      iPoseProof ("SIM" $! _ _ with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (???????) "$"; done. }
      { iIntros (???????) "P !>". iApply Hg'; ss. }
    }
    destruct b; cycle 1.
    { force_l (Some false). steps_l. steps_r. by_coind CIH. iFrame. }

    force_l (Some true). steps_r. steps_l. rewrite Hsps Hspt.
    steps_r. rewrite Hc. steps_r. destruct _q as [[mtid stid] ssch]. rewrite Hc.
    steps_r. rewrite Hg. steps_r. iDestruct "GRT" as "(% & _ & TID)"; hss. rewrite Hcall. steps_r.
    steps_l. destruct msk_s; step_l; ss. force_l (mtid, stid, ssch); ss.
    steps_l. destruct msk_s; step_l; ss. force_l (()↑); s.

    steps_l. destruct msk_s; step_l; ss.
    force_l. iFrame; iSplit; eauto.
    steps_l. destruct msk_s; step_l; ss.
    call "IST". clear st_s st_t; iIntros (? st_s st_t) "IST".
    steps_r.
    steps_l. destruct msk_s; step_l; ss. steps_l. destruct msk_s; steps_l; ss.
    rewrite Ht. force_r _q. steps_r. rewrite Ha. force_r. iFrame. steps_r.
    by_coind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_src Ep r g (msk_s : emask) sp_s k_s i_t :
    msk_s _ (subevent _ (Choose (option bool))) →
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt (st_src, k_s tt) (st_tgt, i_t) ⊢
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒩)) >>= k_s) (st_tgt, i_t).
  Proof using.
    iIntros "%Hmsk SIM".
    rewrite /NDS.yield; unseal NDS.
    unfold_iterC_l; steps_l.
    case_match; cycle 1.
    { rewrite ->Hmsk in *; done. }
    force_l None; steps_l. iApply "SIM".
  Qed.

  Lemma wsim_yield_global_tgt_rr
      (E : coPset) (r g : rel)
      (k_s : () → itree crisE R_s) (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask) (sp_s sp_t : specmap) :
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call NDSHdr.yield_global ()↑))) →
    sp_s !! speckey_fn NDSHdr.yield_global = None →
    sp_t !! speckey_fn NDSHdr.yield_global = None →
    Ist st_src st_tgt ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
      (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒴)) >>= k_t).
  Proof using.
    intros Hchoose Hcall Hsps Hspt.
    revert st_src. combine_quant st_tgt.
    combine_quant ps. combine_quant pt.
    eapply wsim_coind. intros g' Hg CIH [pt [ps [st_t st_s]]].
    s; destruct_quant CIH.
    rewrite {2 3}yield_global_unfold.
    iIntros "[IST SIM]".
    steps_l. destruct (msk_s _); step_l; ss.
    steps_r. rewrite Hchoose. steps_r. destruct _q; cycle 1.
    { force_l (Some false). steps_l. steps_r.
      iPoseProof ("SIM" $! _ _ with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (???????) "$"; done. }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { force_l (Some false). steps_l. steps_r. by_coind CIH. iFrame. }

    force_l (Some true). steps_r. steps_l.
    rewrite Hsps Hspt.
    steps_l. destruct (msk_s _); step_l; ss.
    steps_r. rewrite Hcall; steps_r.
    call "IST". clear st_s st_t; iIntros (? st_s st_t) "IST".
    steps_r. steps_l.
    by_coind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_global_tgt_ir
      (Es : coPset) (r g : rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap)
      (mtid stid ssch : nat) :
    sp_s !! speckey_fn NDSHdr.yield_global = fsp_some (NDSA.yield_global_spec Es) →
    sp_t !! speckey_fn NDSHdr.yield_global = None →
    (∀ X, msk_t _ (subevent _ (Choose X))) →
    (msk_t _ (subevent _ (Call NDSHdr.yield_global ()↑))) →
    Ist st_src st_tgt ∗ NDSA.Tid mtid stid ssch ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗ NDSA.Tid mtid stid ssch -∗
      wsim fl_s fl_t Ist (Es, Es) r g R_s R_t RR true true
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (Es, Es) r g R_s R_t RR ps pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
      (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt Hmsk Hcall.
    revert st_src. combine_quant st_tgt.
    combine_quant ps. combine_quant pt.
    eapply wsim_coind. intros g' Hg CIH [pt [ps [st_t st_s]]].
    s; destruct_quant CIH.

    rewrite {2 3}yield_global_unfold.
    iIntros "[IST [TID SIM]]".
    steps_l. destruct (msk_s _); step_l; ss.
    steps_r. rewrite Hmsk. steps_r. destruct _q; cycle 1.
    { force_l (Some false). steps_l. steps_r.
      iPoseProof ("SIM" $! _ _ with "IST TID") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (???????) "$"; done. }
      { iIntros (???????) "P !>". iApply Hg; ss. }
    }
    destruct b; cycle 1.
    { force_l (Some false). steps_l. steps_r. by_coind CIH. iFrame. }

    force_l (Some true). steps_r. steps_l. rewrite Hsps Hspt.
    steps_l. destruct msk_s; step_l; ss. force_l (mtid, stid, ssch); ss.
    steps_l. destruct msk_s; step_l; ss. force_l (()↑); s.

    steps_l. destruct msk_s; step_l; ss. force_l; iFrame; iSplit; eauto.
    steps_l. destruct msk_s; step_l; ss. steps_r. rewrite Hcall; steps_r.
    call "IST". clear st_s st_t; iIntros (? st_s st_t) "IST".
    steps_r.
    steps_l. destruct msk_s; step_l; ss. steps_l. destruct msk_s; steps_l; ss.
    by_coind CIH. iFrame. iDestruct "ASM" as "(? & ? & $)".
  (*SLOW*)Qed.

  Lemma wsim_yield_global_tgt_ii
      (E Es Et : coPset) (r g : rel)
      (k_s : () → itree crisE R_s)
      (k_t : () → itree crisE R_t)
      (msk_s msk_t : emask)
      (sp_s sp_t : specmap) :
    sp_s !! speckey_fn NDSHdr.yield_global = fsp_some (NDSA.yield_global_spec Es) →
    sp_t !! speckey_fn NDSHdr.yield_global = fsp_some (NDSA.yield_global_spec Et) →
    img_msk msk_t →
    (∀ fn arg, msk_t _ (subevent _ (Call fn arg)) = true) →
    Et ⊆ Es →
    E = Es ∖ Et →
    Ist st_src st_tgt ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
        (st_tgt, k_t tt)) ⊢
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s)
      (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t 𝒩𝒴)) >>= k_t).
  Proof using.
    intros Hsps Hspt [Ht [Hc [Ha [Har Hg]]]] Hcall HE ->.
    revert st_src. combine_quant st_tgt.
    combine_quant ps. combine_quant pt.
    eapply wsim_coind. intros g' Hg' CIH [pt [ps [st_t st_s]]].
    s; destruct_quant CIH.

    rewrite {2 3}yield_global_unfold.
    iIntros "[IST SIM]".
    steps_l. destruct (msk_s _); step_l; ss.
    steps_r. rewrite Hc. steps_r. destruct _q; cycle 1.
    { force_l (Some false). steps_l. steps_r.
      iPoseProof ("SIM" $! _ _ with "IST") as "SIM".
      iPoseProof (wsim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (???????) "$"; done. }
      { iIntros (???????) "P !>". iApply Hg'; ss. }
    }
    destruct b; cycle 1.
    { force_l (Some false). steps_l. steps_r. by_coind CIH. iFrame. }

    force_l (Some true). steps_r. steps_l. rewrite Hsps Hspt.
    steps_r. rewrite Hc. steps_r. destruct _q as [[mtid stid] ssch]. rewrite Hc.
    steps_r. rewrite Hg. steps_r. iDestruct "GRT" as "(% & _ & TID)"; hss. rewrite Hcall. steps_r.
    steps_l. destruct msk_s; step_l; ss. force_l (mtid, stid, ssch); ss.
    steps_l. destruct msk_s; step_l; ss. force_l (()↑); s.

    steps_l. destruct msk_s; step_l; ss.
    force_l. iFrame; iSplit; eauto.
    steps_l. destruct msk_s; step_l; ss.
    call "IST". clear st_s st_t; iIntros (? st_s st_t) "IST".
    steps_r.
    steps_l. destruct msk_s; step_l; ss. steps_l. destruct msk_s; steps_l; ss.
    rewrite Ht. force_r _q. steps_r. rewrite Ha. force_r. iFrame. steps_r.
    by_coind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_yield_global_src Ep r g (msk_s : emask) sp_s k_s i_t :
    msk_s _ (subevent _ (Choose (option bool))) →
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt (st_src, k_s tt) (st_tgt, i_t) ⊢
    wsim fl_s fl_t Ist Ep r g R_s R_t RR true pt
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s 𝒩𝒴)) >>= k_s) (st_tgt, i_t).
  Proof using.
    iIntros "%Hmsk SIM".
    rewrite /NDS.yield_global; unseal NDS.
    unfold_iterC_l; steps_l.
    case_match; cycle 1.
    { rewrite ->Hmsk in *; done. }
    force_l None; steps_l. iApply "SIM".
  Qed.
End wsim.

Ltac clear_st :=
  hrepeat do 1 match goal with [st: alist key Any.t |- _] => clear st end.

Ltac simpl_sp :=
  try match goal with
  | H : ?sp1 ⊆ ?sp2 |- context [?sp2 !! ?key] =>
    unshelve erewrite (lookup_weaken sp1 sp2 key _ _ H);
    [|rewrite /sp1; simpl_map; reflexivity|]
  end.

Ltac nds_yield_rr IST :=
  (norm_l with 
    (do 1 unshelve iApply (wsim_yield_tgt_rr); [ss|ss|ss|ss|];
      iFrame IST)); clear_st; iIntros (??) IST.

Ltac nds_yield_ir H1 H2 :=
  let H2' := eval compute in (H1 ++ " " ++ H2)%string in
  (norm_l with do 1 (iApply (wsim_yield_tgt_ir); [simpl_sp; ss|simpl_sp; ss|ss|ss|iFrame H2']));
  clear_st; iIntros (??) H2'.

Ltac nds_yield_l :=
  norm_l with do 1 iApply wsim_yield_src; [ss|].

Ltac nds_yield_global_rr IST :=
  (norm_l with 
    (do 1 unshelve iApply (wsim_yield_global_tgt_rr); [ss|ss|ss|ss|];
      iFrame IST)); clear_st; iIntros (??) IST.

Ltac nds_yield_global_ir H1 H2 :=
  let H2' := eval compute in (H1 ++ " " ++ H2)%string in
  (norm_l with do 1 (iApply (wsim_yield_global_tgt_ir); [simpl_sp; ss|simpl_sp; ss|ss|ss|iFrame H2']));
  clear_st; iIntros (??) H2'.

Ltac nds_yield_global_l :=
  norm_l with do 1 iApply wsim_yield_global_src; [ss|].

