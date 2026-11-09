Require Import CRIS.common.CRIS.
From CRIS.scheduler Require Import NDS.NDSHeader NDS.NDSI NDS.NDSA.
From iris Require Import gmap_view.

Module NDSIA. Section sim.
  Import NDSA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_ndsG: !ndsGS}.

  Context (sp sp_nds_user : specmap).
  Context (parent_yield: string).
  Context (parent_yield_fsp: fspec).
  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).
  Context (SchInSp : sp.1 !! (funid parent_yield) = fsp_some parent_yield_fsp).
  Context (NDSInSp :(NDSA.sp sp_nds_user ⊤ T get_stid PYIP) ⊆ sp).
  Context (NdsInSchSp : sp_nds_user ⊆ sp).
  Context (YieldSpec :
              ⊢ fspec_imply parent_yield_fsp
                (fspec_winv ⊤
                   (fspec_mk 
                      (λ x varg arg, 
                        TID (get_stid x) ∗ YIELD (get_stid x) ∗ PYIP x ∗ ⌜varg = arg ∧ varg = tt↑⌝)
                      (λ x vret ret, 
                        TID (get_stid x) ∗ YIELD (get_stid x) ∗ PYIP x ∗ ⌜vret = ret ∧ vret = tt↑⌝))%I)).
  Context (ConcInSp : sp.2).

  Local Notation ths_type :=
    (list (nat * option (SAny.t * SAny.t) * (SAny.t -d> SAny.t -d> leibnizO {n : level & GTerm.t n}))).

  Definition Ist_init (mtid stid ssch: nat) (ths: ths_type) : iProp Σ :=
    (⌜ths = [] ∧ mtid = 0 ∧ ssch = 0⌝ ∗ Pending ∗ pub_priv)%I.
  Definition Ist_private (mtid stid ssch : nat) (ths: ths_type) : iProp Σ :=
    ⌜∃ ro_cur post_cur, ths !! mtid = Some (stid, ro_cur, post_cur)⌝ ∗
    ([∗ list] i ↦ e ∈ ths.*1.*1, if decide (i = mtid) then emp else YIELD e) ∗
    YIELD ssch ∗ Shot ssch ∗ Control 
    ∗ PublicAuth ((λ '(n, rv, _), (n, fst <$> rv : option SAny.t)) <$> ths) None.
  Definition Ist_public (mtid stid ssch : nat) (ths: ths_type) : iProp Σ :=
    ⌜∃ ro_cur post_cur, ths !! mtid = Some (stid, ro_cur, post_cur)⌝ ∗
    ([∗ list] i ↦ e ∈ ths.*1.*1, if decide (i = mtid) then emp else YIELD e) ∗
    YIELD ssch ∗ Shot ssch
    ∗ PublicAuth ((λ '(n, rv, _), (n, fst <$> rv : option SAny.t)) <$> ths) (Some mtid).
  Definition Ist_global_in (mtid stid ssch : nat) (ths: ths_type) : iProp Σ :=
    ⌜∃ ro_cur post_cur, ths !! mtid = Some (stid, ro_cur, post_cur)⌝ ∗
    ([∗ list] _ ↦ e ∈ ths.*1.*1, YIELD e) ∗ Shot ssch ∗ tid_global mtid stid
    ∗ PublicAuth ((λ '(n, rv, _), (n, fst <$> rv : option SAny.t)) <$> ths) None.
  Definition Ist_global_out (mtid stid ssch : nat) (ths: ths_type) : iProp Σ :=
    ⌜∃ ro_cur post_cur, ths !! mtid = Some (stid, ro_cur, post_cur)⌝ ∗
    ([∗ list] i ↦ e ∈ ths.*1.*1, if decide (i = mtid) then emp else YIELD e) ∗
    YIELD ssch ∗ Shot ssch ∗ tid_global mtid stid
    ∗ PublicAuth ((λ '(n, rv, _), (n, fst <$> rv : option SAny.t)) <$> ths) None.

  Section SIM_FUNS.
  Context `{STATE : !stateGS Σ}.

  Definition Ist : iProp Σ :=
      (∃ ths tid_cur stid_cur ssch,
        NDSI.v_ths ↦src
          (((λ '(n, rv, _), (n, fst <$> rv : option SAny.t))
            <$> ths : list (nat * option SAny.t))↑) ∗
        NDSI.v_tid ↦src tid_cur↑ ∗
        NDSI.v_sch ↦src ssch↑ ∗
        NDSI.v_ths ↦tgt
          (((λ '(n, rv, _), (n, snd <$> rv : option SAny.t))
            <$> ths : list (nat * option SAny.t))↑) ∗
        NDSI.v_tid ↦tgt tid_cur↑ ∗
        NDSI.v_sch ↦tgt ssch↑ ∗
        JoinAuth (list_to_map (imap (λ i RR, (i, to_agree RR)) ths.*2)) ∗
        TidAuth (list_to_map (imap pair ths.*1.*1)) ∗
        ([∗ list] i ↦ e ∈ ths,
          match e.1.2 with
          | None => True
          | Some (vrv, rv) =>
              JoinFrag (3/4) i e.2 ∗ interp_cond (e.2 vrv rv) ∨
              JoinFrag 1 i e.2
          end) ∗
        (Ist_init tid_cur stid_cur ssch ths
         ∨ Ist_private tid_cur stid_cur ssch ths
         ∨ Ist_public tid_cur stid_cur ssch ths
         ∨ Ist_global_in tid_cur stid_cur ssch ths
         ∨ Ist_global_out tid_cur stid_cur ssch ths))%I.

  Local Definition NDSAMod := NDSA.t parent_yield sp sp_nds_user T get_stid PYIP.
  Local Definition NDSIMod := NDSI.t parent_yield.

  Lemma simF_init :
    ⊢ ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.init).
  Proof using SchInSp NDSInSp NdsInSchSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /NDSI.init /init.

    cStepS. destruct _q as [[x pre] post].
    cStepsS. iDestruct "ASM" as "(% & % & % & % & (% & % & Spawn) & T & Y & (P & C) & PRE & YI)"; des; subst; cSimpl.
    cStepsS. cStepsT.
    rewrite ConcInSp.

    cForcesS. iSplitL "T"; eauto. cStepsS. cStepsT. cStep. cStepsS. cStepsT.
    iDestruct "ASM" as "[% T]"; subst.

    iDestruct "IST" as (ths tid_cur stid_cur ssch)
      "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
       [IST_init | [IST_private | [IST_public |
        [IST_global_in | IST_global_out]]]])"; cycle 1.
    { iDestruct "IST_private" as "(% & Ys & Ysch & S & C' & Pub)"; des; subst.
      iExFalso. iApply (PendingShot_false with "[P S]"); iFrame. }
    { iDestruct "IST_public" as "(% & Ys & Ysch & S & Pub)"; des; subst.
      iExFalso. iApply (PendingShot_false with "[P S]"); iFrame. }
    { iDestruct "IST_global_in" as "(% & Ys & S & tidF & Pub)"; des; subst.
      iExFalso. iApply (PendingShot_false with "[P S]"); iFrame. }
    { iDestruct "IST_global_out" as "(% & Ys & Ysch & S & tidF)"; des; subst.
      iExFalso. iApply (PendingShot_false with "[P S]"); iFrame. }

    iDestruct "IST_init" as "(% & P' & Pub)"; des; subst; cSimpl.
    cStepsS. cStepsT. cSimpl.
    cStepsS. cStepsT. simpl_sp.

    cForceS ((fn, tt↑↑)↑).
    cStepsS. cSpawn as (stid_new).
    cStepsS. cForceS (false, pre, post). cStepsS.
    cStepsT. iDestruct "ASM" as "Ynew".
    set (mtid_new := 0).

    iMod (own_update with "JoinA") as "[JoinA JoinF]".
    { eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) (to_agree post)); ss. }
    
    iMod (own_update with "TidA") as "[TidA TidF]".
    { eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) (to_agree stid_new)); ss. }

    iMod (Pending_Shot (get_stid x) with "[P P']") as "S"; iFrame.
    iPoseProof (Shot_dup with "S") as "[S S']".

    rewrite -{2}Qp.three_quarter_quarter -dfrac_op_own -{2}(agree_idemp (to_agree _)).
    iDestruct "JoinF" as "[JoinF1 JoinF2]".

    rewrite -{4}Qp.half_half -dfrac_op_own -{2}(agree_idemp (to_agree stid_new)).
    iDestruct "TidF" as "[TidF1 TidF2]".

    iMod (own_update with "Pub") as "[PubA PubF]".
    { eapply (gmap_view_alloc _ None (DfracOwn 1) (to_agree (false))); ss. }
    iMod (own_update with "PubA") as "[PubA PubF']".
    { eapply (gmap_view_alloc _ (Some 0) (DfracOwn 1) (to_agree (false))); ss. }
    
    cForceS. iSplitL "JoinF1 TidF1 C PRE PubF' Spawn".
    { iIntros "Y T W". iFrame. iExists _. iSplit; eauto. rewrite /Public. unseal NDS. iFrame; eauto. }

    cStepsS.
    cStepsS. cStepsT.
    cStepsS. cStepsT.
    rewrite /SModTr.HoareYield.
    rewrite ConcInSp.
    cForceS; iFrame. cStepsS.
    iApply wsim_unfold; iIntros "WI".
    cForcesS. iFrame. cStepsS. cStepsT.
    iApply wsim_yield.
    iSplitL "Y THSS TIDS SCHS THST TIDT SCHT JoinA JoinF2 TidA TidF2 S' PubA".
    { iExists [(stid_new, None, post)], 0, stid_new, (get_stid x).
      iFrame "THSS TIDS SCHS THST TIDT SCHT". ss. iFrame.
      iSplit; eauto. do 4 iRight. iFrame; ss.
      rewrite /PublicAuth. unseal NDS. rewrite /tid_global. iSplit; eauto. }
    iIntros "IST".

    cStepsS. cStepsT. iDestruct "ASM" as "(T & Y & WI)".

    cBind (λ _ _, False%I) as (??) "F"; ss.

    clear H1. iApply wsim_reset.
    cCoind CIH g Hg with x.
    iIntros "(PYIP & S & PubF & IST & T & Y & WI)"; subst.
    unfoldIterCS. unfoldIterCT.

    cStepsT. cStepsS. rewrite SchInSp.
    destruct parent_yield_fsp; ss.
    iPoseProof (YieldSpec with "") as "SPEC".
    unfold fspec_imply; ss.
    iSpecialize ("SPEC" with "[] [T Y WI PYIP]").
    { iPureIntro. rr; ss. exists x. esplits; eauto. }
    { rewrite /FSpec.precond /fspec_winv /= /FSpec.precond. iFrame. iSplit; eauto. }
    iMod "SPEC" as (??) "[%SPEC0 [PRE POST]]".
    destruct SPEC0 as [x0 [pre0 post0]].
    cForceS x0. cForcesS. iSplitL "PRE".
    { instantiate (1:=tt↑). subst P0. iFrame. }
    unfoldPrePost.

    cStepsS. cCall "IST" as (?) "IST". cStepsS. cStepsT.

    iSpecialize ("POST" $! _q ret).
    iMod ("POST" with "[ASM]") as "(WI & (T & Y & PYIP & %))"; des; subst.
    { iFrame. }

    iDestruct "IST" as (ths tid_cur stid_cur0 ssch)
      "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
       [IST_init | [IST_private | [IST_public |
        [IST_global_in | IST_global_out]]]])"; cycle 4.
    { iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF)"; des; subst.
      iExFalso. iPoseProof (Shot_match with "S S'") as "%"; subst.
      iPoseProof (YieldToken_both with "Ysch Y") as "%"; ss. }
    { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
      iPoseProof (PendingShot_false with "[P S]") as "%"; iFrame; ss. }
    { iDestruct "IST_private" as "(% & Ys & Ysch & S' & C')"; des; subst.
      iExFalso. iPoseProof (Shot_match with "S S'") as "%"; subst.
      iPoseProof (YieldToken_both with "Ysch Y") as "%"; ss. }
    { iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
      iExFalso. iPoseProof (Shot_match with "S S'") as "%"; subst.
      iPoseProof (YieldToken_both with "Ysch Y") as "%"; ss. }
    
    iDestruct "IST_global_in" as "(% & Ys & S' & tidF & PubA)"; des; subst.
    iPoseProof (Shot_match with "S S'") as "%"; subst.

    cStepsS. cStepsT.
    cStepsS. cStepsT.
    cStepsS. cStepsT.
    rewrite !list_lookup_fmap !H /=. cStepsS. cStepsT.
    rewrite ConcInSp.
    cStepsT. cForcesS.

    iPoseProof (big_sepL_delete _ ths.*1.*1 tid_cur with "Ys") as "[Y' Ys]"; eauto.
    { rewrite ?list_lookup_fmap H //. }

    iSplitL "Y' T WI"; iFrame.

    cStepsS. iApply wsim_yield.
    iSplitL "THSS TIDS SCHS THST TIDT SCHT JoinA TidA Rs S' tidF Y Ys PubA".
    { iExists ths, tid_cur, stid_cur0, (get_stid x).
      iFrame "THSS TIDS SCHS THST TIDT SCHT". iFrame. do 4 iRight.
      iFrame. eauto. }
    iIntros "IST".
    
    cStepsS. cStepsT.

    cByCoind CIH; eauto. iFrame.
  (*SLOW*)Qed.

  Lemma simF_inner_spawn :
    ⊢ ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr._spawn).
  Proof using SchInSp NDSInSp NdsInSchSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /NDSI.inner_spawn /inner_spawn.

    cStepsS. destruct _q as [[b pre] postS].
    destruct b.
    { (* CASE 1 : normal case *)
      iDestruct "ASM" as "[%stid [%fvarg [%farg [%fn [%mtid [[-> ->] [Spawn [PRE [JoinF [TidF [PubF [WI [TID YIELD]]]]]]]]]]]]]".
      cStepsS.

      iDestruct "IST" as (ths tid_cur stid_cur ssch)
        "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
         [IST_init | [IST_private | [IST_public |
          [IST_global_in | IST_global_out]]]])"; cycle 2.
      { iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
        iExFalso. iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        destruct (decide (tid_cur = mtid)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
          case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
        rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0.
        iPoseProof (Public_Auth_Token with "PubA PubF") as "%". ss. }
      { iDestruct "IST_global_in" as "(% & Ys & S' & tidF)"; des; subst.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        destruct (decide (tid_cur = mtid)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
          by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
        iPoseProof (big_sepL_delete _ ths.*1.*1 mtid with "Ys") as "[Y' Ys]"; eauto.
        by iPoseProof (YieldToken_both with "Y' YIELD") as "%". }
      { iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF & PubA)"; des; subst.
        iExFalso. iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        destruct (decide (tid_cur = mtid)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
          case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
        iPoseProof (big_sepL_delete _ ths.*1.*1 mtid with "Ys") as "[Y' Ys]"; eauto.
        iCombine "tidF TidF" gives %wf. rewrite -gmap_view_frag_op dfrac_op_own in wf.
        eapply gmap_view_frag_valid in wf; des; ss. }
      { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%"; iFrame.
        rewrite lookup_empty // in H. }

      iDestruct "IST_private" as "(% & Ys & Ysch & S' & C' & PubA)"; des; subst.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      destruct (decide (tid_cur = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
      rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0.

      iDestruct "Spawn" as "(%fsp & %Hspawn & Spawn)". cSimpl.

      iPoseProof (Public_update_public with "PubA PubF") as ">[PubA PubF]"; eauto.
      { rewrite !list_lookup_fmap H /=. eauto. }

      iPoseProof (Shot_dup with "S'") as "[S S']".

      iDestruct ("Spawn" with "[] [WI PRE TidF TID YIELD S' C' PubF]") as "> [% [% [%Hfsp [Hpre Hpost]]]]".
      { iPureIntro; exists (mtid, stid, ssch); split; done. }
      { rewrite /precond /fspec_winv. iFrame. iSplit; eauto. }
      cForceS (FSpec_mk _ _ Hfsp).
      cForcesS. iFrame "Hpre".
      cStepsS. cStepsT.

      cCall "THSS TIDS SCHS THST TIDT SCHT TidA JoinA Rs Ys Ysch PubA S"
        as (?) "IST".
      { iExists ths, mtid, stid, ssch.
        iFrame "THSS TIDS SCHS THST TIDT SCHT".
        iFrame. do 2 iRight. iLeft. iFrame. eauto. }

      (* after cCall - prepare for termination *)
      cStepsS. rename _q into vret.
      iMod ("Hpost" $! vret ret with "ASM") as "POST".
      iDestruct "POST" as "[W (% & % & (TidF & TID & YIELD & S & C & PubF) & % & % & Q)]"; des; subst.
      cStepsS. cStepsT.

      iDestruct "IST" as (ths0 tid_cur stid_cur0 ssch0)
        "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
         [IST_init | [IST_private | [IST_public |
          [IST_global_in | IST_global_out]]]])"; cycle 3.
      { iDestruct "IST_global_in" as "(% & Ys & S' & tidF & PubA)"; des; subst.
        iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
      { iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF & PubA)"; des; subst.
        iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
      { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
        iExFalso. iPoseProof (PendingShot_false with "[P S]") as "%"; iFrame; ss. }
      { iDestruct "IST_private" as "(% & Ys & Ysch & S' & C' & PubA)"; des; subst.
        iExFalso. iPoseProof (Control_nodup with "[C C']") as "%"; iFrame; ss. }

      iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
      iPoseProof (Shot_match with "S S'") as "%"; subst.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      destruct (decide (tid_cur = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
      rewrite !list_lookup_fmap H0 in Hmtid0. inv Hmtid0.

      cStepsS. cStepsT.
      cStepsS. cStepsT.
      cStepsS. cStepsT.
      rewrite ?list_lookup_fmap H0 /=.
      cStepsS. cStepsT.
      cStepsS. cStepsT.

      iCombine "TidA TidF"
        gives %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
      rewrite lookup_fmap_Some ?imap_fmap in Hav'; destruct Hav' as [? [? Hav']].
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hav'.
      destruct Hav' as [mtid2 [[[stid2 ?] ?] [EQ Hmtid2]]]; symmetry in EQ; inv EQ.
      apply to_agree_included_L in Hincl; symmetry in Hincl; inv Hincl; ss; clarify.

      iCombine "JoinA JoinF"
        gives %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hav'.
      destruct Hav' as [mtid3 [postS' [EQ Hmtid3]]]; symmetry in EQ; inv EQ.
      apply to_agree_included in Hincl; symmetry in Hincl.
      rewrite list_lookup_fmap H0 in Hmtid3; ss. clarify.

      (* IST construction *)
      cIst "IST" with
        "[THSS TIDS SCHS THST TIDT SCHT JoinF JoinA TidA Rs Ys Ysch S' PubA Q]".
      { iExists (<[mtid := (stid, Some (vr, sret), _)]> ths0),
          mtid, stid, ssch0.
        iSplitL "THSS"; first (rewrite list_fmap_insert; iFrame).
        iSplitL "TIDS"; first iFrame.
        iSplitL "SCHS"; first iFrame.
        iSplitL "THST"; first (rewrite list_fmap_insert; iFrame).
        iSplitL "TIDT"; first iFrame.
        iSplitL "SCHT"; first iFrame.
        eapply elem_of_list_split_length in H0 as [ths1 [ths2 [-> Hlen]]].
        iSplitL "JoinA".
        { rewrite Hlen. rewrite insert_app_r_alt; last done.
          rewrite Nat.sub_diag /= ?fmap_app ?imap_app //=.
        }
        iSplitL "TidA".
        { rewrite Hlen; rewrite insert_app_r_alt; last done.
          rewrite Nat.sub_diag /= ?fmap_app ?imap_app //=.
        }
        iSplitL "Rs Q JoinF".
        { rewrite Hlen insert_app_r_alt; last done.
          iPoseProof (big_sepL_insert_acc _ _ mtid with "Rs") as "[_ RET]"; ss.
          { rewrite Hlen lookup_app_Some; right; split; ss; rewrite Nat.sub_diag //=. }
          iPoseProof ("RET" $! (stid, Some (vr, sret), postS') with "[Q JoinF]") as "RET".
          { ss. specialize (Hincl vr sret) as Hincl'. rewrite Hincl'.
            rewrite /JoinFrag /=; iLeft; iFrame. rewrite Hlen -Hincl. iFrame. }
          rewrite Nat.sub_diag insert_app_r_alt !Hlen // Nat.sub_diag //=.
        }
        do 2 iRight. iLeft. rewrite /Ist_public.
        rewrite Hlen insert_app_r_alt // Nat.sub_diag /=.
        rewrite ?fmap_app ?fmap_cons /=.
        iFrame. iSplit; eauto.
        { iPureIntro. do 2 eexists. rewrite lookup_app.
          des_ifs.
          { eapply lookup_lt_Some in Heq. nia. }
          rewrite Nat.sub_diag //.
        }
        rewrite /PublicAuth. unseal NDS. rewrite !fmap_app !imap_app !map_app /=. iFrame.
      }

      (* Coinduction on yield loop *)
      iApply wsim_fold; iFrame "W".
      rewrite !/NDS.terminate /ccallU. unseal NDS.
      clear H H0.
      iApply wsim_reset.
      cCoind CIH g __ with stid.
      iIntros "[TidF [TID [YIELD [S [C [PubA IST]]]]]] /=".
      unfoldIterCS. unfoldIterCT.

      iApply wsim_unfold; iIntros "W".
      cStepsS. cSimpl.
      cForceS (mtid, stid, ssch0). cForceS (tt↑). cStepsS.
      iApply wsim_guarantee_src; iFrame "W TidF TID YIELD C PubA S". iSplit; eauto.

      cStepsT. cCall "IST" as (?) "IST".
      cStepsS. iDestruct "ASM" as "(% & % & (TidF & TID & YIELD & S & C & PubF))".
      subst. cStepsS. cStepsT.
      cByCoind CIH; eauto. iFrame.
    }
    { (* CASE 2 : init case *)
      iDestruct "ASM" as "[%stid [%fvarg [%farg [%fn [%mtid [[-> [-> ->]] [Spawn [PRE [JoinF [TidF [C [PubF [W [TID YIELD]]]]]]]]]]]]]]".
      cStepsS.

      iDestruct "IST" as (ths tid_cur stid_cur ssch)
        "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
         [IST_init | [IST_private | [IST_public |
          [IST_global_in | IST_global_out]]]])".
      { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%"; iFrame.
        rewrite lookup_empty // in H. }
      { iDestruct "IST_private" as "(% & Ys & Ysch & S' & C' & PubA)"; des; subst.
        iExFalso. iPoseProof (Control_nodup with "[C C']") as "%"; iFrame; ss. }
      { iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
        iExFalso. iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        destruct (decide (tid_cur = 0)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ 0 with "Ys") as "[YIELD2 _]"; eauto.
          case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
        rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0.
        iPoseProof (Public_Auth_Token with "PubA PubF") as "%". ss. }
      { iDestruct "IST_global_in" as "(% & Ys & S' & tidF)"; des; subst.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        destruct (decide (tid_cur = 0)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ 0 with "Ys") as "[YIELD2 _]"; eauto.
          by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
        (* rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0. *)
        iPoseProof (big_sepL_delete _ ths.*1.*1 0 with "Ys") as "[Y' Ys]"; eauto.
        by iPoseProof (YieldToken_both with "Y' YIELD") as "%". }

      iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF & PubA)"; des; subst.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      destruct (decide (tid_cur = 0)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ 0 with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
      rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0.
      iCombine "tidF TidF" as "TidF". rewrite agree_idemp.

      iDestruct "Spawn" as "(%fsp & %Hspawn & Spawn)". cSimpl.

      iPoseProof (Public_update_public with "PubA PubF") as ">[PubA PubF]"; eauto.
      { rewrite !list_lookup_fmap H /=. eauto. }

      iPoseProof (Shot_dup with "S'") as "[S S']".

      iDestruct ("Spawn" with "[] [W PRE TidF TID YIELD S' C PubF]") as "> [% [% [%Hfsp [P Hpost]]]]".
      { iPureIntro; exists (0, stid, ssch); split; done. }
      { rewrite /precond /fspec_winv. iFrame. iSplit; eauto. }
      cForceS (FSpec_mk _ _ Hfsp).
      cForcesS. iFrame "P".
      cStepsS. cStepsT.

      cCall "THSS TIDS SCHS THST TIDT SCHT TidA JoinA Rs Ys Ysch PubA S"
        as (?) "IST".
      { iExists ths, 0, stid, ssch.
        iFrame "THSS TIDS SCHS THST TIDT SCHT".
        iFrame. do 2 iRight. iLeft. iFrame. eauto. }

      (* after cCall - prepare for termination *)
      cStepsS. rename _q into vret.
      iMod ("Hpost" $! vret ret with "ASM") as "POST".
      iDestruct "POST" as "[W (% & % & (TidF & TID & YIELD & S & C & PubF) & % & % & Q)]"; des; subst.
      cStepsS. cStepsT.

      iDestruct "IST" as (ths0 tid_cur stid_cur0 ssch0)
        "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
         [IST_init | [IST_private | [IST_public |
          [IST_global_in | IST_global_out]]]])"; cycle 3.
      { iDestruct "IST_global_in" as "(% & Ys & S' & tidF & PubA)"; des; subst.
        iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
      { iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF & PubA)"; des; subst.
        iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
      { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
        iExFalso. iPoseProof (PendingShot_false with "[P S]") as "%"; iFrame; ss. }
      { iDestruct "IST_private" as "(% & Ys & Ysch & S' & C' & PubA)"; des; subst.
        iExFalso. iPoseProof (Control_nodup with "[C C']") as "%"; iFrame; ss. }

      iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
      iPoseProof (Shot_match with "S S'") as "%"; subst.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      destruct (decide (tid_cur = 0)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ 0 with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
      rewrite !list_lookup_fmap H0 in Hmtid0. inv Hmtid0.

      cStepsS. cStepsT.
      cStepsS. cStepsT.
      cStepsS. cStepsT.
      rewrite ?list_lookup_fmap H0 /=.
      cStepsS. cStepsT.
      cStepsS. cStepsT.

      iCombine "TidA TidF"
        gives %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
      rewrite lookup_fmap_Some ?imap_fmap in Hav'; destruct Hav' as [? [? Hav']].
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hav'.
      destruct Hav' as [mtid2 [[[stid2 ?] ?] [EQ Hmtid2]]]; symmetry in EQ; inv EQ.
      apply to_agree_included_L in Hincl; symmetry in Hincl; inv Hincl; ss; clarify.

      iCombine "JoinA JoinF"
        gives %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hav'.
      destruct Hav' as [mtid3 [postS' [EQ Hmtid3]]]; symmetry in EQ; inv EQ.
      apply to_agree_included in Hincl; symmetry in Hincl.
      rewrite list_lookup_fmap H0 in Hmtid3; ss. clarify.

      (* IST construction *)
      cIst "IST" with
        "[THSS TIDS SCHS THST TIDT SCHT JoinF JoinA TidA Rs Ys Ysch S' PubA Q]".
      { iExists (<[0 := (stid, Some (vr, sret), _)]> ths0),
          0, stid, ssch0.
        iSplitL "THSS"; first (rewrite list_fmap_insert; iFrame).
        iSplitL "TIDS"; first iFrame.
        iSplitL "SCHS"; first iFrame.
        iSplitL "THST"; first (rewrite list_fmap_insert; iFrame).
        iSplitL "TIDT"; first iFrame.
        iSplitL "SCHT"; first iFrame.
        eapply elem_of_list_split_length in H0 as [ths1 [ths2 [-> Hlen]]].
        iSplitL "JoinA".
        { rewrite Hlen; rewrite insert_app_r_alt; last done.
          rewrite Nat.sub_diag /= ?fmap_app ?imap_app //=.
        }
        iSplitL "TidA".
        { rewrite Hlen; rewrite insert_app_r_alt; last done.
          rewrite Nat.sub_diag /= ?fmap_app ?imap_app //=.
        }
        iSplitL "Rs Q JoinF".
        { rewrite Hlen insert_app_r_alt; last done.
          iPoseProof (big_sepL_insert_acc _ _ 0 with "Rs") as "[_ RET]"; ss.
          { rewrite Hlen lookup_app_Some; right; split; ss; rewrite Nat.sub_diag //=. }
          iPoseProof ("RET" $! (stid, Some (vr, sret), postS') with "[Q JoinF]") as "RET".
          { ss. specialize (Hincl vr sret) as Hincl'. rewrite Hincl'.
            rewrite /JoinFrag Hlen /=; iLeft; iFrame. rewrite Hincl. iFrame. }
          rewrite Nat.sub_diag insert_app_r_alt !Hlen // Nat.sub_diag //=.
          rewrite -Hlen. ss.
        }
        do 2 iRight. iLeft. rewrite /Ist_public.
        rewrite Hlen insert_app_r_alt // Nat.sub_diag /=.
        rewrite ?fmap_app ?fmap_cons /=.
        iFrame. iSplit; eauto; destruct ths1; ss. eauto.
      }

      (* Coinduction on yield loop *)
      iApply wsim_fold; iFrame "W".
      rewrite !/NDS.terminate /ccallU. unseal NDS.
      clear H H0.
      iApply wsim_reset.
      cCoind CIH g __ with stid.
      iIntros "[TidF [TID [YIELD [S [C [PubA IST]]]]]] /=".
      unfoldIterCS. unfoldIterCT.

      iApply wsim_unfold; iIntros "W".
      cStepsS. cSimpl.
      cForceS (0, stid, ssch0). cForceS (tt↑). cStepsS.
      iApply wsim_guarantee_src; iFrame "W TidF TID YIELD C PubA S". iSplit; eauto.

      cStepsT. cCall "IST" as (?) "IST".
      cStepsS. iDestruct "ASM" as "(<- & % & (TidF & TID & YIELD & S & C & PubF))".
      subst. cStepsS. cStepsT.
      cByCoind CIH; eauto. iFrame.
    }
  (*SLOW*)Qed.

  Lemma simF_spawn :
    ⊢ ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.spawn).
  Proof using SchInSp NDSInSp NdsInSchSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /NDSI.spawn /spawn.

    (* preprocess source precondition *)
    cStepsS. destruct _q as [[[[mtid stid] ssch] user_pre] user_post].
    iDestruct "ASM" as "(% & % & % & % & % & % & (% & % & Spawn) & (TidF & T & Y & S & C & PubF) & ASM)"; des; subst.
    cStepsS. cStepsT.

    iDestruct "IST" as (ths tid_cur stid_cur ssch0)
      "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
       [IST_init | [IST_private | [IST_public |
        [IST_global_in | IST_global_out]]]])"; cycle 3.
    { iDestruct "IST_global_in" as "(% & Ys & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
      iExFalso. iPoseProof (PendingShot_false with "[P S]") as "%"; iFrame; ss. }
    { iDestruct "IST_private" as "(% & Ys & Ysch & S' & C' & PubA)"; des; subst.
      iExFalso. iPoseProof (Control_nodup with "[C C']") as "%"; iFrame; ss. }

    iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
    iPoseProof (Shot_match with "S S'") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
    rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0.

    cStepsS. cStepsT.
    cStepsS. cStepsT. cSimpl. simpl_sp.

    (* System spawn precondition *)
    cForceS ((fn, farg)↑). cStepsS.
    cStepsT. cSpawn as (tid_new). cStepsS. cForceS (true, user_pre, user_post). cStepsS.
    cStepsT. rewrite ?length_fmap /=. set (mtid_new := length ths).

    iMod (own_update with "JoinA") as "[JoinA JoinF]".
    { etrans; first eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) (to_agree (user_post))); ss.
      { rewrite -not_elem_of_list_to_map fmap_imap; intros Hcont%elem_of_lookup_imap.
        subst mtid_new; destruct Hcont as [? [? [? Hcont]]]; ss; subst.
        eapply lookup_lt_Some in Hcont; rewrite length_fmap in Hcont; lia.
      }
      refl.
    }
    iMod (own_update with "TidA") as "[TidA TidF']".
    { etrans; first eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) (to_agree (tid_new))); ss.
      { apply not_elem_of_dom. rewrite dom_fmap. apply not_elem_of_dom.
        rewrite -not_elem_of_list_to_map ?imap_fmap fmap_imap; intros Hcont%elem_of_lookup_imap.
        subst mtid_new; destruct Hcont as [? [? [? Hcont]]]; ss; subst.
        eapply lookup_lt_Some in Hcont; lia.
      }
      refl.
    }
    rewrite -{4}Qp.three_quarter_quarter -dfrac_op_own -{2}(agree_idemp (to_agree (_))).

    iMod (Public_alloc with "PubA") as "[PubA PubF']"; eauto.
    { right. esplits; eauto. rewrite list_lookup_fmap H //. }

    iDestruct "JoinF" as "[JoinF1 JoinF2]".
    cForceS. iSplitL "ASM JoinF1 TidF' PubF' Spawn".
    { iIntros "Y T W". iFrame " Y T W ASM JoinF1 TidF' Spawn".
      iExists fn. rewrite length_fmap. subst mtid_new. iFrame. iPureIntro; esplits; eauto. }
    cStepsS.
    cStepsS. cStepsT.
    cForceS (mtid_new↑). cStepsS.
    cForceS. iSplitL "JoinF2 T Y TidF S C PubF".
    { iExists _; iSplit; eauto. iFrame; eauto. }
    cStep.

    iSplit; eauto.
    iExists (ths ++ [(tid_new, None, user_post)]), _, _, ssch0.
    iSplitL "THSS"; first (rewrite fmap_app /=; iFrame).
    iSplitL "TIDS"; first iFrame.
    iSplitL "SCHS"; first iFrame.
    iSplitL "THST"; first (rewrite fmap_app /=; iFrame).
    iSplitL "TIDT"; first iFrame.
    iSplitL "SCHT"; first iFrame.
    iSplitL "JoinA".
    { rewrite -list_to_map_snoc.
      { rewrite fmap_app imap_app /= Nat.add_0_r length_fmap; subst mtid_new; done. }
      subst mtid_new; rewrite fmap_imap.
      intros [? [? [Heq Hin]]]%elem_of_lookup_imap; ss; rewrite -Heq in Hin.
      eapply lookup_lt_Some in Hin; rewrite length_fmap in Hin; lia.
    }
    iSplitL "TidA".
    { rewrite /TidAuth ?fmap_app /= imap_app /= ?length_fmap Nat.add_0_r list_to_map_snoc.
      { rewrite fmap_insert //. }
      subst mtid_new; rewrite fmap_imap.
      intros [? [? [Heq Hin]]]%elem_of_lookup_imap; ss; rewrite -Heq in Hin.
      eapply lookup_lt_Some in Hin; rewrite ?length_fmap in Hin; lia.
    }
    iSplitL "Rs".
    { rewrite big_sepL_app /=; iFrame; done. }
    do 2 iRight. iLeft. iFrame. iSplit; eauto.
    { iPureIntro. esplits; eauto. rewrite lookup_app H //. }
    iSplitL "Ys ASM'".
    { by rewrite ?fmap_app big_sepL_app /=; des_ifs; iFrame. }
    rewrite /PublicAuth. unseal NDS. rewrite !fmap_app !imap_app !map_app /=. iFrame.
    Unshelve. exact (tid_new, None).
  (*SLOW*)Qed.

  Lemma simF_yield :
    ⊢ ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.yield).
  Proof using SchInSp NDSInSp NdsInSchSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /NDSI.yield /yield.

    cStepsS. destruct _q as [[mtid stid] ssch].
    iDestruct "ASM" as "(% & % & (TidF & TID & YIELD & S & C & PubF))"; des; subst.
    cStepsS. cStepsT.

    iDestruct "IST" as (ths tid_cur stid_cur ssch0)
      "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
       [IST_init | [IST_private | [IST_public |
        [IST_global_in | IST_global_out]]]])"; cycle 3.
    { iDestruct "IST_global_in" as "(% & Ys & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
      iExFalso. iPoseProof (PendingShot_false with "[P S]") as "%"; iFrame; ss. }
    { iDestruct "IST_private" as "(% & Ys & Ysch & S' & C' & PubA)"; des; subst.
      iExFalso. iPoseProof (Control_nodup with "[C C']") as "%"; iFrame; ss. }

    iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
    iPoseProof (Shot_match with "S S'") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
    rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0.

    cStepsS. cStepsT.
    cStepsS. cStepsT.

    (* GetTid reasoning *)
    rewrite ConcInSp.
    cForcesS; iFrame "TID". cStepsS.
    cStepsT. cStep.
    cStepsS. iDestruct "ASM" as "[-> TID]". cStepsS. cStepsT.
    cStepsS. cStepsT.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    destruct Hmtid as [? [? [EQ Hmtid]]]; symmetry in EQ; inv EQ.

    rewrite ?list_lookup_fmap H /=; cNormS. cNormT. case_decide; subst; clarify.

    (* Choose the next tid *)
    cStepsT. cStepsS.
    destruct _q as [[tidn stidn] Htidn]. unshelve cForceS (exist _ (tidn, stidn) _); last cStepS.
    { ss. revert Htidn; rewrite ?list_lookup_fmap; destruct (ths !! tidn) as [[[? ?] ?]|]; ss. }
    cStepsS. cStepsT.
    cStepsS. cStepsT.

    (* HoareYield *)
    rewrite ConcInSp.
    rewrite ?list_lookup_fmap /= in Htidn.
    iAssert (YIELD stidn ∗
        [∗ list] i ↦ e ∈ ths.*1.*1, if decide (i = tidn) then emp else YIELD e)%I
      with "[YIELD Ys]" as "[YIELD Ys]".
    { destruct (decide (mtid = tidn)). 
      { subst; destruct (ths !! tidn) as [[[? ?] ?]|]; ss; clarify. iFrame. }
      iPoseProof (big_sepL_delete _ ths.*1.*1 mtid with "[Ys YIELD]") as "Ys"; eauto.
      { ss. instantiate (1:=λ _ i, YIELD i). iFrame. }
      rewrite big_sepL_delete; try iFrame.
      rewrite ?list_lookup_fmap; destruct (ths !! tidn) as [[[? ?] ?]|]; ss.
    }
    iApply wsim_unfold; iIntros "WI".
    cForcesS. iFrame "WI TID YIELD".

    iMod (Public_update_private with "PubA PubF") as "[PubA PubF]"; eauto.
    { rewrite list_lookup_fmap H //. eauto. }

    iPoseProof (Shot_dup with "S") as "[S S'']".

    cStepsS. cStepsT.
    iApply wsim_yield.
    iSplitL "THSS TIDS SCHS THST TIDT SCHT JoinA TidA Rs Ysch S'' PubA S Ys C".
    { destruct (ths !! tidn) as [[[? ?] ?]|] eqn : ?; ss; clarify.
      iExists ths, tidn, stidn, ssch0.
      iFrame "THSS TIDS SCHS THST TIDT SCHT".
      iFrame. iRight. iLeft. iFrame. eauto.
    }
    iIntros "IST".

    cStepsS. iDestruct "ASM" as "[TID [YIELD WINV]]".


    iDestruct "IST" as (ths0 tid_cur stid_cur0 ssch)
      "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
       [IST_init | [IST_private | [IST_public |
        [IST_global_in | IST_global_out]]]])"; cycle 2.
    { iDestruct "IST_public" as "(% & Ys & Ysch & S'' & PubA)"; des; subst.
      iExFalso. iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid0"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid0; rewrite elem_of_lookup_imap in Hmtid0.
      des. sym in Hmtid0. inv Hmtid0.
      destruct (decide (tid_cur = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
      rewrite !list_lookup_fmap H1 in Hmtid1. inv Hmtid1.
      iPoseProof (Public_Auth_Token with "PubA PubF") as "%". ss. }
    { iDestruct "IST_global_in" as "(% & Ys & S'' & tidF & PubA)"; des; subst.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid0"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid0; rewrite elem_of_lookup_imap in Hmtid0.
      des. sym in Hmtid0. inv Hmtid0.
      destruct (decide (tid_cur = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
      iPoseProof (big_sepL_delete with "Ys") as "[Y Ys]"; eauto.
      by iPoseProof (YieldToken_both with "Y YIELD") as "%". }
    { iDestruct "IST_global_out" as "(% & Ys & Ysch & S'' & tidF & PubA)"; des; subst.
      iExFalso. iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid0"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid0; rewrite elem_of_lookup_imap in Hmtid0.
      des. sym in Hmtid0. inv Hmtid0.
      destruct (decide (tid_cur = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iCombine "tidF TidF" gives %wf. rewrite -gmap_view_frag_op dfrac_op_own in wf.
      eapply gmap_view_frag_valid in wf; des; ss. }
    { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%"; iFrame.
      rewrite lookup_empty // in H1. }

    iDestruct "IST_private" as "(% & Ys & Ysch & S'' & C' & PubA)"; des; subst.
    iPoseProof (Shot_match with "S' S''") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid0"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid0; rewrite elem_of_lookup_imap in Hmtid0.
    des. sym in Hmtid0. inv Hmtid0.
    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
    rewrite !list_lookup_fmap H1 in Hmtid1. inv Hmtid1.

    iMod (Public_update_public with "PubA PubF") as "[PubA PubF]"; eauto.
    { rewrite list_lookup_fmap H1. eauto. }

    cForcesS. iFrame. iSplit; eauto.
    cStep. iSplit; eauto. iExists ths0, mtid, stid, ssch.
    iFrame "THSS TIDS SCHS THST TIDT SCHT".
    iFrame. do 2 iRight. iLeft. iFrame.
    esplits; eauto.
  (*SLOW*)Qed.

  Lemma simF_yield_global :
    ⊢ ISim.sim_fun open NDSAMod NDSIMod Ist
        (fid NDSHdr.yield_global).
  Proof using SchInSp NDSInSp NdsInSchSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /NDSI.yield_global /yield_global.

    cStepS. destruct _q as [[mtid stid] ssch].
    cStepsS.
    iDestruct "ASM" as "(% & % & (TidF & TID & YIELD & S & C & PubF))"; des; subst. 
    cStepsS. cStepsT.

    iDestruct "IST" as (ths tid_cur stid_cur ssch0)
      "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
       [IST_init | [IST_private | [IST_public |
        [IST_global_in | IST_global_out]]]])"; cycle 3.
    { iDestruct "IST_global_in" as "(% & Ys & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
      iExFalso. iPoseProof (PendingShot_false with "[P S]") as "%"; iFrame; ss. }
    { iDestruct "IST_private" as "(% & Ys & Ysch & S' & C' & PubA)"; des; subst.
      iExFalso. iPoseProof (Control_nodup with "[C C']") as "%"; iFrame; ss. }

    iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
    iPoseProof (Shot_match with "S S'") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
    rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0.

    cStepsS. cStepsT.
    cStepsS. cStepsT.

    (* HoareYield *)
    rewrite ConcInSp.
    iApply wsim_unfold; iIntros "WI".
    cForcesS. iFrame "WI TID Ysch".

    iMod (Public_update_private with "PubA PubF") as "[PubA PubF]"; eauto.
    { rewrite list_lookup_fmap H //. eauto. }

    iPoseProof (Shot_dup with "S") as "[S S'']".

    rewrite -{2}Qp.half_half -dfrac_op_own -(agree_idemp (to_agree (stid))).
    iDestruct "TidF" as "[TidF TidF']".

    cStepsS. cStepsT. iApply wsim_yield.
    iSplitL "THSS TIDS SCHS THST TIDT SCHT JoinA TidA Rs Ys S'' PubA YIELD TidF".
    { iExists ths, mtid, stid, ssch0.
      iFrame "THSS TIDS SCHS THST TIDT SCHT".
      iFrame. do 3 iRight. iLeft. iFrame. eauto. iSplit; eauto.
      iApply big_sepL_delete; eauto.
      { rewrite !list_lookup_fmap. erewrite H. eauto. }
      iFrame.
    }
    iIntros "IST".

    cStepsS. iDestruct "ASM" as "[TID [YIELD WINV]]".

    iDestruct "IST" as (ths0 tid_cur stid_cur0 ssch)
      "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
       [IST_init | [IST_private | [IST_public |
        [IST_global_in | IST_global_out]]]])".
    { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
      iExFalso. iPoseProof (PendingShot_false with "[P S]") as "%"; iFrame; ss. }
    { iDestruct "IST_private" as "(% & Ys & Ysch & S'' & C' & PubA)"; des; subst.
      iExFalso. iPoseProof (Control_nodup with "[C C']") as "%"; iFrame; ss. }
    { iDestruct "IST_public" as "(% & Ys & Ysch & S'' & PubA)"; des; subst.
      iExFalso. iPoseProof (Tid_Auth_Tid with "[TidA TidF']") as "%Hmtid0"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid0; rewrite elem_of_lookup_imap in Hmtid0.
      des. sym in Hmtid0. inv Hmtid0.
      destruct (decide (tid_cur = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
      rewrite !list_lookup_fmap H0 in Hmtid1. inv Hmtid1.
      iPoseProof (Public_Auth_Token with "PubA PubF") as "%". ss. }
    { iDestruct "IST_global_in" as "(% & Ys & S'' & tidF & PubA)"; des; subst.
      iExFalso. iPoseProof (Tid_Auth_Tid with "[TidA TidF']") as "%Hmtid0"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid0; rewrite elem_of_lookup_imap in Hmtid0.
      des. sym in Hmtid0. inv Hmtid0.
      destruct (decide (tid_cur = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
      iPoseProof (big_sepL_delete with "Ys") as "[Y Ys]"; eauto.
      by iPoseProof (YieldToken_both with "Y YIELD") as "%". }

    iDestruct "IST_global_out" as "(% & Ys & Ysch & S'' & tidF & PubA)"; des; subst.
    iPoseProof (Shot_match with "S' S''") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF']") as "%Hmtid0"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid0; rewrite elem_of_lookup_imap in Hmtid0.
    des. sym in Hmtid0. inv Hmtid0.
    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "YIELD YIELD2") as "%". }
    rewrite !list_lookup_fmap H0 in Hmtid1. inv Hmtid1.

    iMod (Public_update_public with "PubA PubF") as "[PubA PubF]"; eauto.
    { rewrite list_lookup_fmap H0. eauto. }

    iCombine "TidF' tidF" as "TidF". rewrite agree_idemp.

    cForcesS. iFrame. iSplit; eauto.
    cStep. iSplit; eauto. iExists ths0, mtid, stid, ssch.
    iFrame "THSS TIDS SCHS THST TIDT SCHT".
    iFrame. do 2 iRight. iLeft. iFrame.
    esplits; eauto.
  (*SLOW*)Qed.

  Lemma simF_join :
    ⊢ ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.join).
  Proof using SchInSp NDSInSp NdsInSchSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /NDSI.join /join.

    cStepS. destruct _q as [[[[mtid stid] ssch] tid] postS].
    cStepsS. iDestruct "ASM" as "(% & % & % & (TidF & T & Y & S & C & PubF) & JoinF)"; des; subst.

    cStepsS. cStepsT. iApply wsim_reset.
    cCoind CIH g' __ with tid.
    iIntros "(IST & Tid & T & Y & S & C & PubF & JoinF)".
    unfoldIterCS; unfoldIterCT.

    iDestruct "IST" as (ths tid_cur stid_cur ssch0)
      "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
       [IST_init | [IST_private | [IST_public |
        [IST_global_in | IST_global_out]]]])"; cycle 3.
    { iDestruct "IST_global_in" as "(% & Ys & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
      iExFalso. iPoseProof (PendingShot_false with "[P S]") as "%"; iFrame; ss. }
    { iDestruct "IST_private" as "(% & Ys & Ysch & S' & C' & PubA)"; des; subst.
      iExFalso. iPoseProof (Control_nodup with "[C C']") as "%"; iFrame; ss. }

    iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
    iPoseProof (Shot_match with "S S'") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA Tid]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
    rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0.
    
    cStepsS. cStepsT.
    cStepsS. cStepsT.

    rewrite ?list_lookup_fmap.
    destruct (ths !! tid) as [[[stid_join [[rv vrv]|]] post2]|] eqn : Htid.
    { cStepsS. cStepsT.
      iPoseProof (big_sepL_lookup_acc _ _ tid with "Rs") as "[J RET]"; eauto; ss.
      iDestruct "J" as "[[JoinF2 Post] | JoinF2]"; cycle 1.
      { iExFalso; iCombine "JoinF" "JoinF2" gives %[WF _]%gmap_view_frag_op_valid.
        rewrite dfrac_op_own // in WF.
      }
      iCombine "JoinF" "JoinF2" gives %[_ WF%to_agree_op_valid]%gmap_view_frag_op_valid.
      iCombine "JoinF" "JoinF2" as "JoinF"; rewrite Qp.quarter_three_quarter.
      (* Search (to_agree _ ⋅ (to_agree _)) *)
      iEval (rewrite WF agree_idemp) in "JoinF".
      iPoseProof ("RET" with "[JoinF]") as "RET"; first (iRight; iFrame).
      cForcesS. iEval (rewrite -WF) in "Post". iFrame "Tid Post T Y S C PubF".
      iSplitR; eauto.
      cStep. iSplit; eauto.
      iExists ths, mtid, stid, ssch0.
      iFrame "THSS TIDS SCHS THST TIDT SCHT".
      iFrame. do 2 iRight. iLeft. iFrame. eauto.
    }
    { cStepsS. cStepsT. cSimpl.
      cForceS (mtid, stid, ssch0). cStepsS. cForceS. cForceS. iFrame "Tid T Y S C PubF". iSplit; eauto.
      cStepsS.
      cCall "THSS TIDS SCHS THST TIDT SCHT JoinA TidA Rs Ys Ysch S' PubA"
        as (?) "IST".
      { iExists ths, mtid, stid, ssch0.
        iFrame "THSS TIDS SCHS THST TIDT SCHT".
        iFrame. do 2 iRight. iLeft. iFrame; eauto. }
      cStepsS. iDestruct "ASM" as "(% & % & (TidF & TID & YIELD & S & C & PubF))"; des; subst.
      cStepsS. cStepsT.
      cByCoind CIH. iFrame.
    }
    { iExFalso; iCombine "JoinA" "JoinF" gives %WF%gmap_view_both_dfrac_valid_discrete_total.
      destruct WF as [? [_ [_ [[? [? [EQ Hcont]]]%elem_of_list_to_map_2%elem_of_lookup_imap _]]]].
      inv EQ. rewrite list_lookup_fmap Htid // in Hcont.
    }
  (*SLOW*)Qed.

  Lemma simF_get_tid :
    ⊢ ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.get_tid).
  Proof using SchInSp NDSInSp NdsInSchSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /NDSI.get_tid /get_tid.

    cStepS. destruct _q as [[mtid stid] ssch].
    cStepsS. iDestruct "ASM" as "(% & % & (Tid & T & Y & S & C & PubF))"; des; subst.
    cStepsS. cStepsT.

    iDestruct "IST" as (ths tid_cur stid_cur ssch0)
      "(THSS & TIDS & SCHS & THST & TIDT & SCHT & JoinA & TidA & Rs &
       [IST_init | [IST_private | [IST_public |
        [IST_global_in | IST_global_out]]]])"; cycle 3.
    { iDestruct "IST_global_in" as "(% & Ys & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_global_out" as "(% & Ys & Ysch & S' & tidF & PubA)"; des; subst.
      iExFalso. by iPoseProof (Public_Auth_Token with "PubA PubF") as "%". }
    { iDestruct "IST_init" as "(% & P & PubA)"; des; subst; ss.
      iExFalso. iPoseProof (PendingShot_false with "[P S]") as "%"; iFrame; ss. }
    { iDestruct "IST_private" as "(% & Ys & Ysch & S' & C' & PubA)"; des; subst.
      iExFalso. iPoseProof (Control_nodup with "[C C']") as "%"; iFrame; ss. }

    iDestruct "IST_public" as "(% & Ys & Ysch & S' & PubA)"; des; subst.
    iPoseProof (Shot_match with "S S'") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA Tid]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid_cur = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
    rewrite !list_lookup_fmap H in Hmtid0. inv Hmtid0.

    iPoseProof (Tid_Auth_Tid with "[TidA Tid]") as "%Hin"; iFrame.
    apply elem_of_list_to_map_2 in Hin; rewrite elem_of_lookup_imap in Hin.
    destruct Hin as [? [? [EQ Hin]]]; symmetry in EQ; inv EQ.

    cStepsS. cForcesS. iFrame. iSplit; eauto.
    cStepsT. cStep.

    iSplit; eauto.
    iExists ths, mtid, stid, ssch0.
    iFrame "THSS TIDS SCHS THST TIDT SCHT".
    iFrame. do 2 iRight. iLeft. iFrame; eauto.
  (*SLOW*)Qed.

  End SIM_FUNS.

  Lemma sim : NDSA.init_cond ⊢ ISim.t open NDSAMod NDSIMod.
  Proof using SchInSp NDSInSp NdsInSchSp YieldSpec ConcInSp.
    cStartModSim (fun STATE : stateGS Σ => Ist (STATE := STATE)).
    - rewrite /init_cond.
      iDestruct "INIT" as "(TiA & JoinA & P & PubA)".
      iEval (rewrite /state_init_src /=) in "SRC".
      iEval (rewrite /state_init_tgt /=) in "TGT".
      assert (SL : state_slice ({[NDS]} : gset string)
          {[NDSI.v_ths # ([] : thpool)↑;
            NDSI.v_tid # 0↑;
            NDSI.v_sch # 0↑]} =
          {[NDSI.v_ths := ([] : thpool)↑;
            NDSI.v_tid := 0↑;
            NDSI.v_sch := 0↑]}).
      { apply map_eq. intros k. rewrite state_slice_lookup.
        destruct (decide (k = NDSI.v_ths)); subst; simpl_map.
        - case_decide; done.
        - destruct (decide (k = NDSI.v_tid)); subst; simpl_map.
          + case_decide; done.
          + destruct (decide (k = NDSI.v_sch)); subst; simpl_map.
            * case_decide; done.
            * repeat case_decide; done.
      }
      iEval (rewrite right_id_L SL) in "SRC".
      iEval (rewrite right_id_L SL) in "TGT".
      iDestruct "SRC" as "[SRC _]".
      iEval (rewrite big_sepM_insert) in "SRC"; last simpl_map.
      iDestruct "SRC" as "[THSS SRC]".
      iEval (rewrite big_sepM_insert) in "SRC"; last simpl_map.
      iDestruct "SRC" as "[TIDS SCHS]".
      iEval (rewrite big_sepM_singleton) in "SCHS".
      iDestruct "TGT" as "[TGT _]".
      iEval (rewrite big_sepM_insert) in "TGT"; last simpl_map.
      iDestruct "TGT" as "[THST TGT]".
      iEval (rewrite big_sepM_insert) in "TGT"; last simpl_map.
      iDestruct "TGT" as "[TIDT SCHT]".
      iEval (rewrite big_sepM_singleton) in "SCHT".
      iExists [], 0, 0, 0.
      iFrame "THSS TIDS SCHS THST TIDT SCHT JoinA TiA".
      iSplit; first done. iLeft; rewrite /Ist_init.
      iSplit.
      { iPureIntro. exact (conj eq_refl (conj eq_refl eq_refl)). }
      rewrite /Pending /pub_priv. unseal NDS. iFrame.
    - iApply simF_init.
    - iApply simF_inner_spawn.
    - iApply simF_spawn.
    - iApply simF_yield.
    - iApply simF_yield_global.
    - iApply simF_join.
    - iApply simF_get_tid.
  Qed.
End sim.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _NDS: !ndsGS}.

  Context (parent_yield: string).
  Context (parent_yield_fsp: fspec).
  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).

  Lemma ctxr sp sp_nds_user
    (SchInSp : sp.1 !! (funid parent_yield) = fsp_some parent_yield_fsp)
    (NDSInSp :(NDSA.sp sp_nds_user ⊤ T get_stid PYIP) ⊆ sp)
    (NdsInSchSp : sp_nds_user ⊆ sp)
    (YieldSpec :
              ⊢ fspec_imply parent_yield_fsp
                (fspec_winv ⊤
                   (fspec_mk 
                      (λ x varg arg, 
                        TID (get_stid x) ∗ YIELD (get_stid x) ∗ PYIP x ∗ ⌜varg = arg ∧ varg = tt↑⌝)
                      (λ x vret ret, 
                        TID (get_stid x) ∗ YIELD (get_stid x) ∗ PYIP x ∗ ⌜vret = ret ∧ vret = tt↑⌝))%I))
    (ConcInSp : sp.2) :
    NDSA.init_cond ⊢
      ctx_refines
        (NDSI.t parent_yield)
        (NDSA.t parent_yield sp sp_nds_user T get_stid PYIP).
  Proof.
    etrans; first (eapply sim; eauto).
    eapply main_adequacy.
  Qed.
End ctxr.
End NDSIA.
