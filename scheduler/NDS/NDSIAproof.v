Require Import CRIS.
Require Import NDSHeader NDSI NDSA.
From iris Require Import gmap_view.

Module NDSIA. Section sim.
  Import NDSA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_ndsG: !ndsGS}.

  Context (sp (* sp_sch_user *) sp_nds_user : specmap).
  Context (parent_yield: string).
  Context (parent_yield_fsp: fspec).
  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).
  Context (SchInSp : sp.1 !! (fid parent_yield) = fsp_some parent_yield_fsp).
  Context (NDSInSp :(NDSA.sp sp_nds_user ⊤ T get_stid PYIP) ⊆ sp).
  (* Context (SpSchInSp : sp_sch_user ⊆ sp). *)
  (* Context (NdsInSchSp : sp_nds_user ⊆ sp_sch_user). *)
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

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    λ st_src st_tgt,
      (∃ ths tid_cur stid_cur ssch,
        ⌜st_src =
          {[NDSI.v_ths # ((λ '(n, rv, _), (n, fst <$> rv : option SAny.t))
                         <$> ths : list (nat * option SAny.t))↑;
            NDSI.v_tid # tid_cur↑; 
            NDSI.v_sch# ssch↑]} ∧
         st_tgt =
           {[NDSI.v_ths #
                   ((λ '(n, rv, _), (n, snd <$> rv : option SAny.t))
                       <$> ths : list (nat * option SAny.t))↑;
             NDSI.v_tid # tid_cur↑;
             NDSI.v_sch # ssch↑]}⌝ ∗
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

  Lemma simF_init : ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.init).
  Proof using SchInSp NDSInSp (* SpSchInSp *) NdsInSchSp YieldSpec ConcInSp.
    iStartSim. rewrite /NDSI.init /init.

    step_l. destruct _q as [[x pre] post].
    steps_l. iDestruct "ASM" as "(% & % & % & % & (% & % & Spawn) & T & Y & (P & C) & PRE & YI)"; des; subst; hss.
    steps_l. steps_r.
    rewrite ConcInSp.

    forces_l. iSplitL "T"; eauto. steps_l. steps_r. step. steps_l. steps_r.
    iDestruct "ASM" as "[% T]"; subst.

    iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 1.
    { iDestruct "IST_private" as "(% & Ys & Ysch & S & C' & Pub)"; des; subst.
      iExFalso. iApply (PendingShot_false with "[P S]"); iFrame. }
    { iDestruct "IST_public" as "(% & Ys & Ysch & S & Pub)"; des; subst.
      iExFalso. iApply (PendingShot_false with "[P S]"); iFrame. }
    { iDestruct "IST_global_in" as "(% & Ys & S & tidF & Pub)"; des; subst.
      iExFalso. iApply (PendingShot_false with "[P S]"); iFrame. }
    { iDestruct "IST_global_out" as "(% & Ys & Ysch & S & tidF)"; des; subst.
      iExFalso. iApply (PendingShot_false with "[P S]"); iFrame. }

    iDestruct "IST_init" as "(% & P' & Pub)"; des; subst; hss.
    steps_l. steps_r. simpl_sp.
    rewrite ConcInSp.
    
    force_l (false, pre, post). steps_l. force_l ((fn, tt↑↑)↑).
    steps_l. iApply wsim_spawn. iIntros (stid_new).
    steps_l. steps_r. iDestruct "ASM" as "Ynew".
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
    
    force_l. iSplitL "JoinF1 TidF1 C PRE PubF' Spawn".
    { iIntros "Y T W". iFrame. iExists _. iSplit; eauto. rewrite /Public. unseal NDS. iFrame; eauto. }

    steps_l. rewrite /SModTr.HoareYield.
    rewrite ConcInSp.
    force_l; iFrame. steps_l.
    iApply wsim_unfold; iIntros "WI".
    forces_l. iFrame. steps_l. steps_r.
    iApply wsim_yield. iSplitL "Y JoinA JoinF2 TidA TidF2 S' PubA".
    { iExists [(stid_new, None, post)], 0, stid_new, (get_stid x). iSplit; eauto. ss. iFrame.
      iSplit; eauto. do 4 iRight. iFrame; ss.
      rewrite /PublicAuth. unseal NDS. rewrite /tid_global. iSplit; eauto. }
    iIntros (st_s' st_t') "IST".

    steps_l. steps_r. iDestruct "ASM" as "(T & Y & WI)".
    
    steps_l. iApply wsim_bind. iSplitL; cycle 1.
    { instantiate (1:= λ _ _, False%I). iIntros (????) "X"; ss. }

    clear H1. iClear "Rs". iApply wsim_reset.
    cCoind CIH g Hg with x st_s' st_t'.
    iIntros "(PYIP & S & PubF & IST & T & Y & WI)"; subst.
    unfold_iterC_l. unfold_iterC_r.

    steps_r. steps_l. rewrite SchInSp.
    destruct parent_yield_fsp; ss.
    iPoseProof (YieldSpec with "") as "SPEC".
    unfold fspec_imply; ss.
    iSpecialize ("SPEC" with "[]").
    { iPureIntro. rr; ss. exists x. esplits; eauto. }
    iDestruct "SPEC" as (??) "[%SPEC0 SPEC1]".
    destruct SPEC0 as [x0 [pre0 post0]].
    force_l x0. steps_l.
    iSpecialize ("SPEC1" $! tt↑ tt↑).
    iPoseProof ("SPEC1" with "[T Y WI PYIP]") as ">[PRE POST]".
    { rewrite /FSpec.precond /fspec_winv /= /FSpec.precond. iFrame. iSplit; eauto. }
    forces_l. iSplitL "PRE".
    { instantiate (1:=tt↑). subst P0. iFrame. }
    
    steps_l. call "IST". iIntros (???) "IST". steps_l. steps_r. 

    iSpecialize ("POST" $! _q ret).
    iMod ("POST" with "[ASM]") as "(WI & (T & Y & PYIP & %))"; des; subst.
    { iFrame. }
    iClear "SPEC1".

    iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 4.
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

    steps_l. steps_r.
    rewrite !list_lookup_fmap !H /=. steps_l. steps_r.
    rewrite ConcInSp.
    steps_r. forces_l.

    iPoseProof (big_sepL_delete _ ths.*1.*1 tid_cur with "Ys") as "[Y' Ys]"; eauto.
    { rewrite ?list_lookup_fmap H //. }

    iSplitL "Y' T WI"; iFrame.

    steps_l. iApply wsim_yield. iSplitL "JoinA TidA Rs S' tidF Y Ys PubA".
    { iExists ths, tid_cur, stid_cur0, (get_stid x). iSplit; eauto. iFrame. do 4 iRight.
      iFrame. eauto. }
    iIntros (??) "IST".
    
    steps_l. steps_r.

    by_coind CIH; eauto. iFrame.
  (*SLOW*)Qed.

  Lemma simF_inner_spawn : ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr._spawn).
  Proof using SchInSp NDSInSp (* SpSchInSp *) NdsInSchSp YieldSpec ConcInSp.
    iStartSim. rewrite /NDSI.inner_spawn /inner_spawn.

    steps_l. destruct _q as [[b pre] postS].
    destruct b.
    { (* CASE 1 : normal case *)
      iDestruct "ASM" as "[%stid [%fvarg [%farg [%fn [%mtid [[-> ->] [Spawn [PRE [JoinF [TidF [PubF [WI [TID YIELD]]]]]]]]]]]]]".
      steps_l.

      iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 2.
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

      iDestruct "Spawn" as "(%fsp & %Hspawn & Spawn)".
      erewrite lookup_weaken; cycle 1.
      { eapply Hspawn. } { eapply NdsInSchSp. }
      iDestruct ("Spawn" with "[]") as "[% [% [%Hfsp Hspawn]]]".
      { iPureIntro; exists (mtid, stid, ssch); split; done. }

      iPoseProof (Public_update_public with "PubA PubF") as ">[PubA PubF]"; eauto.
      { rewrite !list_lookup_fmap H /=. eauto. }

      iPoseProof (Shot_dup with "S'") as "[S S']".

      iPoseProof ("Hspawn" with "[WI PRE TidF TID YIELD S' C' PubF]") as ">[Hpre Hpost]".
      { rewrite /precond /fspec_winv. iFrame. iSplit; eauto. }
      force_l (FSpec_mk _ _ Hfsp).
      forces_l. iFrame "Hpre".
      steps_l. steps_r.

      call "TidA JoinA Rs Ys Ysch PubA S".
      { iExists ths, mtid, stid, ssch. iFrame. iSplit; eauto. do 2 iRight. iLeft. iFrame. eauto. }
      iIntros (???) "IST".

      (* after call - prepare for termination *)
      steps_l. rename _q into vret.
      iMod ("Hpost" $! vret ret with "ASM") as "POST".
      iDestruct "POST" as "[W (% & % & (TidF & TID & YIELD & S & C & PubF) & % & % & Q)]"; des; subst.
      steps_l. steps_r.

      iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 3.
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

      steps_l. steps_r.
      rewrite ?list_lookup_fmap H0 /=.
      steps_l. steps_r.

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
      set (st_s2 := {[_:=_;_:=_;_:=_]}).
      set (st_t2 := {[_:=_;_:=_;_:=_]}).
      iAssert (Ist st_s2 st_t2) with "[JoinF JoinA TidA Rs Ys Ysch S' PubA Q]" as "IST".
      { subst st_s2 st_t2.
        iExists (<[mtid := (stid, Some (vr, sret), _)]> ths0), mtid, stid, ssch0.
        iSplit.
        { rewrite !list_fmap_insert. ss. }
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
      clearbody st_s2 st_t2.
      iApply wsim_reset.
      cCoind CIH g __ with st_s2 st_t2.
      iIntros "[TidF [TID [YIELD [S [C [PubA IST]]]]]] /=".
      unfold_iterC_l. unfold_iterC_r.

      iApply wsim_unfold; iIntros "W".
      steps_l.
      erewrite lookup_weaken; try eapply NDSInSp; cycle 1.
      { rewrite /NDSA.sp. simpl_map. refl. }
      force_l (mtid, stid, ssch0). force_l (tt↑). steps_l.
      iApply wsim_guarantee_src; iFrame "W TidF TID YIELD C PubA S". iSplit; eauto.

      steps_r. call "IST". iIntros (???) "IST".
      steps_l. iDestruct "ASM" as "(% & % & (TidF & TID & YIELD & S & C & PubF))".
      steps_l.
      steps_r.
      by_coind CIH; eauto. iFrame.
    }
    { (* CASE 2 : init case *)
      iDestruct "ASM" as "[%stid [%fvarg [%farg [%fn [%mtid [[-> [-> ->]] [Spawn [PRE [JoinF [TidF [C [PubF [W [TID YIELD]]]]]]]]]]]]]]".
      steps_l.

      iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]".
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

      iDestruct "Spawn" as "(%fsp & %Hspawn & Spawn)".
      erewrite lookup_weaken; cycle 1.
      { eapply Hspawn. } { apply NdsInSchSp. }
      iDestruct ("Spawn" with "[]") as "[% [% [%Hfsp Hspawn]]]".
      { iPureIntro; exists (0, stid, ssch); split; done. }

      iPoseProof (Public_update_public with "PubA PubF") as ">[PubA PubF]"; eauto.
      { rewrite !list_lookup_fmap H /=. eauto. }

      iPoseProof (Shot_dup with "S'") as "[S S']".

      iPoseProof ("Hspawn" with "[W PRE TidF TID YIELD S' C PubF]") as ">[P Hpost]".
      { rewrite /precond /fspec_winv. iFrame. iSplit; eauto. }
      force_l (FSpec_mk _ _ Hfsp).
      forces_l. iFrame "P".
      steps_l. steps_r.

      call "TidA JoinA Rs Ys Ysch PubA S".
      { iExists ths, 0, stid, ssch. iFrame. iSplit; eauto. do 2 iRight. iLeft. iFrame. eauto. }
      iIntros (???) "IST".

      (* after call - prepare for termination *)
      steps_l. rename _q into vret.
      iMod ("Hpost" $! vret ret with "ASM") as "POST".
      iDestruct "POST" as "[W (% & % & (TidF & TID & YIELD & S & C & PubF) & % & % & Q)]"; des; subst.
      steps_l. steps_r.

      iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 3.
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

      steps_l. steps_r.
      rewrite ?list_lookup_fmap H0 /=.
      steps_l. steps_r.

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
      set (st_s2 := {[_:=_;_:=_;_:=_]}).
      set (st_t2 := {[_:=_;_:=_;_:=_]}).
      iAssert (Ist st_s2 st_t2) with "[JoinF JoinA TidA Rs Ys Ysch S' PubA Q]" as "IST".
      { subst st_s2 st_t2.
        iExists (<[0 := (stid, Some (vr, sret), _)]> ths0), 0, stid, ssch0.
        iSplit.
        { rewrite ?list_fmap_insert //. }
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
      clearbody st_s2 st_t2.
      iApply wsim_reset.
      cCoind CIH g __ with st_s2 st_t2.
      iIntros "[TidF [TID [YIELD [S [C [PubA IST]]]]]] /=".
      unfold_iterC_l. unfold_iterC_r.

      iApply wsim_unfold; iIntros "W".
      steps_l.
      erewrite lookup_weaken; try eapply NDSInSp; cycle 1.
      { rewrite /NDSA.sp. simpl_map. refl. }
      force_l (0, stid, ssch0). force_l (tt↑). steps_l.
      iApply wsim_guarantee_src; iFrame "W TidF TID YIELD C PubA S". iSplit; eauto.

      steps_r. call "IST". iIntros (???) "IST".
      steps_l. iDestruct "ASM" as "(WI & % & (TidF & TID & YIELD & S & C & PubF))".
      steps_l.
      steps_r.
      by_coind CIH; eauto. iFrame.
    }
  (*SLOW*)Qed.

  Lemma simF_spawn : ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.spawn).
  Proof using SchInSp NDSInSp (* SpSchInSp *) NdsInSchSp YieldSpec ConcInSp.
    iStartSim. rewrite /NDSI.spawn /spawn.

    (* preprocess source precondition *)
    steps_l. destruct _q as [[[[mtid stid] ssch] user_pre] user_post].
    iDestruct "ASM" as "(% & % & % & % & % & % & (% & % & Spawn) & (TidF & T & Y & S & C & PubF) & ASM)"; des; subst.
    steps_l. steps_r.

    iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 3.
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

    steps_l. steps_r.

    (* System spawn precondition *)
    erewrite lookup_weaken; try eapply NDSInSp; cycle 1.
    { rewrite /NDSA.sp. simpl_map. refl. }
    rewrite ConcInSp.
    force_l (true, user_pre, user_post). steps_l. force_l ((fn, farg)↑). steps_l.
    steps_r. iApply wsim_spawn.
    iIntros (tid_new). steps_l.
    steps_r. rewrite ?length_fmap /=. set (mtid_new := length ths).

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
    force_l. iSplitL "ASM JoinF1 TidF' PubF' Spawn".
    { iIntros "Y T W". iFrame " Y T W ASM JoinF1 TidF' Spawn".
      iExists fn. rewrite length_fmap. subst mtid_new. iFrame. iPureIntro; esplits; eauto. }
    steps_l. force_l (mtid_new↑). steps_l.
    force_l. iSplitL "JoinF2 T Y TidF S C PubF".
    { iExists _; iSplit; eauto. iFrame; eauto. }
    step_l. step.

    iSplit; eauto.
    iExists (ths ++ [(tid_new, None, user_post)]), _, _, ssch0; iSplitR.
    { iPureIntro. rewrite ?fmap_app /=. esplits; eauto. }
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

  Lemma simF_yield : ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.yield).
  Proof using SchInSp NDSInSp (* SpSchInSp *) NdsInSchSp YieldSpec ConcInSp.
    iStartSim. rewrite /NDSI.yield /yield.

    steps_l. destruct _q as [[mtid stid] ssch].
    iDestruct "ASM" as "(% & % & (TidF & TID & YIELD & S & C & PubF))"; des; subst.
    steps_l. steps_r.

    iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 3.
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

    steps_l. steps_r.

    (* GetTid reasoning *)
    rewrite ConcInSp.
    forces_l; iFrame "TID". steps_l.
    steps_r. step.
    steps_l. iDestruct "ASM" as "[-> TID]". steps_l. steps_r.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    destruct Hmtid as [? [? [EQ Hmtid]]]; symmetry in EQ; inv EQ.

    rewrite ?list_lookup_fmap H /=; case_decide; subst; clarify.

    (* Choose the next tid *)
    steps_r. steps_l.
    destruct _q as [[tidn stidn] Htidn]. unshelve force_l (exist _ (tidn, stidn) _); last step_l.
    { ss. revert Htidn; rewrite ?list_lookup_fmap; destruct (ths !! tidn) as [[[? ?] ?]|]; ss. }
    steps_l. steps_r.

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
    forces_l. iFrame "WI TID YIELD".

    iMod (Public_update_private with "PubA PubF") as "[PubA PubF]"; eauto.
    { rewrite list_lookup_fmap H //. eauto. }

    iPoseProof (Shot_dup with "S") as "[S S'']".

    steps_l. steps_r.
    iApply wsim_yield. iSplitL "JoinA TidA Rs Ysch S'' PubA S Ys C".
    { destruct (ths !! tidn) as [[[? ?] ?]|] eqn : ?; ss; clarify.
      iExists ths, tidn, stidn, ssch0.
      iFrame. iSplit; eauto. iRight. iLeft. iFrame. eauto.
    }
    iIntros (??) "IST".

    steps_l. iDestruct "ASM" as "[TID [YIELD WINV]]".


    iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 2.
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

    forces_l. iFrame. iSplit; eauto.
    step. iSplit; eauto. iExists ths0, mtid, stid, ssch.
    iSplit; eauto. iFrame. do 2 iRight. iLeft. iFrame.
    esplits; eauto.
  (*SLOW*)Qed.

  Lemma simF_yield_global : ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.yield_global).
  Proof using SchInSp NDSInSp (* SpSchInSp *) NdsInSchSp YieldSpec ConcInSp.
    iStartSim. rewrite /NDSI.yield_global /yield_global.

    step_l. destruct _q as [[mtid stid] ssch].
    steps_l.
    iDestruct "ASM" as "(% & % & (TidF & TID & YIELD & S & C & PubF))"; des; subst. 
    steps_l. steps_r.

    iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 3.
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

    steps_l. steps_r.

    (* HoareYield *)
    rewrite ConcInSp.
    iApply wsim_unfold; iIntros "WI".
    forces_l. iFrame "WI TID Ysch".

    iMod (Public_update_private with "PubA PubF") as "[PubA PubF]"; eauto.
    { rewrite list_lookup_fmap H //. eauto. }

    iPoseProof (Shot_dup with "S") as "[S S'']".

    rewrite -{2}Qp.half_half -dfrac_op_own -(agree_idemp (to_agree (stid))).
    iDestruct "TidF" as "[TidF TidF']".

    steps_l. steps_r. iApply wsim_yield. iSplitL "JoinA TidA Rs Ys S'' PubA YIELD TidF".
    { iExists ths, mtid, stid, ssch0.
      iFrame. iSplit; eauto. do 3 iRight. iLeft. iFrame. eauto. iSplit; eauto.
      iApply big_sepL_delete; eauto.
      { rewrite !list_lookup_fmap. erewrite H. eauto. }
      iFrame.
    }
    iIntros (??) "IST".

    steps_l. iDestruct "ASM" as "[TID [YIELD WINV]]".

    iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]".
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

    forces_l. iFrame. iSplit; eauto.
    step. iSplit; eauto. iExists ths0, mtid, stid, ssch.
    iSplit; eauto. iFrame. do 2 iRight. iLeft. iFrame.
    esplits; eauto.
  (*SLOW*)Qed.

  Lemma simF_join : ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.join).
  Proof using SchInSp NDSInSp (* SpSchInSp *) NdsInSchSp YieldSpec ConcInSp.
    iStartSim. rewrite /NDSI.join /join.

    step_l. destruct _q as [[[[mtid stid] ssch] tid] postS].
    steps_l. iDestruct "ASM" as "(% & % & % & (TidF & T & Y & S & C & PubF) & JoinF)"; des; subst.

    steps_l. steps_r. iApply wsim_reset.
    cCoind CIH g' __ with st_src st_tgt.
    iIntros "(IST & Tid & T & Y & S & C & PubF & JoinF)".
    unfold_iterC_l; unfold_iterC_r.

    iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 3.
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
    
    steps_l. steps_r.

    rewrite ?list_lookup_fmap.
    destruct (ths !! tid) as [[[stid_join [[rv vrv]|]] post2]|] eqn : Htid.
    { steps_l. steps_r.
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
      forces_l. iEval (rewrite -WF) in "Post". iFrame "Tid Post T Y S C PubF".
      iSplitR; eauto.
      step. iSplit; eauto.
      iFrame. do 3 iExists _. iSplit; eauto. do 2 iRight. iLeft. iFrame. eauto.
    }
    { steps_l. steps_r.
      erewrite lookup_weaken; try eapply NDSInSp; cycle 1.
      { rewrite /NDSA.sp. simpl_map. refl. }
      force_l (mtid, stid, ssch0). steps_l. force_l. force_l. iFrame "Tid T Y S C PubF". iSplit; eauto.
      steps_l. call "JoinA TidA Rs Ys Ysch S' PubA".
      { do 4 iExists _. iFrame. iSplit; eauto. do 2 iRight. iLeft. iFrame; eauto. }
      iIntros (???) "IST".
      steps_l. iDestruct "ASM" as "(% & % & (TidF & TID & YIELD & S & C & PubF))"; des; subst.
      steps_l. steps_r.
      by_coind CIH. iFrame.
    }
    { iExFalso; iCombine "JoinA" "JoinF" gives %WF%gmap_view_both_dfrac_valid_discrete_total.
      destruct WF as [? [_ [_ [[? [? [EQ Hcont]]]%elem_of_list_to_map_2%elem_of_lookup_imap _]]]].
      inv EQ. rewrite list_lookup_fmap Htid // in Hcont.
    }
  (*SLOW*)Qed.

  Lemma simF_get_tid : ISim.sim_fun open NDSAMod NDSIMod Ist (fid NDSHdr.get_tid).
  Proof using SchInSp NDSInSp (* SpSchInSp *) NdsInSchSp YieldSpec ConcInSp.
    iStartSim. rewrite /NDSI.get_tid /get_tid.

    step_l. destruct _q as [[mtid stid] ssch].
    steps_l. iDestruct "ASM" as "(% & % & (Tid & T & Y & S & C & PubF))"; des; subst.
    steps_l. steps_r.

    iDestruct "IST" as "[% [% [% [% [[-> -> ] [JoinA [TidA [Rs
        [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]]]]]]]]]]"; cycle 3.
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

    steps_l. forces_l. iFrame. iSplit; eauto.
    steps_r. step.

    iSplit; eauto.
    do 4 iExists _. iFrame. iSplit; eauto. do 2 iRight. iLeft. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open NDSAMod NDSIMod NDSA.init_cond Ist.
  Proof using SchInSp NDSInSp (* SpSchInSp *) NdsInSchSp YieldSpec ConcInSp.
    init_sim.
    - rewrite /init_cond.
      iIntros "[TiA [JoinA [P PubA]]]". iExists [], 0, 0, 0.
      iFrame. ss. iSplit; eauto. iSplit; eauto. iLeft; rewrite /Ist_init.
      iSplit; eauto. rewrite /Pending /pub_priv. unseal NDS. iFrame.
    - eapply simF_init.
    - eapply simF_inner_spawn.
    - eapply simF_spawn.
    - eapply simF_yield.
    - eapply simF_yield_global.
    - eapply simF_join.
    - eapply simF_get_tid.
  Qed.
End sim.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _NDS: !ndsGS}.

  Context (parent_yield: string).
  Context (parent_yield_fsp: fspec).
  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).

  Lemma ctxr sp (* sp_sch_user *) sp_nds_user
    (SchInSp : sp.1 !! (fid parent_yield) = fsp_some parent_yield_fsp)
    (NDSInSp :(NDSA.sp sp_nds_user ⊤ T get_stid PYIP) ⊆ sp)
    (* (SpSchInSp : sp_sch_user ⊆ sp) *)
    (* (NdsInSchSp : sp_nds_user ⊆ sp_sch_user) *)
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
    ctx_refines
      (NDSA.t parent_yield sp sp_nds_user T get_stid PYIP, NDSA.init_cond)
      (NDSI.t parent_yield,                                emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr.
End NDSIA.
