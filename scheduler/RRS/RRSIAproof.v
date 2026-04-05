Require Import CRIS.
Require Import SchHeader SchA RRSHeader RRSI RRSA.
From iris.algebra Require Import gmap_view frac_auth.

Local Open Scope nat_scope.

Module RRSIA. Section RRSIA.
  Import RRSAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_RRSA: !RRSA.rrsGS}.

  Context (sp (* sp_sch_user *) sp_rrs_user: specmap).
  Context (parent_yield: string).
  Context (parent_yield_fsp: fspec).
  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).
  Context (SchInSp : sp.1 !! fid parent_yield = fsp_some parent_yield_fsp).
  Context (RRSInSp : RRSAS.sp sp_rrs_user ⊤ get_stid PYIP ⊆ sp).
  (* Context (FunInSchSp : sp_sch_user ⊆ sp). *)
  (* Context (FunInRrsSp : sp_rrs_user ⊆ sp_sch_user). *)
  Context (FunInRrsSp : sp_rrs_user ⊆ sp).
  Context (YieldSpec :
              ⊢ fspec_imply parent_yield_fsp
                (fspec_winv ⊤
                   (fspec_mk 
                      (λ x varg arg, 
                        TID (get_stid x) ∗ YIELD (get_stid x) ∗ PYIP x ∗ ⌜varg = arg ∧ varg = tt↑⌝)
                      (λ x vret ret, 
                        TID (get_stid x) ∗ YIELD (get_stid x) ∗ PYIP x ∗ ⌜vret = ret ∧ vret = tt↑⌝))%I)).
  Context (ConcInSp : sp.2).

  (**************************)

  Definition Ist_init (rrinvO: gmap nat InvO) : iProp Σ := ⌜rrinvO = ∅⌝ ∗ rrinv ∅ ∗ pub_init.
  Definition Ist_private (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) (Inv: InvO) : iProp Σ :=
    ⌜<<STID: ths !! tid = Some stid>> ∧ <<LKUP: rrinvO !! (pred_rr tid (size rrinvO)) = Some Inv>>⌝ ∗
    ([∗ list] i ↦ e ∈ ths, if decide (i = tid) then emp else YIELD e) ∗
    rrinv_admin rrinvO ∗ ⟦ projT2 Inv ⟧ ∗ YIELD ssch ∗ Control ∗ Shot ssch ∗
    PublicAuth ths None.
  Definition Ist_public (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) : iProp Σ :=
    ⌜<<STID: ths !! tid = Some stid>>⌝ ∗
    ([∗ list] i ↦ e ∈ ths, if decide (i = tid) then emp else YIELD e) ∗
    rrinv rrinvO ∗ YIELD ssch ∗ Shot ssch ∗
    PublicAuth ths (Some tid).
  Definition Ist_global_in (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) : iProp Σ :=
    ⌜<<STID: ths !! tid = Some stid>>⌝ ∗
    ([∗ list] i ↦ e ∈ ths, YIELD e) ∗ 
    rrinv rrinvO ∗ tid_global tid stid ∗
    Shot ssch ∗ PublicAuth ths None.
  Definition Ist_global_out (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) : iProp Σ :=
    ⌜<<STID: ths !! tid = Some stid>>⌝ ∗
    ([∗ list] i ↦ e ∈ ths, if decide (i = tid) then emp else YIELD e) ∗
    rrinv rrinvO ∗ tid_global tid stid ∗
    YIELD ssch ∗ Shot ssch ∗ PublicAuth ths None.

  Definition Ist: gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    λ st_src st_tgt,
      (∃ (ths: RRSI.thpool) (tid stid ssch: nat) (rrinvO: gmap nat InvO) (Inv: InvO),
          ⌜st_tgt = {[RRSI.v_ths # ths↑; RRSI.v_tid # tid↑; RRSI.v_sch # ssch↑]}
          ∧ st_src = st_tgt ∧ <<INVWF: size rrinvO = length ths>>⌝ ∗
          TidAuth (list_to_map (imap pair ths)) ∗
          (Ist_init rrinvO
           ∨ Ist_private ths tid stid ssch rrinvO Inv
           ∨ Ist_public ths tid stid ssch rrinvO
           ∨ Ist_global_in ths tid stid ssch rrinvO
           ∨ Ist_global_out ths tid stid ssch rrinvO))%I.
           
  Local Definition RRSAMod := RRSA.t parent_yield sp sp_rrs_user get_stid PYIP.
  Local Definition RRSIMod := RRSI.t parent_yield.

  Lemma simF_init : ISim.sim_fun open RRSAMod RRSIMod Ist (fid RRSHdr.init).
  Proof using (* FunInSchSp *) FunInRrsSp SchInSp RRSInSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /RRSA.init /RRSI.init.

    cStepS. destruct _q as [[x pre] Inv].
    cStepsS. iDestruct "ASM" as "(% & % & % & % & (% & % & Spawn) & Tsch & Ysch & [RRI [P C]] & PRE & PYIP)"; des; subst.
    cStepsT. cStepsS.

    (* Get Tid from parent scheduler *)
    rewrite ConcInSp.
    cForcesS; iFrame. cStepsS. cStep. cStepsS.
    iDestruct "ASM" as "[-> Tsch]". cStepsT.

    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 1.
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S & PubA)".
      iCombine "P S" as "PS". iApply (PendingShot_false with "PS"). }
    { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S & PubA)".
      iCombine "P S" as "PS". iApply (PendingShot_false with "PS"). }
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF & S & PubA)".
      iCombine "P S" as "PS". iApply (PendingShot_false with "PS"). }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF & Ysch' & S & PubA)".
      iCombine "P S" as "PS". iApply (PendingShot_false with "PS"). }
    iDestruct "IST_init" as "(% & RRIA & PubA)"; subst.
    rewrite map_size_empty in INVWF. destruct ths; ss.

    cStepsT. cStepsS. simpl_sp.
    rewrite ConcInSp.
    cForceS. cStepsS.
    iApply wsim_spawn. iIntros (stid_0).

    iCombine "RRIA RRI" as "RRIA".
    iPoseProof (rrinv_merge with "RRIA") as "RRIA".
    iPoseProof (rrinv_admin_alloc ∅ Inv with "RRIA") as ">RRIA".
    iPoseProof (rrinv_merge with "RRIA") as "[RRIA RRI]".
    iPoseProof (rrinv_prev_gen with "RRI") as "[RRI RRIP]".

    iMod (own_update with "PubA") as "[PubA PubF]".
    { eapply (gmap_view_alloc _ None (DfracOwn 1) ((to_agree false))); ss. }
    iMod (own_update with "PubA") as "[PubA PubF']".
    { eapply (gmap_view_alloc _ (Some 0) (DfracOwn 1) ((to_agree false))); ss. }
    
    iMod (own_update with "TidA") as "[TidA TidF]".
    { etrans; first eapply (gmap_view_alloc _ 0 (DfracOwn 1) ((to_agree stid_0))); ss. refl. }
    rewrite -{5}Qp.half_half -dfrac_op_own -{2}(agree_idemp (to_agree stid_0)) gmap_view_frag_op.
    iDestruct "TidF" as "[TidF TidF0]".

    iMod (Pending_Shot (get_stid x) with "P") as "S".
    iPoseProof (Shot_dup with "S") as "[S S']".

    cStepsT. cStepsS. cForceS (false, 0, pre). cStepsS.
    iDestruct "ASM" as "Y".
    cForcesS. iSplitL "PRE RRI TidF0 C PubF' Spawn".
    { iIntros "Y T W". do 5 iExists _. rewrite /Public. unseal RRS. iFrame. iPureIntro; eauto. }

    cStepsS. rewrite ConcInSp.
    iApply wsim_unfold; iIntros "WI".
    cForcesS. iSplitL "Tsch Y WI"; first iFrame.
    cStepsS. cStepsT. iApply wsim_yield; iSplitL "Ysch RRIA TidA TidF S' PubA".
    { do 6 iExists _. iSplit; eauto.
      { iPureIntro. esplits; eauto.
        instantiate (1 := <[0:=Inv]> ∅). set_solver. }
      iFrame. do 4 iRight. iFrame.
      rewrite /PublicAuth. unseal RRS. iFrame. ss. }
    iIntros (??) "IST".

    cStepsS. cStepsT. iDestruct "ASM" as "(Tsch & Ysch & WI)".

    cStepsS. iApply wsim_bind. iSplitL; cycle 1.
    { instantiate (1:= λ _ _, False%I). iIntros (????) "X"; ss. }

    clear H1. iApply wsim_reset.
    cCoind CIH g Hg with st_s' st_t' x.
    iIntros "(PYIP & RRIP & PubF & S & IST & Tsch & Ysch & WI)"; subst.
    unfoldIterCS. unfoldIterCT.

    cStepsT. cStepsS. rewrite SchInSp.
    destruct parent_yield_fsp; ss.
    iPoseProof (YieldSpec with "") as "SPEC".
    unfold fspec_imply; ss.
    iSpecialize ("SPEC" with "[]").
    { iPureIntro. rr; ss. exists x. esplits; eauto. }
    iDestruct "SPEC" as (??) "[%SPEC0 SPEC1]".
    destruct SPEC0 as [x0 [pre0 post0]].
    cForceS x0. cStepsS.
    iSpecialize ("SPEC1" $! tt↑ tt↑).
    iPoseProof ("SPEC1" with "[Tsch Ysch WI PYIP]") as ">[PRE POST]".
    { rewrite /FSpec.precond /fspec_winv /= /FSpec.precond. iFrame. iSplit; eauto. }
    cForcesS. iSplitL "PRE".
    { instantiate (1:=tt↑). subst P0. iFrame. }
    
    cStepsS. cCall "IST". iIntros (???) "IST". cStepsS. cStepsT. 

    iSpecialize ("POST" $! _q ret).
    iMod ("POST" with "[ASM]") as "(WI & (Tsch & Ysch & PYIP & %))"; des; subst.
    { iFrame. }
    iClear "SPEC1".

    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 4.
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF & Ysch' & S' & PubA)".
      iPoseProof (Shot_match with "S S'") as "%". subst.
      iPoseProof (YieldToken_both with "Ysch Ysch'") as "%"; ss. }
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRIP RRIA" as "RRIA".
      iPoseProof (rrinv_prev_subset with "RRIA") as "%".
      eapply map_subseteq_spec in H; eauto.
      instantiate (1 := Inv). instantiate (1 := size (∅: gmap nat InvO)). rewrite lookup_insert. ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S' & PubA)".
      iPoseProof (Shot_match with "S S'") as "%". subst.
      iPoseProof (YieldToken_both with "NschY Ysch") as "%"; ss. }
    { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)".
      iPoseProof (Shot_match with "S S'") as "%"; subst.
      iPoseProof (YieldToken_both with "Ysch NschY") as "%"; ss. }

    iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF & S' & PubA)". 
    
    cStepsT. cStepsS. rewrite H. cStepsT. cStepsS.
    rewrite ConcInSp.

    iPoseProof (Shot_match with "S S'") as "%". subst. 
    iPoseProof (big_sepL_delete with "Ys") as "[Y Ys]"; eauto.

    cForcesS. iSplitL "Tsch Y WI"; first iFrame.

    cStepsS. cStepsT. iApply wsim_yield; iSplitL "TidA RRIA Ys Ysch TidF S PubA".
    { do 6 iExists _. iSplit; eauto. iFrame "TidA". do 4 iRight. iFrame; eauto. }
    iIntros (??) "IST".

    cStepsT. cStepsS. iDestruct "ASM" as "(Tsch & Ysch & WI)".

    cByCoind CIH; eauto. iFrame.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_inner_spawn : ISim.sim_fun open RRSAMod RRSIMod Ist (fid RRSHdr._spawn).
  Proof using (* FunInSchSp *) FunInRrsSp SchInSp RRSInSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /RRSA.inner_spawn /RRSI.inner_spawn.

    cStepS. destruct _q as [[b mtid] pre].

    cStepsS.
    destruct b.
    { (** CASE 1 : normal case **)
      iDestruct "ASM" as "[(% & % & % & % & % & % & (% & % & Spawn) & PRE & RRIP & TidF & WI & T & Y) PubF]"; des; subst; cSimpl.

      cStepsS. cStepsT.
      iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 2.
      { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". cSimpl.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
        destruct (decide (tid = mtid)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
          case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
        rewrite H in Hmtid0. inv Hmtid0.
        iPoseProof (Public_Auth_Token with "PubA [PubF]") as "%".
        { rewrite /Public. unseal RRS. ss. }
        ss. }
      { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". cSimpl.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
        iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
      { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
        destruct (decide (tid = mtid)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
          case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
        rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
        rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
      { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRIP RRIA" as "RRIA".
        iPoseProof (rrinv_prev_subset with "RRIA") as "%".
        eapply map_choose in H2. des. eapply lookup_weaken in H; eauto. }

      iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S' & PubA)". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
      rewrite STID in Hmtid0. inv Hmtid0. simpl_sp.

      iDestruct ("Spawn" with "[]") as "[% [% [%Hfsp Hspawn]]]".
      { iPureIntro; exists (mtid, stid, ssch); split; done. }
      
      iPoseProof (rrinv_merge with "RRIA") as "[RRIA RRI]".
      iPoseProof (rrinv_wf with "RRIA") as "%WF".
      hexploit gmap_wf_lookup_size_none; eauto; intros LKN.
      hexploit (@gmap_wf_lookup_exists _ rrinvO (Nat.pred (size rrinvO))); eauto; i; des.
      { destruct (size rrinvO); try nia. destruct ths; ss. }

      iPoseProof (Shot_dup with "S'") as "[S S']".

      iPoseProof (Public_update_public with "PubA PubF") as ">[PubA PubF]"; eauto.

      iPoseProof ("Hspawn" $! fvarg↑ farg↑ with "[WI TidF Y RRIP PRE S' RRI Inv' C' PubF T]") as "> [Pre Post]".
      { iFrame; eauto. }
      cForceS (FSpec_mk _ _ Hfsp); eauto. cForcesS. iFrame.

      cStepsS. cCall "TidA Ys RRIA S NschY PubA".
      { do 6 iExists _. iSplit; eauto. iFrame "TidA". do 2 iRight. iLeft. iFrame; eauto. }
      iIntros (???) "IST".
      
      cStepsT. cStepsS.

      iApply wsim_bind. iSplitL; cycle 1.
      { instantiate (1:= λ _ _, False%I). iIntros (????) "F"; ss. }
      
      (* Coinduction on yield loop *)
      iClear "IST ASM Post".
      rewrite !/RRS.spin. unseal "RRS". iApply wsim_reset.
      cCoind CIH g __ with st_s' st_t'. iIntros "_".
      unfoldIterCS. unfoldIterCT.
      cStepsS; cStepsT.
      cByCoind CIH; eauto.
    }
    { (** CASE 2: init case **)
      iDestruct "ASM" as "(% & % & % & % & % & % & (% & % & Spawn) & PRE & RRI & TidF & C & PubF & WI & T & Y)"; des; subst; cSimpl.

      cStepsS. cStepsT.

      iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst.
      { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRI RRIA" as "RRIA".
        iPoseProof (rrinv_match with "RRIA") as "%"; ss. }
      { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". cSimpl.
        iCombine "C C'" as "C". iApply (Control_nodup with "C"). }
      { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". cSimpl.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        destruct (decide (tid = 0)); subst; cycle 1.
        { iPoseProof (big_sepL_lookup_acc _ _ 0 with "Ys") as "[YIELD2 _]"; eauto.
          case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
        rewrite H in Hmtid0. inv Hmtid0.
        iPoseProof (Public_Auth_Token with "PubA PubF") as "%". ss. }
      { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". cSimpl.
        iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
        eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
        des. sym in Hmtid. inv Hmtid.
        iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
        iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }

      iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S' & PubA)". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      destruct (decide (tid = 0)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ 0 with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
      rewrite H in Hmtid0. inv Hmtid0.

      iPoseProof (rrinv_wf with "RRI") as "%WF".
      iPoseProof (rrinv_match with "[RRIA RRI]") as "%"; first iFrame. subst.
      iPoseProof (rrinv_prev_gen with "RRI") as "[RRI RRIP]".
      iCombine "TidF TidF'" as "TidF". rewrite agree_idemp. simpl_sp.

      iDestruct ("Spawn" with "[]") as "[% [% [%Hfsp Hspawn]]]".
      { iPureIntro; exists (0, stid, ssch); split; done. }

      hexploit gmap_wf_lookup_size_none; eauto; intros LKN.
      remember {[0 := Inv]} as rrinvO.
      hexploit (@gmap_wf_lookup_exists _ rrinvO (Nat.pred (size rrinvO))); eauto; i; des.
      { destruct (size rrinvO); try nia. destruct ths; ss. }

      iPoseProof (Shot_dup with "S'") as "[S S']".

      iPoseProof (Public_update_public with "PubA PubF") as ">[PubA PubF]"; eauto.
      
      iPoseProof ("Hspawn" $! fvarg↑ farg↑ with "[WI TidF Y RRIP PRE S' C RRI PubF T]") as "> [Pre Post]".
      { iFrame; eauto. }
      cForceS (FSpec_mk _ _ Hfsp); eauto. cForcesS. iFrame.

      cStepsS. cCall "TidA Ys RRIA S Ysch' PubA".
      { do 6 iExists _. iSplit; eauto. iFrame "TidA". do 2 iRight. iLeft. iFrame; eauto. }
      iIntros (???) "IST".
      
      cStepsT. cStepsS.

      iApply wsim_bind. iSplitL; cycle 1.
      { instantiate (1:= λ _ _, False%I). iIntros (????) "F"; ss. }
      
      (* Coinduction on yield loop *)
      iClear "IST ASM Post".
      rewrite !/RRS.spin. unseal "RRS". iApply wsim_reset.
      cCoind CIH g __ with st_s' st_t'. iIntros "_".
      unfoldIterCS. unfoldIterCT.
      cStepsS; cStepsT.
      cByCoind CIH; eauto.
    }

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_spawn : ISim.sim_fun open RRSAMod RRSIMod Ist (fid RRSHdr.spawn).
  Proof using (* FunInSchSp *) FunInRrsSp SchInSp RRSInSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /RRSA.spawn /RRSI.spawn.

    cStepS. destruct _q as [[[[[mtid stid] ssch] pre] Invs] Inv].
    cStepsS. iDestruct "ASM" as "(% & % & (% & % & % & % & Spawn & PRE) & (TidF & Y & T & S & C & PubF) & RRI)"; des; subst; cSimpl.
    
    cStepsS; cStepsT.
    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 3.
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst.
      iPoseProof (rrinv_match with "[RRIA RRI]") as "%"; first iFrame. subst; ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". cSimpl.
      iApply (Control_nodup with "[C C']"); iFrame. }

    iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". cSimpl.
    iPoseProof (Shot_match with "S S'") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
    rewrite H in Hmtid0. inv Hmtid0.

    cStepsS. cStepsT. cSimpl.
    set (size rrinvO) as mtid_new.
    cStepsS. cStepsT. simpl_sp.

    cForceS. cStepsS. iApply wsim_spawn. iIntros (stid_new).

    iPoseProof (rrinv_wf with "RRIA") as "%".
    iPoseProof (rrinv_match with "[RRIA RRI]") as "%"; first iFrame; subst.
    iCombine "RRIA RRI" as "RRIA".
    iPoseProof (rrinv_merge with "RRIA") as "RRIA".
    iPoseProof (rrinv_admin_alloc rrinvO Inv with "RRIA") as ">RRIA".
    iPoseProof (rrinv_merge with "RRIA") as "[RRIA RRI]".
    iPoseProof (rrinv_prev_gen with "RRI") as "[RRI RRIP]".
    hexploit gmap_wf_lookup_size_none; eauto. intros LKN.

    iMod (own_update with "TidA") as "[TidA TidF']".
    { etrans; first eapply (gmap_view_alloc _ mtid_new (DfracOwn 1) ((to_agree stid_new))); ss.
      { apply not_elem_of_dom. rewrite dom_fmap. apply not_elem_of_dom.
        rewrite -not_elem_of_list_to_map ?imap_fmap fmap_imap; intros Hcont%elem_of_lookup_imap.
        subst mtid_new. destruct Hcont as [? [? [? Hcont]]]; ss; subst.
        eapply lookup_lt_Some in Hcont; lia.
      }
      refl.
    }

    iMod (Public_alloc with "PubA") as "[PubA PubF']"; eauto.

    cStepsT. cStepsS. cForceS (true, mtid_new, pre). cStepsS.
    cForcesS. iSplitL "PRE RRIP TidF' PubF' Spawn"; first iFrame.
    { subst mtid_new. rewrite -INVWF. iFrame. iIntros "Y T WI". iFrame. iPureIntro. esplits; eauto. eapply insert_non_empty. }

    iApply wsim_unfold; iIntros "WI".
    cStepsS. cForceS.  cStepsS.
    iApply wsim_guarantee_src.
    iSplitL "WI TidF RRI Y T S C PubF"; iFrame; eauto.
    cStepsS. cStep. iSplit; eauto.
    do 6 iExists _. iSplit; eauto.
    { iPureIntro. esplits; eauto. instantiate (1 := <[size rrinvO := Inv]> rrinvO).
      rewrite map_size_insert LKN last_length INVWF //. }
    iSplitL "TidA".
    { rewrite /TidAuth ?fmap_app /= imap_app /= ?length_fmap Nat.add_0_r list_to_map_snoc.
      { subst mtid_new. rewrite fmap_insert -INVWF //. }
      subst mtid_new; rewrite fmap_imap.
      intros [? [? [Heq Hin]]]%elem_of_lookup_imap; ss; rewrite -Heq in Hin.
      eapply lookup_lt_Some in Hin; rewrite ?length_fmap in Hin; lia. }

    do 2 iRight. iLeft. rewrite /Ist_public. iFrame. ss. iSplit; eauto.
    { iPureIntro. rewrite lookup_app. rewrite H //. }
    rewrite Nat.add_0_r. des_ifs. iFrame; eauto.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_yield : ISim.sim_fun open RRSAMod RRSIMod Ist (fid RRSHdr.yield).
  Proof using (* FunInSchSp *) FunInRrsSp SchInSp RRSInSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /RRSA.yield /RRSI.yield.

    cStepS. destruct _q as [[[mtid stid] ssch] Inv].

    cStepsS. iDestruct "ASM" as "(% & % & (TidF & Y & T & S & C & PubF) & RRI & % & % & Inv)"; des; subst.
    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 3.
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst.
      iPoseProof (rrinv_match with "[RRIA RRI]") as "%"; first iFrame. subst; ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". cSimpl.
      iApply (Control_nodup with "[C C']"); iFrame. }

    iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". cSimpl.
    iPoseProof (Shot_match with "S S'") as "->".
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
    rewrite H in Hmtid0. inv Hmtid0.

    iPoseProof (rrinv_prev_gen with "RRI") as "[RRI RRIP]".
    assert (NEMP: Inv ≠ ∅) by set_solver.
    iCombine "RRIA RRI" as "RRIA".
    iPoseProof (rrinv_match with "RRIA") as "->".
    iPoseProof (rrinv_merge with "RRIA") as "RRIA".

    iMod (Public_update_private with "PubA PubF") as "[PubA PubF]"; eauto.

    cStepsS. cStepsT. cSimpl.
    cStepsS. cStepsT.
    cForcesS. iSplitL "T"; first iFrame.
    cStepsS. cStep. cStepsS. cStepsT. iDestruct "ASM" as "[-> T]". cSimpl.
    cStepsS. cStepsT. rewrite H. case_decide; ss. cStepsS. cStepsT.
    eapply lookup_lt_Some in H as LEN.
    generalize (succ_rr_upperbound mtid (length ths) LEN); intro LEN0.
    eapply lookup_lt_is_Some in LEN0. rewrite /is_Some in LEN0. des. rewrite LEN0.

    rename x into stidn. set (succ_rr mtid (length ths)) as mtidn.
    cStepsT. cStepsS. rewrite ConcInSp.
    iAssert (YIELD stidn ∗
        [∗ list] i ↦ e ∈ ths, if decide (i = mtidn) then emp else YIELD e)%I
      with "[Y Ys]" as "[Y Ys]".
    { destruct (decide (mtid = mtidn)). 
      { subst mtidn; subst; destruct (ths !! mtid) eqn:L; ss; clarify.
        rewrite e in L. rewrite L in LEN0. inv LEN0. rewrite -e. iFrame. }
      iPoseProof (big_sepL_delete _ ths mtid with "[Ys Y]") as "Ys"; eauto.
      { do 2 iFrame. }
      rewrite big_sepL_delete; try iFrame.
      subst mtidn. eauto. }
    iApply wsim_unfold; iIntros "WI".
    cForcesS. iSplitL "T Y WI"; first iFrame.
    cStepsS. cStepsT. iApply wsim_yield; iSplitL "TidA Ys RRIA Inv NschY C S' PubA".
    { do 6 iExists _. iSplit; eauto. iFrame "TidA". iRight. iLeft. iFrame.
      iPureIntro. esplits.
      { subst mtidn. eauto. }
      { subst mtidn. rewrite INVWF pred_succ_id //. }
    }
    iIntros (??) "IST". cStepsS. cStepsT.
    iDestruct "ASM" as "(T & Y & WI)".

    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 2.
    { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H2 in Hmtid0. inv Hmtid0.
      iPoseProof (Public_Auth_Token with "PubA PubF") as "%"; ss. }
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H2 in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRIP RRIA" as "RRIA".
      iPoseProof (rrinv_prev_subset with "RRIA") as "%".
      eapply map_choose in NEMP. des. eapply lookup_weaken in H2; eauto. }

    iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S' & PubA)". cSimpl.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; by iPoseProof (YieldToken_both with "Y YIELD2") as "%". }
    rewrite STID in Hmtid0. inv Hmtid0.
    iPoseProof (rrinv_merge with "RRIA") as "[RRIA RRI]".
    iPoseProof (rrinv_prev_subset with "[RRIP RRI]") as "%"; first iFrame.
    iMod (Public_update_public with "PubA PubF") as "[PubA PubF]"; eauto.
    
    cForcesS. iFrame. iSplitR.
    { iPureIntro. esplits; eauto. }

    cStep. iSplit; eauto. do 6 iExists _. iSplit; eauto. iFrame "TidA". do 2 iRight. iLeft. iFrame. eauto.
    
    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_yield_global : ISim.sim_fun open RRSAMod RRSIMod Ist (fid RRSHdr.yield_global).
  Proof using (* FunInSchSp *) FunInRrsSp SchInSp RRSInSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /RRSA.yield_global /RRSI.yield_global.

    cStepS. destruct _q as [[mtid stid] ssch].

    cStepsS. iDestruct "ASM" as "(% & % & (TidF & Y & T & S & C & PubF))"; des; subst.
    cStepsS. cStepsT.
    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 3.
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "[% RRIA]". subst.
      destruct ths; ss. iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%"; first iFrame.
      rewrite lookup_empty in H. ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". cSimpl.
      iApply (Control_nodup with "[C C']"); iFrame. }

    iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". cSimpl.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
    rewrite H in Hmtid0. inv Hmtid0.
    iPoseProof (Shot_match with "S S'") as "%"; subst.

    iPoseProof (rrinv_prev_gen with "RRIA") as "[RRIA RRIP]".
    assert (NEMP: rrinvO ≠ ∅).
    { destruct ths; ss. assert (size rrinvO > 0) by nia. set_solver. }
    rewrite -Qp.half_half -dfrac_op_own -(agree_idemp (to_agree stid)) gmap_view_frag_op.
    iDestruct "TidF" as "[TidF TidF0]".

    iMod (Public_update_private with "PubA PubF") as "[PubA PubF]"; eauto.

    cStepsS. cSimpl. cStepsS. cStepsT. cSimpl. cStepsT.
    iApply wsim_unfold; iIntros "WI".
    cForcesS. iSplitL "T NschY WI"; first iFrame.
    cStepsS. cStepsT. iApply wsim_yield; iSplitL "TidA Ys RRIA TidF0 S' Y PubA".
    { do 6 iExists _. iSplit; eauto. iFrame "TidA". do 3 iRight. iLeft. iFrame.
      iPoseProof (big_sepL_delete with "[Y Ys]") as "Ys"; eauto; iFrame. }
    iIntros (??) "IST". cStepsT. cStepsS.

    iDestruct "ASM" as "(T & Y & WI)".
    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst.
    { iExFalso. iDestruct "IST_init" as "(% & RRIA & PubA)". subst. iCombine "RRIP RRIA" as "RRIA".
      iPoseProof (rrinv_prev_subset with "RRIA") as "%".
      eapply map_choose in NEMP. des. eapply lookup_weaken in H0; eauto. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". cSimpl.
      iCombine "C C'" as "C". iApply (Control_nodup with "C"). }
    { iExFalso. iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify; iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H0 in Hmtid0. inv Hmtid0.
      iPoseProof (Public_Auth_Token with "PubA PubF") as "%"; ss. }
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }

    iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch & S' & PubA)".
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify; iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
    rewrite H0 in Hmtid0. inv Hmtid0.

    iCombine "TidF TidF'" as "TidF". rewrite agree_idemp.

    iMod (Public_update_public with "PubA PubF") as "[PubA PubF]"; eauto.

    cForcesS. iSplitL "WI Y T S C TidF PubF"; iFrame; eauto.
    cStep. iSplit; eauto. do 6 iExists _. iSplit; eauto. iFrame "TidA".
    do 2 iRight. iLeft. iFrame. eauto.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma simF_get_tid : ISim.sim_fun open RRSAMod RRSIMod Ist (fid RRSHdr.get_tid).
  Proof using (* FunInSchSp *) FunInRrsSp SchInSp RRSInSp YieldSpec ConcInSp.
    cStartFunSim. rewrite /RRSA.get_tid /RRSI.get_tid.

    cStepS. destruct _q as [[mtid stid] ssch].

    cStepsS. iDestruct "ASM" as "[% [% (TidF & Y & T & S & C & PubF)]]"; cSimpl.
    cStepsS; cStepsT.

    iDestruct "IST" as (??????) "(% & TidA & [IST_init | [IST_private | [IST_public | [IST_global_in | IST_global_out]]]])"; des; subst; cycle 3.
    { iExFalso. iDestruct "IST_global_in" as "(% & Ys & RRIA & TidF' & S')". cSimpl.
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
      des. sym in Hmtid. inv Hmtid.
      iPoseProof (big_sepL_delete with "Ys") as "[Y' Ys]"; eauto.
      iPoseProof (YieldToken_both with "Y Y'") as "%". ss. }
    { iExFalso. iDestruct "IST_global_out" as "(% & Ys & RRIA & TidF' & Ysch' & S')".
      iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
      eapply elem_of_list_to_map_2, elem_of_lookup_imap in Hmtid. des. sym in Hmtid; inv Hmtid.
      destruct (decide (tid = mtid)); subst; cycle 1.
      { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
        case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
      rewrite H in Hmtid0. inv Hmtid0. iCombine "TidF TidF'" gives %wf.
      rewrite -gmap_view_frag_op dfrac_op_own gmap_view_frag_valid in wf. des; ss. }
    { iExFalso. iDestruct "IST_init" as "[% RRIA]". subst.
      destruct ths; ss. iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%"; first iFrame.
      rewrite lookup_empty in H. ss. }
    { iExFalso. iDestruct "IST_private" as "(% & Ys & RRIA & Inv' & NschY & C' & S')". cSimpl.
      iApply (Control_nodup with "[C C']"); iFrame. }

    iDestruct "IST_public" as "(% & Ys & RRIA & NschY & S' & PubA)". cSimpl.
    iPoseProof (Shot_match with "S S'") as "%"; subst.
    iPoseProof (Tid_Auth_Tid with "[TidA TidF]") as "%Hmtid"; first iFrame.
    eapply elem_of_list_to_map_2 in Hmtid; rewrite elem_of_lookup_imap in Hmtid.
    des. sym in Hmtid. inv Hmtid.
    destruct (decide (tid = mtid)); subst; cycle 1.
    { iPoseProof (big_sepL_lookup_acc _ _ mtid with "Ys") as "[YIELD2 _]"; eauto.
      case_decide; clarify. iPoseProof (YieldToken_both with "Y YIELD2") as "%"; ss. }
    rewrite H in Hmtid0. inv Hmtid0.

    cStepsS. cStepsT. cSimpl. cStepsS. cStepsT. cForcesS. iSplitL "TidF Y T S C PubF"; first iFrame; eauto.
    cStep. iSplit; eauto. do 6 iExists _. iSplit; eauto. iFrame "TidA". do 2 iRight. iLeft. iFrame; eauto.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open RRSAMod RRSIMod RRSA.init_cond Ist.
  Proof using (* FunInSchSp *) FunInRrsSp SchInSp RRSInSp YieldSpec ConcInSp.
    cStartModSim.
    - rewrite /RRSA.init_cond /init_inv /init_tid /init_pub. unseal RRS.
      iIntros "(RRI & tid & pub)". rewrite /Ist.
      iExists [], 0, 0, 0, ∅, (existT 0 emp%SAT).
      iSplit; eauto. ss. iFrame. iLeft. iFrame; eauto.
    - eapply simF_init.
    - eapply simF_inner_spawn.
    - eapply simF_spawn.
    - eapply simF_yield.
    - eapply simF_yield_global.
    - eapply simF_get_tid.
  Qed.
End RRSIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_rrsG: !rrsGS}.

  Context (parent_yield: string).
  Context (parent_yield_fsp: fspec).
  Context (T: Type) (get_stid : T → nat) (PYIP: T → iProp Σ).

  Lemma ctxr sp sp_rrs_user
    (SchInSp : sp.1 !! fid parent_yield = fsp_some parent_yield_fsp)
    (RRSInSp : RRSAS.sp sp_rrs_user ⊤ get_stid PYIP ⊆ sp)
    (FunInRrsSp : sp_rrs_user ⊆ sp)
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
      (RRSI.t parent_yield,                              emp%I)
      (RRSA.t parent_yield sp sp_rrs_user get_stid PYIP, RRSA.init_cond).
  Proof using. eapply main_adequacy, sim; eauto. Qed.

End ctxr.
End RRSIA.
