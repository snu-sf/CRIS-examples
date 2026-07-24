Require Import CRIS.common.CRIS.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.system Require Import SystemHeader SystemA SystemTactics.
From CRIS.promise_free.elimination_stack Require Import StackHeader StackA StackI.
From CRIS.filter Require Import CallFilter.
From CRIS.helping Require Import HelpingTactics.

Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG,
    _SYS: !sysGS, _STACK: !stackG, _HELP: !helpingGS, !schGS}.
  Context (mn : string) (sp_user sp : specmap).
  Context (Hsys : (SystemA.sp sp_user (↑stackN)) ⊆ sp).

  Local Definition SysF := CFilter.filter (Helping.exports mn)
    (SystemA.t sp_user (↑stackN) sp).
  Local Definition SchF := CFilter.filter (Helping.exports mn) SchI.t.
  Local Definition MA :=
    ((StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
        HelpingOn.t mn StackM.jobCode) ★ SysF) ★ SchF.
  Local Definition MI :=
    ((CFilter.filter (Helping.exports mn) StackI.t ★
        HelpingDummy.t mn) ★ SysF) ★ SchF.
  Local Notation Ist :=
    (IstProd (IstSB [mn] (IstHelp IstTrue ⊤)) IstEq).

  Lemma target_record_prim target :
    target_record target -∗
      ∃ q C V, @{V} target.1 p↦{q} C.
  Proof.
    destruct target as [loc V]. simpl.
    iDestruct 1 as (f t LT Vmsg b γ) "[PT _]".
    rewrite AtomicPtsTo_eq /AtomicPtsTo_def.
    iDestruct "PT" as (tx) "PT".
    rewrite /view_at AtomicPtsToX_eq /AtomicPtsToX_def.
    iDestruct "PT" as (C Va ->) "[SYNC [HIST _]]".
    iDestruct "SYNC" as "[SEEN _]".
    rewrite /SeenLocal. iDestruct "SEEN" as %SEEN.
    iExists 1%Qp,
      (Cell.singleton (Message.message Val.zero Vmsg b) LT), V.
    rewrite /view_at /own_loc_prim.
    iSplit; last done. iPureIntro. split; first apply SEEN.
    eexists t, (f, Message.message Val.zero Vmsg b). split.
    { rewrite Cell.singleton_get. des_ifs. }
    apply SEEN. rewrite Cell.singleton_get. des_ifs; eauto.
  Qed.

  Lemma target_pool_prim targets target :
    target ∈ targets → target_pool targets -∗
      ∃ q C V, @{V} target.1 p↦{q} C.
  Proof.
    intros IN. iIntros "POOL".
    iDestruct (target_pool_lookup _ _ IN with "POOL") as "REC".
    iApply (target_record_prim with "REC").
  Qed.

  Lemma cell_add_lt ζ from to msg ζ'
      (ADD : Cell.add ζ from to msg ζ') :
    Time.lt from to.
  Proof. inversion ADD; done. Qed.

  Lemma pop_simF :
    ISim.sim_fun open MA MI Ist (fid StackHdr.pop).
  Proof.
    cStartFunSim. rewrite /StackI.pop /StackM.pop /stack_atomic_fun.
    cStepsS. cStepsT.
    destruct _q as [[[ γs tid] stid] V].
    cStepsS. iDestruct "ASM" as "[%stack [-> [#HANDLE TV]]]".
    cStepsT.
    iApply wsim_reset.
    cCoind CIH g' __ with st_src st_tgt V.
    iIntros "[#HANDLE [IST TV]] /=".
    aUnfoldT. rewrite /StackI.pop_once. cHideT. sYields.
    rewrite /stack_handle.
    iDestruct "HANDLE" as
      (stack_loc γstackinv γh γslot ζh_seen ζo_seen γguard ζguard γnm)
      "[%STACK [#Hinv [#SNh [#SNo #SNg]]]]".
    destruct STACK as [-> STACK_BASE].
    cStepsT.
    sYield. cStepsT.
    iEval (rewrite IstHelp_nested_equiv) in "IST".
    iInv "Hinv" with "[IST]" as "[IST INV]" "ACC";
      first by iFrame.
    iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INV".
    iDestruct "INV" as
      (vs head offer ζh ζo Vbh Vbo Vh Vo targets nodes)
      "[Hs [HEAD [HPURE [CHAIN [SLOT [OPURE [OFFER [TARGETS REG]]]]]]]]".
    iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def) in "HEAD".
    iDestruct "HEAD" as (txh) "HEAD".
    cInlineT.
    cForceT (meta1 (tid, stid, stack_loc, Ordering.acqrel,
      ζh, ζh_seen, txh, γh, 1%Qp, CASOnly, V, Vbh))%cris.
    cForcesT. iFrame "TV SNh HEAD". iSplit; eauto.
    iSplit; ss. rewrite shift_0. ss.
    cStepT. cStepT. cStepT.
    iDestruct "GRT" as
      "[-> [%ζread [%fread [%na [%vret [%vactual [%Vmsg [%V1 [HREAD [#SNh1 [HEAD TV]]]]]]]]]]]".
    iDestruct "HREAD" as
      %[-> [Hval [Hseen [Hle [Hget [HVle HVmsg]]]]]].
    iPoseProof "HPURE" as "#HPUREcopy".
    iDestruct "HPUREcopy" as
      %(CURh & CASHh & PTRh & HEADH & LINKS & SENT).
    pose proof (Hle _ _ _ Hget) as Hgeth.
    destruct (PTRh _ _ _ _ _ Hgeth) as
      (head_loc & Vguard & Hactual & Htarget & Hsafe).
    subst vactual.
    pose proof (StackHdr.le_vptr_eq Hval) as Hret. subst vret.
    simpl in HVmsg.
    iAssert (⌜current_message ζh head Vh ∧ cas_history ζh ∧
      pointer_history (stack_loc >> 2) targets ζh ∧
      head_history (stack_loc >> 2) nodes ζh ∧
      node_links (stack_loc >> 2) targets nodes ∧
      (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targets)⌝)%I
      as "HPURE"; first done.
    iMod ("ACC" with "[//]") as "[ACC _]".
    iMod ("ACC" with
      "[Hs HEAD HPURE CHAIN SLOT OPURE OFFER TARGETS REG] IST") as "IST".
    { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
      iExists vs, head, offer, ζh, ζo, Vbh, Vbo, Vh, Vo, targets, nodes.
      solve_base_sl_red; iFrame "Hs HPURE CHAIN SLOT OPURE OFFER TARGETS REG".
      rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
      iExists txh. iFrame. }
    iEval (rewrite -IstHelp_nested_equiv) in "IST".
    destruct (decide (head_loc = stack_loc >> 2)) as [Hempty|Hnonempty].
    - subst head_loc. cStepsT. case_decide; last contradiction.
      cStepsT. sYield. cStepsT.
      iEval (rewrite IstHelp_nested_equiv) in "IST".
      iInv "Hinv" with "[IST]" as "[IST INV]" "ACC";
        first by iFrame.
      iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INV".
      iDestruct "INV" as
        (vs2 head2 offer2 ζh2 ζo2 Vbh2 Vbo2 Vh2 Vo2 targets2 nodes2)
        "[Hs2 [HEAD2 [HPURE2 [CHAIN2 [SLOT2 [OPURE2 [OFFER2 [TARGETS2 REG2]]]]]]]]".
      iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def) in "HEAD2".
      iDestruct "HEAD2" as (txh2) "HEAD2".
      iPoseProof (AtomicPtsToX_AtomicSeen_latest with "HEAD2 SNh1") as "%Hread_le2".
      pose proof (Hread_le2 _ _ _ Hget) as Hgeth2.
      iPoseProof "HPURE2" as "#HPURE2copy".
      iDestruct "HPURE2copy" as
        %(CURh2 & CASHh2 & PTRh2 & HEADH2 & LINKS2 & SENT2).
      destruct (PTRh2 _ _ _ _ _ Hgeth2) as
        (sentinel2 & Vguard2 & Heq2 & Htarget2 & Hsafe2).
      inversion Heq2; subst sentinel2.
      iPoseProof (view_at_view_mon_pred
        (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard))
        _ _ HVle with "SNg") as "#SNg1".
      cInlineT.
      cForceT (tid, stid, stack_loc,
        Val.Vptr (stack_loc >> 2), Val.Vptr (stack_loc >> 2),
        Ordering.relaxed, Ordering.acqrel, V1, γh, ζread,
        Vbh2, txh2, ζh2, CASOnly, target_pool targets2).
      cForcesT.
      iSplitL "TV HEAD2 TARGETS2".
      { iSplit.
        { iPureIntro. repeat split; eauto; try done.
        }
        iFrame "TV SNh1 HEAD2 TARGETS2".
        iSplit.
        { iPureIntro. rewrite shift_0. repeat split; eauto; try done.
          intros t f value V0 b LE GET.
          destruct (PTRh2 _ _ _ _ _ GET) as (loc & Vg & EQ & _ & _).
          subst value. done. }
        iModIntro. iIntros "TARGETS2". iModIntro. iSplit.
        { iDestruct (target_pool_lookup _ _ Htarget2 with "TARGETS2") as "REC".
          iDestruct (target_record_prim with "REC") as (q C Vp) "PRIM".
          iExists q, C, Vp, γguard, ζguard. iFrame "PRIM SNg1". }
        iIntros (t f loc V0 b) "%OTHER".
        destruct OTHER as (_ & GET & NE).
        destruct (PTRh2 _ _ _ _ _ GET) as
          (loc2 & Vg2 & EQ & IN & SAFE). inversion EQ; subst loc2.
        iDestruct (target_pool_prim _ _ IN with "TARGETS2") as (q C Vp) "PRIM".
        iExists q, C, Vp. done. }
      cStepsT.
      iDestruct "GRT" as
        "[-> [%casret [%ζseen2 [%ζnew [%tread [%fread2 [%LTread [%vread [%Vr [%bread [%V2 [HCAS [TV [SNh2 [TARGETS2 HCASE]]]]]]]]]]]]]]]".
      iDestruct "HCAS" as
        %[-> [Hseen12 [Hseen_new [Hcasget [Htread H12]]]]].
      iDestruct "HCASE" as "[HFAIL|HSUCC]".
      { iDestruct "HFAIL" as "[%FAIL HEAD2]". destruct FAIL as
          (-> & Hneq & Hacq & ->).
        iAssert (⌜current_message ζnew head2 Vh2 ∧ cas_history ζnew ∧
          pointer_history (stack_loc >> 2) targets2 ζnew ∧
          head_history (stack_loc >> 2) nodes2 ζnew ∧
          node_links (stack_loc >> 2) targets2 nodes2 ∧
          (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targets2)⌝)%I
          as "HPURE2"; first done.
        iMod ("ACC" with "[//]") as "[ACC _]".
        iMod ("ACC" with
          "[Hs2 HEAD2 HPURE2 CHAIN2 SLOT2 OPURE2 OFFER2 TARGETS2 REG2] IST")
          as "IST".
        { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
          iExists vs2, head2, offer2, ζnew, ζo2, Vbh2, Vbo2, Vh2, Vo2,
            targets2, nodes2.
          solve_base_sl_red.
          iFrame "Hs2 HPURE2 CHAIN2 SLOT2 OPURE2 OFFER2 TARGETS2 REG2".
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
          iExists txh2. iFrame. }
        iEval (rewrite -IstHelp_nested_equiv) in "IST".
        inversion H12 as [Hrel12 Hcur12 Hacq12].
        assert (Hcur02 : View.le (TView.cur V) (TView.cur V2)) by
          (etrans; [exact HVle|exact Hcur12]).
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen (stack_loc >> 1) γslot ζo_seen))
          _ _ Hcur02 with "SNo") as "#SNo2".
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard))
          _ _ Hcur02 with "SNg") as "#SNg2".
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen stack_loc γh ζread))
          _ _ Hcur12 with "SNh1") as "#SNh2'".
        iAssert (stack_handle γs (Val.Vptr stack_loc) (TView.cur V2))%I
          with "[]" as "#HANDLE2".
        { rewrite /stack_handle.
          iExists stack_loc, γstackinv, γh, γslot, ζread, ζo_seen,
            γguard, ζguard, γnm.
          iSplit; first done. iFrame "Hinv SNh2' SNo2 SNg2". }
        cStepsT. sYield. cStepsT.
        cByCoind CIH. iFrame "HANDLE2 IST TV WINV". }
      { iDestruct "HSUCC" as (Vw) "[%SUCC [_ HEAD2]]".
        destruct SUCC as (-> & Heq & twrite & HADD & Hvrw & Hvrne & Hnotle & HneqV & Hord).
        subst vread.
        assert (Htwrite : Time.lt tread twrite) by
          (eapply cell_add_lt; exact HADD).
        assert (Htread_ne : tread ≠ twrite) by
          (intros ->; eapply Time.lt_strorder; exact Htwrite).
        assert (Hget_base :
          Cell.get tread ζh2 =
            Some (fread2,
              Message.message (Val.Vptr (stack_loc >> 2)) Vr bread)).
        { pose proof (Hseen_new _ _ _ Hcasget) as Hget_new.
          erewrite Cell.add_o in Hget_new; eauto.
          destruct (Time.eq_dec tread twrite); [contradiction|done]. }
        assert (Hmax : tread = Cell.max_ts ζh2).
        { eapply cas_history_add_from_max; eauto. }
        assert (Hhead2 : head2 = Val.Vptr (stack_loc >> 2)).
        { destruct CURh2 as (fcur & bcur & Hcur).
          rewrite <- Hmax in Hcur. congruence. }
        subst head2.
        iDestruct (live_chain_sentinel_empty with "CHAIN2")
          as "[CHAIN2 %Hvs2]". subst vs2.
        sYieldS. cForceS false. cStepsS.
        aUnfoldS. sYieldS. cStepsS.
        iDestruct (stack_content_auth_agree with "Hs2 ASM") as %Hq.
        subst _q.
        cForceS (inr Val.Vundef↑). cForcesS. iFrame "ASM".
        assert (CURnew : current_message ζnew
          (Val.Vptr (stack_loc >> 2)) Vw).
        { eapply current_message_add; eauto. }
        assert (CASHnew : cas_history ζnew).
        { eapply cas_history_add; eauto. }
        assert (PTRnew :
          pointer_history (stack_loc >> 2) targets2 ζnew).
        { eapply pointer_history_add; [exact PTRh2| |exact HADD].
          exists Vguard2. split; first exact Htarget2. left; done. }
        assert (HEADnew : head_history (stack_loc >> 2) nodes2 ζnew).
        { eapply head_history_add; [exact HEADH2| |exact HADD].
          left; done. }
        iAssert (⌜current_message ζnew (Val.Vptr (stack_loc >> 2)) Vw ∧
          cas_history ζnew ∧
          pointer_history (stack_loc >> 2) targets2 ζnew ∧
          head_history (stack_loc >> 2) nodes2 ζnew ∧
          node_links (stack_loc >> 2) targets2 nodes2 ∧
          (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targets2)⌝)%I
          as "HPURE2"; first done.
        iMod ("ACC" with "[//]") as "[ACC _]".
        iMod ("ACC" with
          "[Hs2 HEAD2 HPURE2 CHAIN2 SLOT2 OPURE2 OFFER2 TARGETS2 REG2] IST")
          as "IST".
        { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
          iExists [], (Val.Vptr (stack_loc >> 2)), offer2, ζnew, ζo2,
            (Vbh2 ⊔ TView.cur V2), Vbo2, Vw, Vo2, targets2, nodes2.
          solve_base_sl_red.
          iFrame "Hs2 HPURE2 CHAIN2 SLOT2 OPURE2 OFFER2 TARGETS2 REG2".
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
          iExists txh2. iFrame. }
        iEval (rewrite -IstHelp_nested_equiv) in "IST".
        inversion H12 as [Hrel12 Hcur12 Hacq12].
        assert (Hcur02 : View.le (TView.cur V) (TView.cur V2)) by
          (etrans; [exact HVle|exact Hcur12]).
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen (stack_loc >> 1) γslot ζo_seen))
          _ _ Hcur02 with "SNo") as "#SNo2".
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard))
          _ _ Hcur02 with "SNg") as "#SNg2".
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen stack_loc γh ζread))
          _ _ Hcur12 with "SNh1") as "#SNh2'".
        iAssert (stack_handle γs (Val.Vptr stack_loc) (TView.cur V2))%I
          with "[]" as "#HANDLE2".
        { rewrite /stack_handle.
          iExists stack_loc, γstackinv, γh, γslot, ζread, ζo_seen,
            γguard, ζguard, γnm.
          iSplit; first done. iFrame "Hinv SNh2' SNo2 SNg2". }
        cStepsT. sYield. cStepsS. cStepsT.
        sYieldS. cStepsS. cForcesS.
        iSplitL "TV".
        { iExists V2. iSplit; first done. iFrame "TV". }
        cStepsS. cStepsT. cStep. iFrame "IST". done. }
    - cStepsT. case_decide; first contradiction.
      cStepsT. sYield. cStepsT.
      iEval (rewrite IstHelp_nested_equiv) in "IST".
      iInv "Hinv" with "[IST]" as "[IST INV]" "ACC";
        first by iFrame.
      iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INV".
      iDestruct "INV" as
        (vsc headc offerc ζhc ζoc Vbhc Vboc Vhc Voc targetsc nodesc)
        "[Hsc [HEADc [HPUREc [CHAINc [SLOTc [OPUREc [OFFERc [TARGETSc REGc]]]]]]]]".
      iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def)
        in "HEADc".
      iDestruct "HEADc" as (txhc) "HEADc".
      iPoseProof (AtomicPtsToX_AtomicSeen_latest with "HEADc SNh1")
        as "%Hread_cur".
      pose proof (Hread_cur _ _ _ Hget) as Hget_cur.
      iPoseProof "HPUREc" as "#HPUREcopyc".
      iDestruct "HPUREcopyc" as
        %(CURhc & CASHhc & PTRhc & HEADHc & LINKSc & SENTc).
      destruct (head_history_lookup _ _ _ _ _ _ _ _ Hnonempty Hget_cur HEADHc)
        as (d & LOOKd & LEpub).
      change (View.le Vmsg (TView.cur V1)) in HVmsg.
      assert (LEpub1 : View.le d.(node_pub_view) (TView.cur V1)) by
        (etrans; eauto).
      iDestruct (node_registry_lookup_acc γnm nodesc head_loc d LOOKd
        with "REGc") as "[RECd [#NEXTold CLOSEd]]".
      iEval (rewrite /node_record /immutable_field) in "RECd".
      iDestruct "RECd" as
        (fnext0 tnext0 LTnext Vnext_msg0 Vfield bnext γnext)
        "[%LEfield [NEXT SWNEXT]]".
      destruct LEfield as [LEfield LEmsg].
      assert (LEfield1 : View.le Vfield (TView.cur V1)) by
        (etrans; [exact LEfield|exact LEpub1]).
      iPoseProof (AtomicSWriter_AtomicSeen with "SWNEXT") as "#SNnext0".
      iPoseProof (view_at_view_mon_pred
        (view_at (AtomicSeen (head_loc >> 1) γnext
          (Cell.singleton
            (Message.message (Val.Vptr d.(node_next)) Vnext_msg0 bnext)
            LTnext))) _ _ LEfield1 with "SNnext0") as "#SNnext".
      iEval (rewrite AtomicPtsTo_eq /AtomicPtsTo_def) in "NEXT".
      iDestruct "NEXT" as (txnext) "NEXT".
      cInlineT.
      cForceT (meta1 (tid, stid, head_loc >> 1, Ordering.relaxed,
        (Cell.singleton
          (Message.message (Val.Vptr d.(node_next)) Vnext_msg0 bnext)
          LTnext),
        (Cell.singleton
          (Message.message (Val.Vptr d.(node_next)) Vnext_msg0 bnext)
          LTnext),
        txnext, γnext, 1%Qp, SingleWriter, V1, Vfield))%cris.
      cForcesT. iFrame "TV SNnext NEXT". iSplit; eauto.
      cStepT. cStepT. cStepT.
      iDestruct "GRT" as
        "[-> [%ζnext_read [%fnext [%nanext [%vnext [%vnext_actual [%Vnext_msg [%V2 [HREADnext [#SNnext2 [NEXT TV]]]]]]]]]]]".
      iDestruct "HREADnext" as
        %[-> [Hnext_val [Hnext_seen [Hnext_le [Hnext_get [H12 Hnext_msg]]]]]].
      pose proof (Hnext_le _ _ _ Hnext_get) as Hnext_get_global.
      rewrite Cell.singleton_get in Hnext_get_global.
      des_ifs.
      pose proof (StackHdr.le_vptr_eq Hnext_val) as Hnext_ret.
      subst vnext.
      iAssert (@{Vfield} (head_loc >> 1) sw↦{γnext}
        (Cell.singleton
          (Message.message (Val.Vptr d.(node_next)) Vnext_msg nanext)
          LTnext))%I
        with "[NEXT]" as "NEXT".
      { rewrite AtomicPtsTo_eq /AtomicPtsTo_def. iExists txnext. done. }
      iAssert (node_record head_loc d)%I with "[NEXT SWNEXT]" as "RECd".
      { rewrite /node_record /immutable_field.
        iExists fnext, (Cell.max_ts ζnext_read), LTnext,
          Vnext_msg, Vfield, nanext, γnext.
        iFrame. iPureIntro. split; done. }
      iPoseProof ("CLOSEd" with "RECd") as "REGc".
      iAssert (⌜current_message ζhc headc Vhc ∧ cas_history ζhc ∧
        pointer_history (stack_loc >> 2) targetsc ζhc ∧
        head_history (stack_loc >> 2) nodesc ζhc ∧
        node_links (stack_loc >> 2) targetsc nodesc ∧
        (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targetsc)⌝)%I
        as "HPUREc"; first done.
      iMod ("ACC" with "[//]") as "[ACC _]".
      iMod ("ACC" with
        "[Hsc HEADc HPUREc CHAINc SLOTc OPUREc OFFERc TARGETSc REGc] IST")
        as "IST".
      { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
        iExists vsc, headc, offerc, ζhc, ζoc, Vbhc, Vboc, Vhc, Voc,
          targetsc, nodesc.
        solve_base_sl_red.
        iFrame "Hsc HPUREc CHAINc SLOTc OPUREc OFFERc TARGETSc REGc".
        rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
        iExists txhc. iFrame. }
      iEval (rewrite -IstHelp_nested_equiv) in "IST".
      cStepsT. sYield. cStepsT.
      iPoseProof (view_at_view_mon_pred
        (view_at (AtomicSeen stack_loc γh ζread))
        _ _ H12 with "SNh1") as "#SNh2".
      iEval (rewrite IstHelp_nested_equiv) in "IST".
      iInv "Hinv" with "[IST]" as "[IST INV]" "ACC";
        first by iFrame.
      iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INV".
      iDestruct "INV" as
        (vs2 head2 offer2 ζh2 ζo2 Vbh2 Vbo2 Vh2 Vo2 targets2 nodes2)
        "[Hs2 [HEAD2 [HPURE2 [CHAIN2 [SLOT2 [OPURE2 [OFFER2 [TARGETS2 REG2]]]]]]]]".
      iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def)
        in "HEAD2".
      iDestruct "HEAD2" as (txh2) "HEAD2".
      iPoseProof (AtomicPtsToX_AtomicSeen_latest with "HEAD2 SNh2")
        as "%Hread_cur2".
      pose proof (Hread_cur2 _ _ _ Hget) as Hget_cur2.
      iPoseProof "HPURE2" as "#HPUREcopy2".
      iDestruct "HPUREcopy2" as
        %(CURh2 & CASHh2 & PTRh2 & HEADH2 & LINKS2 & SENT2).
      destruct (PTRh2 _ _ _ _ _ Hget_cur2) as
        (head_loc2 & Vguard2 & Heqhead2 & Htarget2 & Hsafe2).
      inversion Heqhead2; subst head_loc2.
      assert (Hguard2 : View.le Vguard2 (TView.cur V2)).
      { destruct Hsafe2 as [EQ|LE]; first contradiction.
        etrans; [exact LE|]. etrans; [exact HVmsg|exact H12]. }
      cInlineT.
      cForceT (tid, stid, stack_loc, Val.Vptr head_loc,
        Val.Vptr d.(node_next), Ordering.relaxed, Ordering.acqrel, V2,
        γh, ζread, Vbh2, txh2, ζh2, CASOnly, target_pool targets2)%cris.
      cForcesT.
      iSplitL "TV HEAD2 TARGETS2".
      { iSplit.
        { iPureIntro. rewrite shift_0. reflexivity. }
        iFrame "TV SNh2 HEAD2 TARGETS2".
        iSplit.
        { iPureIntro. repeat split; eauto.
          intros t f value0 V0 b Htime Hget0.
          destruct (PTRh2 _ _ _ _ _ Hget0) as
            (loc0 & Vguard0 & EQ & IN & SAFE).
          subst value0. done. }
        iModIntro. iIntros "TARGETS2". iModIntro. iSplit.
        { iDestruct (target_pool_lookup _ _ Htarget2 with "TARGETS2")
            as "REC".
          iDestruct (target_record_take (head_loc, Vguard2)
            (TView.cur V2) Hguard2 with "REC")
            as (q C Vp γp Cp) "[PRIM #SEENp]".
          iExists q, C, Vp, γp, Cp. iFrame "PRIM". simpl. iExact "SEENp". }
        iIntros (t f loc V0 b) "%OTHER".
        destruct OTHER as (_ & GET & NE).
        destruct (PTRh2 _ _ _ _ _ GET) as
          (loc2 & Vg2 & EQ & IN & SAFE). inversion EQ; subst loc2.
        iDestruct (target_pool_prim _ _ IN with "TARGETS2")
          as (q C Vp) "PRIM".
        iExists q, C, Vp. done. }
      cStepsT.
      iDestruct "GRT" as
        "[-> [%casret [%ζseen3 [%ζnew [%tread [%fread3 [%LTread [%vread [%Vr [%bread [%V3 [HCAS [TV [SNh3 [TARGETS2 HCASE]]]]]]]]]]]]]]]".
      iDestruct "HCAS" as
        %[-> [Hseen23 [Hseen_new [Hcasget [Htread H23]]]]].
      iDestruct "HCASE" as "[HFAIL|HSUCC]".
      { iDestruct "HFAIL" as "[%FAIL HEAD2]".
        destruct FAIL as (-> & Hneq & Hacq & ->).
        iAssert (⌜current_message ζnew head2 Vh2 ∧ cas_history ζnew ∧
          pointer_history (stack_loc >> 2) targets2 ζnew ∧
          head_history (stack_loc >> 2) nodes2 ζnew ∧
          node_links (stack_loc >> 2) targets2 nodes2 ∧
          (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targets2)⌝)%I
          as "HPURE2"; first done.
        iMod ("ACC" with "[//]") as "[ACC _]".
        iMod ("ACC" with
          "[Hs2 HEAD2 HPURE2 CHAIN2 SLOT2 OPURE2 OFFER2 TARGETS2 REG2] IST")
          as "IST".
        { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
          iExists vs2, head2, offer2, ζnew, ζo2, Vbh2, Vbo2, Vh2, Vo2,
            targets2, nodes2.
          solve_base_sl_red.
          iFrame "Hs2 HPURE2 CHAIN2 SLOT2 OPURE2 OFFER2 TARGETS2 REG2".
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
          iExists txh2. iFrame. }
        iEval (rewrite -IstHelp_nested_equiv) in "IST".
        cStepsT. sYield. cStepsT. sYield. cStepsT.
        inversion H23 as [Hrel23 Hcur23 Hacq23].
        assert (Hcur03 : View.le (TView.cur V) (TView.cur V3)) by
          (etrans; [exact HVle|]; etrans; [exact H12|exact Hcur23]).
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen (stack_loc >> 1) γslot ζo_seen))
          _ _ Hcur03 with "SNo") as "#SNo3".
        iEval (rewrite IstHelp_nested_equiv) in "IST".
        iInv "Hinv" with "[IST]" as "[IST INV]" "ACC";
          first by iFrame.
        iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INV".
        iDestruct "INV" as
          (vs4 head4 offer4 ζh4 ζo4 Vbh4 Vbo4 Vh4 Vo4 targets4 nodes4)
          "[Hs4 [HEAD4 [HPURE4 [CHAIN4 [SLOT4 [OPURE4 [OFFER4 [TARGETS4 REG4]]]]]]]]".
        iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def)
          in "SLOT4".
        iDestruct "SLOT4" as (txo4) "SLOT4".
        iPoseProof (AtomicPtsToX_AtomicSeen_latest with "SLOT4 SNo3")
          as "%Horead_cur".
        cInlineT.
        cForceT (meta1 (tid, stid, stack_loc >> 1, Ordering.acqrel,
          ζo4, ζo_seen, txo4, γslot, 1%Qp, CASOnly, V3, Vbo4))%cris.
        cForcesT. iFrame "TV SNo3 SLOT4". iSplit; eauto.
        cStepT. cStepT. cStepT.
        iDestruct "GRT" as
          "[-> [%ζoread [%foread [%nao [%voret [%voactual [%Vomsg [%V4 [HOREAD [#SNo4 [SLOT4 TV]]]]]]]]]]]".
        iDestruct "HOREAD" as
          %[-> [Hoval [Hoseen [Hole [Hoget [H34 Homsg]]]]]].
        pose proof (Hole _ _ _ Hoget) as Hoget4.
        iPoseProof "OPURE4" as "#OPUREcopy4".
        iDestruct "OPUREcopy4" as %(CURo4 & CASHo4 & PTRo4).
        destruct (PTRo4 _ _ _ _ _ Hoget4) as
          (offer_loc & Voguard & Hoactual & Hotarget & Hosafe).
        subst voactual.
        pose proof (StackHdr.le_vptr_eq Hoval) as Horet. subst voret.
        iPoseProof "HPURE4" as "#HPUREcopy4".
        iDestruct "HPUREcopy4" as
          %(CURh4 & CASHh4 & PTRh4 & HEADH4 & LINKS4 & SENT4).
        iAssert (⌜current_message ζh4 head4 Vh4 ∧ cas_history ζh4 ∧
          pointer_history (stack_loc >> 2) targets4 ζh4 ∧
          head_history (stack_loc >> 2) nodes4 ζh4 ∧
          node_links (stack_loc >> 2) targets4 nodes4 ∧
          (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targets4)⌝)%I
          as "HPURE4"; first done.
        iAssert (⌜current_message ζo4 offer4 Vo4 ∧ cas_history ζo4 ∧
          pointer_history (stack_loc >> 2) targets4 ζo4⌝)%I
          as "OPURE4"; first done.
        iMod ("ACC" with "[//]") as "[ACC _]".
        iMod ("ACC" with
          "[Hs4 HEAD4 HPURE4 CHAIN4 SLOT4 OPURE4 OFFER4 TARGETS4 REG4] IST")
          as "IST".
        { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
          iExists vs4, head4, offer4, ζh4, ζo4, Vbh4, Vbo4, Vh4, Vo4,
            targets4, nodes4.
          solve_base_sl_red.
          iFrame "Hs4 HEAD4 HPURE4 CHAIN4 OPURE4 OFFER4 TARGETS4 REG4".
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
          iExists txo4. iFrame. }
        iEval (rewrite -IstHelp_nested_equiv) in "IST".
        destruct (decide (offer_loc = stack_loc >> 2))
          as [Hoffer_empty|Hoffer_nonempty].
        { subst offer_loc. cStepsT. case_decide; last contradiction.
          cStepsT.
          assert (Hcur04 : View.le (TView.cur V) (TView.cur V4)) by
            (etrans; [exact Hcur03|exact H34]).
          assert (Hcur24 : View.le (TView.cur V2) (TView.cur V4)) by
            (etrans; [exact Hcur23|exact H34]).
          iPoseProof (view_at_view_mon_pred
            (view_at (AtomicSeen stack_loc γh ζread))
            _ _ Hcur24 with "SNh2") as "#SNh4".
          iPoseProof (view_at_view_mon_pred
            (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard))
            _ _ Hcur04 with "SNg") as "#SNg4".
          iAssert (stack_handle γs (Val.Vptr stack_loc) (TView.cur V4))%I
            with "[]" as "#HANDLE4".
          { rewrite /stack_handle.
            iExists stack_loc, γstackinv, γh, γslot, ζread, ζoread,
              γguard, ζguard, γnm.
            iSplit; first done. iFrame "Hinv SNh4 SNo4 SNg4". }
          cByCoind CIH. iFrame "HANDLE4 IST TV WINV". }
        { cStepsT. case_decide; first contradiction.
          cStepsT. sYield. cStepsT.
          iEval (rewrite IstHelp_nested_equiv) in "IST".
          iInv "Hinv" with "[IST]" as "[IST INV]" "ACC";
            first by iFrame.
          iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INV".
          iDestruct "INV" as
            (vs5 head5 offer5 ζh5 ζo5 Vbh5 Vbo5 Vh5 Vo5 targets5 nodes5)
            "[Hs5 [HEAD5 [HPURE5 [CHAIN5 [SLOT5 [OPURE5 [OFFER5 [TARGETS5 REG5]]]]]]]]".
          iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def)
            in "SLOT5".
          iDestruct "SLOT5" as (txo5) "SLOT5".
          iPoseProof (AtomicPtsToX_AtomicSeen_latest with "SLOT5 SNo4")
            as "%Horead_cur5".
          pose proof (Horead_cur5 _ _ _ Hoget) as Hoget5.
          iPoseProof "HPURE5" as "#HPUREcopy5".
          iDestruct "HPUREcopy5" as
            %(CURh5 & CASHh5 & PTRh5 & HEADH5 & LINKS5 & SENT5).
          iPoseProof "OPURE5" as "#OPUREcopy5".
          iDestruct "OPUREcopy5" as %(CURo5 & CASHo5 & PTRo5).
          destruct (PTRo5 _ _ _ _ _ Hoget5) as
            (offer_loc5 & Voguard5 & Heqoffer5 & Hotarget5 & Hosafe5).
          inversion Heqoffer5; subst offer_loc5.
          change (View.le Vomsg (TView.cur V4)) in Homsg.
          assert (Hoguard5 : View.le Voguard5 (TView.cur V4)).
          { destruct Hosafe5 as [EQ|LE]; first contradiction.
            etrans; [exact LE|exact Homsg]. }
          cInlineT.
          cForceT (tid, stid, stack_loc >> 1, Val.Vptr offer_loc,
            Val.Vptr (stack_loc >> 2), Ordering.acqrel, Ordering.acqrel,
            V4, γslot, ζoread, Vbo5, txo5, ζo5, CASOnly,
            target_pool targets5)%cris.
          cForcesT.
          iSplitL "TV SLOT5 TARGETS5".
          { iSplit.
            { iPureIntro. repeat split; eauto. }
            iFrame "TV SNo4 SLOT5 TARGETS5".
            iSplit.
            { iPureIntro. repeat split; try done.
              intros t f value0 V0 b Htime Hget0.
              destruct (PTRo5 _ _ _ _ _ Hget0) as
                (loc0 & Vguard0 & EQ & IN & SAFE).
              subst value0. done. }
            iModIntro. iIntros "TARGETS5". iModIntro. iSplit.
            { iDestruct (target_pool_lookup _ _ Hotarget5 with "TARGETS5")
                as "REC".
              iDestruct (target_record_take (offer_loc, Voguard5)
                (TView.cur V4) Hoguard5 with "REC")
                as (q C Vp γp Cp) "[PRIM #SEENp]".
              iExists q, C, Vp, γp, Cp. iFrame "PRIM".
              simpl. iExact "SEENp". }
            iIntros (t f loc V0 b) "%OTHER".
            destruct OTHER as (_ & GET & NE).
            destruct (PTRo5 _ _ _ _ _ GET) as
              (loc2 & Vg2 & EQ & IN & SAFE). inversion EQ; subst loc2.
            iDestruct (target_pool_prim _ _ IN with "TARGETS5")
              as (q C Vp) "PRIM".
            iExists q, C, Vp. done. }
          cStepsT.
          iDestruct "GRT" as
            "[-> [%claimret [%ζoseen5 [%ζonew [%toread [%foread5 [%LToread [%voread [%Vor [%boread [%V5 [HCLAIM [TV [#SNo5 [TARGETS5 HCLAIMCASE]]]]]]]]]]]]]]]".
          iDestruct "HCLAIM" as
            %[-> [Hoseen45 [Hoseen_new [Hoclaimget [Htoread H45]]]]].
          iDestruct "HCLAIMCASE" as "[HCLAIMFAIL|HCLAIMSUCC]".
          { iDestruct "HCLAIMFAIL" as "[%CLAIMFAIL SLOT5]".
            destruct CLAIMFAIL as (-> & Hclaimneq & Hclaimacq & ->).
            iAssert (⌜current_message ζh5 head5 Vh5 ∧ cas_history ζh5 ∧
              pointer_history (stack_loc >> 2) targets5 ζh5 ∧
              head_history (stack_loc >> 2) nodes5 ζh5 ∧
              node_links (stack_loc >> 2) targets5 nodes5 ∧
              (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targets5)⌝)%I
              as "HPURE5"; first done.
            iAssert (⌜current_message ζonew offer5 Vo5 ∧
              cas_history ζonew ∧
              pointer_history (stack_loc >> 2) targets5 ζonew⌝)%I
              as "OPURE5"; first done.
            iMod ("ACC" with "[//]") as "[ACC _]".
            iMod ("ACC" with
              "[Hs5 HEAD5 HPURE5 CHAIN5 SLOT5 OPURE5 OFFER5 TARGETS5 REG5] IST")
              as "IST".
            { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
              iExists vs5, head5, offer5, ζh5, ζonew, Vbh5, Vbo5,
                Vh5, Vo5, targets5, nodes5.
              solve_base_sl_red.
              iFrame "Hs5 HEAD5 HPURE5 CHAIN5 OPURE5 OFFER5 TARGETS5 REG5".
              rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
              iExists txo5. iFrame. }
            iEval (rewrite -IstHelp_nested_equiv) in "IST".
            inversion H23 as [Hrel23' Hcur23' Hacq23'].
            inversion H45 as [Hrel45 Hcur45 Hacq45].
            assert (Hcur25 : View.le (TView.cur V2) (TView.cur V5)) by
              (etrans; [exact Hcur23'|]; etrans; [exact H34|exact Hcur45]).
            assert (Hcur05 : View.le (TView.cur V) (TView.cur V5)) by
              (etrans; [exact HVle|]; etrans; [exact H12|exact Hcur25]).
            iPoseProof (view_at_view_mon_pred
              (view_at (AtomicSeen stack_loc γh ζread))
              _ _ Hcur25 with "SNh2") as "#SNh5".
            iPoseProof (view_at_view_mon_pred
              (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard))
              _ _ Hcur05 with "SNg") as "#SNg5".
            iAssert (stack_handle γs (Val.Vptr stack_loc) (TView.cur V5))%I
              with "[]" as "#HANDLE5".
            { rewrite /stack_handle.
              iExists stack_loc, γstackinv, γh, γslot, ζread, ζoseen5,
                γguard, ζguard, γnm.
              iSplit; first done. iFrame "Hinv SNh5 SNo5 SNg5". }
            cStepsT. sYield. cStepsT.
            cByCoind CIH. iFrame "HANDLE5 IST TV WINV". }
          { iDestruct "HCLAIMSUCC" as (Vow) "[%CLAIMSUCC [_ SLOT5]]".
            destruct CLAIMSUCC as
              (-> & Heqclaim & towrite & HOADD & Hovrw & Hovrne &
                Honotle & HoneV & Hoord).
            subst voread.
            assert (Hotwrite : Time.lt toread towrite) by
              (eapply cell_add_lt; exact HOADD).
            assert (Hotread_ne : toread ≠ towrite) by
              (intros ->; eapply Time.lt_strorder; exact Hotwrite).
            assert (Hoget_base :
              Cell.get toread ζo5 =
                Some (foread5,
                  Message.message (Val.Vptr offer_loc) Vor boread)).
            { pose proof (Hoseen_new _ _ _ Hoclaimget) as Hget_new.
              erewrite Cell.add_o in Hget_new; eauto.
              destruct (Time.eq_dec toread towrite);
                [contradiction|done]. }
            assert (Homax : toread = Cell.max_ts ζo5).
            { eapply cas_history_add_from_max; eauto. }
            assert (Hoffer5 : offer5 = Val.Vptr offer_loc).
            { destruct CURo5 as (fcur & bcur & Hcur).
              rewrite <- Homax in Hcur. congruence. }
            subst offer5.
            assert (HVo5 : Vo5 = Vor).
            { destruct CURo5 as (fcur & bcur & Hcur).
              rewrite <- Homax in Hcur. congruence. }
            subst Vor.
            assert (CURonew : current_message ζonew
              (Val.Vptr (stack_loc >> 2)) Vow).
            { eapply current_message_add; eauto. }
            assert (CASHonew : cas_history ζonew).
            { eapply cas_history_add; eauto. }
            destruct SENT5 as (Vsent5 & Hsent5).
            assert (PTRonew :
              pointer_history (stack_loc >> 2) targets5 ζonew).
            { eapply pointer_history_add; [exact PTRo5| |exact HOADD].
              exists Vsent5. split; first exact Hsent5. left; done. }
            iMod ("ACC" with "[//]") as "[ACC _]".
            iMod ("ACC" with
              "[Hs5 HEAD5 CHAIN5 SLOT5 TARGETS5 REG5] IST")
              as "IST".
            { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
              iExists vs5, head5, (Val.Vptr (stack_loc >> 2)), ζh5,
                ζonew, Vbh5, (Vbo5 ⊔ TView.cur V5), Vh5, Vow,
                targets5, nodes5.
              solve_base_sl_red.
              iFrame "Hs5 HEAD5 CHAIN5 TARGETS5 REG5".
              iSplit.
              { iPureIntro.
                split; first exact CURh5.
                split; first exact CASHh5.
                split; first exact PTRh5.
                split; first exact HEADH5.
                split; first exact LINKS5.
                exists Vsent5. exact Hsent5. }
              iSplitL "SLOT5".
              { rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
                iExists txo5. iFrame. }
              iSplit.
              { iPureIntro.
                split; first exact CURonew.
                split; [exact CASHonew|exact PTRonew]. }
              rewrite /is_offer. case_decide; done. }
            iEval (rewrite -IstHelp_nested_equiv) in "IST".
            iEval (rewrite /is_offer) in "OFFER5".
            case_decide; first contradiction.
            iDestruct "OFFER5" as
              (Vstate Vvalue γinv γo value reqid) "[%Hofferpub #OfferInv]".
            change (Vow = TView.cur V5) in Hoord. subst Vow.
            destruct Hofferpub as [Hstatepub Hvaluepub].
            assert (Hstate5 : View.le Vstate (TView.cur V5)) by
              (etrans; [exact Hstatepub|exact Hovrw]).
            assert (Hvalue5 : View.le Vvalue (TView.cur V5)) by
              (etrans; [exact Hvaluepub|exact Hovrw]).
            cStepsT. sYield. cStepsT. sYield. cStepsT.
            iEval (rewrite IstHelp_nested_equiv) in "IST".
            iInv "OfferInv" with "[IST]" as "[IST OINV]" "OACC";
              first by iFrame.
            iEval (solve_base_sl_red) in "OINV".
            iDestruct "OINV" as
              (state ζstate ζstate_seen Vbstate Vmsgstate γstate)
              "[STATE [#SNstate [STATEPURE OSTATE]]]".
            iDestruct "STATEPURE" as
              %(Hstate_seen & CURstate & NUMstate & CASHstate & STATEHIST).
            iPoseProof (view_at_view_mon_pred
              (view_at (AtomicSeen (offer_loc >> 1) γstate ζstate_seen))
              _ _ Hstate5 with "SNstate") as "#SNstate5".
            iEval (rewrite AtomicPtsTo_eq /AtomicPtsTo_def) in "STATE".
            iDestruct "STATE" as (txstate) "STATE".
            cInlineT.
            cForceT (tid, stid, offer_loc >> 1, Val.zero, Val.one,
              Ordering.acqrel, Ordering.acqrel, V5, γstate, ζstate_seen,
              Vbstate, txstate, ζstate, CASOnly, emp%I)%cris.
            cForcesT.
            iSplitL "TV STATE".
            { iSplit.
              { iPureIntro. repeat split; eauto. }
              iFrame "TV SNstate5 STATE".
              iSplit.
              { iPureIntro. repeat split; eauto.
                intros t f v V0 b _ Hget0.
                destruct (NUMstate _ _ _ _ _ Hget0) as [z ->]. done. }
              solve_base_sl_red. }
            cStepsT.
            iDestruct "GRT" as
              "[-> [%tookret [%ζstate_read [%ζstate_new [%tstate [%fstate [%LTstate [%vstate [%Vstate_read [%bstate [%V6 [HTAKE [TV [SNstate6 [_ HTAKECASE]]]]]]]]]]]]]]]".
            iDestruct "HTAKE" as
              %[-> [Hstate_seen56 [Hstate_read_new
                [Hstate_get [Htstate H56]]]]].
            iDestruct "HTAKECASE" as "[HTAKEFAIL|HTAKESUCC]".
            { iDestruct "HTAKEFAIL" as "[%TAKEFAIL STATE]".
              destruct TAKEFAIL as (-> & Htakeneq & Htakeacq & ->).
              iAssert (@{Vbstate} (offer_loc >> 1) cas↦{γstate}
                ζstate_new)%I with "[STATE]" as "STATE".
              { rewrite AtomicPtsTo_eq /AtomicPtsTo_def.
                iExists txstate. done. }
              iMod ("OACC" with "[//]") as "[OACC _]".
              iMod ("OACC" with "[STATE OSTATE] IST") as "IST".
              { solve_base_sl_red.
                iExists state, ζstate_new, ζstate_seen,
                  Vbstate, Vmsgstate, γstate.
                iFrame "STATE SNstate OSTATE". done. }
              iEval (rewrite -IstHelp_nested_equiv) in "IST".
              inversion H23 as [Hrel23'' Hcur23'' Hacq23''].
              inversion H45 as [Hrel45' Hcur45' Hacq45'].
              inversion H56 as [Hrel56 Hcur56 Hacq56].
              assert (Hcur26 : View.le (TView.cur V2) (TView.cur V6)) by
                (etrans; [exact Hcur23''|]; etrans; [exact H34|];
                 etrans; [exact Hcur45'|exact Hcur56]).
              assert (Hcur06 : View.le (TView.cur V) (TView.cur V6)) by
                (etrans; [exact HVle|]; etrans; [exact H12|exact Hcur26]).
              iPoseProof (view_at_view_mon_pred
                (view_at (AtomicSeen stack_loc γh ζread))
                _ _ Hcur26 with "SNh2") as "#SNh6".
              iPoseProof (view_at_view_mon_pred
                (view_at (AtomicSeen (stack_loc >> 1) γslot ζoseen5))
                _ _ Hcur56 with "SNo5") as "#SNo6".
              iPoseProof (view_at_view_mon_pred
                (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard))
                _ _ Hcur06 with "SNg") as "#SNg6".
              iAssert (stack_handle γs (Val.Vptr stack_loc) (TView.cur V6))%I
                with "[]" as "#HANDLE6".
              { rewrite /stack_handle.
                iExists stack_loc, γstackinv, γh, γslot, ζread, ζoseen5,
                  γguard, ζguard, γnm.
                iSplit; first done. iFrame "Hinv SNh6 SNo6 SNg6". }
              cStepsT. sYield. cStepsT.
              cByCoind CIH. iFrame "HANDLE6 IST TV WINV". }
            { iDestruct "HTAKESUCC" as (Vstate_write)
                "[%TAKESUCC [_ STATE]]".
              destruct TAKESUCC as
                (-> & Heqtake & tstate_write & HSTATEADD & Hsvrw &
                  Hsvrne & Hsnotle & HsneV & Hstateord).
              subst vstate.
              assert (Htstate_write : Time.lt tstate tstate_write) by
                (eapply cell_add_lt; exact HSTATEADD).
              assert (Htstate_ne : tstate ≠ tstate_write) by
                (intros ->; eapply Time.lt_strorder; exact Htstate_write).
              assert (Hstate_get_base :
                Cell.get tstate ζstate =
                  Some (fstate,
                    Message.message Val.zero Vstate_read bstate)).
              { pose proof (Hstate_read_new _ _ _ Hstate_get) as Hget_new.
                erewrite Cell.add_o in Hget_new; eauto.
                destruct (Time.eq_dec tstate tstate_write);
                  [contradiction|done]. }
              assert (Hstatemax : tstate = Cell.max_ts ζstate).
              { eapply cas_history_add_from_max; eauto. }
              assert (Hstatezero : state = Val.zero).
              { destruct CURstate as (fcur & bcur & Hcur).
                rewrite <- Hstatemax in Hcur. congruence. }
              subst state.
              iEval (simpl) in "OSTATE".
              iDestruct "OSTATE" as "[PAYLOAD HelpPend]".
              change (Vstate_write = TView.cur V6) in Hstateord.
              subst Vstate_write.
              assert (CURstate_new : current_message ζstate_new
                Val.one (TView.cur V6)).
              { eapply current_message_add; eauto. }
              assert (NUMstate_new : numeric_history ζstate_new).
              { eapply numeric_history_add; eauto. }
              assert (CASHstate_new : cas_history ζstate_new).
              { eapply cas_history_add; eauto. }
              assert (STATEHISTnew :
                offer_state_history ζstate_new Val.one).
              { eapply offer_state_history_add_from_zero; eauto. }
              assert (Hstate_seen_new : Cell.le ζstate_seen ζstate_new) by
                (etrans; eauto).
              iAssert (@{Vbstate ⊔ TView.cur V6}
                (offer_loc >> 1) cas↦{γstate} ζstate_new)%I
                with "[STATE]" as "STATE".
              { rewrite AtomicPtsTo_eq /AtomicPtsTo_def.
                iExists txstate. done. }
              cStepsT.
              sYieldS. cForceS true. cStepsS. cInlineS. cStepsS.
              prependRetT tt.
              iApply (wsim_helping_help with "HelpPend").
              iExists 1.
              iMod ("OACC" with "[//]") as "[_ > OACC]". iModIntro.
              aUnfoldS. cStepsS. iApply wsim_yield_namespace_src.
              rewrite /StackM.jobCode.
              cNormS. cStepsS.
              iInv "Hinv" with "[IST]" as "[IST HINV]" "HACC".
              { iFrame. solve_ndisj. }
              iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "HINV".
              iDestruct "HINV" as
                (vsh headh offerh ζhh ζoh Vbhh Vboh Vhh Voh targetsh nodesh)
                "[Hsh [HEADh [HPUREh [CHAINh [SLOTh [OPUREh [OFFERh [TARGETSh REGh]]]]]]]]".
              iDestruct (stack_content_auth_agree with "Hsh ASM") as %Hjob.
              subst _q.
              iMod (stack_content_auth_update γs vsh (value :: vsh)
                with "Hsh ASM") as "[Hsh ASM]".
              cForcesS; first iFrame "ASM".
              iMod ("HACC" with "[//]") as "[_ > HACC]".
              cStep. iFrame.
              iIntros "#Done".
              cStepsS. aUnfoldS. sYieldS. cStepsS.
              iDestruct (stack_content_auth_agree with "Hsh ASM")
                as %Hpop.
              subst _q.
              iMod (stack_content_auth_update γs (value :: vsh) vsh
                with "Hsh ASM") as "[Hsh ASM]".
              cForceS (inr value↑). cForcesS. iFrame "ASM".
              iMod ("HACC" with
                "[Hsh HEADh HPUREh CHAINh SLOTh OPUREh OFFERh TARGETSh REGh] IST")
                as "IST".
              { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
                iExists vsh, headh, offerh, ζhh, ζoh, Vbhh, Vboh,
                  Vhh, Voh, targetsh, nodesh.
                solve_base_sl_red.
                iFrame "Hsh HEADh HPUREh CHAINh SLOTh OPUREh OFFERh TARGETSh REGh". }
              iMod ("OACC" with "[STATE Done] IST") as "IST".
              { solve_base_sl_red.
                iExists Val.one, ζstate_new, ζstate_seen,
                  (Vbstate ⊔ TView.cur V6), (TView.cur V6), γstate.
                iFrame "STATE SNstate".
                iSplit; first done.
                simpl. iExact "Done". }
              iEval (rewrite -IstHelp_nested_equiv) in "IST".
              inversion H56 as [Hrel56' Hcur56' Hacq56'].
              assert (Hvalue6 : View.le Vvalue (TView.cur V6)) by
                (etrans; [exact Hvalue5|exact Hcur56']).
              iPoseProof (view_at_view_mon_pred
                (view_at (own_loc_na (offer_loc >> 2) 1
                  (StackHdr.encode value)))
                Vvalue (TView.cur V6) Hvalue6 with "PAYLOAD")
                as "PAYLOAD".
              sYield. cStepsT. sYield. cStepsT.
              cInlineT.
              cForceT (meta0 (tid, stid, offer_loc >> 2, Ordering.na,
                StackHdr.encode value, 1%Qp, V6))%cris.
              cForcesT. iFrame "TV PAYLOAD".
              iSplit; eauto. cStepsT.
              iDestruct "GRT" as
                "[-> [%offer_payload [%V7 [[-> %Hoffer_payload] [PAYLOAD TV]]]]]".
              pose proof (StackHdr.decode_le_encode Hoffer_payload)
                as Hofferdecode.
              cStepsT. sYield. cStepsT.
              rewrite Hofferdecode.
              sYieldS. cStepsS. cForcesS.
              iSplitL "TV".
              { iExists V7. iSplit; first done. iFrame "TV". }
              cStepsS. cStepsT. cStep. iFrame "IST". done. } } } }
      { iDestruct "HSUCC" as (Vw) "[%SUCC [_ HEAD2]]".
        destruct SUCC as
          (-> & Heqread & twrite & HADD & Hvrw & Hvrne & Hnotle & HneqV & Hord).
        subst vread.
        assert (Htwrite : Time.lt tread twrite) by
          (eapply cell_add_lt; exact HADD).
        assert (Htread_ne : tread ≠ twrite) by
          (intros ->; eapply Time.lt_strorder; exact Htwrite).
        assert (Hget_base :
          Cell.get tread ζh2 =
            Some (fread3, Message.message (Val.Vptr head_loc) Vr bread)).
        { pose proof (Hseen_new _ _ _ Hcasget) as Hget_new.
          erewrite Cell.add_o in Hget_new; eauto.
          destruct (Time.eq_dec tread twrite); [contradiction|done]. }
        assert (Hmax : tread = Cell.max_ts ζh2).
        { eapply cas_history_add_from_max; eauto. }
        assert (Hhead2 : head2 = Val.Vptr head_loc).
        { destruct CURh2 as (fcur & bcur & Hcur).
          rewrite <- Hmax in Hcur. congruence. }
        subst head2.
        destruct (head_history_lookup _ _ _ _ _ _ _ _ Hnonempty
          Hget_base HEADH2) as (dcur & LOOKcur & LEcurVr).
        destruct (head_history_lookup _ _ _ _ _ _ _ _ Hnonempty
          Hget_cur2 HEADH2) as (dpre & LOOKpre & LEpre).
        iDestruct (node_registry_lookup_acc γnm nodes2 head_loc dcur LOOKcur
          with "REG2") as "[RECcur [#NEXTcur CLOSEcur]]".
        iPoseProof ("CLOSEcur" with "RECcur") as "REG2".
        iDestruct (node_next_token_agree with "NEXTold NEXTcur")
          as %Hnext_agree.
        rewrite Hnext_agree in HADD.
        assert (dpre = dcur) by congruence. subst dpre.
        assert (LEcur2 : View.le dcur.(node_pub_view) (TView.cur V2)) by
          (etrans; [exact LEpre|]; etrans; [exact HVmsg|exact H12]).
        destruct vs2 as [|value2 tail2].
        { iDestruct "CHAIN2" as "%EQ". inversion EQ; subst. contradiction. }
        iDestruct "CHAIN2" as (node2 dchain)
          "[%REL [VALUE TAIL]]".
        destruct REL as (Hrep & Hnode_ne & Hlookchain & Hvalue).
        inversion Hrep; subst node2.
        assert (dchain = dcur) by congruence. subst dchain.
        sYieldS. cForceS false. cStepsS.
        aUnfoldS. sYieldS. cStepsS.
        iDestruct (stack_content_auth_agree with "Hs2 ASM") as %Hstack.
        subst _q.
        iMod (stack_content_auth_update γs (value2 :: tail2) tail2
          with "Hs2 ASM") as "[Hs2 ASM]".
        cForceS (inr value2↑). cForcesS. iFrame "ASM".
        inversion H23 as [Hrel23 Hcur23 Hacq23].
        assert (LEcur3 : View.le dcur.(node_pub_view) (TView.cur V3)) by
          (etrans; [exact LEcur2|exact Hcur23]).
        change (View.le (TView.cur V3) Vw) in Hord.
        destruct (LINKS2 _ _ LOOKcur) as [_ Hnext_link].
        assert (PTRnew_info :
          ∃ Vguard, (dcur.(node_next), Vguard) ∈ targets2 ∧
            (dcur.(node_next) = stack_loc >> 2 ∨ View.le Vguard Vw)).
        { destruct Hnext_link as [HSENT|(dnext & Vguardn & LOOKnext & INnext &
              LEpubnext & LEguardnext)].
          - destruct SENT2 as (Vsent & INsent).
            exists Vsent. split.
            { rewrite HSENT. exact INsent. }
            { left. exact HSENT. }
          - exists Vguardn. split; first done. right.
            etrans; [exact LEguardnext|].
            etrans; [exact LEcur3|exact Hord]. }
        assert (HEADnew_info :
          dcur.(node_next) = stack_loc >> 2 ∨
            ∃ dnext, nodes2 !! dcur.(node_next) = Some dnext ∧
              View.le dnext.(node_pub_view) Vw).
        { destruct Hnext_link as [HSENT|(dnext & Vguardn & LOOKnext & INnext &
              LEpubnext & LEguardnext)].
          - left; done.
          - right. exists dnext. split; first done.
            etrans; [exact LEpubnext|].
            etrans; [exact LEcur3|exact Hord]. }
        assert (CURnew : current_message ζnew
          (Val.Vptr dcur.(node_next)) Vw).
        { eapply current_message_add; eauto. }
        assert (CASHnew : cas_history ζnew).
        { eapply cas_history_add; eauto. }
        assert (PTRnew : pointer_history (stack_loc >> 2) targets2 ζnew).
        { eapply pointer_history_add; eauto. }
        assert (HEADnew : head_history (stack_loc >> 2) nodes2 ζnew).
        { eapply head_history_add; eauto. }
        iDestruct (live_value_take head_loc dcur (TView.cur V3) LEcur3
          with "VALUE") as "PAYLOAD".
        iEval (rewrite Hvalue) in "PAYLOAD".
        iAssert (⌜current_message ζnew (Val.Vptr dcur.(node_next)) Vw ∧
          cas_history ζnew ∧
          pointer_history (stack_loc >> 2) targets2 ζnew ∧
          head_history (stack_loc >> 2) nodes2 ζnew ∧
          node_links (stack_loc >> 2) targets2 nodes2 ∧
          (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targets2)⌝)%I
          as "HPURE2"; first done.
        iMod ("ACC" with "[//]") as "[ACC _]".
        iMod ("ACC" with
          "[Hs2 HEAD2 HPURE2 TAIL SLOT2 OPURE2 OFFER2 TARGETS2 REG2] IST")
          as "IST".
        { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
          iExists tail2, (Val.Vptr dcur.(node_next)), offer2, ζnew, ζo2,
            (Vbh2 ⊔ TView.cur V3), Vbo2, Vw, Vo2, targets2, nodes2.
          solve_base_sl_red.
          iFrame "Hs2 HPURE2 TAIL SLOT2 OPURE2 OFFER2 TARGETS2 REG2".
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
          iExists txh2. iFrame. }
        iEval (rewrite -IstHelp_nested_equiv) in "IST".
        cStepsT. sYield. cStepsT. sYield. cStepsT.
        cInlineT.
        cForceT (meta0 (tid, stid, head_loc >> 2, Ordering.na,
          StackHdr.encode value2, 1%Qp, V3))%cris.
        cForcesT. iFrame "TV PAYLOAD".
        iSplit; eauto. cStepsT.
        iDestruct "GRT" as
          "[-> [%vpayload [%V4 [[-> %Hpayload] [PAYLOAD TV]]]]]".
        pose proof (StackHdr.decode_le_encode Hpayload) as Hdecode.
        cStepsT. sYield. cStepsT.
        rewrite Hdecode.
        sYieldS. cStepsS. cForcesS.
        iSplitL "TV".
        { iExists V4. iSplit; first done. iFrame "TV". }
        cStepsS. cStepsT. cStep. iFrame "IST". done. }
  Qed.
End StackIM.
