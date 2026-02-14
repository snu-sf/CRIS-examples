Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import PFMemIAproof.

Section free.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  (* Move to Memory.v *)
  Lemma free_get_size mem1 mem2 loc
      (WF : Memory.well_alloced mem1)
      (FREE : Memory.free mem1 loc mem2) :
    ∀ loc',
      Loc.get_tbid loc = Loc.get_tbid loc'
        ∧ (∃sz, Memory.get_size loc' mem1 = Some sz)
        ∧ Memory.get_size loc' mem2 = None
      ∨ Loc.get_tbid loc ≠ Loc.get_tbid loc'
        ∧ Memory.get_size loc' mem1 = Memory.get_size loc' mem2.
  Proof.
    intros loc'; destruct (decide (Loc.get_tbid loc = Loc.get_tbid loc')); [left | right]; split; ss.
    { 
      inv FREE; rewrite /Memory.get_size /=; des_ifs; destruct loc'; ss; des; clarify; split; ss.
      rewrite /Memory.is_freeable /Block.is_freeable in FREEABLE. des_ifs. ss.
      rewrite /Block.get_size; des_ifs. eauto.
    }
    inv FREE; rewrite /Memory.get_size /=; des_ifs.
    destruct loc'; ss; des; clarify.
  Qed.

  (* Move to HistoryRA.v *)
  Lemma hist_freeable_size_free lc1 gl1 sz lc2 gl2 loc sz' 
      (WF : Global.wf gl1)
      (STEP : Local.free_step lc1 gl1 loc sz lc2 gl2) 
    :
    hist_freeable loc 1 sz' ∗ hist_freeable_auth (Global.memory gl1)
    ==∗ ⌜sz' = sz⌝ ∗ hist_freeable loc 1 sz' ∗ hist_freeable_auth (Global.memory gl1)
    .
  Proof.
    rewrite hist_freeable_auth_eq /hist_freeable_auth_def hist_freeable_eq /hist_freeable_def.
    destruct loc as [[tid | ] bid ofs]; (inv STEP; inv FREE).
    iIntros "[F A]".
    iDestruct "F" as (? ?) "[% F]". inv H.
    iCombine "A F" as "A" gives %WF0. eapply auth_both_valid_discrete in WF0. des.
    eapply discrete_fun_included_spec_1 in WF0.
    instantiate (1:= (tid, bid)) in WF0. ss.
    rewrite discrete_fun_lookup_singleton in WF0. des_ifs.
    eapply Some_included_exclusive in WF0; ss; [|eapply pair_exclusive_r; ss].
    inv WF0. ss.
    iDestruct "A" as "[A F]". iFrame; eauto.
  Qed.

  (* Move to HistoryRA.v *)
  (* Maybe integrated lemma with 'hist_freeable_size_free' *)
  Lemma hist_freeable_size_racy_free lc1 gl1 sz loc sz' race
      (WF : Global.wf gl1)
      (STEP : Local.racy_free_step lc1 gl1 loc sz race) 
    :
    hist_freeable loc 1 sz' ∗ hist_freeable_auth (Global.memory gl1)
    ==∗ ⌜sz' = sz⌝ ∗ hist_freeable loc 1 sz' ∗ hist_freeable_auth (Global.memory gl1)
    .
  Proof.
    rewrite hist_freeable_auth_eq /hist_freeable_auth_def hist_freeable_eq /hist_freeable_def.
    destruct loc as [[tid | ] bid ofs]; (inv STEP); cycle 1.
    { 
      exfalso. inv WF. inv MEM_WELL_ALLOCED.
      specialize (GLOBAL bid). des.
      rewrite /Memory.is_freeable /Block.is_freeable GLOBAL in STATE.
      ss.
    }
    iIntros "[F A]".
    iDestruct "F" as (? ?) "[% F]". inv H.
    iCombine "A F" as "A" gives %WF0. eapply auth_both_valid_discrete in WF0. des.
    eapply discrete_fun_included_spec_1 in WF0.
    instantiate (1:= (tid0, bid0)) in WF0. ss.
    rewrite discrete_fun_lookup_singleton in WF0. des_ifs.
    eapply Some_included_exclusive in WF0; ss; [|eapply pair_exclusive_r; ss].
    inv WF0. ss.
    iDestruct "A" as "[A F]". iFrame; eauto.
  Qed.

  (* Move to HistoryRA.v *)
  Lemma hist_freeable_auth_free lc1 gl1 sz lc2 gl2 loc sz'
      (WF : Global.wf gl1)
      (STEP : Local.free_step lc1 gl1 loc sz lc2 gl2)
    :
    hist_freeable loc 1 sz' ∗ hist_freeable_auth (Global.memory gl1)
    ==∗ hist_freeable_auth (Global.memory gl2).
  Proof.
    rewrite hist_freeable_auth_eq /hist_freeable_auth_def hist_freeable_eq /hist_freeable_def.
    destruct loc as [[tid | ] bid ofs]; last (inv STEP; inv FREE).
    iIntros "[F A]".
    iDestruct "F" as (? ?) "[% F]". inv H.
    iCombine "A F" as "A". iMod (own_update with "A") as "A"; eauto.
    eapply auth_update_dealloc,  discrete_fun_local_update; intros [tid' bid']; s. 
    inv STEP. inv WF; ss.
    hexploit (Memory.free_is_freeable); eauto.
    instantiate (1:=Loc.mk (Some tid') bid' 0); ss. intros [[NEW [F1 F2]] | [NEQ EQ]].
    { des_ifs.  
      rewrite discrete_fun_lookup_singleton.
      eapply delete_option_local_update, pair_exclusive_r. ss. 
    }
    rewrite /Loc.get_tbid in NEQ; ss.
    rewrite discrete_fun_lookup_singleton_ne; last ii; clarify.
    rewrite EQ; des_ifs; ss.
    { (* free_get_size *) 
      hexploit free_get_size; eauto. 
      instantiate (1:= {| Loc.tid := Some tid'; Loc.bid := bid'; Loc.ofs := 0 |}). 
      i. inv H; rewrite Heq0 Heq1 in H0; inv H0. refl.
    }
    { 
      exfalso. hexploit free_get_size; eauto. 
      instantiate (1:= {| Loc.tid := Some tid'; Loc.bid := bid'; Loc.ofs := 0 |}). 
      i. inv H; rewrite Heq0 Heq1 in H0; inv H0.
    }
    { exfalso.  
      rewrite /Memory.is_freeable /Block.is_freeable in EQ. 
      rewrite /Memory.get_size /Block.get_size in Heq0. 
      des_ifs.
    }
  Qed.

  Lemma hist_auth_free_vs lc1 gl1 sz lc2 gl2 loc Vcut 𝓥 sz'
      (WF : Global.wf gl1)
      (WFP : wf_prealloc (Global.memory gl1))
      (STEP : Local.free_step lc1 gl1 loc sz lc2 gl2)
      (CUT : Memory.closed_view Vcut (Global.memory gl1)) 
      (EQ: sz = sz')
    :
    hist_auth (Memory.cut Vcut (Global.memory gl1)) ∗ own_loc_vec loc 1 (Z.to_nat sz') (TView.cur 𝓥)
    ==∗ (hist_auth (Memory.cut Vcut (Global.memory gl2))).
  Proof.
    subst. iIntros "[HA [%ALV OLV]]".
    inv STEP; ss. inv FREE. unfold Loc.get_tbid in *; ss.
    clear FULFILL FULFILLS.
    rewrite own_loc_eq /own_loc_def /own_loc_prim.
    rewrite hist_eq /hist_def hist_auth_eq /hist_auth_def.

    destruct (sz' <? 0)%Z eqn: SZ.
    {
      set (c:=_:HistoryRA.histR_aux).
      set (d:=_:HistoryRA.histR_aux) at 2.
      assert (c ≡ d); [|rewrite H //].
      subst c d. intros l. destruct l.
      destruct (Loc.id_eq_dec (tid0, bid0) (Some tid, bid)) eqn: EQ; ss.
      { des. subst. rewrite /Memory.accessible /Block.accessible /= EQ.
        rewrite /Memory.get_size /Block.get_size /= in SIZE.
        destruct (Block.state (Memory.blocks (Global.memory gl1) (Some tid) bid)) eqn: ST; ss; inv SIZE;
        des_ifs; bsimpl; des; nia.
      }
      { des_safe. subst. rewrite /Memory.accessible /Block.accessible /= EQ.
        destruct (Block.state (Memory.blocks (Global.memory gl1) tid0 bid0)) eqn: ST; ss;
        rewrite /Memory.get_cell /= /Memory.get_cell /= EQ /= //.
      }
    }

    eapply Z.ltb_ge in SZ.
    assert (SZ1: ∃ sz: nat, Z.of_nat sz = sz').
    { exists (Z.to_nat sz'). nia. }
    des. subst. replace (Z.to_nat sz) with sz by nia.
    
    set (c:=_:HistoryRA.histR_aux).
    assert (HIST: c ≡
      ((λ l: Loc.t,
          if Loc.id_eq_dec (Loc.tid l, Loc.bid l) (Some tid, bid)
          then 
            (if (0 <=? Loc.ofs l)%Z && (Loc.ofs l <? sz)%Z
            then Some (DfracOwn 1, to_agree (Memory.get_cell l (Memory.cut Vcut (Global.memory gl1)))) else None)
          else
            (if Memory.accessible l (Memory.cut Vcut (Global.memory gl1))
            then Some (DfracOwn 1, to_agree (Memory.get_cell l (Memory.cut Vcut (Global.memory gl1))))
            else None))
          : HistoryRA.histR_aux)
    ).
    { subst c. intros l. destruct l.
      destruct (Loc.id_eq_dec (tid0, bid0) (Some tid, bid)) eqn: EQ; ss; des_safe.
      { rewrite /Memory.accessible /Block.accessible /=.
        rewrite /Memory.get_size /Block.get_size /= in SIZE.
        destruct (Block.state (Memory.blocks (Global.memory gl1) (Some tid) bid)) eqn: ST; inv SIZE; ss;
        rewrite EQ /=; des_ifs; bsimpl; des; nia.
      }
      { rewrite /Memory.accessible /Block.accessible /=.
        rewrite /Memory.get_size /Block.get_size /= in SIZE.
        destruct (Block.state (Memory.blocks (Global.memory gl1) (Some tid) bid)) eqn: ST; inv SIZE; ss;
        rewrite EQ /=; des_ifs; bsimpl; des; nia.
      }
    }
    rewrite HIST. clear HIST c.

    set (m:=Memory.cut Vcut {| Memory.blocks := _; Memory.next_bid := _ |} :Memory.t).
    set (c:=_:HistoryRA.histR_aux) at 2.
    assert (HIST: c ≡
      ((λ l: Loc.t,
          if Loc.id_eq_dec (Loc.tid l, Loc.bid l) (Some tid, bid)
          then None
          else
            (if Memory.accessible l (Memory.cut Vcut (Global.memory gl1))
            then Some (DfracOwn 1, to_agree (Memory.get_cell l m))
            else None))
          : HistoryRA.histR_aux)
    ).
    { subst c m. intros l. destruct l. ss.
      destruct (Loc.id_eq_dec (tid0, bid0) (Some tid, bid)) eqn: EQ; ss; des_safe.
      { rewrite /Memory.accessible /Block.accessible /=.
        rewrite /Memory.get_size /Block.get_size /= in SIZE.
        destruct (Block.state (Memory.blocks (Global.memory gl1) (Some tid) bid)) eqn: ST; inv SIZE; ss;
        rewrite EQ /=; des_ifs; bsimpl; des; nia.
      }
      { rewrite /Memory.accessible /Block.accessible /=.
        rewrite /Memory.get_size /Block.get_size /= in SIZE.
        destruct (Block.state (Memory.blocks (Global.memory gl1) (Some tid) bid)) eqn: ST; inv SIZE; ss;
        rewrite EQ /=; des_ifs; bsimpl; des; nia.
      }
    }
    rewrite HIST. clear HIST c. subst m.
    clear SIZE SZ.

    iStopProof. induction sz.
    { ss. iIntros "[HA _]".
      set (c:=_:HistoryRA.histR_aux).
      set (d:=_:HistoryRA.histR_aux) at 2.
      assert (c ≡ d); [|rewrite H //].
      subst c d. intros l. destruct l.
      destruct (Loc.id_eq_dec (tid0, bid0) (Some tid, bid)) eqn: EQ; ss.
      { des. subst. rewrite /Memory.accessible /Block.accessible /= EQ.
        des_ifs; bsimpl; des. exfalso. eapply Z.leb_le in Heq. eapply Z.ltb_lt in Heq0. nia. }
      { des_safe. subst. rewrite /Memory.accessible /Block.accessible /= EQ.
        destruct (Block.state (Memory.blocks (Global.memory gl1) tid0 bid0)) eqn: ST; ss;
        rewrite /Memory.get_cell /= /Memory.get_cell /= EQ /= //.
      }
    }
    iIntros "[HA OLV]".
    rewrite seq_S. ss. iPoseProof (big_sepL_snoc with "OLV") as "[OLV OL]".
    iDestruct "OL" as (????) "[_ OL]".

    iAssert (
      |==> own hist_name
        ((● ((λ l: Loc.t,
          if Loc.id_eq_dec (Loc.tid l, Loc.bid l) (Some tid, bid)
          then 
            (if (0 <=? Loc.ofs l)%Z && (Loc.ofs l <? sz)%Z
            then Some (DfracOwn 1, to_agree (Memory.get_cell l (Memory.cut Vcut (Global.memory gl1)))) else None)
          else
            (if Memory.accessible l (Memory.cut Vcut (Global.memory gl1))
            then Some (DfracOwn 1, to_agree (Memory.get_cell l (Memory.cut Vcut (Global.memory gl1))))
            else None))
          : HistoryRA.histR_aux)) : histR)
    )%I with "[HA OL]" as ">HA".
    {
      iCombine "HA OL" as "O". iPoseProof (own_update with "O") as "O"; [|iFrame].
      eapply auth_update_dealloc. eapply discrete_fun_local_update. intros l.
      destruct l; ss.
      destruct (Loc.id_eq_dec (tid0, bid0) (Some tid, bid)) eqn: EQ; ss.
      { des; subst.
        destruct (ofs =? sz)%Z eqn: OFS.
        { eapply Z.eqb_eq in OFS. subst.
          assert ((0 <=? sz)%Z = true).
          { eapply Z.leb_le. nia. }
          assert ((sz <? S sz)%Z = true).
          { eapply Z.ltb_lt. nia. }
          assert ((sz <? sz)%Z = false).
          { eapply Z.ltb_ge. nia. }
          rewrite H1 H H0 /=.
          rewrite discrete_fun_lookup_singleton.
          eapply delete_option_local_update.
          eapply pair_exclusive_l, dfrac_full_exclusive.
        }
        rewrite discrete_fun_lookup_singleton_ne; cycle 1.
        { ii. rewrite /HistoryRA.shift in H. eapply Z.eqb_neq in OFS. eapply OFS. inv H. }
        des_ifs; bsimpl; des; try nia.
        { eapply Z.eqb_neq in OFS. eapply Z.ltb_lt in Heq1. eapply Z.ltb_ge in Heq0. nia. }
        { eapply Z.leb_le in Heq0. eapply Z.ltb_lt in Heq1. eapply Z.ltb_ge in Heq. nia. }
      }
      rewrite discrete_fun_lookup_singleton_ne; cycle 1.
      { ii. des; apply o; inv H. }
      refl.
    }
    iApply IHsz; iFrame.
  Qed.
  
  (* Move to Memory.v *)
  Lemma free_get_state mem1 loc mem2
      (WF: Memory.well_alloced mem1)
      (FREE: Memory.free mem1 loc mem2)
    :
    ∀ loc', 
      Loc.get_tbid loc = Loc.get_tbid loc'
        ∧ (∃ sz, Memory.get_state loc' mem1 = Block.heap sz)
        ∧ Memory.get_state loc' mem2 = Block.freed
      ∨ Loc.get_tbid loc ≠ Loc.get_tbid loc'
        ∧ Memory.get_state loc' mem1 = Memory.get_state loc' mem2.
  Proof.
    intros loc'; destruct (decide (Loc.get_tbid loc = Loc.get_tbid loc')); [left | right]; split; ss.
    { inv FREE; rewrite /Memory.get_state /=; des_ifs; destruct loc'; ss; des; clarify; split; ss.
      inv WF. rewrite /Memory.is_freeable /Block.is_freeable in FREEABLE. des_ifs. eauto.
    }
    inv FREE; rewrite /Memory.get_state /=; des_ifs.
    destruct loc'; ss; des; clarify.
  Qed.

  (* Move to Memory.v *)
  Lemma free_get_cell 
        m1 loc m2
        (FREE : Memory.free m1 loc m2) :
    ∀ l, Memory.get_cell l m2 = Memory.get_cell l m1.
  Proof. intros l; apply Cell.ext; intros ts. hexploit Memory.free_o; eauto. Qed.

  (* Move to PFMemIAproof.v *)
  Lemma wf_prealloc_free mem1 mem2 loc
      (WA: Memory.well_alloced mem1)
      (FREE: Memory.free mem1 loc mem2)
      (WF: wf_prealloc mem1)
    :
    wf_prealloc mem2.
  Proof.
    ii. hexploit free_get_state; eauto. instantiate (1:= loc0).
    intros [[EQ [_ FREED]] | [NEQ STATE]].
    {
      rewrite /Memory.get_state in FREED.
      rewrite /Memory.is_prealloced /Block.is_prealloced FREED // in H.
    }
    erewrite free_get_cell; eauto.
    apply WF; move: H; rewrite /Memory.is_prealloced /Block.is_prealloced.
    move : STATE; rewrite /Memory.get_state.
    intros ->; des_ifs.
  Qed.

  Lemma simF_free : ISim.sim_fun open MA MI Ist (Some PFMemHdr.free).
  Proof.
    iStartSim.
    steps_l. destruct _q as [[[tid loc] sz] V]. iDestruct "ASM" as "[-> [-> [TV [OLV F]]]]".
    iDestruct "IST" as "[%gl [%ths [%Vcut [[-> [%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]]] [HA [TA FA]]]]]]".
    hss_r. steps_r.
    rewrite /PFMemI.check_ident.
    steps_r. des_ifs.
    { steps_r. destruct _q as [[e config'] [TEV STEP]].
      (* inv STEP. inv STEP0; [inv LOCAL|]. *)
      dup STEP; inv STEP0. inv STEP1; [inv LOCAL|].
      rewrite TEV in STATE. ss. inv LOCAL.
      { (* free_step *)
        des_ifs. steps_r.
        force_l. steps_l. force_l. steps_l. force_l. iSplit; eauto.
        steps_l.
        iPoseProof (tview_auth_update with "TA TV") as ">[TA TV]"; eauto. ss. inv TEV.
        iPoseProof (hist_freeable_size_free with "[FA F]") as ">(% & F & FA)"; eauto; [inv WF; ss|iFrame|].
        iMod (hist_freeable_auth_free with "[F FA]") as "FA"; eauto; [inv WF; ss|iFrame|].
        iMod (hist_auth_free_vs with "[HA OLV]") as "HA"; eauto; [inv WF; ss|iFrame|].
        { subst. rewrite Nat2Z.id. done. }
        step. iSplit; eauto. clear EVENT n.
        unfold Ist. iExists gl2, (IdentMap.add tid (existT lang st2, lc2) ths), Vcut.
        iFrame.
        iSplit; iPureIntro; ss.
        esplits.
        { intros ??????FIND ?. eapply CUT.
          { erewrite <- Memory.free_o; eauto. inv LOCAL0; eauto. }
          inv LOCAL0; eapply Memory.free_accessible; eauto.
        }
        { inv LOCAL0. eapply Memory.free_closed_view; eauto. }
        { eapply PFConfiguration.estep_future; eauto. }
        { inv WF. inv GL_WF. inv LOCAL0. ss. eapply wf_prealloc_free; eauto. } 
        { destruct gl, gl2. inv LOCAL0. ss.
          inv PFG; ss.
          rewrite /Global.promise_free; ss. esplits.
          { rewrite H in FULFILLS. eapply Promises.Promises.fulfills_bot_inv in FULFILLS. des. eauto. }
          { rewrite H0 in FULFILL. eapply Promises.FreePromises.sfulfill_bot_inv in FULFILL. des. eauto. }
        }
        { ii; destruct (decide (tid0 = tid)); subst.
          { hexploit (PFL tid); eauto. s in H0; rewrite IdentMap.gss in H0; inv H0.
            inv LOCAL0; inv FREE; ss.
            rewrite /Local.promise_free; ss.  
            i. des. esplits; eauto.
            { rewrite H in FULFILLS. eapply Promises.Promises.fulfills_bot in FULFILLS. des. eauto. }
            { rewrite H1 in FULFILL. eapply Promises.FreePromises.sfulfill_bot in FULFILL. des. eauto. } 
          }
          { rewrite IdentMap.gso in H0; clarify; hexploit (PFL tid0); eauto. }
        }
      }
      {
        (* racy_free *)
        des_ifs. iExFalso. ss. inv TEV.
        iPoseProof (hist_freeable_size_racy_free with "[FA F]") as ">(% & F & FA)"; eauto; [inv WF; ss|iFrame|].
        subst.
        inv LOCAL0. des. clear i EVENT.
        inv RACE0. { inv PFG. rewrite H /Promises.Promises.bot // in GET. }
        rename to0 into to. 
        rewrite /own_loc_vec. 
        iPoseProof (tview_both_valid with "TA TV") as "%".
        destruct H as [l [lc [FOUND LCEQ]]].
        rewrite FOUND in Heq; inv Heq.
        rewrite own_loc_eq /own_loc_def /own_loc_prim.
        iDestruct "OLV" as "[_ OLV]".
        iPoseProof (big_sepL_lookup_acc with "OLV") as "[OFS OLV]".
        { instantiate (2:= Z.to_nat ofs). eapply lookup_seq_lt. nia. }
        iDestruct "OFS" as "[%f [%t [%LT [%m [%ALLOC_LOCAL HIST]]]]]".
        iPoseProof (hist_own_hist_cut with "HA HIST") as "[%tcut [<- [%CELL_CUT %ACC]]]". ss.
        destruct ALLOC_LOCAL as [ALLOC_VIEW [t' [(from', msg') [CELL_GET SEEN_LOCAL]]]].
        dup CELL_GET.
        rewrite Cell.singleton_get in CELL_GET; des_ifs.
        rewrite CELL_CUT Cell.cut_spec in CELL_GET0; des_ifs.
        remember ({| Loc.tid := Loc.tid loc; Loc.bid := Loc.bid loc; Loc.ofs := ofs |}) as loc'.
        assert (LOC: loc >> Z.to_nat ofs = loc').
        { unfold ">>". destruct loc; ss. subst. f_equal. nia. }
        destruct (loc >> Z.to_nat ofs).
        assert (LECUT: Time.lt (View.rlx Vcut loc') to).
        { inv SEEN_LOCAL.
          { ett. eapply l. etrans; eauto. }
          { ett. eapply l. inv H; eauto. }
        }
        assert (CUT_GET: Cell.get to (Cell.singleton msg' LT) = Some (from, Message.message val released na)).
        { rewrite CELL_CUT Cell.cut_spec; des_ifs; timetac. }
        rewrite Cell.singleton_get in CUT_GET. ss.
        exfalso.
        eapply (TimeFacts.le_not_lt to (View.rlx (TView.TView.cur (Local.tview lc2)) loc')); eauto; des_ifs.
      }
      (* inaccessible free *)
      inv LOCAL0.
      { des.
        { inv RACE0; ss.
          { inv PFG. rewrite H0 /Promises.FreePromises.bot // in FREEPROMISE. }
          { exfalso. apply INACCESSIBLE. unfold Memory.accessible, Block.accessible. 
            ss. unfold Memory.is_freeable, Block.is_freeable, Memory.get_size, Block.get_size in *.
            des_ifs. rewrite -Z.leb_le in RACE. rewrite -Z.ltb_lt in RACE1.
            rewrite RACE RACE1. ss.
          }
          {
            (* alloc_view, duplicated. *)
            iExFalso. ss. inv TEV.
            iPoseProof (tview_both_valid with "TA TV") as "%". des.
            rewrite Heq in H. inv H.
            iDestruct "OLV" as "[% OLV]". ss. 
          }
        }
        { inv PFG. rewrite H0 /Promises.FreePromises.bot // in RACE. }
      }
      des.
      {
        iExFalso. ss. inv TEV. 
        rewrite hist_freeable_eq /hist_freeable_def. 
        iDestruct "F" as (? ?) "[% F]".
        subst. ss.
      }
      {  
        iExFalso. ss. inv TEV.
        rewrite hist_freeable_eq /hist_freeable_def.
        rewrite hist_freeable_auth_eq /hist_freeable_auth_def.
        iDestruct "F" as (? ?) "[% F]".
        iCombine "FA F" as "A" gives %WF0. eapply auth_both_valid_discrete in WF0. des.
        eapply discrete_fun_included_spec_1 in WF0.
        instantiate (1:= (tid0, bid)) in WF0. ss.
        rewrite discrete_fun_lookup_singleton in WF0.
        subst. des_ifs.
        eapply Some_included_is_Some in WF0. rewrite /is_Some in WF0. des. ss.
      }
      {
        (* alloc_view, duplicated. *)
        iExFalso.
        iPoseProof (tview_both_valid with "TA TV") as "%". des.
        rewrite Heq in H. inv H.
        iDestruct "OLV" as "[% OLV]". ss. inv TEV. ss.
      }
    }
    {(* UB case *)
      iPoseProof (tview_both_valid with "TA TV") as "%F"; des; clarify.
    }
  (*SLOW*)Qed.
End free.
