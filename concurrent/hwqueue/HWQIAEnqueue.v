Require Export CRIS.common.CRIS.
From CRIS.imp_system Require Export imp.ImpPrelude.
From CRIS.hwqueue Require Export HWQHeader.
Require Export CRIS.scheduler.SchHeader.
From CRIS.imp_system Require Export mem.MemHeader.
Require Export CRIS.prophecy.ProphecyHeader CRIS.helping.HelpingHeader.
Require Export CRIS.filter.CallFilter.
From CRIS.imp_system Require Export mem.MemA.
Require Export CRIS.scheduler.SchA CRIS.prophecy.ProphecyA.
From CRIS.hwqueue Require Export HWQRA.
From CRIS.imp_system Require Import mem.MemI mem.MemIAproof mem.MemTactics.
From CRIS.prophecy Require Import ProphecyI ProphecyFacts.
Require Import CRIS.helping.HelpingTactics.
From CRIS.hwqueue Require Import HWQI HWQP.
From CRIS.scheduler Require Import SchI SchTactics.
From CRIS.hwqueue Require Import HWQA.
From stdpp Require Import streams list.

Section HWQPM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !prophGS, !hwqGS}.
  Context (mnh mnp : string).
  Context (sp_mem : specmap).

  Definition Ist : ist_type Σ := λ st_src st_tgt,
    (∃ (X : gset val),
      free_id (λ x, x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type ∗
      [∗ set] x ∈ X, ∃ ptr ofs, ⌜x = Vptr (ptr, ofs)⌝ ∗ ∃ v, (ptr, ofs) ↦{1/2} v)%I.
  Definition IstFull : ist_type Σ := IstHelp_gen Ist mnh ⊤.

  Notation HWQM := (HWQM.t mnh).
  Notation HWQP := (HWQP.t mnp).
  Notation HelpOn := (HelpingOn.t mnh HWQM.jobCode).
  Notation HelpDummy := (HelpingDummy.t mnh).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mnp ∅).

  Lemma big_lemma γe γs (ls : list val) slots (p : list nat) (N : namespace) F
      msks n sz blk γh γc γi γb fl_s fl_t g ps pt st_src st_tgt :
    fl_s !! funid (Helping.help mnh) =
      Some (Some (SB.sandbox_body
        (msk_scp (HelpingOn.scopes mnh) msk_true,
        (SModTr.trans_fnsem ∅
          (None, HelpingOn.help mnh HWQM.jobCode))))) →
    NoDup p →
    (∀ i, i ∈ p → was_committed <$> slots !! i = Some false) →
    (□ hinv N γh (syn_inv_hwq sz γb γi γe γc γs blk : GTerm.t n)) -∗
    (IstHelp_gen Ist mnh F st_src st_tgt) -∗
    own γs (● (of_slot_data <$> slots) : slotUR) -∗
    ([∗ map] i ↦ d ∈ slots, per_slot_own γe γs i d) -∗
    own γe (● (Excl' ls)) -∗
      wsim fl_s fl_t IstFull (↑N, ↑N) g unit unit
        (λ rs rt, winv (↑N, ↑N) ∗
          (IstHelp_gen Ist mnh F rs.1 rt.1) ∗
          own γs (● (of_slot_data <$> map_imap (helped p) slots) : slotUR) ∗
          ([∗ map] i ↦ d ∈ map_imap (helped p) slots, per_slot_own γe γs i d) ∗
          own γe (● (Excl' (ls ++ get_values slots p)))
        )
        ps pt 
        (st_src, SB.sandbox msks (SModTr.trans ∅
          (ITree.iter (λ _,
            'b : bool <- trigger (Choose bool);;
            if b 
            then trigger (Call (Helping.help mnh) ((Some N)↑));;; Ret (inl ()) 
            else Ret (inr ())) ())))
        (st_tgt, Ret ()).
  Proof.
    intros Hf. revert p. iIntros (p).
    iInduction p as [|e p] "IH" forall (st_src st_tgt ps pt slots ls);
      iIntros (HNoDup Ha) "#Hinv Hist Hs● Hbig He●".
    { aUnfoldS. case_match; cStepsS; ss.
      cForceS false. cStep.
      rewrite /= app_nil_r map_imap_helped_nil. iFrame.
    }
    aUnfoldS. case_match; cStepsS; ss. cForceS true. cStepsS.
    destruct orb; ss. destruct msks; cStepsS; ss.
    cInlineS. cStepsS.
    assert (∀ i : nat, i ∈ p → was_committed <$> slots !! i = Some false) as Ha1.
    { intros i Hi. apply Ha. apply elem_of_list_further, Hi. }
    assert (was_committed <$> slots !! e = Some false) as Ha2.
    { apply Ha, elem_of_list_here. }
    assert (∃ ln γn wn, slots !! e = Some (ln, Pend γn, wn)) as Hn.
    { destruct (slots !! e) as [[[ln sn] wn]|]; last by inversion Ha2.
      (destruct sn as [γn|γn|]; last by idtac); by exists ln, γn, wn. }
    apply NoDup_cons in HNoDup. destruct HNoDup as [Hn_not_in_ps HNoDup].
    destruct Hn as [l [γ [w Hn]]].
    assert (slots = <[e:=(l, Pend γ, w)]> (delete e slots)) as Hs.
    { by rewrite insert_delete_insert insert_id //. }
    rewrite [in ([∗ map] _ ↦ _ ∈ slots, _)%I]Hs.
    iDestruct (big_sepM_insert with "Hbig") as "[Hbig_n Hbig]"; first by apply lookup_delete.
    iDestruct "Hbig_n" as "[Hq [Hval_wit_n [Hwritten_n [%N2 [Hpending_tok_n H]]]]]".
    appendRetT. s. iApply (wsim_helping_help with "H Hist").
    iExists (S n). clear_st; iIntros (st_src) "IST !>".
    aUnfoldS; sYieldS; rewrite /HWQM.jobCode; cStepsS.
    iRename "ASM" into "He◯".
    iDestruct (sync_elts with "He● He◯") as %<-.
    iMod (update_elts _ _ _ (ls ++ [l]) with "He● He◯") as "[He● He◯]".
    cForceS; iFrame "He◯". cStep. iFrame.
    clear_st. iIntros (st_src st_tgt) "Done IST". cStepsS.
    iMod (use_pending_tok with "Hs● Hpending_tok_n")
      as "[Hs● Hcommitted_wit_n]"; first by rewrite Hn.
    iDestruct (big_sepM_insert _ (delete e slots) e (l, Help γ, w)
      with "[Done Hval_wit_n Hwritten_n Hcommitted_wit_n Hbig Hq]")
      as "Hbig"; first by apply lookup_delete.
    { iClear "IH". iFrame "Hbig". rewrite /per_slot_own /=. iFrame. }
    rewrite insert_delete_insert /update_slot Hn insert_delete_insert.
    assert (∀ i : nat, i ∈ p → was_committed <$> <[e:=(l, Help γ, w)]> slots !! i = Some false) as HHH.
    { intros i Hi. rewrite lookup_insert_ne; [ by apply Ha1 | by set_solver ]. }
    iSpecialize ("IH" $! _ st_tgt true false _ _ HNoDup HHH with "Hinv IST [$] [$] [$]").
    appendRetS; appendRetT. iApply wsim_bind. iSplitL "IH"; first iApply "IH". s.
    iIntros (????) "[W [Hs● [Hbig [He● ?]]]]". cStep.
    assert (map_imap (helped p) (<[e:=(l, Help γ, w)]> slots)
            = map_imap (helped (e :: p)) slots) as Heq.
    { apply map_eq. intros i. destruct (decide (i = e)) as [->|Hi_not_n].
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert Hn /=.
        rewrite /helped /=. rewrite decide_True; first done. set_solver.
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert_ne; last done.
        destruct (slots !! i) as [[[li si] wi]|]; last done. simpl.
        rewrite /helped /=. destruct si; try done.
        destruct (decide (i ∈ e :: p)).
        + rewrite decide_True; first done. set_solver.
        + rewrite decide_False; first done. set_solver. }
    rewrite Heq. iFrame. rewrite -app_assoc /= get_values_not_in //; iFrame.
  Qed.

  Lemma simF_enqueue :
    ISim.sim_fun open
      ((HWQM ★ HelpOn) ★ MemA ★ ProphA) ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
      IstFull (fid HWQHdr.enqueue).
  Proof.
    cStartFunSim. rewrite /HWQM.enqueue /HWQI.enqueue. cStepS.
    aStepS (N [γq v]) "[%qblk [%qofs [%q [%n [%sz [[-> ->] [#Inv HQ]]]]]]]". cStepsT.
    iDestruct "Inv" as (γb γi γc γs γh blk ->) "#Inv".
    cStepsS. iApply (wsim_helping_run with "IST"); [simpl_map; s; f_equal|..].

    clear st_src; iIntros (st_src req_id) "IST Tkn".
    sYields.
    (* Open the invariant to perform the increment. *)
    iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
    iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[H_sz Hinv]".
    mLoad. iMod ("Close" with "[//] [$] IST") as "> > IST".
    sYields.
    rewrite /MemHdr.faa. cStepsT.
    clear pvs pref rest slots deqs back cont.
    iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
    iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
    iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
    iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont & Hlem).
    destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
    mLoad. mStore.
    assert (back + 1 = S back)%Z as -> by lia.
    iMod (back_incr with "Hb●") as "Hb●".
    iAssert (i2_lower_bound γi match cont with
                              | WithCont _ i2 => i2
                              | NoCont _ => back `min` sz
                              end -∗ |==>
              i2_lower_bound γi match cont with
                                | WithCont _ i2 => i2
                                | NoCont _      => (S back) `min` sz
                                end)%I as "Hup".
    { destruct cont as [i1 i2|bs]; iIntros "Hi●"; first done.
      iMod (i2_lower_bound_update with "Hi●") as "$"; [ lia | done ]. }
    iMod ("Hup" with "Hi●") as "Hi● {Hup}".
    (* We first handle the case where there is no more space in the queue. *)
    destruct (decide (back < sz)%Z) as [Hback_sz|Hback_sz]; last first.
    { iMod ("Close" with "[//] [-IST] IST") as "> > IST".
      { iExists (S back), pvs, pref, rest, cont, slots, deqs.
        assert (S back `min` sz = back `min` sz) as -> by lia.
        iFrame. iPureIntro. repeat split_and; try done.
        destruct cont as [i1 i2|bs]; last done.
        destruct Hcont as ((Ha1 & Ha2) & Ha3 & Ha4).
        by repeat (split; first lia).
      }
      sYields.
      destruct Z.ltb eqn: Hlt.
      { apply Z.ltb_lt in Hlt; lia. }
      sYields.
      iApply wsim_reset. iStopProof. revert st_src. combine_quant st_tgt.
      eapply wsim_coind. iIntros (? ? CIH [st_src st_tgt]) "[? IST]". destruct_quant CIH. s.
      aUnfoldT. sYields. cByCoind CIH. iFrame.
    }
    (* We now have a reserved slot [i], which is still free. *)
    pose (i := back). pose (elts := map (get_value slots deqs) pref ++ rest).
    assert (slots !! back = None) as Hi_free.
    { destruct (Hslots i) as [Ha1 Ha2]. rewrite min_l in Ha1; last by lia.
      assert (¬ is_Some (slots !! back)). { intro Ha. apply Ha2 in Ha. lia. }
      apply eq_None_not_Some. eauto. }
    (* Useful fact: our index was not yet dequeued. *)
    assert (i ∉ deqs) as Hi_not_in_deq.
    { intros Ha. apply Hdeqs in Ha as (Ha & _). rewrite Hi_free in Ha. inversion Ha. }
    (* We then handle the case where there is a contradiction going on. *)
    destruct cont as [i1 i2|bs].
    { (* We access the atomic update and commit the element. *)
      sYieldS.
      prependRetT tt. iApply (wsim_helping_pend_try_run with "Tkn IST").
      clear_st; iIntros (st_src) "IST".
      aUnfoldS. sYieldS. rewrite {3}/HWQM.jobCode. cStepsS. iRename "ASM" into "He◯".
      iDestruct (sync_elts with "He● He◯") as %<-.
      set (l := Vptr (qblk, qofs)).
      iMod (update_elts _ _ _ (elts ++ [l]) with "He● He◯") as "[He● He◯]".
      cForceS; iFrame "He◯". cStep; iFrame.
      clear_st. iIntros (st_src st_tgt) "Done IST".
      (* We allocate the new slot. *)
      iMod (alloc_done_slot γs slots i l Hi_free with "Hs●")
        as "[Hs [Htok_i [#val_wit_i [#commit_wit_i Hwriting_tok_i]]]]".
      (* We also remember that we had contradiciton states. *)
      iDestruct "Hcont" as "#cont_wit".
      (* And we can close the invariant. *)
      iMod ("Close" with "[//] [- IST Hwriting_tok_i] IST") as "> > IST".
      { iExists (S back), pvs, pref, (rest ++ [l]), (WithCont i1 i2).
        iExists (<[i := (l, Done, false)]> slots), deqs.
        rewrite fmap_insert /= array_content_NONEV; try done. iFrame.
        iFrame. iSplitL "He●".
        { rewrite /elts app_assoc map_get_value_not_in_pref; try done.
          intros Hi%Hpref. rewrite Hi_free in Hi. destruct Hi; done. }
        iSplitL "Hbig Htok_i HQ".
        { iApply big_sepM_insert.
          + apply eq_None_not_Some. intros Ha. apply Hslots in Ha. lia.
          + iFrame "Hbig HQ". repeat (iSplit; first done). done. }
        iFrame "cont_wit".
        destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
        iPureIntro. repeat split_and; try done; try by lia.
        - intros k. destruct sz as [|sz]; first by lia.
          split; intros Hk.
          + destruct (decide (k = i)) as [->|k_not_i].
            * rewrite lookup_insert. by eexists.
            * rewrite lookup_insert_ne; last done. apply Hslots. by lia.
          + destruct (decide (k = i)) as [->|k_not_i].
            * destruct sz; by lia.
            * rewrite lookup_insert_ne in Hk; last done.
              apply Hslots in Hk. by lia.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + by rewrite lookup_insert.
          + rewrite lookup_insert_ne; last done. apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|HNeq].
          + split; first by rewrite lookup_insert. split; first done.
            intros ->. apply Hpref in Hk as (_ & _ & ?). done.
          + rewrite lookup_insert_ne; last done. apply Hpref, Hk.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + by rewrite lookup_insert.
          + rewrite /array_get. rewrite lookup_insert_ne; last done.
            apply Hdeqs in Hk as (? & ? & Ha). repeat (split; first done).
            rewrite /array_get in Ha.
            destruct (slots !! k) as [[[dl ds] dw]|]; last done. done.
        - destruct (decide (i1 = i)) as [->|Hi1_not_i].
          + by rewrite lookup_insert.
          + by rewrite lookup_insert_ne.
        - rewrite /array_get lookup_insert_ne; first done. lia.
        - rewrite /array_get lookup_insert_ne; last by lia.
          destruct (slots !! i1) as [[[li1 si1] wi2]|] eqn : Hli1; last by inversion HC4.
          rewrite /array_get Hli1 // in HC7.
        - intros i' v; destruct (decide (i' = i)) as [->|Hi'_not_i].
          + rewrite lookup_insert //=; intros <-%Some_inj; eauto.
          + rewrite lookup_insert_ne //; intros ?; eapply Hlem; eauto. 
      }
      (* Let's clean up the context a bit. *)
      clear Hslots Hstate Hpref Hdeqs Hcont Hi_not_in_deq Hi_free Hpvs_ND Hpvs_sz Hlem.
      clear elts pvs pref rest slots deqs. subst i. rename back into i.
      (* We can now move to the store. *)
      cStepsS. aUnfoldS. cForceS false. sYields.
      rewrite (proj2 (Z.ltb_lt _ _) Hback_sz). cStepsT. sYields.
      (* We open the invariant again for the store. *)
      iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
      iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
      iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
      iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
      iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont & Hlem).
      destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
      (* Using witnesses, we show that our value and state have not changed. *)
      iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
      iDestruct (use_committed_wit with "Hs● commit_wit_i") as %Hval_commit_i.
      iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
      (* We also show that the same contradiction ist still going on. *)
      destruct cont as [i1' i2'|bs]; last first.
      { by iDestruct (contra_not_no_contra with "Hcont cont_wit") as %Absurd. }
      iDestruct (contra_agree with "cont_wit Hcont") as %[-> ->].
      destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
      (* Our slot is mapped. *)
      assert (is_Some (slots !! i)) as Hslots_i.
      { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
      (* Our index is in the array. *)
      assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
      (* An we perform the store. *)
      destruct (array_content_is_Some sz i slots deqs) as [x Hix]; first by lia.
      iPoseProof (big_sepL_insert_acc _ _ i with "H_ar") as "[↦ H_ar]"; eauto.
      replace (0 + 2 + i)%Z with (i + 2)%Z by lia.
      mStore.
      iPoseProof ("H_ar" with "↦") as "H_ar". clear x Hix.
      (* We perform some updates. *)
      iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
      (* It remains to re-establish the invariant. *)
      pose (new_slots := update_slot i set_written slots).
      iMod ("Close" with "[//] [- IST] IST") as "> > IST".
      { iExists back, pvs, pref, rest, (WithCont i1 i2), new_slots, deqs.
        subst new_slots. iFrame. iSplitL "H_ar".
        { rewrite array_content_set_written;
            [ by iFrame | by lia | done | by apply Hstate ]. }
        iSplitL "He●".
        { erewrite map_ext; first by iFrame. rewrite /get_value. intros k.
          destruct (decide (k = i)) as [->|Hk_not_i].
          - rewrite update_slot_lookup. destruct Hslots_i as [d Hslots_i].
            destruct d as [[ld sd] wd]. rewrite Hslots_i in Hnot_written_i.
            inversion Hnot_written_i; subst wd. rewrite Hslots_i /=. done.
          - rewrite update_slot_lookup_ne; last done. done. }
        iSplitL "Hbig".
        { rewrite /update_slot. destruct (slots !! i) as [d|] eqn:HEq; last done.
          iApply big_sepM_insert; first by rewrite lookup_delete.
          assert (slots = <[i:=d]> (delete i slots)) as HEq_slots.
          { rewrite insert_delete //. }
          rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I] HEq_slots.
          iDestruct (big_sepM_insert with "Hbig")
            as "[[H1 [H2 [H3 ?]]] $]"; first by rewrite lookup_delete.
          rewrite /per_slot_own val_of_set_written state_of_set_written.
          iFrame. by rewrite was_written_set_written. }
        iPureIntro.
        destruct Hslots_i as [[[li si] wi] Hslots_i].
        repeat split_and; try done.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + rewrite update_slot_lookup. split; intros ?; last done.
            rewrite Hslots_i. by eexists.
          + rewrite update_slot_lookup_ne; last done. by apply Hslots.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + rewrite update_slot_lookup Hslots_i /=. split; intros ?.
            * exfalso. rewrite Hslots_i in Hval_commit_i.
              destruct si as [γ|γ|]; try by inversion Hval_commit_i.
            * done.
          + rewrite update_slot_lookup_ne; last done. apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup Hslots_i /=. repeat split.
            * rewrite Hslots_i in Hval_commit_i.
              destruct si; try by inversion Hval_commit_i.
            * intros Hi%Hdeqs. destruct Hi as [Ha _].
              rewrite Hnot_written_i in Ha. inversion Ha.
            * by apply Hpref in Hk as (_ & _ & ?).
          + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup Hslots_i /update_slot /=.
            rewrite Hslots_i /= insert_delete_insert /array_get lookup_insert.
            rewrite decide_True; last done. repeat split; try done.
            destruct si; try done. rewrite Hslots_i in Hval_commit_i. done.
          + rewrite /array_get update_slot_lookup_ne; last done.
            apply Hdeqs in Hk. rewrite /array_get in Hk. done.
        - destruct (decide (i1 = i)) as [->|Hi1_not_i].
          + rewrite update_slot_lookup Hslots_i /=.
            rewrite Hslots_i in HC4. by inversion HC4.
          + by rewrite update_slot_lookup_ne.
        - destruct (decide (i1 = i)) as [->|Hi1_not_i].
          + rewrite /array_get update_slot_lookup Hslots_i /=.
            destruct (decide (i ∈ deqs)) as [Ha|Ha]; last done.
            exfalso. apply Hdeqs in Ha as (Ha1 & ? & ?).
            rewrite Hnot_written_i in Ha1. inversion Ha1.
          + by rewrite /array_get update_slot_lookup_ne.
        - destruct (decide (i1 = i)) as [->|Hi1_not_i].
          + rewrite /array_get update_slot_lookup Hslots_i /=.
            rewrite Hslots_i in HC5. inversion HC5; subst wi.
            rewrite /array_get Hslots_i // in HC7.
          + rewrite /array_get update_slot_lookup_ne; last done.
            destruct (slots !! i1) as [[[li1 si1] wi1]|] eqn : Hi1; last by inversion HC4.
            rewrite /array_get Hi1 // in HC7.
        - intros i3 v; destruct (decide (i3 = i)) as [->|Hi3_not_i].
          + rewrite update_slot_lookup Hslots_i /=; rewrite Hslots_i in Hval_wit_i; ss; clarify.
            intros <-%Some_inj; eauto.
          + rewrite update_slot_lookup_ne //; eapply Hlem. }
      sYields. sYieldS. cStep; iFrame. ss.
    }
    (* There is no [Contra1]/[Contra2], first assume the prophecy is trivial. *)
    destruct bs as [|b blocks].
    { (* We access the atomic update and commit the element. *)
      sYieldS. prependRetT tt; iApply (wsim_helping_pend_try_run with "Tkn IST").
      clear_st; iIntros (st_src) "IST". aUnfoldS; rewrite {3}/HWQM.jobCode; sYieldS.
      cStepsS. iRename "ASM" into "He◯".
      iDestruct (sync_elts with "He● He◯") as %<-.
      iMod (update_elts _ _ _ (elts ++ [Vptr (qblk, qofs)]) with "He● He◯") as "[He● He◯]".
      cForceS; iFrame "He◯". cStepsS. cStep. iFrame.
      clear_st; iIntros (st_src st_tgt) "Done IST". cStepsS.
      (* We allocate the new slot. *)
      iMod (alloc_done_slot γs slots i (Vptr (qblk, qofs)) Hi_free with "Hs●")
        as "[Hs [Htok_i [#val_wit_i [#commit_wit_i Hwriting_tok_i]]]]".
      (* And we can close the invariant. *)
      iMod ("Close" with "[//] [- IST Hwriting_tok_i] IST") as ">>IST".
      { iExists (S back), pvs, pref, (rest ++ [Vptr (qblk, qofs)]), (NoCont []).
        iExists (<[i := (Vptr (qblk, qofs), Done, false)]> slots), deqs.
        rewrite array_content_NONEV //. iFrame.
        iFrame. iSplitL "He●".
        { rewrite /elts app_assoc map_get_value_not_in_pref; try done.
          intros Hi%Hpref. rewrite Hi_free in Hi. destruct Hi; done. }
        iSplitL "Hbig Htok_i HQ".
        { iApply big_sepM_insert.
          + apply eq_None_not_Some. intros ?%Hslots. lia.
          + iFrame "Hbig HQ". repeat (iSplit; first done). done. }
        destruct Hcont as (HC1 & HC2 & HC3).
        iPureIntro. repeat split_and; try done; try by lia.
        - intros k. destruct sz as [|sz]; first by lia.
          split; intros Hk.
          + destruct (decide (k = i)) as [->|k_not_i].
            * rewrite lookup_insert. by eexists.
            * rewrite lookup_insert_ne; last done. apply Hslots. by lia.
          + destruct (decide (k = i)) as [->|k_not_i].
            * destruct sz; by lia.
            * rewrite lookup_insert_ne in Hk; last done.
              apply Hslots in Hk. by lia.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + by rewrite lookup_insert.
          + rewrite lookup_insert_ne; last done. apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + by rewrite lookup_insert.
          + rewrite lookup_insert_ne; last done. apply Hpref, Hk.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + by rewrite lookup_insert.
          + rewrite /array_get. rewrite lookup_insert_ne; last done.
            apply Hdeqs in Hk as (? & ? & Ha3). repeat (split; first done).
            rewrite /array_get in Ha3.
            destruct (slots !! k) as [[[dl ds] dw]|]; last done. done.
        - intros b Hb. by inversion Hb.
        - intros i' v; destruct (decide (i' = i)) as [->|Hi'_not_i].
          + rewrite lookup_insert; intros <-%Some_inj; eauto.
          + rewrite lookup_insert_ne //; eapply Hlem.
      }
      (* Let's clean up the context a bit. *)
      clear Hslots Hstate Hpref Hdeqs Hcont Hi_not_in_deq Hi_free Hpvs_ND Hpvs_sz Hlem.
      clear pvs pref rest slots deqs elts. subst i. rename back into i.
      (* We can now move to the store. *)
      aUnfoldS; cForceS false. sYields.
      rewrite (proj2 (Z.ltb_lt _ _) Hback_sz). cStepsT. sYields.
      (* We open the invariant again for the store. *)
      iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
      iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
      iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
      iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
      iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont & Hlem).
      destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
      (* Using witnesses, we show that our value and state have not changed. *)
      iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
      iDestruct (use_committed_wit with "Hs● commit_wit_i") as %Hval_commit_i.
      iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
      (* Our slot is mapped. *)
      assert (is_Some (slots !! i)) as Hslots_i.
      { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
      (* Our index is in the array. *)
      assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
      (* An we perform the store. *)
      destruct (array_content_is_Some sz i slots deqs) as [x Hix]; first by lia.
      iPoseProof (big_sepL_insert_acc _ _ i with "H_ar") as "[↦ H_ar]"; eauto.
      replace (0 + 2 + i)%Z with (i + 2)%Z by lia.
      mStore.
      iPoseProof ("H_ar" with "↦") as "H_ar". clear x Hix.
      (* We perform some updates. *)
      iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
      (* It remains to re-establish the invariant. *)
      pose (new_slots := update_slot i set_written slots).
      iMod ("Close" with "[//] [- IST] [$]") as ">> IST".
      { iExists back, pvs, pref, rest, cont, new_slots, deqs.
        subst new_slots. iFrame. iSplitL "H_ar".
        { rewrite array_content_set_written;
            [ by iFrame | by lia | done | by apply Hstate ]. }
        iSplitL "He●".
        { erewrite map_ext; first by iFrame. rewrite /get_value. intros k.
          destruct (decide (k = i)) as [->|Hk_not_i].
          - rewrite update_slot_lookup. destruct Hslots_i as [d Hslots_i].
            destruct d as [[ld sd] wd]. rewrite Hslots_i in Hnot_written_i.
            inversion Hnot_written_i; subst wd. rewrite Hslots_i /=. done.
          - rewrite update_slot_lookup_ne; last done. done. }
        iSplitL "Hbig".
        { rewrite /update_slot. destruct (slots !! i) as [d|] eqn:HEq; last done.
          iApply big_sepM_insert; first by rewrite lookup_delete.
          assert (slots = <[i:=d]> (delete i slots)) as HEq_slots.
          { rewrite insert_delete_insert. by rewrite insert_id. }
          rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I] HEq_slots.
          iDestruct (big_sepM_insert with "Hbig")
            as "[[H1 [H2 [H3 ?]]] $]"; first by rewrite lookup_delete.
          rewrite /per_slot_own val_of_set_written state_of_set_written.
          iFrame. by rewrite was_written_set_written. }
        iPureIntro.
        destruct Hslots_i as [[[li si] wi] Hslots_i].
        repeat split_and; try done.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + rewrite update_slot_lookup. split; intros ?; last done.
            rewrite Hslots_i. by eexists.
          + rewrite update_slot_lookup_ne; last done. by apply Hslots.
        - intros k. destruct (decide (k = i)) as [->|k_not_i].
          + rewrite update_slot_lookup Hslots_i /=. split; intros ?.
            * exfalso. rewrite Hslots_i in Hval_commit_i.
              destruct si as [γ|γ|]; try by inversion Hval_commit_i.
            * by inversion H.
          + rewrite update_slot_lookup_ne; last done. apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup Hslots_i /=. repeat split.
            * rewrite Hslots_i in Hval_commit_i.
              destruct si; try by inversion Hval_commit_i.
            * by intros Hi%Hpref.
            * by apply Hpref in Hk as (_ & _ & ?).
          + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup Hslots_i /update_slot /=.
            rewrite Hslots_i /= insert_delete_insert /array_get lookup_insert.
            rewrite decide_True; last done. repeat split; try done.
            destruct si; try done. rewrite Hslots_i in Hval_commit_i. done.
          + rewrite /array_get update_slot_lookup_ne; last done.
            apply Hdeqs in Hk. rewrite /array_get in Hk. done.
        - destruct cont as [i1 i2|bs].
          + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6). split; first done.
            destruct (decide (i1 = i)) as [->|Hi1_not_i].
            * rewrite /array_get update_slot_lookup Hslots_i /=.
              repeat split_and; try done.
              ** rewrite Hslots_i in Hval_commit_i. destruct si; try done.
              ** rewrite /array_get Hslots_i // in HC5. case_match; clarify.
            * rewrite /array_get update_slot_lookup_ne; last done.
              rewrite /array_get in HC3. done.
          + destruct Hcont as (HC1 & HC2 & HC3). repeat split_and; try done.
            intros b Hb. apply HC1 in Hb as (Hb1 & Hb2). split.
            * destruct (decide (b.1 = i)) as [Hb1_is_i|Hb1_not_i].
              ** rewrite -Hb1_is_i in Hslots_i. by rewrite Hslots_i in Hb1.
              ** rewrite /update_slot Hslots_i insert_delete_insert.
                by rewrite lookup_insert_ne.
            * intros k Hk. destruct (decide (k = i)) as [Hk_is_i|Hk_not_i].
              ** rewrite /update_slot Hslots_i insert_delete_insert. subst k.
                rewrite lookup_insert /=. rewrite Hslots_i in Hval_commit_i.
                destruct (was_committed (li, si, true)); last done.
                exfalso. apply Hb2 in Hk. rewrite Hslots_i in Hk. inversion Hk.
                destruct si; try done.
              ** rewrite /update_slot Hslots_i insert_delete_insert.
                rewrite lookup_insert_ne; last done. apply Hb2, Hk.
        - intros i3 v; destruct (decide (i3 = i)) as [->|Hi3_not_i].
          + rewrite update_slot_lookup Hslots_i /=; rewrite Hslots_i in Hval_wit_i; ss; clarify.
            intros <-%Some_inj; eauto.
          + rewrite update_slot_lookup_ne //; eapply Hlem.
      }
      sYields. sYieldS. cStep; iFrame. done.
    }
    (* There is no [Contra1]/[Contra2], and the prophecy is non-trivial. *)
    destruct Hcont as (Hblocks & Hrest & Hpvs).
    assert (rest = []) as -> by by apply Hrest.
    rewrite app_nil_r in elts. rewrite app_nil_r.
    destruct b as [b_unused b_pendings].
    (* We compare our index with the unused element of the prophecy. *)
    destruct (decide (b_unused = i)) as [->|b_unused_not_i].
    + (* We are the non-committed element of the prophecy: commit the block. *)
      (* We allocate the new slot. *)
      iMod (alloc_done_slot γs slots i (Vptr (qblk, qofs)) Hi_free with "Hs●")
        as "[Hs● [Htok_i [#val_wit_i [#commit_wit_i Hwriting_tok_i]]]]".
      (* We then commit at our index. *)
      sYieldS.
      prependRetT tt; iApply (wsim_helping_pend_try_run with "Tkn IST").
      clear_st; iIntros (st_src) "IST". aUnfoldS; sYieldS; rewrite {3}/HWQM.jobCode; cStepsS.
      iRename "ASM" into "He◯".
      iDestruct (sync_elts with "He● He◯") as %<-.
      iMod (update_elts _ _ _ (elts ++ [Vptr (qblk, qofs)]) with "He● He◯") as "[He● He◯]".
      cForceS; iFrame "He◯". cStep. iFrame.
      clear_st; iIntros (st_src st_tgt) "#Done IST". cStepsS.
      (* Our prophecy block must be valid. *)
      assert (block_valid slots (i, b_pendings))
        as Hb_valid by apply Hblocks, elem_of_list_here.
      rewrite /block_valid /= in Hb_valid.
      destruct Hb_valid as [Hb_valid1 Hb_valid2].
      (* We also need to commit for all indices in in [p_pendings] *)
      assert (NoDup (i :: b_pendings)) as Hblock_ND.
      { apply NoDup_app in Hpvs_ND as (Ha & _ & _). subst pvs.
        apply NoDup_app in Ha as (_ & _ & Ha). simpl in Ha.
        rewrite app_comm_cons in Ha. by apply NoDup_app in Ha as (Ha & _ & _). }
      apply NoDup_cons in Hblock_ND as (Hi & HNoDup).
      iAssert (per_slot_own γq γs i (Vptr (qblk, qofs), Done, false)) with "[Htok_i HQ]" as "Hi".
      { rewrite /per_slot_own /=. eauto with iFrame. }
      iDestruct (big_sepM_insert (per_slot_own γq γs) slots i (Vptr (qblk, qofs), Done, false)
              with "[Hi Hbig]") as "Hbig"; [ done | by iFrame | .. ].
      iMod ("Close" with "[//]") as "[_ > Close]".
      prependRetT tt. iApply wsim_bind. iSplitL "Hs● Hbig He● IST".
      { iApply (big_lemma with "[$] [$] Hs● Hbig He●");
          [by simpl_map|apply HNoDup|..].
        intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
        + exfalso. apply Hi, Hk.
        + rewrite lookup_insert_ne; last done. apply Hb_valid2, Hk.
      }
      clear_st. iIntros (st_src [] st_tgt []) "[? [IST [Hs● [Hbig He●]]]]".
      iApply wsim_fold; iFrame.
      (* And then we can close the invariant. *)
      iMod ("Close" with "[-IST Hwriting_tok_i] IST") as "IST /=".
      { pose (new_pref := pref ++ i :: b_pendings).
        pose (new_slots := map_imap (helped b_pendings) (<[i:=(Vptr (qblk, qofs), Done, false)]> slots)).
        iExists (S back), pvs, new_pref, [], (NoCont blocks), new_slots, deqs.
        iFrame. iSplitL "H_ar".
        { assert (array_content sz slots deqs = array_content sz new_slots deqs) as ->; last done.
          apply array_content_ext. intros k Hk. rewrite /new_slots /array_get.
          rewrite map_lookup_imap. destruct (decide (k = i)) as [->|Hk_not_i].
          - by rewrite lookup_insert Hb_valid1 /helped /= decide_False.
          - rewrite lookup_insert_ne; last done.
            destruct (slots !! k) as [[[dl ds] dw]|]; last done.
            rewrite /helped /=. destruct ds as [dγ|dγ|].
            + destruct dw; try done; by destruct (decide (k ∈ b_pendings)).
            + by destruct dw.
            + by destruct dw. }
          iSplitL "He●".
          { rewrite app_nil_r /new_pref /elts map_app map_cons.
            rewrite [in get_value new_slots deqs i]/get_value.
            rewrite [in new_slots !! i]/new_slots.
            rewrite map_lookup_imap lookup_insert /= -app_assoc cons_middle.
            assert (NoDup (pref ++ i :: b_pendings)) as HND.
            { apply NoDup_app in Hpvs_ND as (HND & _ & _).
              rewrite cons_middle app_assoc.
              rewrite Hpvs /= in HND. rewrite cons_middle in HND.
              rewrite app_assoc app_assoc in HND.
              by apply NoDup_app in HND as (HND & _ & _). }
            rewrite annoying_lemma_1 //; last first.
            { intros k Hk. by apply Hpref in Hk as (? & ? & _). }
            assert (map (get_value new_slots deqs) b_pendings
                  = get_values (<[i:=(Vptr (qblk, qofs), Done, false)]> slots) b_pendings) as ->.
            - rewrite /new_slots. by eapply annoying_lemma_2.
            - done. }
          iPureIntro. repeat split_and; try done.
          - intros k. rewrite /new_slots map_lookup_imap. split; intros Hk.
            + destruct (decide (k = i)) as [->|Hk_not_i].
              * rewrite lookup_insert /helped /=. by eexists.
              * rewrite lookup_insert_ne; last done.
                assert (is_Some (slots !! k)) as [d ->] by (apply Hslots; lia).
                by apply is_Some_helped.
            + destruct (decide (k = i)) as [->|Hk_not_i]; first by lia.
              rewrite lookup_insert_ne in Hk; last done.
              assert (k < back `min` sz) as ?; last by lia.
              apply Hslots. destruct (slots !! k) as [d|]; first by exists d.
              by inversion Hk.
          - intros k. rewrite /new_slots map_lookup_imap.
            destruct (decide (k = i)) as [->|Hk_not_i];
              first by rewrite lookup_insert /helped /=.
            rewrite lookup_insert_ne; last done. split; intros Hk.
            + destruct (slots !! k) as [d|] eqn:HEq; last done.
              assert (was_committed <$> Some d ≫= helped b_pendings k = was_committed <$> Some d) as HEq1.
              { destruct d as [[dl []] dw]; simpl; simpl in Hk; by rewrite Hk. }
              rewrite HEq1 -HEq in Hk. apply Hstate in Hk. rewrite HEq in Hk.
              assert (was_written <$> Some d ≫= helped b_pendings k = was_written <$> Some d) as HEq2.
              { destruct d as [[dl []] []]; simpl; simpl in Hk; try by inversion Hk.
                rewrite /helped /=. destruct (decide (k ∈ b_pendings)); done. }
              rewrite HEq2. by inversion Hk.
            + destruct (slots !! k) as [d|] eqn:HEq; last done.
              assert (was_written <$> Some d ≫= helped b_pendings k = was_written <$> Some d) as HEq1.
              { by destruct d as [[dl []] dw]; rewrite /helped; destruct (decide (k ∈ b_pendings)). }
              rewrite HEq1 -HEq in Hk. apply Hstate in Hk. done.
          - intros k Hk. subst new_pref new_slots. apply elem_of_app in Hk as [Hk|Hk].
            { apply Hpref in Hk as (Ha1 & ?). split; last done.
              rewrite map_imap_insert /=. destruct (decide (k = i)) as [->|Hk_not_i].
              - by rewrite lookup_insert.
              - rewrite lookup_insert_ne; last done. rewrite map_lookup_imap.
                destruct (slots !! k) as [[[dl ds] dw]|]; last by inversion Ha1.
                rewrite /= /helped. destruct ds as [dγ|dγ|]; try done. }
            apply elem_of_cons in Hk as [Hk|Hk].
            { subst k. split; last done. by rewrite map_imap_insert /= lookup_insert. }
            apply Hb_valid2 in Hk as Hb_valid2_k. split.
            + rewrite map_lookup_imap. destruct (decide (k = i)) as [->|Hk_not_i].
              * by rewrite lookup_insert /=.
              * rewrite lookup_insert_ne; last done.
                destruct (slots !! k) as [[[kl ks] kw]|]; last by inversion Hb_valid2_k.
                rewrite /= /helped. destruct ks; try done. by rewrite /= decide_True.
            + apply Hstate in Hb_valid2_k. apply Hstate in Hb_valid2_k. done.
          - intros k Hk. subst new_slots. rewrite /array_get map_lookup_imap.
            assert (k ≠ i) as Hk_not_i. { intros ->. apply Hi_not_in_deq, Hk. }
            rewrite lookup_insert_ne; last done. dup Hk; apply Hdeqs in Hk as (Ha1 & ? & Ha3).
            destruct (slots !! k) as [[[lk sk] wk]|] eqn:HEq; last by inversion Ha1.
            inversion Ha1; subst wk. rewrite /=. repeat split_and; try by destruct sk.
            destruct sk; try done; simpl.
            + rewrite decide_True; first done.
              rewrite /array_get HEq in Ha3. simpl in Ha3.
              destruct (decide (k ∈ deqs)); first done. by inversion Ha3.
            + rewrite decide_True; first done.
              rewrite /array_get HEq in Ha3. simpl in Ha3.
              destruct (decide (k ∈ deqs)); first done. by inversion Ha3.
          - intros b Hk. subst new_slots. rewrite map_imap_insert /=.
            assert (b ∈ (i, b_pendings) :: blocks) as Ha by set_solver +Hk.
            assert (NoDup (i :: b_pendings ++ flatten_blocks blocks)) as HND.
            { subst pvs. apply NoDup_app in Hpvs_ND as (HND & _ & _).
              apply NoDup_app in HND as (_ & _ & HND). done. }
            apply flatten_blocks_mem1 in Hk as Hk1.
            apply Hblocks in Ha as (Ha1 & Ha2). split.
            + assert (b.1 ≠ i) as Hb1_not_i.
              { intros HEq. apply NoDup_cons in HND as [HND1 HND2]. apply HND1.
                rewrite -HEq. apply elem_of_app. by right. }
              rewrite lookup_insert_ne; last done. by rewrite map_lookup_imap Ha1.
            + intros j Hj. assert (j ≠ i) as Hj_not_i.
              { intros HEq. apply NoDup_cons in HND as [HND1 HND2]. apply HND1.
                rewrite -HEq. apply elem_of_app. right.
                apply (flatten_blocks_mem2 _ _ Hk _ Hj). }
              rewrite lookup_insert_ne; last done. rewrite map_lookup_imap.
              apply Ha2 in Hj as Hcomm.
              destruct (slots !! j) as [[[lj sj] wj]|]; last by inversion Hj.
              rewrite /= /helped. destruct sj; try done. simpl.
              assert (j ∉ b_pendings); last by rewrite decide_False.
              intros Hj_contra. apply NoDup_cons in HND as [_ HND].
              apply NoDup_app in HND. destruct HND as (HND1 & HND2 & HND3).
              apply (HND2 _ Hj_contra). apply (flatten_blocks_mem2 _ _ Hk _ Hj).
          - by rewrite Hpvs /= /new_pref app_comm_cons app_assoc.
          - intros k v Hk; subst new_pref new_slots.
            rewrite map_lookup_imap in Hk.
            destruct (decide (i = k)) as [->|Hk_not_i].
            + rewrite lookup_insert in Hk; ss; clarify; eauto. 
            + rewrite lookup_insert_ne // in Hk.
              destruct (Hlem k v) as [->|[? [? ->]]]; eauto.
              destruct (slots !! k) as [[[? [| |]] ?]|]; ss.
              rewrite /helped /= in Hk; case_decide; clarify.
      }

      clear Hslots Hstate Hpref Hdeqs Hpvs Hrest Hblocks Hi_free Hi_not_in_deq Hlem.
      clear Hpvs_ND Hpvs_sz Hb_valid1 Hb_valid2 HNoDup Hi elts pvs pref slots deqs.
      clear blocks b_pendings. subst i. rename back into i.
      sYields. rewrite (proj2 (Z.ltb_lt _ _) Hback_sz). cStepsT. sYields.
      
      (* We open the invariant again for the store. *)
      iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
      iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
      iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
      iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
      iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont & Hlem).
      destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
      (* Using witnesses, we show that our value and state have not changed. *)
      iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
      iDestruct (use_committed_wit with "Hs● commit_wit_i") as %Hval_commit_i.
      iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
      (* Our slot is mapped. *)
      assert (is_Some (slots !! i)) as Hslots_i.
      { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
      (* Our index is in the array. *)
      assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
      (* An we perform the store. *)
      destruct (array_content_is_Some sz i slots deqs) as [x Hix]; first by lia.
      iPoseProof (big_sepL_insert_acc _ _ i with "H_ar") as "[↦ H_ar]"; eauto.
      replace (0 + 2 + i)%Z with (i + 2)%Z by lia.
      mStore.
      iPoseProof ("H_ar" with "↦") as "H_ar". clear x Hix.
      (* We perform some updates. *)
      iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
      (* It remains to re-establish the invariant. *)
      iMod ("Close" with "[//] [- IST] [$]") as ">> IST".
      { pose (new_slots := update_slot i set_written slots).
        iExists back, pvs, pref, rest, cont, new_slots, deqs.
        subst new_slots. iFrame. iSplitL "H_ar".
        { rewrite array_content_set_written;
            [ by iFrame | by lia | done | by apply Hstate ]. }
        iSplitL "He●".
        { erewrite map_ext; first by iFrame. rewrite /get_value. intros k.
          destruct (decide (k = i)) as [->|Hk_not_i].
          - rewrite update_slot_lookup. destruct Hslots_i as [d Hslots_i].
            destruct d as [[ld sd] wd]. rewrite Hslots_i in Hnot_written_i.
            inversion Hnot_written_i; subst wd. rewrite Hslots_i /=. done.
          - rewrite update_slot_lookup_ne; last done. done. }
        iSplitL "Hbig".
        { rewrite /update_slot. destruct (slots !! i) as [d|] eqn:HEq; last done.
          iApply big_sepM_insert; first by rewrite lookup_delete.
          assert (slots = <[i:=d]> (delete i slots)) as HEq_slots.
          { rewrite insert_delete //. }
          rewrite {1} HEq_slots.
          iDestruct (big_sepM_insert with "Hbig")
            as "[[H1 [H2 [H3 ?]]] $]"; first by rewrite lookup_delete.
          rewrite /per_slot_own val_of_set_written state_of_set_written.
          iFrame. by rewrite was_written_set_written. }
        iPureIntro.
        repeat split_and; try done.
        - intros k. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup. split; intros Hk; last by lia.
            by apply fmap_is_Some.
          + rewrite update_slot_lookup_ne; last done. apply Hslots.
        - intros k. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup. split; intros Hk; exfalso.
            * destruct (slots !! i) as [[[li si] wi]|]; last by inversion Hk.
              inversion_clear Hnot_written_i. destruct si; inversion Hk.
              inversion Hval_commit_i.
            * destruct (slots !! i) as [[[li si] wi]|]; by inversion Hk.
          + rewrite update_slot_lookup_ne; last done. by apply Hstate.
        - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
          + rewrite update_slot_lookup /=. split.
            * destruct (slots !! i) as [[[li si] wi]|]; first done.
              by inversion Hval_wit_i.
            * apply Hpref, Hk.
          + rewrite update_slot_lookup_ne; last done. by apply Hpref.
        - intros k Hk. assert (k ≠ i) as Hk_not_i.
          { intros ->. dup Hk; apply Hdeqs in Hk as (Ha1 & ? & Ha3).
            apply Hstate in Hnot_written_i. rewrite /array_get in Ha3.
            destruct Hslots_i as [[[li si] wi] Hslots_i].
            rewrite Hslots_i decide_False in Ha3; last done.
            rewrite Hslots_i in Ha1. inversion Ha1; subst wi. set_solver. }
          rewrite /array_get update_slot_lookup_ne; last done.
          apply Hdeqs in Hk. rewrite /array_get in Hk. done.
        - destruct cont as [i1 i2|bs].
          + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6).
            split; first done. repeat split_and; try done.
            * destruct (decide (i1 = i)) as [->|Hi1_not_i].
              ** rewrite update_slot_lookup.
                destruct (slots !! i) as [[[li si] wi]|]; first done.
                by inversion Hval_wit_i.
              ** by rewrite update_slot_lookup_ne.
            * destruct (decide (i1 = i)) as [->|Hi1_not_i].
              ** rewrite /array_get update_slot_lookup.
                destruct (slots !! i) as [[[li si] wi]|] eqn:HEq; try done.
              ** by rewrite /array_get update_slot_lookup_ne.
            * destruct (decide (i1 = i)) as [->|Hi1_not_i].
              ** rewrite /array_get update_slot_lookup.
                destruct (slots !! i) as [[[li si] wi]|] eqn:HEq; try done.
                inversion  HC3; subst wi. done.
              ** rewrite /array_get update_slot_lookup_ne; last done.
                destruct (slots !! i1) as [[[li1 si1] wi1]|] eqn:HEq; try done.
                rewrite /array_get HEq // in HC5.
          + destruct Hcont as (HC1 & HC2 & HC3). repeat split_and; try done.
            destruct Hslots_i as [[[li si] wi] Hslots_i].
            intros b Hb. apply HC1 in Hb as (Hb1 & Hb2). split.
            * destruct (decide (b.1 = i)) as [Hb1_is_i|Hb1_not_i].
              ** rewrite -Hb1_is_i in Hslots_i. rewrite Hb1 in Hslots_i.
                by inversion Hslots_i.
              ** by rewrite /update_slot Hslots_i insert_delete_insert lookup_insert_ne.
            * intros k Hk. destruct (decide (k = i)) as [Hk_is_i|Hk_not_i].
              ** rewrite /update_slot Hslots_i insert_delete_insert. subst k.
                rewrite lookup_insert /=. rewrite Hslots_i in Hval_commit_i.
                destruct (was_committed (li, si, true)) eqn:Ha; last done.
                exfalso. apply Hb2 in Hk. rewrite Hslots_i in Hk. inversion Hk.
                destruct si; try done.
              ** rewrite /update_slot Hslots_i insert_delete_insert.
                rewrite lookup_insert_ne; last done. apply Hb2, Hk.
        - intros i2 v; destruct (decide (i2 = i)) as [->|Hi2_not_i].
          + rewrite update_slot_lookup; destruct (slots !! i); ss; clarify.
            destruct s as [[? [| |]] ?]; ss; i; clarify; eauto.
          + rewrite update_slot_lookup_ne //; eapply Hlem.
      }
      sYields. sYieldS. cStep. iFrame. done.
    + (* We are not the first non-done element, we will give away our AU. *)
      iMod (alloc_pend_slot γs slots i (Vptr (qblk, qofs)) req_id Hi_free with "Hs●")
        as "[Hs● [Htok_i [#val_wit_i [Hpend_tok_i [Hname_tok_i Hwriting_tok_i]]]]]".
      (* We close the invariant, storing our AU. *)
      iMod ("Close" with "[//] [- IST Htok_i Hwriting_tok_i Hname_tok_i] [$]") as ">> IST".
      { pose (new_bs := glue_blocks (b_unused, b_pendings) i blocks).
        pose (new_slots := <[i:=(Vptr (qblk, qofs), Pend req_id, false)]> slots).
        iExists (S back), pvs, pref, [], (NoCont new_bs), new_slots, deqs.
        rewrite app_nil_r. iFrame. iSplitL "H_ar".
        { assert (array_content sz slots deqs = array_content sz new_slots deqs) as ->; last done.
          apply array_content_ext. intros k Hk. rewrite /new_slots /array_get.
          destruct (decide (k = i)) as [->|Hk_not_i].
          - by rewrite Hi_free lookup_insert decide_False.
          - rewrite lookup_insert_ne; last done. destruct (slots !! k) as [d|]; last done.
            destruct d as [[dl ds] dw]. rewrite /helped /=.
            destruct ds as [dγ|dγ|]; destruct dw; try done. }
        iSplitL "He●".
        { erewrite map_ext_in; first done. subst new_slots.
          intros k Hk%elem_of_list_In. rewrite /get_value.
          assert (k ≠ i); last by rewrite lookup_insert_ne.
          intros ->. apply Hpref in Hk as (Ha1 & ?).
          rewrite Hi_free in Ha1. inversion Ha1. }
        iSplitL "Hbig Hpend_tok_i Tkn HQ".
        { iApply big_sepM_insert; first done. iFrame "#∗". }
        iPureIntro. subst new_slots. repeat split_and; try done.
        - intros k. destruct sz as [|sz]; first by lia.
          split; intros Hk.
          + destruct (decide (k = i)) as [->|k_not_i].
            * rewrite lookup_insert. by eexists.
            * rewrite lookup_insert_ne; last done. apply Hslots. by lia.
          + destruct (decide (k = i)) as [->|k_not_i].
            * destruct sz; by lia.
            * rewrite lookup_insert_ne in Hk; last done.
              apply Hslots in Hk.  by lia.
        - intros k. destruct (decide (k = i)) as [->|Hk_not_i].
          + by rewrite lookup_insert.
          + rewrite lookup_insert_ne; last done. apply Hstate.
        - intros k Hk. rewrite lookup_insert_ne; first by apply Hpref, Hk.
          intros HEq. subst k. apply Hpref in Hk as [Ha _].
          rewrite Hi_free in Ha. inversion Ha.
        - intros k Hk. rewrite /array_get lookup_insert_ne.
          + apply Hdeqs in Hk. by rewrite /array_get in Hk.
          + intros <-. apply Hdeqs in Hk as [Hk _]. rewrite Hi_free in Hk. done.
        - intros b Hb. subst new_bs. rewrite Hpvs in Hpvs_ND.
          apply NoDup_app in Hpvs_ND as (HND & _ & _).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          by eapply glue_blocks_valid.
        - subst pvs new_bs. f_equal. apply flatten_blocks_glue.
        - intros i2 v; destruct (decide (i2 = i)) as [->|Hi2_not_i].
         + rewrite lookup_insert //=; intros <-%Some_inj; eauto.
         + rewrite lookup_insert_ne //; eapply Hlem.
      }
      clear Hslots Hstate Hpref Hdeqs Hblocks Hrest Hpvs Hi_free Hi_not_in_deq Hlem.
      clear Hpvs_ND Hpvs_sz b_unused b_unused_not_i elts blocks pvs pref slots.
      clear deqs b_pendings. subst i. rename back into i.
      sYields. rewrite (proj2 (Z.ltb_lt _ _) Hback_sz). sYields.
      (* We open the invariant again for the store. *)
      iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
      iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
      iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
      iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
      iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont & Hlem).
      destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
      (* Using witnesses, we show that our value and state have not changed. *)
      iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
      iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
      (* Our slot is mapped. *)
      assert (is_Some (slots !! i)) as Hslots_i.
      { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
      (* Our index is in the array. *)
      assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
      (* An we perform the store. *)
      destruct (array_content_is_Some sz i slots deqs) as [x Hix]; first by lia.
      iPoseProof (big_sepL_insert_acc _ _ i with "H_ar") as "[↦ H_ar]"; eauto.
      replace (0 + 2 + i)%Z with (i + 2)%Z by lia.
      mStore.
      iPoseProof ("H_ar" with "↦") as "H_ar". clear x Hix.
      (* We now look at the state of our cell. *)
      destruct Hslots_i as [[[l' s] w] Hi].
      rewrite Hi in Hval_wit_i. simpl in Hval_wit_i.
      inversion Hval_wit_i; subst l'.
      destruct s as [γs_i'|γs_i'|].
      - (* We are still in the pending state: contradiction. *)
        (* We need to run our atomic update ourselves, we recover it. *)
        rewrite -[in X in ([∗ map] _ ↦ _ ∈ X, _)%I](insert_id _ _ _ Hi).
        rewrite -insert_delete_insert.
        iDestruct (big_sepM_insert with "Hbig") as "[Hbig_i Hbig]"; first by apply lookup_delete.
        iDestruct "Hbig_i" as "[Hq [_ [_ [%N2 [Hcommit_tok_i HAU]]]]]".
        sYieldS.
        (* We use the name token to show that γs_i and γs_i' are equal. *)
        iDestruct (use_name_tok with "Hs● Hname_tok_i") as %Hname_tok_i.
        assert (γs_i' = req_id) as Hγs_i; last subst γs_i'.
        { rewrite Hi /= in Hname_tok_i. by inversion Hname_tok_i. }
        prependRetT tt; iApply (wsim_helping_pend_try_run with "HAU IST").
        clear_st. iIntros (st_src) "IST".
        (* We run our atomic update ourself. *)
        aUnfoldS; sYieldS; rewrite {3}/HWQM.jobCode; cStepsS. iRename "ASM" into "He◯".
        pose (elts := map (get_value slots deqs) pref ++ rest).
        iDestruct (sync_elts with "He● He◯") as %<-.
        iMod (update_elts _ _ _ (elts ++ [Vptr (qblk, qofs)]) with "He● He◯") as "[He● He◯]".
        iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
        iMod (use_pending_tok with "Hs● Hcommit_tok_i") as "[Hs● #commit_wit_i]".
        { by rewrite update_slot_lookup Hi /=. }
        iMod (helped_to_done with "Hs● Hname_tok_i") as "Hs●".
        { by rewrite update_slot_lookup update_slot_lookup Hi. }
        cForceS; iFrame "He◯". cStep. iFrame. clear_st. iIntros (??) "Done IST".
        (* We now act according ot the contradiction status. *)
        destruct cont as [i1 i2|bs].
        * (* A contradiction has arised from somewhere else, we keep it. *)
          iMod ("Close" with "[//] [- IST] IST") as ">>IST".
          { iExists back, pvs, pref, (rest ++ [Vptr (qblk, qofs)]), (WithCont i1 i2).
            iExists (update_slot i set_written_and_done slots), deqs.
            subst elts. rewrite app_assoc. iFrame. iSplitL "H_ar".
            { rewrite array_content_set_written_and_done;
              [ by iFrame | by lia | by rewrite Hi | by apply Hstate ]. }
            iSplitL "He●".
            { erewrite map_ext_in; first done. intros k Hk%elem_of_list_In.
              rewrite /get_value /update_slot Hi insert_delete_insert.
              destruct (decide (k = i)) as [->|Hk_not_i].
              - by rewrite lookup_insert Hi.
              - by rewrite lookup_insert_ne. }
            iSplitL "Hs●".
            { repeat rewrite update_slot_update_slot. by rewrite /update_slot Hi. }
            iSplitL.
            { rewrite /update_slot Hi.
              iApply big_sepM_insert; first by rewrite lookup_delete.
              iFrame "Hbig". rewrite /per_slot_own /=. iFrame.
              iSplit; first done. iSplit; done. }
            iPureIntro.
            destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
            repeat split_and; try lia; try done.
            - intros k. destruct (decide (i = k)) as [->|Hk_not_i].
              + rewrite update_slot_lookup Hi. split; [ by eexists | lia ].
              + rewrite update_slot_lookup_ne; last done. apply Hslots.
            - intros k. split; intros Hk.
              + assert (k ≠ i) as Hk_not_i.
                { intros ->. by rewrite update_slot_lookup Hi in Hk. }
                rewrite update_slot_lookup_ne; last done.
                rewrite update_slot_lookup_ne in Hk; last done.
                by apply Hstate.
              + assert (k ≠ i) as Hk_not_i.
                { intros ->. by rewrite update_slot_lookup Hi in Hk. }
                rewrite update_slot_lookup_ne in Hk; last done. by apply Hstate.
            - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
              + rewrite update_slot_lookup Hi /=. split; [ done | by apply Hpref, Hk ].
              + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
            - intros k Hk. assert (k ≠ i) as Hk_not_i.
              { intros ->. apply Hdeqs in Hk as (Ha1 & ? & Ha3).
                apply Hstate in Hnot_written_i. rewrite /array_get in Ha3.
                rewrite Hi decide_False in Ha3; last done.
                rewrite Hi in Ha1. inversion Ha1; subst w. set_solver. }
              rewrite /array_get update_slot_lookup_ne; last done.
              apply Hdeqs in Hk. rewrite /array_get in Hk. done.
            - destruct (decide (i1 = i)) as [->|Hi1_not_i].
              + by rewrite update_slot_lookup Hi.
              + by rewrite update_slot_lookup_ne.
            - destruct (decide (i1 = i)) as [->|Hi1_not_i].
              + by rewrite update_slot_lookup Hi /=.
              + rewrite update_slot_lookup_ne; last done.
                destruct (slots !! i1) as [[[li1 si1] wi1]|]; last by inversion HC4.
                inversion HC5; subst wi1. done.
            - destruct (decide (i1 = i)) as [->|Hi1_not_i].
              + by rewrite /array_get update_slot_lookup Hi /= decide_False.
              + rewrite /array_get update_slot_lookup_ne; last done.
                destruct (slots !! i1) as [[[li1 si1] wi1]|] eqn : Hli1 ; last by inversion HC4.
                rewrite /array_get Hli1 // in HC7.
            - intros i3 v; destruct (decide (i3 = i)) as [->|Hi2_not_i].
              + rewrite update_slot_lookup; destruct (slots !! i); ss; clarify.
                rewrite /set_written_and_done /=; intros; clarify; eauto.
              + rewrite update_slot_lookup_ne //; eapply Hlem. 
          }
          cStepsS. aUnfoldS; cForceS false; cStepsS. sYields. sYieldS. cStep; iFrame. done.
        * (* No contradiction yet, make it ours if the prophecy is non-trivial. *)
          iAssert (match bs with
                 | [] => i2_lower_bound γi (back `min` sz)
                 | _  => no_contra γc ∗ i2_lower_bound γi (back `min` sz)
                 end -∗ |==>
                   match bs with
                   | []           => True
                   | (i2, _) :: _ => contra γc i i2
                   end ∗
                   match bs with
                   | []           => i2_lower_bound γi (back `min` sz)
                   | (i2, _) :: _ => i2_lower_bound γi i2
                   end)%I as "Hup".
          { destruct bs as [|[i2 ps] bs]; first (iIntros "Hi●"; by iFrame).
            iIntros "[Hcont Hi●]". iMod (to_contra i i2 with "Hcont") as "$".
            iMod (i2_lower_bound_update _ _ i2 with "Hi●") as "$"; last done.
            assert (block_valid slots (i2, ps)) as [Hvalid _].
            { destruct Hcont as (Hblocks & _ & _). apply Hblocks, elem_of_list_here. }
            assert (¬ (i2 < back `min` sz)) as ?%not_lt; last by lia.
            eapply iffRLn.
            - apply Hslots.
            - intros Ha. rewrite Hvalid in Ha. by inversion Ha. }
          iAssert (match bs with
                  | [] => i2_lower_bound γi (back `min` sz)
                  | _  => no_contra γc ∗ i2_lower_bound γi (back `min` sz)
                  end ∗
                  match bs with
                  | [] => no_contra γc
                  | _  => True
                  end)%I with "[Hcont Hi●]" as "[HNC_triv HNC_non_triv]".
          { destruct bs; by iFrame. }
          iMod ("Hup" with "HNC_triv") as "[#HC_triv Hi●]".
          (* We can now close the invariant. *)
          iMod ("Close" with "[//] [- IST] IST") as ">> IST".
          { pose (new_slots := update_slot i set_written_and_done slots).
            pose (cont := match bs with [] => NoCont [] | (i2, _) :: _ => WithCont i i2 end).
            pose (l := Vptr (qblk, qofs)).
            iExists back, pvs, pref, (rest ++ [l]), cont, new_slots, deqs.
            subst new_slots elts cont. rewrite app_assoc. iFrame. iSplitL "H_ar".
            { rewrite array_content_set_written_and_done;
              [ by iFrame | by lia | by rewrite Hi | by apply Hstate ]. }
            iSplitL "Hi●".
            { destruct bs as [|[b_u b_ps] bs]; by iFrame. }
            iSplitL "He●".
            { erewrite map_ext_in; first done. intros k Hk%elem_of_list_In.
              rewrite /get_value /update_slot Hi insert_delete_insert //.
              destruct (decide (k = i)) as [->|Hk_not_i].
              - simpl. by rewrite lookup_insert Hi.
              - by rewrite lookup_insert_ne. }
            iSplitL "Hs●".
            { repeat rewrite update_slot_update_slot. by rewrite /update_slot Hi. }
            iSplitR "HNC_non_triv".
            { rewrite /update_slot Hi.
              iApply big_sepM_insert; first by rewrite lookup_delete.
              iFrame "Hbig". rewrite /per_slot_own /=. iFrame.
              iSplit; first done. iSplit; done. }
            iSplitL "HNC_non_triv"; first by destruct bs as [|[i2 ps] bs].
            iPureIntro. repeat split_and.
            - intros k. destruct (decide (i = k)) as [->|Hk_not_i].
              + rewrite update_slot_lookup Hi. split; [ by eexists | lia ].
              + rewrite update_slot_lookup_ne; last done. apply Hslots.
            - intros k. split; intros Hk.
              + assert (k ≠ i) as Hk_not_i.
                { intros ->. by rewrite update_slot_lookup Hi in Hk. }
                rewrite update_slot_lookup_ne; last done.
                rewrite update_slot_lookup_ne in Hk; last done.
                by apply Hstate.
              + assert (k ≠ i) as Hk_not_i.
                { intros ->. by rewrite update_slot_lookup Hi in Hk. }
                rewrite update_slot_lookup_ne in Hk; last done. by apply Hstate.
            - intros k Hk. apply Hpref in Hk as (Ha1 & ? & _). repeat split; try done.
              + destruct (decide (k = i)) as [->|Hk_not_i].
                * by rewrite update_slot_lookup Hi.
                * by rewrite update_slot_lookup_ne.
              + destruct bs as [|[b_u b_ps] bs]; first done.
                intros ->. rewrite Hi in Ha1. by inversion Ha1.
            - intros k Hk. assert (k ≠ i) as Hk_not_i.
              { intros ->. apply Hdeqs in Hk as (Ha1 & ? & Ha3).
                apply Hstate in Hnot_written_i. rewrite /array_get in Ha3.
                rewrite Hi decide_False in Ha3; last done.
                rewrite Hi in Ha1. inversion Ha1; subst w. inversion Ha3. }
              rewrite /array_get update_slot_lookup_ne; last done.
              apply Hdeqs in Hk. rewrite /array_get in Hk. done.
            - done.
            - done.
            - destruct Hcont as (HC1 & HC2 & HC3).
              destruct bs as [|[i2 ps] bs].
              + repeat split_and; try done. intros. by set_solver.
              + repeat split_and; try lia.
                * assert (i < back `min` sz)
                    as Hi_lt by (apply Hslots; by eexists).
                  assert (block_valid slots (i2, ps))
                    as Hvalid by apply HC1, elem_of_list_here.
                  assert (slots !! i2 = None)
                    as Hi2_None by by destruct Hvalid as (? & _).
                  assert (¬ i2 < back `min` sz) as Hi2_ge; last by lia.
                  intros Ha%Hslots. rewrite Hi2_None in Ha. by inversion Ha.
                * apply Hpvs_sz. subst pvs. apply elem_of_app. right. simpl.
                  by apply elem_of_list_here.
                * by rewrite update_slot_lookup Hi /=.
                * by rewrite update_slot_lookup Hi /=.
                * by apply Hstate.
                * rewrite /array_get update_slot_lookup Hi /=.
                  rewrite decide_False; first done. apply Hstate. done.
                * rewrite HC3 /=. exists (ps ++ flatten_blocks bs).
                  by rewrite cons_middle app_assoc.
            - intros i3 v; destruct (decide (i3 = i)) as [->|Hi2_not_i].
              + rewrite update_slot_lookup; destruct (slots !! i); ss; clarify.
                rewrite /set_written_and_done /=; intros; clarify; eauto.
              + rewrite update_slot_lookup_ne //; eapply Hlem.  
          }
          cStepsS. aUnfoldS; cForceS false; cStepsS. sYields; sYieldS; cStep.
          iFrame; done.
      - (* We have moved to the helped state. *)
        pose (l := Vptr (qblk, qofs)).
        assert (slots = <[i := (l, Help γs_i', w)]> (delete i slots))
          as Hslots_i by by rewrite insert_delete_insert insert_id.
        rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I]Hslots_i.
        (* We recover our postcondition. *)
        iDestruct (big_sepM_insert with "Hbig")
          as "[Hbig_i Hbig]"; first by apply lookup_delete.
        iDestruct "Hbig_i" as "[Hq [_ [_ [Hcommit_wit_i Hpost]]]]".
        sYieldS. cStepsS.
        (* We use the name token to show that γs_i and γs_i' are equal. *)
        iDestruct (use_name_tok with "Hs● Hname_tok_i") as %Hname_tok_i.
        assert (γs_i' = req_id) as Hγs_i; last subst γs_i'.
        { rewrite Hi /= in Hname_tok_i. by inversion Hname_tok_i. }
        iApply (wsim_HelpDone_try_run with "Hpost IST"). iIntros "IST".
        (* We need to move from helped to done. *)
        iMod (helped_to_done with "Hs● Hname_tok_i") as "Hs●". { by rewrite Hi. }
        (* We perform some updates. *)
        iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
        iMod ("Close" with "[//] [- IST] IST") as ">>IST".
        { pose (new_slots := update_slot i set_written_and_done slots).
          iExists back, pvs, pref, rest, cont, new_slots, deqs.
          subst new_slots. iFrame. iSplitL "H_ar".
          { rewrite array_content_set_written_and_done;
              [ by iFrame | by lia | by rewrite Hi | by apply Hstate ]. }
          iSplitL "He●".
          { erewrite map_ext_in; first done. intros k Hk%elem_of_list_In.
            rewrite /get_value /update_slot Hi insert_delete_insert.
            destruct (decide (k = i)) as [->|Hk_not_i].
            - by rewrite lookup_insert Hi.
            - by rewrite lookup_insert_ne. }
          iSplitL "Hs●".
          { repeat rewrite update_slot_update_slot. by rewrite /update_slot Hi. }
          iSplitL.
          { rewrite /update_slot Hi.
            iApply big_sepM_insert; first by rewrite lookup_delete.
            iFrame "Hbig". rewrite /per_slot_own /=. iFrame. iSplit; done. }
          iPureIntro. repeat split_and; try done.
          - intros k. destruct (decide (i = k)) as [->|Hk_not_i].
            + rewrite update_slot_lookup Hi. split; [ by eexists | lia ].
            + rewrite update_slot_lookup_ne; last done. apply Hslots.
          - intros k. split; intros Hk.
            + assert (k ≠ i) as Hk_not_i.
              { intros ->. by rewrite update_slot_lookup Hi in Hk. }
              rewrite update_slot_lookup_ne; last done.
              rewrite update_slot_lookup_ne in Hk; last done.
              by apply Hstate.
            + assert (k ≠ i) as Hk_not_i.
              { intros ->. by rewrite update_slot_lookup Hi in Hk. }
              rewrite update_slot_lookup_ne in Hk; last done. by apply Hstate.
          - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
            + rewrite update_slot_lookup Hi. split; first done. apply Hpref, Hk.
            + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
          - intros k Hk. assert (k ≠ i) as Hk_not_i.
            { intros ->. apply Hdeqs in Hk as (Ha1 & Ha2 & Ha3).
              apply Hstate in Hnot_written_i. rewrite /array_get in Ha3.
              rewrite Hi decide_False in Ha3; last done.
              rewrite Hi in Ha1. inversion Ha1; subst w. inversion Ha3. }
            rewrite /array_get update_slot_lookup_ne; last done.
            apply Hdeqs in Hk. rewrite /array_get in Hk. done.
          - destruct cont as [i1 i2|bs].
            + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6).
              split; first done. repeat split_and; try done.
              * destruct (decide (i1 = i)) as [->|Hi1_not_i].
                ** by rewrite update_slot_lookup Hi.
                ** by rewrite update_slot_lookup_ne.
              * destruct (decide (i1 = i)) as [->|Hi1_not_i].
                ** by rewrite /array_get update_slot_lookup Hi /=.
                ** rewrite /array_get update_slot_lookup_ne; last done.
                  rewrite /array_get in HC3. done.
              * destruct (decide (i1 = i)) as [->|Hi1_not_i].
                ** by rewrite /array_get update_slot_lookup Hi decide_False.
                ** rewrite /array_get update_slot_lookup_ne; last done.
                  rewrite /array_get in HC3. done.
            + destruct Hcont as (HC1 & HC2 & HC3). repeat split_and; try done.
              intros b Hb. apply HC1 in Hb as (Ha1 & Ha2). split.
              ** assert (b.1 ≠ i) as Hb1_not_i.
                { intros Ha. rewrite Ha in Ha1. by rewrite Hi in Ha1. }
                by rewrite update_slot_lookup_ne.
              ** intros k Hk. assert (k ≠ i) as Hb1_not_i.
                { intros ?. subst k. apply Ha2 in Hk. rewrite Hi in Hk.
                  by inversion Hk. }
                rewrite update_slot_lookup_ne; last done. by apply Ha2.
          - intros i3 v; destruct (decide (i3 = i)) as [->|Hi2_not_i].
            + rewrite update_slot_lookup; destruct (slots !! i); ss; clarify.
              rewrite /set_written_and_done /=; intros; clarify; eauto.
            + rewrite update_slot_lookup_ne //; eapply Hlem. 
        }
        cStepsS. aUnfoldS; cForceS false; cStepsS. sYields; sYieldS; cStep; iFrame; done.
      - (* We are in the done state: contradiction. *)
        iDestruct (big_sepM_lookup _ _ i with "Hbig")
          as "[_ [_ [_ H]]]"; first done; simpl.
        iDestruct "H" as "[_ Htok_i']".
        by iDestruct (slot_token_exclusive with "Htok_i Htok_i'") as "H".
  Qed.
End HWQPM.
