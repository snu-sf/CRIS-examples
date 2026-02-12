Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import PFMemIAproof.

Section read.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !histGS, !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  Lemma simF_read : ISim.sim_fun open MA MI PFMemIA.Ist (Some PFMemHdr.read).
  Proof.
    iStartSim.
    step_l. destruct _q as [? ? [? | ?]].
    { (* non-atomic read *)
      steps_l. rename _q into varg.
      destruct f as [[[[[[tid loc] ord] val] q] 𝓥] [-> ->]]. unfold_pre_post.
      iDestruct "ASM" as "[-> [-> [PT TV]]]". hss_r. steps_r.
      iDestruct "IST" as "[%gl [%ths [%Vcut [[-> [%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]]] [HA [TA FA]]]]]]".
      steps_r. hss. steps_r.
      rewrite /PFMemI.check_ident.
      des_ifs; last (iPoseProof (tview_both_valid with "TA TV") as "%F"; des; ss; clarify).
      steps_r. destruct _q as [[[e val'] config'] [EVREAD STEP]].
      destruct e; inv EVREAD; inv STEP; clear EVENT; rename STEP0 into STEP; s in STEP; cycle 1.
      { (* RACY READ *)
        inv STEP; inv LOCAL. inv LOCAL0. inv RACE.
        { inv PFG; rewrite H3 in GET; ss. }
        iPoseProof (tview_both_valid with "TA TV") as "%IN".
        destruct IN as [l [lc [FOUND LCEQ]]].
        s; rewrite FOUND in Heq; inv Heq.
        rewrite own_loc_na_eq /own_loc_na_def /view_at.
        iDestruct "PT" as "[%f [%t [%LT [%V' [%na' [[%ALLOC_LOCAL HIST] %LC]]]]]]".
        iPoseProof (hist_own_hist_cut with "HA HIST") as "[%tcut [<- [%CELL_CUT %ACC]]]".
        destruct ALLOC_LOCAL as [ALLOC_VIEW [t' [(from', msg') [CELL_GET SEEN_LOCAL]]]].
        assert (CELL_GET' := CELL_GET); ss.
        rewrite Cell.singleton_get in CELL_GET; des_ifs.
        rewrite CELL_CUT Cell.cut_spec in CELL_GET'; des_ifs.
        assert (LECUT: Time.lt (View.rlx Vcut loc) to0).
        { inv SEEN_LOCAL.
          { ett. eapply l. etrans; eauto. }
          { ett. eapply l. inv H3; eauto. }
        }
        assert (CUT_GET: Cell.get to0 (Cell.singleton (Message.message val V' na') LT) = Some (from, Message.message val0 released na)).
        { rewrite CELL_CUT Cell.cut_spec; des_ifs; timetac. }
        rewrite Cell.singleton_get in CUT_GET.
        exfalso.
        eapply (TimeFacts.le_not_lt to0 (View.rlx (TView.TView.cur (Local.tview lc2)) loc)); eauto; des_ifs.
      }
      { (* INACCESSIBLIE READ *)
        ss. inv STEP; inv LOCAL.
        iPoseProof (tview_both_valid with "TA TV") as "[% [% [%FIND <-]]]".
        rewrite own_loc_na_eq /own_loc_na_def /view_at.
        iDestruct "PT" as "[%f [%t [%LT [%V' [%na' [[%ALLOC_LOCAL HIST] %LC]]]]]]".
        iPoseProof (hist_own_hist_cut with "HA HIST") as "[%tcut [<- [%CELL_CUT %ACC]]]".
        destruct ALLOC_LOCAL as [ALLOC_VIEW [t' [(from', msg') [CELL_GET SEEN_LOCAL]]]].
        exfalso; inv RACE; try done.
        hexploit (PFL tid); eauto; clear PFL; intros PFL.
        inv PFL; inv PFG.
        des; rewrite H6 H7 in FREEPROMISE.
        rewrite Promises.FreePromises.minus_bot in FREEPROMISE. inv FREEPROMISE.
      }
      (* VALID READ *)
      inv STEP; inv LOCAL. des_ifs. clear n.
      steps_r.
      iPoseProof (tview_both_valid with "TA TV") as "%F"; des; subst.
      rewrite F in Heq; inv Heq.

      rewrite own_loc_na_eq /own_loc_na_def /view_at.
      iDestruct "PT" as "[%f [%t [%LT [%V' [%na' [[%ALLOC_LOCAL HIST] %LC]]]]]]".
      destruct ALLOC_LOCAL as [ALLOC_VIEW [t' [(from', msg') [CELL_GET SEEN_LOCAL]]]].
      iPoseProof (hist_own_hist_cut with "HA HIST") as "[%tcut [<- [%CELL_CUT %ACC]]]".

      assert (CELL_GET' := CELL_GET).
      rewrite Cell.singleton_get in CELL_GET; des_ifs.
      rewrite CELL_CUT Cell.cut_spec in CELL_GET'; des_ifs.

      assert (TEQ: t = ts).
      { inv LOCAL0. 
        assert (LECUT: Time.le (View.rlx Vcut loc) ts).
        { inv READABLE. inv SEEN_LOCAL.
          { etrans. eapply l. rewrite Time.le_lteq; left; tet; eauto. }
          { etrans. eapply l. inv H3. eauto. }
        }

        assert (CUT_GET: Cell.get ts (Cell.singleton (Message.message val V' na') LT) = Some (from, Message.message val'0 released na)).
        { rewrite CELL_CUT Cell.cut_spec; des_ifs; timetac. }
        rewrite Cell.singleton_get in CUT_GET; des_ifs.
      }
      subst.

      iMod ((tview_auth_update ths (IdentMap.add tid (existT lang st2, lc2) ths)) with "TA TV") as "[TA TV]"; eauto.

      inv LOCAL0.
      assert (EQ: val'0 = val ∧ V' = released ∧ na' = na ∧ from' = from).
      { rewrite Memory.get_memory_cell in CELL_GET'; des_ifs. }
      destruct EQ as [H3 [H5 [H6 H7]]]; subst.
      
      remember ({[_ := _]}) as st_tgt.
      iAssert (Ist st_src st_tgt)%I with "[HA FA TA]" as "IST".
      { iFrame. iPureIntro; esplits; eauto.
        { hexploit (@PFConfiguration.step_future ThreadEvent.get_machine_event); eauto.
          { econs; eauto. econs; eauto.
            { econs 2.
              { instantiate (2:=(ThreadEvent.read loc ts val' released ord)); eauto. }
              eauto.
            }
            econs. }
          i; des; eauto.
        }
        { i. destruct (decide (tid0 = tid)).
          { subst. rewrite IdentMap.gss in H3; inv H3.
            hexploit PFL; eauto. }
          { rewrite IdentMap.gso in H3; eauto. }
        }
      }

      force_l (val'↑). steps_l. force_l (val'↑). steps_l. force_l.
      iSplitR "IST".
      { iFrame. iSplit; eauto. iExists val'.
        iSplit; eauto.
        iSplit.
        { iSplit; eauto. 
          (* iPureIntro; rewrite /alloc_local. *)
          { ss. iPureIntro. do 2 eapply AllocView.join_l; eauto. }
          { iPureIntro. eexists ts, (from, Message.message val released na).
            rewrite Cell.singleton_get; des_ifs.
            split; ss.
            unfold seen_local in *.
            etrans; eauto. etrans; eapply View.join_l.  
          }
        }
        { iPureIntro; etrans; eauto. etrans; eapply View.join_l. }
      }
      step. iSplit; eauto.
    }
    { destruct f as [[[[[[[[[[[tid loc] ord] ζ] ζ'] t] γ] q] mode] 𝓥] Vb] [-> ->]].
      steps_l. rename _q into varg.
      iDestruct "ASM" as "[-> [[-> %ORDRLX] [SEEN [PT TV]]]]". hss_r.
      iDestruct "IST" as "[%gl [%ths [%Vcut [[-> [%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]]] [HA [TA FA]]]]]]".
      steps_r. hss. steps_r.
      rewrite /PFMemI.check_ident.
      des_ifs; last (iPoseProof (tview_both_valid with "TA TV") as "%F"; des; ss; clarify).
      steps_r. destruct _q as [[[e v] config'] [EVREAD STEP]].
      destruct e; inv EVREAD; inv STEP; clear EVENT; rename STEP0 into STEP; s in STEP; cycle 1.
      { (* RACY READ *)
        inv STEP; inv LOCAL. inv LOCAL0.
        iExFalso. iApply atomic_is_racy_impossible; eauto; iFrame.
      }
      { (* INACCESSIBLIE READ *)
        inv STEP; inv LOCAL.
        iExFalso. iApply atomic_is_inaccessible_impossible; eauto; iFrame.
      }
      (* VALID READ *)
      inv STEP; inv LOCAL. des_ifs. clear n.
      steps_r. rewrite /alist_upd /_alist_upd /=.
      (* 1. we don't need to update hist and points to *)
      (* 2. we do need to udpate seen *)
      (* 3. we do need to update 𝓥 *)
      iPoseProof (tview_both_valid with "TA TV") as "%F"; des; subst.
      rewrite F in Heq; inv Heq.

      iPoseProof (AtomicPtsToX_AtomicSeen_latest with "PT SEEN") as "%LE".

      rewrite AtomicPtsToX_eq /AtomicPtsToX_def /view_at.
      iDestruct "PT" as "[%ζhist [%Vna [-> [SYNC [HIST [AA AF]]]]]]".
      iPoseProof (hist_own_hist_cut with "HA HIST") as "[%loccut %FACTS]"; des.

      iAssert (⌜Time.le (View.rlx Vcut loc) ts⌝)%I with "[SEEN]" as "%LECUT".
      { inv LOCAL0. inv READABLE. rewrite AtomicSeen_eq /AtomicSeen_def /=.
        iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [AR [%GOODHIST [%Vna' [%VNATV NA]]]]]".
        destruct (classic (∃ ts' f' m', Cell.get ts' ζ' = Some (f', m'))) as [HEX|FAL]; cycle 1.
        { exfalso; apply GOODHIST, Cell.ext; i; rewrite Cell.bot_get.
          destruct (Cell.get ts0 ζ') eqn : GET'; ss.
          destruct p; exfalso; apply FAL; esplits; eauto.
        }
        destruct HEX as [ts' [f' [m' FOUND']]].
        hexploit (SEEN ts'); eauto; intros LC1.
        apply LE in FOUND'.
        rewrite Cell.cut_spec in FOUND'; des_ifs.
        iPureIntro.
        etrans; eauto. etrans; eauto.
      }

      destruct (Cell.get ts ζ') eqn:GETTS.
      { (* When it reads value from its last view, *)
        (* We don't need to update ζ'. *)

        iAssert (⌜Time.eq ts (View.rlx (TView.cur (Local.tview lc1)) loc)⌝)%I with "[SEEN]" as "%EQ".
        { rewrite AtomicSeen_eq /AtomicSeen_def /=.
          iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [AR [%GOODHIST [%Vna' [%VNATV NA]]]]]".
          hexploit SEEN; eauto; intros LE0.
          unfold seen_local in LE0.
          inv LOCAL0.
          inv READABLE.
          clear -RLX LE0. inv LE0; eauto. timetac.
        }

        iAssert (⌜Cell.max_ts ζ' = ts⌝)%I with "[SEEN]" as "%MAXTS".
        { rewrite AtomicSeen_eq /AtomicSeen_def /=.
          iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [AR [%GOODHIST [%Vna' [%VNATV NA]]]]]".
          iPureIntro.
          specialize (SEEN (Cell.max_ts ζ')).
          destruct p. hexploit Cell.max_ts_spec; eauto; i.
          des. hexploit SEEN; eauto; intros SEENLOCAL.
          rewrite /seen_local in SEENLOCAL. rewrite -EQ in SEENLOCAL.
          destruct SEENLOCAL; eauto. timetac.
        }

        iAssert (@{TView.cur (Local.tview lc2)} loc sn⊒{γ} ζ')%I
        with "[SEEN]" as "SEEN".
        { rewrite AtomicSeen_eq /AtomicSeen_def /=.
          iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [AR [%GOODHIST [%Vna' [%VNATV NA]]]]]".
          iFrame. rewrite /SeenLocal. iPureIntro; esplits; eauto.
          { inv LOCAL0; ss. do 2 eapply AllocView.join_l; eauto. }
          { i. inv LOCAL0; ss. hexploit SEEN; eauto; i. unfold seen_local in *.
            etrans; eauto. etrans; eapply View.join_l.
          }
          { inv LOCAL0; ss. etrans; eauto. etrans; eapply View.join_l. }
        }

        iMod ((tview_auth_update ths (IdentMap.add tid (existT lang st2, lc2) ths)) with "TA TV") as "[TA TV]"; eauto.

        remember ({[_ := _]}) as st_tgt.
        iAssert (Ist st_src st_tgt)%I with "[HA FA TA]" as "IST".
        { iFrame. iPureIntro; esplits; eauto.
          { hexploit (@PFConfiguration.step_future ThreadEvent.get_machine_event); eauto.
            { econs; eauto. econs; eauto.
              { econs 2; eauto. }
              econs. }
            i; des; eauto.
          }
          { i. destruct (decide (tid0 = tid)).
            { subst. rewrite IdentMap.gss in H3; inv H3.
              hexploit PFL; eauto; intros PF. inv PF; des.
              econs; inv LOCAL0; eauto. }
            { rewrite IdentMap.gso in H3; eauto. }
          }
        }

        inv LOCAL0; ss.
        force_l (v↑). steps_l. force_l (v↑). steps_l. force_l.
        iSplitR "IST".
        { rewrite AtomicPtsToX_eq /AtomicPtsToX_def /view_at.
          iFrame. iSplit; eauto. iExists from, na, v, val', released.
          iPureIntro; esplits; eauto; [refl| | |].
          { rewrite GETTS. f_equal.
            destruct p. unfold Cell.le in LE. eapply LE in GETTS.
            subst. rewrite Cell.cut_spec in GETTS.
            destruct (Time.le_lt_dec (View.rlx Vcut loc) (Cell.max_ts ζ')); ss.
            rewrite /Memory.get_cell in GETTS.
            rewrite /Memory.get /Block.get in GET.
            rewrite GETTS in GET. inv GET. eauto.
          }
          { etrans; eapply View.join_l. }
          { unfold TView.read_tview; ss.
            rewrite ORDRLX. des_ifs; eapply View.join_r.
          }
        }
        step. iSplit; eauto.
      }
      { (* When it reads value from global history, *)
        (* We need to update ζ'. *)
        dup STATE; dup LOCAL0.
        inv LOCAL0; ss. inv READABLE.
        remember (Message.message _ _ _) as msg.

        hexploit (@Cell.add_exists ζ' from ts msg); eauto.
        { intros ????. dup GET2. revert GET0. intros GET0%LE.
          rewrite Cell.cut_spec in GET0. 
          destruct (Time.le_lt_dec (View.rlx Vcut loc) to2); ss.
          eapply Cell.WF in GET0; eauto. ii.
          subst. rewrite GETTS in GET2. inv GET2.
        }
        { apply Cell.WF in GET; eauto. }
        i; des. rename cell2 into ζ''.

        iPoseProof (at_writer_base_fork_at_reader with "[AA]") as "#R".
        { iDestruct "AA" as "[W [EXW LNA]]". iFrame. }
        iPoseProof (at_reader_extract with "R") as "#RR".
        { instantiate (1:=ζ'').
          ii. destruct (decide (to = ts)).
          { subst. eapply Cell.add_get0 in H3. des.
            rewrite GET1 in LHS. inv LHS.
            rewrite Cell.cut_spec.
            destruct (Time.le_lt_dec (View.rlx Vcut loc) ts); ss.
            timetac.
          }
          { eapply Cell.add_o in H3. instantiate (1:=to) in H3.
            rewrite LHS in H3. destruct (TimeSet.Facts.eq_dec to ts); ss.
            unfold Cell.le in LE. hexploit LE; eauto.
          }
        }
        iClear "R".

        set (lc2 := _: Local.t) at 4.
        iAssert (@{TView.cur (Local.tview lc2)} loc sn⊒{γ} ζ'')%I with "[RR SEEN]" as "SEEN".
        { rewrite AtomicSeen_eq /AtomicSeen_def /=.
          iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [_ [%GOODHIST [%Vna' [%VNATV NA]]]]]".
          iFrame "RR NA". rewrite /SeenLocal. iPureIntro; esplits; eauto.
          { do 2 eapply AllocView.join_l; eauto. }
          { i. destruct (decide (t0 = ts)).
            { subst. rewrite /seen_local.
              set (V := View.join _ _).
              enough (View.le (View.singleton loc ts) V).
              { subst V. inv H5. ss.
                eapply TimeMap.singleton_inv. ii.
                specialize (RLX0 loc0). eauto.
              }
              { subst V. etrans; cycle 1. 
                { eapply View.join_l. }
                eapply View.join_r.
              }
            }
            { eapply Cell.add_o in H3. instantiate (1:=t0) in H3.
              rewrite /is_Some in H4. des. destruct x. rewrite H4 in H3.
              destruct (TimeSet.Facts.eq_dec t0 ts); ss.
              hexploit SEEN; eauto; i. unfold seen_local in *.
              etrans; eauto. etrans; eapply View.join_l.
            }
          }
          { unfold good_absHist in *. ii. subst. inv H3.
            ss. assert (EX: None = Some (from, Message.message val' released na)).
            { rewrite -(Cell.bot_get ts) /Cell.bot /Cell.get /= CELL2.
              rewrite DOMap.gsspec.
              destruct (DOMap.Properties.F.eq_dec ts ts); ss.
            }
            inv EX.
          }
          { etrans; eauto. etrans; eapply View.join_l. }
        }

        assert (GETTS0: Cell.get ts ζ'' = Some (from, msg)).
        { inv H3; eauto. rewrite /Cell.get CELL2 DOMap.gsspec.
          destruct (DOMap.Properties.F.eq_dec ts ts); ss.
        }

        assert (LEREL: View.rlx released loc ⊑ ts).
        { subst. inv WF. inv GL_WF. inv MEM_CLOSED. hexploit CLOSED; eauto.
          i; des; ss. inv MSG_TS. eauto. }
        
        assert (LEREL2: (View.rlx (View.join (View.join (TView.cur (Local.tview lc1)) (View.singleton loc ts)) (if Ordering.le Ordering.acqrel ord then released else View.bot)) loc) ⊑ ts).
        { ss. rewrite !/TimeMap.join. eapply Time.join_spec.
          { eapply Time.join_spec; eauto.
            hexploit (@TimeMap.singleton_spec loc ts (λ _, ts)); eauto; refl.
          }
          { destruct (Ordering.le Ordering.acqrel ord); ss. eapply Time.bot_spec. }
        }

        iAssert (⌜Time.eq ts (View.rlx (TView.cur (Local.tview lc2)) loc)⌝)%I with "[SEEN]" as "%EQ".
        { rewrite AtomicSeen_eq /AtomicSeen_def /=.
          iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [AR [%GOODHIST [%Vna' [%VNATV NA]]]]]".
          hexploit SEEN; eauto; intros LE0.
          unfold seen_local in LE0.
          clear -LEREL2 LE0.
          inv LE0; eauto. inv LEREL2; eauto. timetac.
        }
        
        iAssert (⌜Cell.max_ts ζ'' = ts⌝)%I with "[SEEN]" as "%MAXTS".
        { rewrite AtomicSeen_eq /AtomicSeen_def /=.
          iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [AR [%GOODHIST [%Vna' [%VNATV NA]]]]]".
          iPureIntro.
          specialize (SEEN (Cell.max_ts ζ'')).
          hexploit Cell.max_ts_spec; eauto; i.
          des. hexploit SEEN; eauto; intros SEENLOCAL.
          rewrite /seen_local in SEENLOCAL. rewrite -EQ in SEENLOCAL.
          destruct SEENLOCAL; eauto. timetac.
        }

        iMod ((tview_auth_update ths (IdentMap.add tid (existT lang st2, lc2) ths)) with "TA TV") as "[TA TV]"; eauto.

        remember ({[_ := _]}) as st_tgt.
        iAssert (Ist st_src st_tgt)%I with "[HA FA TA]" as "IST".
        { iFrame. iPureIntro; esplits; eauto.
          { hexploit (@PFConfiguration.step_future ThreadEvent.get_machine_event); eauto.
            { econs; eauto. econs; eauto.
              { econs 2.
                { instantiate (2:=(ThreadEvent.read loc ts v released ord)); eauto. }
                eauto.
              }
              { econs. }
            }
            i; des; eauto.
          }
          { i. destruct (decide (tid0 = tid)).
            { subst. rewrite IdentMap.gss in H4; inv H4.
              hexploit PFL; eauto. }
            { rewrite IdentMap.gso in H4; eauto. }
          }
        }

        force_l (v↑). steps_l. force_l (v↑). steps_l. force_l.
        iSplitR "IST".
        { rewrite AtomicPtsToX_eq /AtomicPtsToX_def /view_at.
          iFrame. iSplit; eauto. iExists from, na, v, val', released.
          iPureIntro; esplits; eauto.
          { intros ??? GET0. eapply Cell.add_get1; eauto. }
          { intros ??? GET0. destruct (decide (to = Cell.max_ts ζ'')).
            { subst.
              rewrite Cell.cut_spec.
              destruct (Time.le_lt_dec (View.rlx Vcut loc) (Cell.max_ts ζ'')); timetac.
              rewrite GETTS0 in GET0. inv GET0.
              rewrite /Memory.get_cell in GET.
              rewrite /Memory.get /Block.get in GET.
              rewrite /Memory.get_cell. rewrite GET. eauto.
            }
            { subst ts. eapply Cell.add_o with (t:= to) in H3.
              destruct (TimeSet.Facts.eq_dec to (Cell.max_ts ζ'')); ss.
              rewrite H3 in GET0.
              unfold Cell.le in LE. eapply LE in GET0.
              rewrite Cell.cut_spec in GET0.
              destruct (Time.le_lt_dec (View.rlx Vcut loc) to) eqn:L; ss.
              rewrite Cell.cut_spec. rewrite L. eauto.
            }
          }
          { subst ts; eauto. rewrite GETTS0. subst msg; ss. }
          { etrans; eapply View.join_l. }
          { unfold TView.read_tview; ss.
            rewrite ORDRLX. destruct (Ordering.le Ordering.acqrel ord); ss;
            eapply View.join_r.
          }
        }
        step. iSplit; eauto.
      }
    }
  (*SLOW*)Qed.
End read.