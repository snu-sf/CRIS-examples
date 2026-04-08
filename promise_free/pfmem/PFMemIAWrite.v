Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import PFMemIAproof.

Section write.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  Lemma simF_write : ISim.sim_fun open MA MI Ist (fid PFMemHdr.write).
  Proof.
    cStartFunSim.
    cStepS. destruct _q as [p|[p|[]]].
    { (* non-atomic write *)
      destruct p as [[[[tid loc] val] ord] 𝓥]. cStepsS.
      iDestruct "ASM" as "[-> [-> [PT TV]]]". cSimpl.
      iDestruct "IST" as "[%gl [%ths [%Vcut [[-> [%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]]] [HA [TA FA]]]]]]".
      cStepsT. cStepsT.
      rewrite /PFMemI.check_ident.
      des_ifs; last (iPoseProof (tview_both_valid with "TA TV") as "%F"; des; ss; clarify).
      cStepsT. destruct _q as [[e config'] [EVWRITE STEP]].
      destruct e; inv EVWRITE; inv STEP; clear EVENT; rename STEP0 into STEP; s in STEP; cycle 1.
      { (* RACY WRITE *)
        inv STEP; inv LOCAL. inv LOCAL0. inv RACE.
        { inv PFG; rewrite H in GET; ss. }
        iPoseProof (tview_both_valid with "TA TV") as "%IN".
        destruct IN as [l [lc [FOUND LCEQ]]].
        s; rewrite FOUND in Heq; inv Heq.
        rewrite own_loc_eq /own_loc_def.
        iDestruct "PT" as "[%f [%t [%LT [%msg [%ALLOC_LOCAL HIST]]]]]".
        iPoseProof (hist_own_hist_cut with "HA HIST") as "[%tcut [<- [%CELL_CUT %ACC]]]".
        destruct ALLOC_LOCAL as [ALLOC_VIEW [t' [(from', msg') [CELL_GET SEEN_LOCAL]]]].
        assert (CELL_GET' := CELL_GET); ss.
        rewrite Cell.singleton_get in CELL_GET; des_ifs.
        rewrite CELL_CUT Cell.cut_spec in CELL_GET'; des_ifs.
        assert (LECUT: Time.lt (View.rlx Vcut loc) to0).
        { inv SEEN_LOCAL.
          { ett. eapply l. etrans; eauto. }
          { ett. eapply l. inv H; eauto. }
        }
        assert (CUT_GET: Cell.get to0 (Cell.singleton msg' LT) = Some (from, Message.message val0 released na)).
        { rewrite CELL_CUT Cell.cut_spec; des_ifs; timetac. }
        rewrite Cell.singleton_get in CUT_GET.
        exfalso.
        eapply (TimeFacts.le_not_lt to0 (View.rlx (TView.TView.cur (Local.tview lc2)) loc)); eauto; des_ifs.
      }
      { (* INACCESSIBLIE WRITE *)
        ss. inv STEP; inv LOCAL.
        iPoseProof (tview_both_valid with "TA TV") as "[% [% [%FIND <-]]]".
        rewrite own_loc_eq /own_loc_def.
        iDestruct "PT" as "[%f [%t [%LT [%msg [%ALLOC_LOCAL HIST]]]]]".
        iPoseProof (hist_own_hist_cut with "HA HIST") as "[%tcut [<- [%CELL_CUT %ACC]]]".
        destruct ALLOC_LOCAL as [ALLOC_VIEW [t' [(from', msg') [CELL_GET SEEN_LOCAL]]]].
        exfalso; inv RACE; try done.
        hexploit (PFL tid); eauto; clear PFL; intros PFL.
        inv PFL; inv PFG.
        des; rewrite H2 H3 in FREEPROMISE.
        rewrite Promises.FreePromises.minus_bot in FREEPROMISE. inv FREEPROMISE.
      }
      (* VALID WRITE *)
      inv STEP; inv LOCAL. des_ifs. clear n.
      cStepsT.
      iPoseProof (tview_both_valid with "TA TV") as "%F"; des; subst.
      rewrite F in Heq; inv Heq.
      rewrite own_loc_eq /own_loc_def.
      iDestruct "PT" as "[%f [%t [%LT [%msg [%ALLOC_LOCAL HIST]]]]]".
      destruct ALLOC_LOCAL as [ALLOC_VIEW [t' [(from', msg') [CELL_GET SEEN_LOCAL]]]].
      iPoseProof (hist_own_hist_cut with "HA HIST") as "[%tcut [<- [%CELL_CUT %ACC]]]".

      assert (CELL_GET' := CELL_GET).
      rewrite Cell.singleton_get in CELL_GET; des_ifs.
      rewrite CELL_CUT Cell.cut_spec in CELL_GET'; des_ifs.

      assert (TTO: Time.lt t to).
      { inv LOCAL0. inv SEEN_LOCAL; inv WRITABLE.
        { etrans; eauto. }
        { rewrite H. auto. }
      }

      assert (AFTER: Time.lt (View.rlx Vcut loc) to).
      { eapply TimeFacts.le_lt_lt; eauto. }

      assert (FT: Time.lt from to).
      { inv LOCAL0; inv WRITE; inv ADD; inv ADD0; ss. }

      (* update resources *)
      iMod (hist_auth_write_non_atomic with "HA HIST") as "[HA HIST]"; ss; eauto.
      iPoseProof (tview_auth_update with "TA TV") as "> [TA TV]"; ss.
      instantiate (1:=lc2). instantiate (1:=st2).
      iMod (hist_freeable_auth_write with "FA") as "FA"; eauto. { inv WF; ss. }
      remember (IdentMap.add _ _ _) as ths2.

      iAssert (Ist st_src _) with "[HA TA FA]" as "IST".
      { iExists gl2, ths2, (View.join (View.singleton loc to) Vcut). iFrame "HA". iSplitR.
        { iPureIntro; esplits; eauto.
          { intros loc' ???? GET.
            inv LOCAL0.
            hexploit Memory.add_o; eauto.
            instantiate (1:=t0). instantiate (1:=loc').
            des_ifs.
            { ss; des; clarify.
              rewrite GET; intros HH; inv HH; revert H3; destruct ord; ss.
              i. rewrite /TimeMap.join /Time.join /TimeMap.singleton /LocFun.add; des_ifs.
              rewrite Time.le_lteq; right; auto.
            }
            intros GET'; rewrite GET' in GET.
            eapply CUT in GET.
            destruct (decide (loc = loc')); subst.
            { hexploit GET; [eauto|clear GET; intros GET].
              i; rewrite /View.join /View.singleton /TimeMap.join /TimeMap.singleton /Time.join /LocFun.add; ss; des_ifs.
              etrans. eauto. timetac. }
            { i; hexploit GET; [eauto|clear GET; intros GET].
              { erewrite <-Memory.add_accessible; eauto. }
              rewrite /View.join /View.singleton /TimeMap.join /TimeMap.singleton /Time.join /LocFun.add; ss; des_ifs.
              rewrite /LocFun.find /LocFun.init in l0. timetac. }
          }
          { eapply Memory.join_closed_view; eauto; cycle 1.
            { eapply Memory.add_closed_view; eauto; inv LOCAL0; eauto. }
            { inv LOCAL0. econs; i; ss.
              { i; ss. destruct (decide (loc0 = loc)); subst; [right | left]; ss.
                { eapply Memory.add_get0 in WRITE; des. 
                  rewrite /TimeMap.singleton /LocFun.add; des_ifs; ss.
                  exists from, val; eexists; eexists; apply GET0.
                }
                { rewrite /TimeMap.singleton /LocFun.add; des_ifs. }
              }
              { destruct (decide (loc0 = loc)); subst; cycle 1.
                { i; ss. rewrite /TimeMap.singleton /LocFun.add; des_ifs. }
                { exfalso. eapply Memory.prealloced_is_not_accessible; cycle 1.
                  eapply ACC.
                  exploit Memory.add_preserve; eauto. i. des.
                  rewrite /Memory.is_prealloced /Block.is_prealloced in H.
                  rewrite /Memory.get_state in GET_STATE.
                  rewrite (GET_STATE loc) in H; ss.
                }
              }
            }
          }
          { eapply PFConfiguration.estep_future; eauto. subst ths2. econs; eauto.
            { econs; eauto. ss. }
            ss.
          }
          { inv WF. inv GL_WF. inv LOCAL0. eapply wf_prealloc_write; eauto. }
          { inv PFG. inv LOCAL0; econs; ss. inv FULFILL. done. rewrite H in GREMOVE.
            hexploit (Promises.Promises.remove_le); eauto.
            intros ?; hexploit (Promises.Promises.antisym); eauto using Promises.Promises.bot_spec.
          }
          { intros tid' ?? LC; destruct (decide (tid' = tid)); try subst tid'.
            { subst ths2; rewrite IdentMap.gss in LC; inv LC.
              hexploit (PFL tid); eauto using F.
              intros PFL'; inv PFL'; inv LOCAL0; econs; ss.
              inv FULFILL; ss.
              hexploit (Promises.Promises.remove_le); first apply REMOVE. rewrite H.
              intros ?; hexploit (Promises.Promises.antisym); eauto using Promises.Promises.bot_spec.
            }
            { subst ths2; rewrite IdentMap.gso in LC; ss.
              eapply PFL; eauto.
            }
          }
        }
        iFrame.
      }

      cForceS (Val.zero↑). cStepsS. cForceS (Val.zero↑). cStepsS. cForceS.
      iSplitR "IST".
      { iFrame. iSplit; eauto.
        iSplit; eauto.
        { iPureIntro; split; ss. inv LOCAL0; ss; eapply TViewFacts.write_tview_incr; eauto.
          inv WF; ss. inv WF0; eauto. hexploit THREADS; eauto. intros INV; inv INV; ss.
        }
        rewrite own_loc_na_eq /own_loc_na_def /view_at.
        iExists from, to, _, (TView.write_released (Local.tview lc1) loc to View.bot ord), (Ordering.le ord Ordering.na).
        iSplit.
        { iSplit; iFrame.
          iPureIntro; rewrite /alloc_local; split.
          { inv LOCAL0; ss. eapply AllocView.join_l; eauto. }
          { inv LOCAL0; eexists to, (from, Message.message val _ _).
            rewrite Cell.singleton_get; des_ifs.
            rewrite /seen_local. rewrite /View.join /= /TimeMap.join.
            rewrite /TimeMap.singleton /LocFun.add; des_ifs; ss.
            split; ss.
            etrans; last apply Time.join_r; done.
          }
        }
        { iPureIntro. inv LOCAL0.
          rewrite /TView.TView.write_released View.join_bot_l /TView.TView.write_tview /=.
          rewrite /LocFun.add; des_ifs.
          eapply View.join_le; last refl.
          inv WF. inv WF0; ss. hexploit (THREADS tid); eauto.
          intros LWF; inv LWF. inv TVIEW_WF; ss.
          apply View.bot_spec.
        }
      }
      cStepsS. cStep. iFrame. done.
      Unshelve. exact.
    }
    (* Atomic write *)
    { destruct p as [[[[[[[[[[[[tid loc] val] ord] 𝓥] γ] ζ'] Vb] tx] ζ] mode] q] tx']. cStepsS.
      iDestruct "ASM" as "[-> [[-> %ORDRLX] [SEEN [PT [TV WRITE]]]]]". cSimpl.
      iDestruct "IST" as "[%gl [%ths [%Vcut [[-> [%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]]] [HA [TA FA]]]]]]".
      cStepsT. cStepsT.
      rewrite /PFMemI.check_ident.
      des_ifs; last (iPoseProof (tview_both_valid with "TA TV") as "%F"; des; ss; clarify).
      cStepsT. destruct _q as [[e config'] [EVWRITE STEP]].
      destruct e; inv EVWRITE; inv STEP; clear EVENT; rename STEP0 into STEP; s in STEP; cycle 1.
      { (* RACY WRITE *)
        inv STEP; inv LOCAL. inv LOCAL0. inv RACE.
        { inv PFG; rewrite H in GET; ss. }
        hexploit MSG; eauto; intros ->; clear MSG.
        iPoseProof (tview_both_valid with "TA TV") as "%IN".
        destruct IN as [l [lc [FOUND LCEQ]]].
        s; rewrite FOUND in Heq; inv Heq.
        rewrite AtomicPtsToX_eq /AtomicPtsToX_def /view_at.
        iDestruct "PT" as "[%ζhist [%Vna [-> [SYNC [HIST [AA AF]]]]]]".
        rewrite AtomicSeen_eq /AtomicSeen_def.
        iDestruct "SEEN" as "[[_ %SEEN] [AR [%GOODHIST [%Vna' [_ NA]]]]]".
        iPoseProof (at_auth_at_last_na_agree with "AA NA") as "<-".
        iPoseProof (hist_own_hist_cut with "HA HIST") as "[%t [<- [%eqcut %]]]".
        iDestruct "AA" as "[AA [AEXCLWRITE _]]".
        iPoseProof (at_writer_base_latest with "AA AR") as "%LE".
        destruct (classic (∃ ts' f' m', Cell.get ts' ζ' = Some (f', m'))) as [HEX|FAL]; cycle 1.
        { exfalso; apply GOODHIST, Cell.ext; i; rewrite Cell.bot_get.
          destruct (Cell.get ts ζ') eqn : GET'; ss. destruct p; exfalso; apply FAL; esplits; eauto.  
        }
        destruct HEX as [ts' [f' [m' FOUND']]].
        exfalso.
        hexploit (SEEN ts'); ss; intros TS.
        eapply (TimeFacts.le_not_lt to0 (View.rlx (TView.TView.cur (Local.tview lc2)) loc)); eauto.
        hexploit (CUT loc to0); eauto => LECUT.
        etrans; first apply LECUT.
        etrans; last apply TS.
        hexploit (LE ts'); eauto; intros ZETA.
        rewrite eqcut Cell.cut_spec in ZETA; des_ifs.
      }
      { (* INACCESSIBLE WRITE *)
        ss. inv STEP; inv LOCAL.
        iPoseProof (tview_both_valid with "TA TV") as "[% [% [%FIND <-]]]".
        rewrite AtomicPtsToX_eq /AtomicPtsToX_def {2}/view_at.
        iDestruct "PT" as "[%ζhist [%Vna [-> [SYNC [HIST [AA AF]]]]]]".
        iPoseProof (hist_own_hist_cut with "HA HIST") as "[%t [%WFHIST [%ZETACUT %ACC]]]".
        rewrite AtomicSeen_eq /AtomicSeen_def.
        iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [AR [%GOODHIST [%Vna' [%VNATV NA]]]]]". ss.
        exfalso; inv RACE; try done.
        hexploit (PFL tid); eauto; clear PFL; intros PFL.
        inv PFL; inv PFG.
        des; rewrite H2 H3 in FREEPROMISE.
        rewrite Promises.FreePromises.minus_bot in FREEPROMISE. inv FREEPROMISE.
      }
      (* VALID WRITE *)
      inv STEP; inv LOCAL. des_ifs. clear n.
      cStepsT.
      iPoseProof (AtomicPtsToX_AtomicSeen_latest with "PT SEEN") as "%LE".
      rewrite AtomicPtsToX_eq /AtomicPtsToX_def {2}/view_at.
      iDestruct "PT" as "[% [% [-> [[%SYNC %SYNC2] [HIST [AA AW]]]]]]". ss.
      iPoseProof (tview_both_valid with "TA TV") as "[% [% [%EQ <-]]]".
      iPoseProof (hist_own_hist_cut with "HA HIST") as "[%loccut %FACTS]".
      rewrite EQ in Heq; inv Heq.
      rewrite /view_at AtomicSeen_eq /AtomicSeen_def.
      iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [AR [%GOODHIST [%Vna' [%VNATV #NA]]]]]".
      assert (LECUT : Time.le (View.rlx Vcut loc) to).
      { inv LOCAL0; ss. inv WRITABLE; ss.
        destruct (classic (∃ ts' f' m', Cell.get ts' ζ' = Some (f', m'))) as [HEX|FAL]; cycle 1.
        { exfalso; apply GOODHIST, Cell.ext; i; rewrite Cell.bot_get.
          destruct (Cell.get ts ζ') eqn : GET'; ss. destruct p; exfalso; apply FAL; esplits; eauto.  
        }
        destruct HEX as [ts' [f' [m' FOUND']]].
        hexploit (SEEN ts'); eauto; intros LC1.
        apply LE in FOUND'.
        destruct FACTS as [-> [-> _]].
        rewrite Cell.cut_spec in FOUND'; des_ifs.
        etrans; eauto. etrans; eauto. left. done.
      }
      (* update history resources *)
      iMod (hist_auth_write_vs with "HA HIST") as "[%ζn [%ADD [HA HIST]]]"; eauto.
      remember (Message.message val _ _) as msg.
      hexploit (@Cell.add_exists ζ' from to msg); eauto.
      { intros ??? GET%LE; inv ADD. eapply DISJOINT; eauto. }
      { inv ADD; ss. }
      subst msg. intros [ζ'' ADD''].
      rewrite /PFMemA.PFMemA.own_writer.
      set txn := if mode is SingleWriter then to else tx'.
      set txn' := if mode is SingleWriter then to else tx'.
      assert (Cell.le ζ'' ζn).
      { intros ??? GET; erewrite Cell.add_o in GET; eauto; des_ifs.
        { erewrite Cell.add_o; eauto; des_ifs. }
        erewrite Cell.add_o; eauto; des_ifs; ss.
        by apply LE.
      }
      iAssert ( |==>
        at_auth γ ζn txn Va ∗
        match mode with
        | SingleWriter => True
        | CASOnly => at_writer γ ζn
        | ConcurrentWriter => at_writer γ ζn ∗ at_exclusive_write γ txn 1
        end ∗
        PFMemA.PFMemA.own_writer γ mode q ζ'' txn' ∗ at_reader γ ζ'')%I
        with "[AA AW WRITE]" as ">(SA' & SW' & W' & #SR')".
      { destruct mode; subst txn txn'; ss.
        (* SingleWriter *)
        { iDestruct "WRITE" as "[ATW ATEXW]".
          iPoseProof (at_auth_at_writer_exact with "AA ATW") as "<-".
          iPoseProof (at_full_auth_exclusive_write_agree with "AA ATEXW") as "<-". iFrame.
          iDestruct "AA" as "[AA1 [AA2 AA3]]".
          iMod (at_writer_update _ _ ζn with "[$] [$]") as "[? ?]"; eauto.
          { intros ????; hexploit Cell.add_get1; first apply ADD; eauto. }
          iPoseProof (at_exclusive_write_update with "AA2 ATEXW") as "> [??]"; iFrame.
          assert (ζn = ζ''); subst.
          { apply Cell.ext; intros ts.
            erewrite (@Cell.add_o ζn ζ), (@Cell.add_o ζ'' ζ); eauto; des_ifs; ss.
          }
          iPoseProof (at_writer_fork_at_reader with "[$]") as "#?". iFrame.
          done.
        }
        (* CasOnly *)
        { iPoseProof (at_full_auth_exclusive_write_agree with "AA WRITE") as "->". iFrame.
          iDestruct "AA" as "[AA1 [AA2 AA3]]".
          iMod (at_writer_update _ _ ζn with "[$] [$]") as "[? ?]"; eauto.
          { intros ????; hexploit Cell.add_get1; first apply ADD; eauto. }
          iPoseProof (at_writer_fork_at_reader with "[$]") as "#?". iFrame.
          iModIntro; iApply (at_reader_extract with "[$]"). done.
        }
        (* ConcurrentWriter *)
        { iDestruct "AW" as "[AW1 AW2]".
          iDestruct "AA" as "[AA1 [AA2 AA3]]". 
          iMod (at_writer_update _ _ ζn with "[$] [$]") as "[? ?]"; eauto.
          { intros ????; hexploit Cell.add_get1; first apply ADD; eauto. }
          iPoseProof (at_writer_fork_at_reader with "[$]") as "#?". iFrame.
          iPoseProof (at_exclusive_write_update with "AA2 AW2") as "> [??]"; iFrame.
          iModIntro; iApply (at_reader_extract with "[$]"). done.
        }
      }
      iAssert (@{TView.TView.cur (Local.tview lc2)} loc sn⊒{γ} ζ'')%I with "[]" as "T".
      { rewrite /view_at AtomicSeen_eq /AtomicSeen_def. iFrame. iFrame "SR'". iSplit.
        { rewrite /SeenLocal.
          iPureIntro. split.
          { inv LOCAL0; ss. rewrite AllocView.join_bot_r.
            inv WRITABLE; ss.
          }
          intros t; erewrite Cell.add_o; eauto. des_ifs; ss.
          { intros _. inv LOCAL0; ss; rr. rewrite /View.join /= /TimeMap.join /TimeMap.singleton.
            rewrite /LocFun.add; des_ifs; ss; eauto using Time.join_r.
          }
          intros SOME; rr; etrans; first eapply SEEN; eauto.
          inv LOCAL0; ss; rewrite /TimeMap.join; eauto using Time.join_l.
        }
        iFrame "NA".
        iPureIntro; split.
        { ii. hexploit Cell.add_get0; eauto. intros [_ FAL].
          clarify; rewrite Cell.bot_get in FAL; ss.
        }
        etrans; eauto.
        inv LOCAL0; ss. apply View.join_l.
      }
      iPoseProof (tview_auth_update with "TA TV") as "> [TA TV]"; ss.
      instantiate (1:=lc2). instantiate (1:=st2).
      iMod (hist_freeable_auth_write with "FA") as "FA"; eauto. { inv WF; ss. }
      remember (IdentMap.add _ _ _) as ths2.
      iAssert (Ist st_src _) with "[HA TA FA]" as "IST".
      { iExists gl2, ths2, _. iFrame "HA". iSplitR.
        { iPureIntro; esplits; eauto.
          { intros loc' ???? GET.
            inv LOCAL0.
            hexploit Memory.add_o; eauto.
            instantiate (1:=t). instantiate (1:=loc').
            des_ifs.
            { ss; des; clarify. rewrite GET; intros HH; inv HH; revert ORDRLX H4; destruct ord; ss. }
            intros GET'; rewrite GET' in GET.
            i; eapply CUT; eauto.
            erewrite <- Memory.add_accessible; eauto.
          }
          { eapply Memory.add_closed_view; eauto. inv LOCAL0; eauto. }
          { eapply PFConfiguration.estep_future; eauto. subst ths2. econs; eauto.
            { econs; eauto. ss. }
            ss.
          }
          { inv WF. inv GL_WF. inv LOCAL0. eapply wf_prealloc_write; eauto. }
          { inv PFG. inv LOCAL0; econs; ss. inv FULFILL. done. rewrite H0 in GREMOVE.
            hexploit (Promises.Promises.remove_le); eauto.
            intros ?; hexploit (Promises.Promises.antisym); eauto using Promises.Promises.bot_spec.
          }
          { intros tid' ?? LC; destruct (decide (tid' = tid)); try subst tid'.
            { subst ths2; rewrite IdentMap.gss in LC; inv LC.
              hexploit (PFL tid); eauto using EQ.
              intros PFL'; inv PFL'; inv LOCAL0; econs; ss.
              inv FULFILL; ss.
              hexploit (Promises.Promises.remove_le); first apply REMOVE. rewrite H0.
              intros ?; hexploit (Promises.Promises.antisym); eauto using Promises.Promises.bot_spec.
            }
            { subst ths2; rewrite IdentMap.gso in LC; ss.
              eapply PFL; eauto.
            }
          }
        }
        iFrame.
      }
      (* update points-to resources *)
      iAssert ( |==> @{Vb ⊔ View.join (TView.TView.cur (Local.tview lc1)) (View.singleton loc to)}
        (AtomicPtsToX loc γ txn ζn mode)
        ∗ (PFMemA.PFMemA.own_writer γ mode q ζ'' txn
        ))%I
      with "[AR SA' HIST SW' W']" as "> [PTS OW]".
      { iAssert (SyncLocal loc ζn (Vb ⊔ View.join (TView.TView.cur (Local.tview lc1))
          (View.singleton loc to)))%I as "#SYNC'".
        { rewrite /SyncLocal; iPureIntro; ss. split.
          { split.
            { rewrite AllocView.join_bot_r /AllocView.join; des_ifs; rewrite /orb; des_ifs. }
            intros t; erewrite Cell.add_o; eauto; des_ifs.
            { intros _; rewrite /seen_local /View.join /= /TimeMap.join.
              do 2 (etrans; last apply Time.join_r).
              rewrite /TimeMap.singleton /LocFun.add; des_ifs.
            }
            intros SOME%SYNC; rr; etrans; first apply SOME.
            rewrite /View.join /=; eapply Time.join_l.
          }
          intros ts; destruct (decide (ts = to)); subst.
          { erewrite Cell.add_o; eauto; des_ifs; intros ???? INV; inv INV.
            split.
            { rewrite /seen_local /View.join /= /TimeMap.join.
              do 2 (etrans; last apply Time.join_r).
              rewrite /TimeMap.singleton /LocFun.add; des_ifs.
            }
            { etrans; last apply View.join_r.
              rewrite /TView.TView.write_released ORDRLX View.join_bot_l.
              rewrite /TView.TView.write_tview /= /LocFun.add; des_ifs.
              eapply View.join_le; last refl.
              inv WF. inv GL_WF. ss. inv WF0. hexploit THREADS; eauto.
              intros INV; inv INV; apply TVIEW_WF.
            }
          }
          erewrite Cell.add_o; eauto; des_ifs.
          intros ?????; hexploit SYNC2; eauto; intros [??]; split.
          { rr; etrans; first done. rewrite /View.join /= /TimeMap.join; eauto using Time.join_l. }
          etrans; eauto; eapply View.join_l.
        }
        rewrite AtomicPtsToX_eq /AtomicPtsToX_def /view_at.
        rewrite /PFMemA.PFMemA.own_writer; destruct mode; subst txn.
        { iFrame. iModIntro; iFrame. iSplit; auto.  }
        { iFrame. iModIntro; iFrame. iSplit; auto. }
        { iModIntro; iFrame. iSplit; auto. }
      }
      cForceS (Val.zero ↑). cStepsS. cForceS (Val.zero ↑). cStepsS. cForceS.
      iSplitR "IST".
      { iSplit; first done.
        unshelve (iExists from, to, _, (TView.TView.write_released (Local.tview lc1) loc to View.bot ord)).
        { inv ADD; ss. }
        s. iExists ζ'', ζn. iSplit.
        { iPureIntro. split; auto.
          split.
          { inv LOCAL0. inv WRITABLE. eapply TimeFacts.le_lt_lt; last apply TS.
            destruct (classic (∃ ts' f' m', Cell.get ts' ζ' = Some (f', m'))) as [HEX|FAL]; cycle 1.
            { exfalso; apply GOODHIST, Cell.ext; i; rewrite Cell.bot_get.
              destruct (Cell.get ts ζ') eqn : GET'; ss. destruct p; exfalso; apply FAL; esplits; eauto.  
            }
            destruct HEX as [ts' [f' [m' FOUND']]].
            hexploit Cell.max_ts_spec; eauto.
            intros [GET _]; des; apply SEEN; eauto.
          }
          split.
          { des_ifs.
            { rewrite /TView.TView.write_released; des_ifs.
              rewrite View.join_bot_l /= Heq /= /LocFun.add; des_ifs.
            }
            split.
            { rewrite /TView.TView.write_released ORDRLX View.join_bot_l /TView.TView.write_tview /=.
              rewrite /LocFun.add; des_ifs; eapply View.join_l.
            }
            { rewrite /TView.TView.write_released ORDRLX View.join_bot_l /TView.TView.write_tview /=.
            rewrite Heq /LocFun.add; des_ifs.
            eapply View.join_le; last refl.
            inv WF. inv WF0; ss. hexploit (THREADS tid); eauto.
            intros LWF; inv LWF. inv TVIEW_WF; ss.
            }
          }
          split; destruct ord; ss.
        }
        iSplitL "T".
        { inv LOCAL0; ss. }
        iFrame.
        iSplitR.
        { rewrite /view_at AtomicSync_eq /AtomicSync_def /=. iFrame "NA". iSplit.
          { iApply SeenLocal_SyncLocal_singleton.
            { iPureIntro; rewrite /TView.TView.write_released ORDRLX View.join_bot_l.
              rewrite /TView.TView.write_tview /= /LocFun.add; des_ifs.
              apply View.join_le; last refl.
              inv WF; inv GL_WF; inv WF0; hexploit THREADS; eauto; intros INV; inv INV; inv TVIEW_WF; ss.
            }
            rewrite /SeenLocal /= AllocView.join_bot_r.
            iPureIntro; split; ss.
            intros t; rewrite Cell.singleton_get; des_ifs; last (intros INV; inv INV).
            rewrite /seen_local; intros _; rewrite /View.join /= /TimeMap.join.
            rewrite /TimeMap.singleton /LocFun.add; des_ifs; ss.
            etrans; last apply Time.join_r; done.
          }
          iSplit.
          { iApply (at_reader_extract with "SR'").
            intros ???; rewrite Cell.singleton_get; des_ifs; intros INV; inv INV.
            erewrite Cell.add_o; eauto; des_ifs; repeat f_equal.
            destruct ord; ss.
          }
          iPureIntro; split.
          { intros Heq; hexploit (Cell.bot_get to); rewrite -Heq Cell.singleton_get; des_ifs. }
          { etrans; eauto. apply View.join_l. }
        }
        inv LOCAL0; ss.
      }
      cStepsS. cStep. iFrame. done.
    }
  (*SLOW*)Qed.
End write.
